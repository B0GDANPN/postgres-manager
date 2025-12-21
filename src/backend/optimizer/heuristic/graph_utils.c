#include "postgres.h"
#include "c.h"
#include "nodes/bitmapset.h"
#include "nodes/pathnodes.h"
#include <limits.h>
#include <stddef.h>
#include <string.h>
#include "optimizer/heuristic/graph_utils.h"
#include "nodes/nodes.h"
#include "nodes/pg_list.h"
#include "optimizer/heuristic/counter.h"
#include "optimizer/joininfo.h"
#include "optimizer/paths.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include <float.h>
#include <optimizer/cost.h>
#include "optimizer/restrictinfo.h"
#include "utils/lsyscache.h"

static const uint64 dphyp_geqo_cc_threshold = 10000;
static const double THRESH = 0.9;
static const Selectivity border_selectivity = 0.4;
static const int max_ray_length = 3;

static void set_complexity_topology(PlannerInfo *root, Topology *topology);
static List *dfs_component(Vertex *v, List *comp, bool *used_vertexes);
static List *dfs_cycle(PlannerInfo *root, Vertex *prev, Vertex *cur, List *stack, List *cycles,
		       bool *visited,
		       bool *used_vertexes_comp); // stack is list of Vertex*
static bool is_star(Vertex *center, const bool *used_vertexes);
static List *find_star(PlannerInfo *root, Vertex *center, bool *used_vertexes, List *chains);
static void print_graph(PlannerInfo *root, List *graph);
static Vertex *find_min_degree_vertex(List *sub);
static double density(List *sub);
static int count_edges(List *sub);

/**
 * @brief Check whether two relations have a legal simple join edge.
 *
 * Uses join clause and join order restriction checks while excluding overlap.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return True if a simple inner edge exists between the relations.
 */
bool has_simple_inner_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	bool a = bms_overlap(rel1->relids, rel2->relids);
	bool b = have_relevant_joinclause(root, rel1, rel2);
	bool c = have_join_order_restriction(root, rel1, rel2);
	bool result = !a && (b || c);
	return result;
}

/**
 * @brief Build a join graph from initial relations.
 *
 * Creates a vertex per relation and adds edges for simple inner joins.
 *
 * @param root Planner context.
 * @param initial_rels Base relations to include.
 *
 * @return List of Vertex items representing the join graph.
 */
List *build_join_graph(PlannerInfo *root, List *initial_rels)
{
	List *vertexes = NIL;
	size_t index = 0;
	ListCell *lc = NULL;
	foreach (lc, initial_rels) {
		RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
		Vertex *v = (Vertex *)palloc0(sizeof(Vertex));
		v->rel = rel;
		v->adj = NIL;
		v->index = index++;
		vertexes = lappend(vertexes, v);
	}
	ListCell *i = NULL;
	ListCell *j = NULL;
	foreach (i, vertexes) {
		Vertex *v_i = (Vertex *)lfirst(i);
		for_each_cell (j, vertexes, lnext(vertexes, i)) {
			Vertex *v_j = (Vertex *)lfirst(j);
			if (has_simple_inner_edge(root, v_i->rel, v_j->rel)) {
				v_i->adj = lappend(v_i->adj, v_j);
				v_j->adj = lappend(v_j->adj, v_i);
			}
		}
	}
	print_graph(root, vertexes);
	return vertexes;
}

/**
 * @brief Emit a debug representation of the join graph.
 *
 * Logs each vertex, its cost, and adjacent edge costs.
 *
 * @param root Planner context.
 * @param graph List of Vertex items.
 */
static void print_graph(PlannerInfo *root, List *graph)
{
	StringInfoData buf;
	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------\n");
	ListCell *lc = NULL;
	foreach (lc, graph) {
		Vertex *vertex = (Vertex *)lfirst(lc);
		Cost cost_rel = vertex->rel->cheapest_total_path->total_cost;
		appendStringInfo(&buf, "%zu(%lf):", vertex->index, cost_rel);
		ListCell *lc2 = NULL;
		foreach (lc2, vertex->adj) {
			Vertex *neighbor = (Vertex *)lfirst(lc2);
			Cost cost_edge = cost_simple_edge(root, vertex->rel, neighbor->rel);
			appendStringInfo(&buf, " %zu(%lf)", neighbor->index, cost_edge);
		}
		appendStringInfo(&buf, "\n");
	}
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Depth-first traversal to collect a connected component.
 *
 * Marks visited vertices and returns the component list.
 *
 * @param v Start vertex.
 * @param comp Current component list.
 * @param used_vertexes Visited marker array.
 *
 * @return Updated component list.
 */
static List *dfs_component(Vertex *v, List *comp, bool *used_vertexes)
{
	used_vertexes[v->index] = true;
	comp = lappend(comp, v);
	ListCell *lc = NULL;
	foreach (lc, v->adj) {
		Vertex *next = (Vertex *)lfirst(lc);
		if (!used_vertexes[next->index]) {
			comp = dfs_component(next, comp, used_vertexes);
		}
	}
	return comp;
}

/**
 * @brief DFS utility to mark reachability in a vertex list.
 *
 * @param vertexes Full vertex list.
 * @param v Start vertex.
 * @param used_vertexes Visited marker array.
 */
void dfs_check(List *vertexes, Vertex *v, bool *used_vertexes)
{
	used_vertexes[v->index] = true;
	ListCell *lc = NULL;
	foreach (lc, v->adj) {
		Vertex *next = (Vertex *)lfirst(lc);
		if (!used_vertexes[next->index]) {
			dfs_check(vertexes, next, used_vertexes);
		}
	}
}

/**
 * @brief Split a join graph into connected components.
 *
 * Builds Topology objects and computes selectivity, volume, and complexity.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 *
 * @return List of Topology components.
 */
List *split_components(PlannerInfo *root, List *vertexes)
{
	List *comps = NIL; // List* of Component*
	int number_of_rels = list_length(vertexes);
	bool *used_vertexes = (bool *)palloc0(number_of_rels * sizeof(bool));
	ListCell *lc = NULL;
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		if (!used_vertexes[v->index]) {
			Topology *component = (Topology *)palloc0(sizeof(Topology));
			List *sub = NIL;
			sub = dfs_component(v, sub, used_vertexes);
			component->vertexes = sub;
			component->form = COMPONENT;
			set_sel_topology(root, component);
			set_vol_topology(root, component);
			set_complexity_topology(root, component);
			comps = lappend(comps, component);
		}
	}
	pfree(used_vertexes);
	return comps;
}

/**
 * @brief DFS-based cycle detection with selectivity pruning.
 *
 * Records cycles and marks vertices belonging to discovered cycles.
 *
 * @param root Planner context.
 * @param prev Previous vertex in DFS.
 * @param cur Current vertex in DFS.
 * @param stack Current DFS stack.
 * @param cycles Accumulated list of cycles.
 * @param visited Per-vertex recursion marker.
 * @param used_vertexes_comp Marks vertices already assigned to cycles.
 *
 * @return Updated list of cycles.
 */
static List *dfs_cycle(PlannerInfo *root, Vertex *prev, Vertex *cur, List *stack, List *cycles,
		       bool *visited, bool *used_vertexes_comp)
{
	visited[cur->index] = true;
	stack = lappend(stack, cur);
	ListCell *lc = NULL;
	foreach (lc, cur->adj) {
		Vertex *nbr = (Vertex *)lfirst(lc);
		if (nbr == prev) {
			continue;
		}
		Selectivity sel = get_selectivity(root, cur->rel, nbr->rel);
		if (sel > border_selectivity) {
			continue;
		}
		if (visited[nbr->index] && stack->length >= 3) {
			List *cycle = NIL;
			ListCell *lc2 = NULL;
			foreach (lc2, stack) {
				Vertex *it = (Vertex *)lfirst(lc2);
				if (it->index == nbr->index) {
					break;
				}
			}
			ListCell *lc3 = NULL;
			for_each_cell (lc3, stack, lc2) {
				Vertex *it = (Vertex *)lfirst(lc3);
				cycle = lappend(cycle, it);
				used_vertexes_comp[it->index] = true;
			}
			cycles = lappend(cycles, cycle);
			break;
		}
		if (!visited[nbr->index] && !used_vertexes_comp[nbr->index]) {
			cycles = dfs_cycle(root,
					   cur,
					   nbr,
					   stack,
					   cycles,
					   visited,
					   used_vertexes_comp);
		}
	}
	visited[cur->index] = false;
	stack = list_delete_nth_cell(stack, stack->length - 1);
	return cycles;
}

/**
 * @brief Find cyclic subgraphs and return them as topologies.
 *
 * Uses DFS with selectivity thresholds to identify cycles.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used_vertexes_comp Marks vertices already assigned to components.
 *
 * @return List of CYCLE topologies.
 */
List *find_cycles(PlannerInfo *root, List *vertexes, bool *used_vertexes_comp)
{
	int nverts_global = list_length(vertexes);
	List *cycles = NIL; // List* of List* of Vertex*
	bool *visited = (bool *)palloc0(nverts_global * sizeof(bool));
	List *stack = NIL;
	ListCell *lc = NULL;
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		if (used_vertexes_comp[v->index]) {
			continue;
		}
		MemSet(visited, false, nverts_global * sizeof(bool));
		cycles = dfs_cycle(root, NULL, v, stack, cycles, visited, used_vertexes_comp);
	}
	List *cyclic_topologies = NIL;
	foreach (lc, cycles) {
		List *cycle = (List *)lfirst(lc);
		Topology *topology = (Topology *)palloc0(sizeof(Topology));
		topology->vertexes = cycle;
		topology->form = CYCLE;
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		cyclic_topologies = lappend(cyclic_topologies, topology);
	}
	pfree(visited);
	return cyclic_topologies;
}

/**
 * @brief Decide whether a vertex can be treated as a star center.
 *
 * Checks degree and relative volume of neighbors.
 *
 * @param center Candidate center vertex.
 * @param used_vertexes Used marker array.
 *
 * @return True if the vertex qualifies as a star center.
 */
static bool is_star(Vertex *center, const bool *used_vertexes)
{
	int count_unused_neighbors = 0;
	int count_light_neighbors = 0;
	double volume_center = center->rel->rows;
	ListCell *lc = NULL;
	foreach (lc, center->adj) {
		Vertex *neighbor = (Vertex *)lfirst(lc);
		if (!used_vertexes[neighbor->index]) {
			double volume_neighbor = neighbor->rel->rows;
			if (volume_center >= 10 * volume_neighbor) {
				count_light_neighbors++;
			}
			count_unused_neighbors++;
		}
	}
	return count_unused_neighbors >= 3 || count_light_neighbors >= 2;
}

/**
 * @brief Build a star topology around a center vertex.
 *
 * Grows rays up to a maximum length by selectivity.
 *
 * @param root Planner context.
 * @param center Star center vertex.
 * @param used_vertexes Used marker array.
 * @param chains Output list of ray chains.
 *
 * @return List of vertices that form the star.
 */
static List *find_star(PlannerInfo *root, Vertex *center, bool *used_vertexes, List *chains)
{
	List *star = NIL;
	star = lappend(star, center);
	used_vertexes[center->index] = true;
	ListCell *lc = NULL;
	foreach (lc, center->adj) {
		int ray_len = 0;
		Vertex *curr = (Vertex *)lfirst(lc);
		List *chain = NIL;
		while (ray_len < max_ray_length) {
			chain = lappend(chain, curr);
			used_vertexes[curr->index] = true;
			ray_len += 1;
			Vertex *new_neighbor = NULL;
			Selectivity sel = border_selectivity;
			ListCell *lc2 = NULL;
			foreach (lc2, curr->adj) {
				Vertex *tmp = (Vertex *)lfirst(lc2);
				if (used_vertexes[tmp->index] || is_star(tmp, used_vertexes)) {
					continue;
				}
				Selectivity tmp_sel = get_selectivity(root, curr->rel, tmp->rel);
				if (tmp_sel < sel) {
					new_neighbor = tmp;
					sel = tmp_sel;
				}
			}
			if (new_neighbor == NULL) {
				break;
			}
			curr = new_neighbor;
		}
		star = list_concat(star, chain);
		chains = lappend(chains, chain);
	}
	return star;
}

/**
 * @brief Find chain components among unused vertices.
 *
 * Each connected component is treated as a chain topology.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used_vertexes Used marker array.
 *
 * @return List of CHAIN topologies.
 */
List *find_chains(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List *chains = NIL; // List* of Topology*
	ListCell *lc = NULL;
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		if (!used_vertexes[v->index]) {
			List *sub = NIL;
			sub = dfs_component(v, sub, used_vertexes);
			Topology *topology = (Topology *)palloc0(sizeof(Topology));
			topology->vertexes = sub;
			topology->form = CHAIN;
			set_sel_topology(root, topology);
			set_vol_topology(root, topology);
			set_complexity_topology(root, topology);
			chains = lappend(chains, topology);
		}
	}
	return chains;
}

/**
 * @brief Find star topologies among unused vertices.
 *
 * Detects star centers and builds star topologies with ray chains.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used_vertexes Used marker array.
 *
 * @return List of STAR topologies.
 */
List *find_stars(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List *stars = NIL;
	ListCell *lc = NULL;
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		if (used_vertexes[v->index] || !is_star(v, used_vertexes)) {
			continue;
		}
		List *chains = NIL;
		List *star = find_star(root,
				       v,
				       used_vertexes,
				       chains); // List* of {star_vertex, List1 of chain
						// vertex, List_n of chain vertex}
		Topology *topology = (Topology *)palloc0(sizeof(Topology));
		topology->vertexes = star; // TODO
		topology->form = STAR;
		topology->extended_info = chains;
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		stars = lappend(stars, topology);
	}
	return stars;
}

/**
 * @brief Count edges inside a vertex subset.
 *
 * @param sub Vertex subset.
 *
 * @return Number of internal edges.
 */
static int count_edges(List *sub)
{
	int m = 0;
	ListCell *lc;
	foreach (lc, sub) {
		Vertex *v1 = (Vertex *)lfirst(lc);
		ListCell *lc2;
		foreach (lc2, v1->adj) {
			Vertex *v2 = (Vertex *)lfirst(lc2);
			if (v1->index < v2->index && list_member_ptr(sub, v2)) {
				m++;
			}
		}
	}
	return m;
}

/**
 * @brief Reassign indices for topology vertices.
 *
 * @param component Topology to update.
 */
void update_indices(Topology *component)
{
	size_t i = 0;
	ListCell *lc;
	foreach (lc, component->vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		v->index = i;
		i++;
	}
}

/**
 * @brief Compute edge density for a vertex subset.
 *
 * @param sub Vertex subset.
 *
 * @return Density in [0,1], or 0 for small sets.
 */
static double density(List *sub)
{
	int n = list_length(sub);
	if (n < 4) {
		return 0.0;
	}

	int m = count_edges(sub);
	double d = (double)m / ((double)n * (n - 1) / 2.0);
	return d;
}

/**
 * @brief Find the minimum-degree vertex in a subset.
 *
 * @param sub Vertex subset.
 *
 * @return Vertex with the lowest internal degree.
 */
static Vertex *find_min_degree_vertex(List *sub)
{
	int best_deg = INT_MAX;
	Vertex *best_v = NULL;
	ListCell *lc;
	foreach (lc, sub) {
		Vertex *v = (Vertex *)lfirst(lc);
		int deg = 0;
		ListCell *lc2;
		foreach (lc2, v->adj) {
			if (list_member_ptr(sub, lfirst(lc2))) {
				deg++;
			}
		}

		if (deg < best_deg) {
			best_deg = deg;
			best_v = v;
		}
	}
	return best_v;
}

/**
 * @brief Find dense subgraphs and return them as topologies.
 *
 * Iteratively prunes low-degree vertices until density exceeds threshold.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used Used marker array.
 *
 * @return List of DENSITY_GRAPH topologies.
 */
List *find_dense_subgraphs(PlannerInfo *root, List *vertexes, bool *used)
{
	List *dense_sets = NIL; // List* of Topology*

	while (true) {
		List *candidate = NIL;
		ListCell *lc;
		foreach (lc, vertexes) {
			Vertex *v = (Vertex *)lfirst(lc);
			if (!used[v->index]) {
				candidate = lappend(candidate, v);
			}
		}

		if (list_length(candidate) < 4) {
			list_free(candidate);
			break;
		}

		while (list_length(candidate) >= 4) {
			double cur_density = density(candidate);
			if (cur_density >= THRESH) {
				break;
			}

			Vertex *vmin = find_min_degree_vertex(candidate);
			if (vmin == NULL) {
				break;
			}

			candidate = list_delete_ptr(candidate, vmin);
		}

		double final_density = density(candidate);
		if (list_length(candidate) < 4 || final_density < THRESH) {
			list_free(candidate);
			break;
		}
		Topology *topology = (Topology *)palloc0(sizeof(Topology));
		topology->vertexes = candidate;
		topology->form = DENSITY_GRAPH;
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		dense_sets = lappend(dense_sets, topology);

		foreach (lc, candidate) {
			Vertex *v = (Vertex *)lfirst(lc);
			used[v->index] = true;
		}
	}

	return dense_sets;
}

/**
 * @brief Estimate topology complexity via connected subgraph counting.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
static void set_complexity_topology(PlannerInfo *root, Topology *topology)
{
	List *initial_rels = NIL;
	ListCell *lc;
	foreach (lc, topology->vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		initial_rels = lappend(initial_rels, v->rel);
	}
	DPHypContext context;
	context.initial_rels = initial_rels;
	context.root = root;
	context.simple_hypernodes = NIL;

	initialize_edges(root, initial_rels, &context);

	uint64 subgraphs_count = count_cc(&context, dphyp_geqo_cc_threshold);
	topology->ccp = subgraphs_count;
}

/**
 * @brief Compute join selectivity for a relation pair.
 *
 * Builds a dummy join rel and evaluates clause selectivity.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return Estimated selectivity for joining rel1 and rel2.
 */
Selectivity get_selectivity(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{ // TODO join_is_legal
	RelOptInfo joinrel;
	joinrel.relids = bms_union(rel1->relids, rel2->relids);
	SpecialJoinInfo sjinfo;
	init_dummy_sjinfo(&sjinfo, rel1->relids, rel2->relids);
	joinrel.relids = add_outer_joins_to_relids(root, joinrel.relids, &sjinfo, NULL);
	List *clauses = build_joinrel_restrictlist(root, &joinrel, rel1, rel2, &sjinfo);

	Selectivity result = clauselist_selectivity(root, clauses, 0, JOIN_INNER, &sjinfo);
	bms_free(joinrel.relids);
	return result;
}

/**
 * @brief Compute topology volume as product of row counts.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
void set_vol_topology(PlannerInfo *root, Topology *topology)
{
	Cardinality vol = 1;
	List *vertexes = topology->vertexes;
	ListCell *i = NULL;
	foreach (i, vertexes) {
		RelOptInfo *rel = ((Vertex *)lfirst(i))->rel;
		vol *= rel->rows;
	}
	topology->vol = vol;
}

/**
 * @brief Compute topology selectivity from join clauses.
 *
 * Aggregates join clauses fully contained in the topology and applies
 * selectivity estimation.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
void set_sel_topology(PlannerInfo *root, Topology *topology)
{
	Relids relids_topology = NULL;
	List *vertexes = topology->vertexes;
	List *clauses = NIL;
	ListCell *lc;

	foreach (lc, vertexes) {
		RelOptInfo *rel = ((Vertex *)lfirst(lc))->rel;

		relids_topology = bms_add_members(relids_topology, rel->relids);
	}

	foreach (lc, vertexes) {
		RelOptInfo *rel = ((Vertex *)lfirst(lc))->rel;
		ListCell *lc2;

		foreach (lc2, rel->joininfo) {
			RestrictInfo *rinfo = (RestrictInfo *)lfirst(lc2);
			Relids clause_relids = rinfo->required_relids;

			if (!bms_is_subset(clause_relids, relids_topology)) {
				continue;
			}

			if (bms_membership(clause_relids) != BMS_MULTIPLE) {
				continue;
			}

			if (list_member_ptr(clauses, rinfo)) {
				continue;
			}

			clauses = lappend(clauses, rinfo);
		}
	}
	List *implied_clauses = NIL;
	foreach (lc, vertexes) {
		RelOptInfo *inner_rel = ((Vertex *)lfirst(lc))->rel;
		Relids outer_relids = bms_difference(relids_topology, inner_rel->relids);
		// SpecialJoinInfo sjinfo;
		// init_dummy_sjinfo(&sjinfo, outer_relids, inner_rel->relids);

		implied_clauses =
			list_concat_unique(implied_clauses,
					   generate_join_implied_equalities(root,
									    relids_topology,
									    outer_relids,
									    inner_rel,
									    NULL));
		bms_free(outer_relids);
	}
	clauses = list_concat(clauses, implied_clauses);

	SpecialJoinInfo sjinfo;
	init_dummy_sjinfo(&sjinfo, relids_topology, relids_topology);
	Selectivity sel = clauselist_selectivity(root, clauses, 0, JOIN_INNER, &sjinfo);
	list_free(clauses);
	bms_free(relids_topology);
	topology->sel = sel;
}

/**
 * @brief Estimate the cheapest join cost between two relations.
 *
 * Considers nestloop, hashjoin, and mergejoin initial costs.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return Minimum estimated join cost.
 */
Cost cost_simple_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Cost min_cost = DBL_MAX;
	JoinPathExtraData extra;
	RelOptInfo *outer_rels[2] = { rel1, rel2 };
	RelOptInfo *inner_rels[2] = { rel2, rel1 };
	for (int i = 0; i < 2; i++) {
		RelOptInfo *outer_rel = outer_rels[i];
		RelOptInfo *inner_rel = inner_rels[i];
		Path *outer_path = outer_rel->cheapest_total_path;
		Path *inner_path = inner_rel->cheapest_total_path;
		JoinCostWorkspace workspace;
		List *hashclauses = NIL;
		List *mergeclauses = NIL;
		SpecialJoinInfo sjinfo;
		RelOptInfo joinrel;
		List *restrictlist;
		ListCell *lc;

		if (PATH_PARAM_BY_REL(outer_path, inner_rel) ||
		    PATH_PARAM_BY_REL(inner_path, outer_rel)) {
			continue;
		}

		joinrel.relids = bms_union(outer_rel->relids, inner_rel->relids);
		init_dummy_sjinfo(&sjinfo, outer_rel->relids, inner_rel->relids);
		joinrel.relids = add_outer_joins_to_relids(root, joinrel.relids, &sjinfo, NULL);
		restrictlist =
			build_joinrel_restrictlist(root, &joinrel, outer_rel, inner_rel, &sjinfo);

		MemSet(&extra, 0, sizeof(JoinPathExtraData));
		extra.restrictlist = restrictlist;
		extra.mergeclause_list = NIL;
		extra.inner_unique = false;
		extra.sjinfo = &sjinfo;
		extra.param_source_rels = joinrel.relids;

		initial_cost_nestloop(root, &workspace, JOIN_INNER, outer_path, inner_path, &extra);
		if (workspace.total_cost < min_cost) {
			min_cost = workspace.total_cost;
		}

		foreach (lc, restrictlist) {
			RestrictInfo *restrictinfo = (RestrictInfo *)lfirst(lc);

			if (!restrictinfo->can_join ||
			    restrictinfo->hashjoinoperator == InvalidOid) {
				continue;
			}

			if (!clause_sides_match_join(restrictinfo,
						     outer_rel->relids,
						     inner_rel->relids)) {
				continue;
			}

			if (!restrictinfo->outer_is_left &&
			    !OidIsValid(
				    get_commutator(castNode(OpExpr, restrictinfo->clause)->opno))) {
				continue;
			}

			hashclauses = lappend(hashclauses, restrictinfo);
		}

		if (hashclauses != NIL) {
			initial_cost_hashjoin(root,
					      &workspace,
					      JOIN_INNER,
					      hashclauses,
					      outer_path,
					      inner_path,
					      &extra,
					      false);
			if (workspace.total_cost < min_cost) {
				min_cost = workspace.total_cost;
			}
		}

		mergeclauses = find_mergeclauses_for_outer_pathkeys(root,
								    outer_path->pathkeys,
								    restrictlist);

		if (mergeclauses != NIL) {
			List *outersortkeys = outer_path->pathkeys;
			List *innersortkeys =
				make_inner_pathkeys_for_merge(root, mergeclauses, outersortkeys);

			initial_cost_mergejoin(root,
					       &workspace,
					       JOIN_INNER,
					       mergeclauses,
					       outer_path,
					       inner_path,
					       outersortkeys,
					       innersortkeys,
					       0,
					       &extra);
			if (workspace.total_cost < min_cost) {
				min_cost = workspace.total_cost;
			}
		}

		bms_free(joinrel.relids);
	}

	return min_cost;
}
