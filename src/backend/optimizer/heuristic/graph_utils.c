#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/heuristic/counter.h"
#include "c.h"
#include "lib/stringinfo.h"
#include "nodes/bitmapset.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/joininfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/restrictinfo.h"
#include "postgres.h"
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/palloc.h"
#include <float.h>
#include <limits.h>
#include <optimizer/cost.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static const uint64 dphyp_geqo_cc_threshold = 10000;
static const double THRESH = 0.9;
static const Selectivity border_selectivity = 0.2;
static const int max_ray_length = 3;
static const int min_length_cycle = 3;
static void set_complexity_topology(PlannerInfo *root, Topology * topology);
static List *bfs_component(Vertex * start, bool *used_vertexes);
static bool dfs_cycle(PlannerInfo *root, Vertex * prev, Vertex * cur,
					  List **stack, bool *visited,
					  bool *used_vertexes_comp);	/* stack is list of Vertex*  */
static bool is_star(Vertex * center, const bool *used_vertexes);
static List *find_star(PlannerInfo *root, Vertex * center, bool *used_vertexes,
					   List **chains);
static Vertex * find_min_degree_vertex(PlannerInfo *root, List *sub);
static double density(PlannerInfo *root, List *sub);
static int	count_edges(PlannerInfo *root, List *sub);

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
bool
has_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	bool		a = bms_overlap(rel1->relids, rel2->relids);
	bool		b = have_relevant_joinclause(root, rel1, rel2);
	bool		c = have_join_order_restriction(root, rel1, rel2);
	bool		result = !a && (b || c);

	return result;
}

/**
 * @brief Emit a debug representation of the join graph.
 *
 * Logs each vertex, its cost, and adjacent edge costs.
 *
 * @param root Planner context.
 * @param graph List of Vertex items.
 */
static void
print_graph(PlannerInfo *root, List *graph)
{
	StringInfoData buf;
	ListCell   *lc = NULL;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_GRAPH\n");
	foreach(lc, graph)
	{
		Vertex	   *vertex = (Vertex *) lfirst(lc);
		ListCell   *lc2 = NULL;
		Cost		cost_rel = vertex->rel->cheapest_total_path->total_cost;

		appendStringInfo(&buf, "%zu(%lf):", vertex->index, cost_rel);
		foreach(lc2, vertex->adj)
		{
			Vertex	   *neighbor = (Vertex *) lfirst(lc2);
			Cost		prel_join_cost = cost_edge(root, vertex->rel, neighbor->rel);
			Selectivity selectivity = get_selectivity(root, vertex->rel, neighbor->rel);

			appendStringInfo(&buf, " %zu(%.3lf, %.9lf)", neighbor->index, prel_join_cost, selectivity);
		}
		appendStringInfo(&buf, "\n");
	}
	appendStringInfo(&buf, "\n");
	foreach(lc, graph)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			i = -1;

		appendStringInfo(&buf, "bitmap v_%zu: ", v->index);
		while ((i = bms_next_member(v->rel->relids, i)) >= 0)
		{
			appendStringInfo(&buf, "%d ", i);
		}
		appendStringInfo(&buf, "\n");
	}
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Debug print a topology.
 *
 * Prints the type of the topology, selectivity, count connected pairs of
 * subgraphs, volume, and budget. If the topology is a star, prints the center
 * and chains of the star (each chain on a new line).
 *
 * Also prints Bitmapset of each vertex in the topology.
 * @param topology Topology to print.
 */
void
print_topology(Topology * topology)
{
	StringInfoData buf;
	ListCell   *lc = NULL;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_TOPOLOGY\n");
	switch (topology->form)
	{
		case CHAIN:
			{
				appendStringInfo(&buf, "Chain\n");
				break;
			}
		case CYCLE:
			{
				appendStringInfo(&buf, "Cycle\n");
				break;
			}
		case DENSITY_GRAPH:
			{
				appendStringInfo(&buf, "Density graph\n");
				break;
			}
		case STAR:
			{
				appendStringInfo(&buf, "Star\n");
				break;
			}
		case COMPONENT:
			{
				appendStringInfo(&buf, "Component\n");
				break;
			}
	}
	appendStringInfo(&buf, "sel: %.10lf\n", topology->sel);
	appendStringInfo(&buf, "ccp: %lu\n", topology->ccp);
	appendStringInfo(&buf, "vol: %lf\n", topology->vol);
	appendStringInfo(&buf, "budget: %lf\n", topology->budget);
	appendStringInfo(&buf, "vertexes: ");

	if (topology->form == STAR)
	{
		Vertex	   *center = (Vertex *) linitial(topology->vertexes);
		ListCell   *lc = NULL;

		appendStringInfo(&buf, "Center: %zu\n", center->index);
		foreach(lc, topology->extended_info)
		{
			List	   *chain = (List *) lfirst(lc);
			ListCell   *lc2 = NULL;

			appendStringInfo(&buf, "Chain: ");
			foreach(lc2, chain)
			{
				Vertex	   *v = (Vertex *) lfirst(lc2);

				appendStringInfo(&buf, "%zu ", v->index);
			}
			appendStringInfo(&buf, "\n");
		}
	}
	else
	{
		ListCell   *lc = NULL;

		foreach(lc, topology->vertexes)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

			appendStringInfo(&buf, "%zu ", v->index);
		}
		appendStringInfo(&buf, "\n");
	}
	/* print bitmap each vertex */
	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			i = -1;

		appendStringInfo(&buf, "bitmap v_%zu: ", v->index);
		while ((i = bms_next_member(v->rel->relids, i)) >= 0)
		{
			appendStringInfo(&buf, "%d ", i);
		}
		appendStringInfo(&buf, "\n");
	}
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
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
List *
build_join_graph(PlannerInfo *root, List *initial_rels)
{
	List	   *vertexes = NIL;
	size_t		index = 0;
	ListCell   *lc = NULL;
	ListCell   *i = NULL;
	ListCell   *j = NULL;

	foreach(lc, initial_rels)
	{
		RelOptInfo *rel = (RelOptInfo *) lfirst(lc);
		Vertex	   *v = (Vertex *) palloc0(sizeof(Vertex));

		v->rel = rel;
		v->adj = NIL;
		v->index = index++;
		vertexes = lappend(vertexes, v);
	}
	foreach(i, vertexes)
	{
		Vertex	   *v_i = (Vertex *) lfirst(i);

		for_each_cell(j, vertexes, lnext(vertexes, i))
		{
			Vertex	   *v_j = (Vertex *) lfirst(j);

			if (has_edge(root, v_i->rel, v_j->rel))
			{
				v_i->adj = lappend(v_i->adj, v_j);
				v_j->adj = lappend(v_j->adj, v_i);
			}
		}
	}
	print_graph(root, vertexes);
	return vertexes;
}

/**
 * @brief BFS to collect a connected component.
 *
 * Marks visited vertices and returns the component list.
 *
 * @param v Start vertex.
 * @param comp Current component list.
 * @param used_vertexes Visited marker array.
 *
 * @return Updated component list.
 */
static List *
bfs_component(Vertex * start, bool *used_vertexes)
{
	List	   *queue = list_make1(start);
	int			begin_queue = 0;

	used_vertexes[start->index] = true;
	while (begin_queue < list_length(queue))
	{
		Vertex	   *v = (Vertex *) lfirst(list_nth_cell(queue, begin_queue));
		ListCell   *lc = NULL;

		begin_queue++;
		foreach(lc, v->adj)
		{
			Vertex	   *next = (Vertex *) lfirst(lc);

			if (!used_vertexes[next->index])
			{
				used_vertexes[next->index] = true;
				queue = lappend(queue, next);
			}
		}
	}
	return queue;
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
List *
split_components(PlannerInfo *root, List *vertexes)
{
	List	   *comps = NIL;	/* List* of Component*   */
	int			number_of_rels = list_length(vertexes);
	bool	   *used_vertexes = (bool *) palloc0(number_of_rels * sizeof(bool));
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used_vertexes[v->index])
		{
			Topology   *component = (Topology *) palloc0(sizeof(Topology));
			List	   *sub = bfs_component(v, used_vertexes);

			component->vertexes = sub;
			component->form = COMPONENT;
			set_id(root, component);
			set_sel_topology(root, component);
			set_vol_topology(root, component);
			set_complexity_topology(root, component);
			comps = lappend(comps, component);
		}
	}
	pfree(used_vertexes);
	return comps;
}

/* find cycle */
static bool
dfs_cycle(PlannerInfo *root, Vertex * prev, Vertex * cur,
		  List **stack, bool *visited, bool *used_vertexes_comp)
{
	ListCell   *lc = NULL;

	visited[cur->index] = true;
	*stack = lappend(*stack, cur);
	foreach(lc, cur->adj)
	{
		Vertex	   *nbr = (Vertex *) lfirst(lc);
		Selectivity sel;

		if (nbr == prev)
		{
			continue;
		}
		sel = get_selectivity(root, cur->rel, nbr->rel);
		if (sel > border_selectivity)
		{
			continue;
		}
		if (visited[nbr->index] && (*stack)->length >= min_length_cycle)
		{
			List	   *cycle = NIL;
			ListCell   *lc2 = NULL;
			ListCell   *lc3 = NULL;

			foreach(lc2, *stack)
			{
				Vertex	   *it = (Vertex *) lfirst(lc2);

				if (it->index == nbr->index)
				{
					break;
				}
			}
			for_each_cell(lc3, *stack, lc2)
			{
				Vertex	   *it = (Vertex *) lfirst(lc3);

				cycle = lappend(cycle, it);
				used_vertexes_comp[it->index] = true;
			}
			list_free(*stack);
			*stack = cycle;
			return true;
		}
		if (!visited[nbr->index] && !used_vertexes_comp[nbr->index])
		{
			bool		was_cycle =
				dfs_cycle(root, cur, nbr, stack, visited, used_vertexes_comp);

			if (was_cycle)
			{
				return true;
			}
		}
	}
	visited[cur->index] = false;
	*stack = list_delete_last(*stack);
	return false;
}

/**
 * @brief Check whether a -selected subgraph is connected.
 *
 * Builds the vertex subset from the bitmap and verifies connectivity with BFS.
 *
 * @param all_vertexes All vertices in the topology.
 * @param bitmap Bitmask selecting a subset of vertices.
 *
 * @return True if the selected subgraph is connected.
 */
bool
is_connected(List *all_vertexes, size_t bitmap)
{
	List	   *vertices = NIL;
	bool	   *used = NULL;
	Vertex	   *start = NULL;
	size_t		topology_id;
	List	   *queue = NIL;
	int			begin_queue = 0;
	ListCell   *lc = NULL;
	bool		connected = true;

	for (uint64 i = 0; ((uint64) 1 << i) <= bitmap; i++)
	{
		if (bitmap & ((uint64) 1 << i))
		{
			Vertex	   *v = (Vertex *) list_nth(all_vertexes, i);

			vertices = lappend(vertices, v);
		}
	}
	/* check that vertexes are connected */
	used = (bool *) palloc0(list_length(all_vertexes) * sizeof(bool));
	start = (Vertex *) linitial(vertices);
	topology_id = start->topology_id;
	queue = list_make1(start);
	used[start->index] = true;
	while (begin_queue < list_length(queue))
	{
		Vertex	   *v = (Vertex *) lfirst(list_nth_cell(queue, begin_queue));

		begin_queue++;
		foreach(lc, v->adj)
		{
			Vertex	   *next = (Vertex *) lfirst(lc);

			if (!used[next->index] && next->topology_id == topology_id)
			{
				used[next->index] = true;
				queue = lappend(queue, next);
			}
		}
	}
	list_free(queue);
	foreach(lc, vertices)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used[v->index])
		{
			connected = false;
			break;
		}
	}
	list_free(vertices);
	pfree(used);
	return connected;
}

/* find non intersecting cycles */
List *
find_cycles(PlannerInfo *root, List *vertexes, bool *used_vertexes_comp)
{
	int			n_local = list_length(vertexes);
	List	   *cycles = NIL;	/* List* of List* of Vertex*  */
	bool	   *visited = (bool *) palloc0(n_local * sizeof(bool));
	ListCell   *lc = NULL;
	List	   *cyclic_topologies = NIL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		List	   *stack = NIL;

		if (used_vertexes_comp[v->index])
		{
			continue;
		}
		memset(visited, false, n_local * sizeof(bool));
		dfs_cycle(root, NULL, v, &stack, visited, used_vertexes_comp);
		if (stack)
		{
			cycles = lappend(cycles, stack);
		}
	}
	foreach(lc, cycles)
	{
		List	   *cycle = (List *) lfirst(lc);
		Topology   *topology = (Topology *) palloc0(sizeof(Topology));

		topology->vertexes = cycle;
		topology->form = CYCLE;
		set_id(root, topology);
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		cyclic_topologies = lappend(cyclic_topologies, topology);
		/* print_topology(topology); */
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
static bool
is_star(Vertex * center, const bool *used_vertexes)
{
	int			count_unused_neighbors = 0;
	int			count_light_neighbors = 0;
	double		volume_center = center->rel->rows;
	ListCell   *lc = NULL;

	foreach(lc, center->adj)
	{
		Vertex	   *neighbor = (Vertex *) lfirst(lc);

		if (!used_vertexes[neighbor->index])
		{
			double		volume_neighbor = neighbor->rel->rows;

			if (volume_center >= 10 * volume_neighbor)
			{
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
static List *
find_star(PlannerInfo *root, Vertex * center, bool *used_vertexes,
		  List **chains)
{
	List	   *star = NIL;
	ListCell   *lc = NULL;

	star = lappend(star, center);
	used_vertexes[center->index] = true;
	foreach(lc, center->adj)
	{
		int			ray_len = 0;
		Vertex	   *curr = (Vertex *) lfirst(lc);
		List	   *chain = NIL;

		if (used_vertexes[curr->index])
		{
			continue;
		}
		while (ray_len < max_ray_length)
		{
			Selectivity sel;
			Vertex	   *new_neighbor = NULL;
			ListCell   *lc2 = NULL;

			chain = lappend(chain, curr);
			used_vertexes[curr->index] = true;
			ray_len += 1;
			sel = border_selectivity;
			foreach(lc2, curr->adj)
			{
				Selectivity tmp_sel;
				Vertex	   *tmp = (Vertex *) lfirst(lc2);

				if (used_vertexes[tmp->index] || is_star(tmp, used_vertexes))
				{
					continue;
				}
				tmp_sel = get_selectivity(root, curr->rel, tmp->rel);
				if (tmp_sel < sel)
				{
					new_neighbor = tmp;
					sel = tmp_sel;
				}
			}
			if (new_neighbor == NULL)
			{
				break;
			}
			curr = new_neighbor;
		}
		star = list_concat(star, chain);
		*chains = lappend(*chains, chain);
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
List *
find_chains(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List	   *chains = NIL;	/* List* of Topology*  */
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used_vertexes[v->index])
		{
			List	   *sub = bfs_component(v, used_vertexes);
			Topology   *topology = (Topology *) palloc0(sizeof(Topology));

			topology->vertexes = sub;
			topology->form = CHAIN;
			set_id(root, topology);
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
List *
find_stars(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List	   *stars = NIL;
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Topology   *topology = NULL;
		Vertex	   *v = (Vertex *) lfirst(lc);
		List	   *chains = NIL;
		List	   *star = NIL;

		if (used_vertexes[v->index] || !is_star(v, used_vertexes))
		{
			continue;
		}
		star = find_star(root, v, used_vertexes,
						 &chains);	/* List* of {star_vertex, List1 of chain
									 * vertex, List_n of chain vertex} */
		topology = (Topology *) palloc0(sizeof(Topology));
		topology->vertexes = star;
		topology->form = STAR;
		topology->extended_info = chains;
		set_id(root, topology);
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		stars = lappend(stars, topology);
		/* print_topology(topology); */
	}
	return stars;
}

/**
 * @brief Count "good" internal edges in a vertex subset.
 *
 * An edge is counted only when its pairwise join selectivity does not
 * exceed border_selectivity, matching the same filter that dfs_cycle
 * applies.  This prevents near-Cartesian edges from inflating the
 * density of a candidate subgraph.
 * @param sub Vertex subset.
 *
 * @return Number of internal edges.
 */
static int
count_edges(PlannerInfo *root, List *sub)
{
	int			m = 0;
	ListCell   *lc = NULL;

	foreach(lc, sub)
	{
		Vertex	   *v1 = (Vertex *) lfirst(lc);
		ListCell   *lc2 = NULL;

		foreach(lc2, v1->adj)
		{
			Vertex	   *v2 = (Vertex *) lfirst(lc2);

			if (v1->index < v2->index && list_member_ptr(sub, v2))
			{
				Selectivity sel = get_selectivity(root, v1->rel, v2->rel);

				if (sel <= border_selectivity)
				{
					m++;
				}
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
void
update_indices(Topology * component)
{
	size_t		i = 0;
	ListCell   *lc = NULL;

	foreach(lc, component->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

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
static double
density(PlannerInfo *root, List *sub)
{
	int			n = list_length(sub);
	int			m;
	double		d;

	if (n < 4)
		return 0.0;

	m = count_edges(root, sub);
	d = (double) m / ((double) n * (n - 1) / 2.0);
	return d;
}

/**
 * @brief Find the vertex with minimum "good" degree in a subset.
 *
 * Only edges with selectivity <= border_selectivity are counted
 * toward a vertex's degree, consistent with the density metric.
 *
 * @param sub Vertex subset.
 *
 * @return Vertex with the lowest internal degree.
 */
static Vertex *
find_min_degree_vertex(PlannerInfo *root, List *sub)
{
	int			best_deg = INT_MAX;
	Vertex	   *best_v = NULL;
	ListCell   *lc = NULL;

	foreach(lc, sub)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			deg = 0;
		ListCell   *lc2 = NULL;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (list_member_ptr(sub, nbr))
			{
				Selectivity sel = get_selectivity(root, v->rel, nbr->rel);

				if (sel <= border_selectivity)
				{
					deg++;
				}
			}
		}

		if (deg < best_deg)
		{
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
List *
find_dense_subgraphs(PlannerInfo *root, List *vertexes, bool *used)
{
	List	   *dense_sets = NIL;	/* List* of Topology* */

	while (true)
	{
		List	   *candidate = NIL;
		ListCell   *lc = NULL;
		Topology   *topology = NULL;
		double		final_density;

		foreach(lc, vertexes)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

			if (!used[v->index])
			{
				candidate = lappend(candidate, v);
			}
		}

		if (list_length(candidate) < 4)
		{
			list_free(candidate);
			break;
		}

		while (list_length(candidate) >= 4)
		{
			Vertex	   *vmin = NULL;
			double		cur_density = density(root, candidate);

			if (cur_density >= THRESH)
			{
				break;
			}

			vmin = find_min_degree_vertex(root, candidate);
			if (vmin == NULL)
			{
				break;
			}

			candidate = list_delete_ptr(candidate, vmin);
		}

		final_density = density(root, candidate);
		if (list_length(candidate) < 4 || final_density < THRESH)
		{
			list_free(candidate);
			break;
		}
		topology = (Topology *) palloc0(sizeof(Topology));
		topology->vertexes = candidate;
		topology->form = DENSITY_GRAPH;
		set_id(root, topology);
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);
		dense_sets = lappend(dense_sets, topology);
		/* print_topology(topology); */
		foreach(lc, candidate)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

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
static void
set_complexity_topology(PlannerInfo *root, Topology * topology)
{
	DPHypContext context = {0};
	List	   *initial_rels = NIL;
	ListCell   *lc = NULL;
	uint64		subgraphs_count;

	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		initial_rels = lappend(initial_rels, v->rel);
	}
	context.initial_rels = initial_rels;
	context.root = root;
	context.simple_hypernodes = NIL;

	initialize_edges(root, initial_rels, &context);

	subgraphs_count = count_cc(&context, dphyp_geqo_cc_threshold);
	topology->ccp = subgraphs_count;
	list_free(context.initial_rels);
	list_free(context.simple_hypernodes);
	pfree(context.simple_edges);
	pfree(context.complex_edges);
	hash_destroy(context.dptable);
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
Selectivity
get_selectivity(PlannerInfo *root, RelOptInfo *rel1,
				RelOptInfo *rel2)
{
	RelOptInfo	joinrel = {0};
	SpecialJoinInfo sjinfo;
	List	   *clauses;
	Selectivity result;

	Relids		base_relids = bms_union(rel1->relids, rel2->relids);

	init_dummy_sjinfo(&sjinfo, rel1->relids, rel2->relids);
	joinrel.relids =
		add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);
	clauses =
		build_joinrel_restrictlist(root, &joinrel, rel1, rel2, &sjinfo);

	result =
		clauselist_selectivity(root, clauses, 0, JOIN_INNER, &sjinfo);
	if (joinrel.relids != base_relids)
	{
		bms_free(base_relids);
	}
	bms_free(joinrel.relids);
	return result;
}

/**
 * @brief Compute topology volume as product of row counts.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
void
set_vol_topology(PlannerInfo *root, Topology * topology)
{
	Cardinality vol = 1;
	List	   *vertexes = topology->vertexes;
	ListCell   *i = NULL;

	foreach(i, vertexes)
	{
		RelOptInfo *rel = ((Vertex *) lfirst(i))->rel;

		vol *= rel->rows;
	}
	topology->vol = vol;
}

void
set_id(PlannerInfo *root, Topology * topology)
{
	ListCell   *lc = NULL;

	topology->id = root->last_topology_id++;
	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		v->topology_id = topology->id;
	}
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
void
set_sel_topology(PlannerInfo *root, Topology * topology)
{
	Selectivity sel = 1.0;
	List	   *vertexes = topology->vertexes;
	ListCell   *lc;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		ListCell   *lc2;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (v->index < nbr->index &&
				nbr->topology_id == v->topology_id)
			{
				sel *= get_selectivity(root, v->rel, nbr->rel);
			}
		}
	}

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
Cost
cost_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Cost		min_cost = DBL_MAX;
	JoinPathExtraData extra = {0};
	RelOptInfo *outer_rels[2] = {rel1, rel2};
	RelOptInfo *inner_rels[2] = {rel2, rel1};

	for (int i = 0; i < 2; i++)
	{
		RelOptInfo *outer_rel = outer_rels[i];
		RelOptInfo *inner_rel = inner_rels[i];
		Path	   *outer_path = outer_rel->cheapest_total_path;
		Path	   *inner_path = inner_rel->cheapest_total_path;
		JoinCostWorkspace workspace;
		List	   *hashclauses = NIL;
		List	   *mergeclauses = NIL;
		SpecialJoinInfo sjinfo;
		RelOptInfo	joinrel = {0};

		List	   *restrictlist = NIL;
		ListCell   *lc = NULL;
		Relids		base_relids = NULL;

		/* memset(&joinrel, 0, sizeof(RelOptInfo)); */
		if (PATH_PARAM_BY_REL(outer_path, inner_rel) ||
			PATH_PARAM_BY_REL(inner_path, outer_rel))
		{
			continue;
		}
		base_relids = bms_union(outer_rel->relids, inner_rel->relids);

		init_dummy_sjinfo(&sjinfo, outer_rel->relids, inner_rel->relids);
		joinrel.relids = add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);

		restrictlist = build_joinrel_restrictlist(root, &joinrel, outer_rel,
												  inner_rel, &sjinfo);

		extra.restrictlist = restrictlist;
		extra.mergeclause_list = NIL;
		extra.inner_unique = false;
		extra.sjinfo = &sjinfo;
		extra.param_source_rels = joinrel.relids;

		initial_cost_nestloop(root, &workspace, JOIN_INNER, outer_path, inner_path,
							  &extra);
		if (workspace.total_cost < min_cost)
		{
			min_cost = workspace.total_cost;
		}

		foreach(lc, restrictlist)
		{
			RestrictInfo *restrictinfo = (RestrictInfo *) lfirst(lc);

			if (!restrictinfo->can_join ||
				restrictinfo->hashjoinoperator == InvalidOid)
			{
				continue;
			}

			if (!clause_sides_match_join(restrictinfo, outer_rel->relids,
										 inner_rel->relids))
			{
				continue;
			}

			if (!restrictinfo->outer_is_left &&
				!OidIsValid(
							get_commutator(castNode(OpExpr, restrictinfo->clause)->opno)))
			{
				continue;
			}

			hashclauses = lappend(hashclauses, restrictinfo);
		}

		if (hashclauses != NIL)
		{
			initial_cost_hashjoin(root, &workspace, JOIN_INNER, hashclauses,
								  outer_path, inner_path, &extra, false);
			if (workspace.total_cost < min_cost)
			{
				min_cost = workspace.total_cost;
			}
		}

		mergeclauses = find_mergeclauses_for_outer_pathkeys(
															root, outer_path->pathkeys, restrictlist);

		if (mergeclauses != NIL)
		{
			List	   *outersortkeys = outer_path->pathkeys;
			List	   *innersortkeys =
				make_inner_pathkeys_for_merge(root, mergeclauses, outersortkeys);

			/*
			 * Callers are expected to clear the explicit sort keys when the
			 * input path is already ordered.  Be forgiving here in case a
			 * caller forgets to do so and avoid redundant work instead of
			 * tripping the assertion below.
			 */
			if (outersortkeys &&
				pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
			{
				outersortkeys = NIL;
			}

			if (innersortkeys &&
				pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
			{
				innersortkeys = NIL;
			}
			initial_cost_mergejoin(root, &workspace, JOIN_INNER, mergeclauses,
								   outer_path, inner_path, outersortkeys,
								   innersortkeys, 0, &extra);
			if (workspace.total_cost < min_cost)
			{
				min_cost = workspace.total_cost;
			}
		}
		if (joinrel.relids != base_relids)
			bms_free(base_relids);
		bms_free(joinrel.relids);
	}

	return min_cost;
}

void
print_trace(RelOptInfo *rel)
{
	StringInfoData buf;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_TRACE\n");
	appendStringInfo(&buf, "%s\n", rel->trace);
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Free a join graph built by build_join_graph().
 *
 * Frees each Vertex's adjacency list spine, the Vertex struct itself,
 * and the outer list.  Does NOT touch the RelOptInfo* that each Vertex
 * references (those belong to the planner's join_rel_list).
 *
 * @param graph  List of Vertex* to free.  Must have been created by
 *               build_join_graph(); do NOT pass component->vertexes.
 */
void
free_join_graph(List *graph)
{
	ListCell   *lc;

	foreach(lc, graph)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		list_free(v->adj);		/* spine only — neighbors are in the same
								 * list */
		pfree(v);
	}
	list_free(graph);
}
