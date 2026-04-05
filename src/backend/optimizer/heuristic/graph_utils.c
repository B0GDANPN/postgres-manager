#include "postgres.h"
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
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/palloc.h"
#include <float.h>
#include <limits.h>
#include <optimizer/cost.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static const double ANCHOR_RATIO = 100.0;	/* rows < max_nbr / 100 */
static const double ANCHOR_ABS_MAX = 50000.0;	/* absolute cap          */
static List *bfs_component(Vertex * start, bool *used_vertexes);

/**
 * @brief Mark anchor zones (anchor + 1-hop + 2-hop neighbours).
 *
 * An anchor is a vertex with rows < ANCHOR_ABS_MAX whose rows are
 * at least ANCHOR_RATIO times smaller than its heaviest neighbour.
 * Sets used_vertexes[i]=true for all vertices in anchor zones.
 *
 * @param vertexes      List of Vertex* forming the join graph.
 * @param used_vertexes Boolean array indexed by vertex->index (modified).
 * @return Number of newly marked vertices.
 */
int
mark_anchor_zones(List *vertexes, bool *used_vertexes)
{
	int			marked = 0;
	ListCell   *lc;
	List	   *hop1_vertices = NIL;	/* 1-hop neighbours to expand */

	/* Pass 1: find anchors, mark them + their immediate neighbours */
	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		Cardinality max_nbr_rows = 0;
		int			unused_nbrs = 0;
		ListCell   *lc2;

		if (used_vertexes[v->index])
			continue;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (!used_vertexes[nbr->index])
			{
				unused_nbrs++;
				if (nbr->rel->rows > max_nbr_rows)
					max_nbr_rows = nbr->rel->rows;
			}
		}

		if (unused_nbrs == 0)
			continue;

		if (v->rel->rows < ANCHOR_ABS_MAX &&
			v->rel->rows * ANCHOR_RATIO < max_nbr_rows)
		{
			if (!used_vertexes[v->index])
			{
				used_vertexes[v->index] = true;
				marked++;
			}

			foreach(lc2, v->adj)
			{
				Vertex	   *nbr = (Vertex *) lfirst(lc2);

				if (!used_vertexes[nbr->index])
				{
					used_vertexes[nbr->index] = true;
					marked++;
					hop1_vertices = lappend(hop1_vertices, nbr);
				}
			}
		}
	}

	foreach(lc, hop1_vertices)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		ListCell   *lc2;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (!used_vertexes[nbr->index])
			{
				used_vertexes[nbr->index] = true;
				marked++;
			}
		}
	}

	list_free(hop1_vertices);
	return marked;
}

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
	bool		result = !bms_overlap(rel1->relids, rel2->relids) &&
		(have_relevant_joinclause(root, rel1, rel2) || have_join_order_restriction(root, rel1, rel2));

	return result;
}

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


void
print_topology(Topology * topology, TypeTopology type)
{
	StringInfoData buf;
	ListCell   *lc = NULL;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_TOPOLOGY\n");
	switch (type)
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
		case GOO:
			{
				appendStringInfo(&buf, "GOO\n");
				break;
			}
		case DP:
			{
				appendStringInfo(&buf, "DP\n");
				break;
			}
		case DP_SUB:
			{
				appendStringInfo(&buf, "DP_SUB\n");
				break;
			}
		case ANCHORS:
			{
				appendStringInfo(&buf, "ANCHORS\n");
				break;
			}
	}
	appendStringInfo(&buf, "vertexes: ");

	if (type == STAR)
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
 * @brief Build a join graph from a list of relations.
 *
 * Allocates a Vertex per RelOptInfo, discovers edges via has_edge(),
 * and emits a debug print. Caller owns the returned Vertex list.
 *
 * @param root         PlannerInfo context.
 * @param initial_rels List of RelOptInfo* (base or composite).
 * @return List of Vertex* with populated adjacency lists.
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
	/* print_graph(root, vertexes); */
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
 * BFS from each unvisited vertex. Each component becomes a Topology
 * with form=COMPONENT and csg computed via set_complexity_topology.
 *
 * @param root     PlannerInfo context.
 * @param vertexes List of Vertex* (the full join graph).
 * @return List of Topology* (one per connected component).
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
			comps = lappend(comps, component);
		}
	}
	pfree(used_vertexes);
	return comps;
}


/**
 * @brief Reassign sequential indices 0..n-1 to topology vertices.
 *
 * Must be called after any vertex list modification (contraction,
 * rebuild) before algorithms that index by vertex->index.
 *
 * @param component Topology whose vertexes to re-index.
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
 * @brief Compute connected subgraph count (csg) for a topology.
 * @param root     PlannerInfo context.
 * @param topology Topology to update (csg field written).
 */
void
set_complexity_topology(PlannerInfo *root, Topology * topology)
{
	DPHypContext context = {0};
	List	   *initial_rels = NIL;
	ListCell   *lc = NULL;

	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		initial_rels = lappend(initial_rels, v->rel);
	}
	context.initial_rels = initial_rels;
	context.root = root;
	context.simple_hypernodes = NIL;

	initialize_edges(root, initial_rels, &context);

	topology->csg = count_cc(&context, 10000);
	list_free(context.initial_rels);
	list_free(context.simple_hypernodes);
	pfree(context.simple_edges);
	pfree(context.complex_edges);
	hash_destroy(context.dptable);
}

/**
 * @brief Estimate join selectivity between two relations.
 *
 * Constructs a dummy join context and evaluates clause selectivity
 * using PostgreSQL's clauselist_selectivity.
 *
 * @param root PlannerInfo context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 * @return Estimated selectivity in [0, 1].
 */
Selectivity
get_selectivity(PlannerInfo *root, RelOptInfo *rel1,
				RelOptInfo *rel2)
{
	RelOptInfo	joinrel = {0};
	SpecialJoinInfo sjinfo;
	List	   *clauses;
	List	   *unique_clauses = NIL;
	Selectivity result;
	Relids		base_relids = bms_union(rel1->relids, rel2->relids);
	List	   *seen_ecs = NIL;
	ListCell   *lc;

	init_dummy_sjinfo(&sjinfo, rel1->relids, rel2->relids);
	joinrel.relids =
		add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);
	clauses =
		build_joinrel_restrictlist(root, &joinrel, rel1, rel2, &sjinfo);

	/*
	 * Deduplicate clauses that belong to the same EquivalenceClass. When rel1
	 * is composite (e.g., {1,4,6} joined on t1.id=t4.id=t6.id), joining with
	 * rel2 on t1.id=t2.id AND t4.id=t2.id AND t6.id=t2.id produces three
	 * clauses that are functionally redundant. They all share the same
	 * EquivalenceClass.  Keep only one per EC.
	 */
	foreach(lc, clauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (rinfo->parent_ec != NULL)
		{
			if (list_member_ptr(seen_ecs, rinfo->parent_ec))
				continue;		/* redundant — same EC already counted */

			seen_ecs = lappend(seen_ecs, rinfo->parent_ec);
		}
		unique_clauses = lappend(unique_clauses, rinfo);
	}

	result = clauselist_selectivity(root, unique_clauses, 0,
									JOIN_INNER, &sjinfo);

	list_free(seen_ecs);
	list_free(unique_clauses);
	if (joinrel.relids != base_relids)
		bms_free(base_relids);
	bms_free(joinrel.relids);
	return result;
}



/**
 * @brief Estimate minimum join cost between two relations.
 *
 * Tries both (rel1,rel2) and (rel2,rel1) orderings with NestLoop,
 * HashJoin, and MergeJoin initial_cost functions. Returns the
 * minimum across all combinations. Does NOT call make_join_rel.
 *
 * @param root PlannerInfo context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 * @return Minimum estimated join cost (DBL_MAX if no join possible).
 */
Cost
cost_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Cost		min_cost = DBL_MAX;
	RelOptInfo *outer_rels[2] = {rel1, rel2};
	RelOptInfo *inner_rels[2] = {rel2, rel1};

	for (int i = 0; i < 2; i++)
	{
		RelOptInfo *outer_rel = outer_rels[i];
		RelOptInfo *inner_rel = inner_rels[i];
		Path	   *outer_path = outer_rel->cheapest_total_path;
		Path	   *inner_path = inner_rel->cheapest_total_path;
		JoinCostWorkspace workspace;
		JoinPathExtraData extra = {0};
		SpecialJoinInfo sjinfo;
		RelOptInfo	joinrel = {0};
		List	   *restrictlist = NIL;
		List	   *hashclauses = NIL;
		List	   *merge_candidates = NIL;
		List	   *mergeclauses = NIL;
		ListCell   *lc = NULL;
		Relids		base_relids = NULL;

		if (PATH_PARAM_BY_REL(outer_path, inner_rel) ||
			PATH_PARAM_BY_REL(inner_path, outer_rel))
		{
			continue;
		}

		base_relids = bms_union(outer_rel->relids, inner_rel->relids);

		init_dummy_sjinfo(&sjinfo, outer_rel->relids, inner_rel->relids);
		joinrel.relids =
			add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);

		restrictlist = build_joinrel_restrictlist(root, &joinrel, outer_rel,
												  inner_rel, &sjinfo);

		extra.restrictlist = restrictlist;
		extra.mergeclause_list = NIL;
		extra.inner_unique = false;
		extra.sjinfo = &sjinfo;
		extra.param_source_rels = joinrel.relids;

		/* ---- Nestloop ---- */
		initial_cost_nestloop(root, &workspace, JOIN_INNER,
							  outer_path, inner_path, &extra);
		if (workspace.total_cost < min_cost)
			min_cost = workspace.total_cost;

		/* ---- Hashjoin ---- */
		foreach(lc, restrictlist)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (!rinfo->can_join ||
				rinfo->hashjoinoperator == InvalidOid)
				continue;

			if (!clause_sides_match_join(rinfo, outer_rel->relids,
										 inner_rel->relids))
				continue;

			if (!rinfo->outer_is_left &&
				!OidIsValid(
							get_commutator(castNode(OpExpr,
													rinfo->clause)->opno)))
				continue;

			hashclauses = lappend(hashclauses, rinfo);
		}

		if (hashclauses != NIL)
		{
			initial_cost_hashjoin(root, &workspace, JOIN_INNER,
								  hashclauses, outer_path, inner_path,
								  &extra, false);
			if (workspace.total_cost < min_cost)
				min_cost = workspace.total_cost;
		}

		/* ---- Mergejoin ---- */

		/*
		 * Pre-filter: only clauses with mergeopfamilies can participate in a
		 * merge join.  find_mergeclauses_for_outer_pathkeys() calls
		 * update_mergeclause_eclasses() which asserts mergeopfamilies != NIL,
		 * so passing unfiltered restrictlist causes an assertion failure.
		 */
		foreach(lc, restrictlist)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (rinfo->mergeopfamilies != NIL)
				merge_candidates = lappend(merge_candidates, rinfo);
		}

		if (merge_candidates != NIL)
		{
			mergeclauses = find_mergeclauses_for_outer_pathkeys(
																root, outer_path->pathkeys,
																merge_candidates);
		}

		if (mergeclauses != NIL)
		{
			List	   *outersortkeys = outer_path->pathkeys;
			List	   *innersortkeys =
				make_inner_pathkeys_for_merge(root, mergeclauses,
											  outersortkeys);

			if (outersortkeys &&
				pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
				outersortkeys = NIL;

			if (innersortkeys &&
				pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
				innersortkeys = NIL;

			initial_cost_mergejoin(root, &workspace, JOIN_INNER,
								   mergeclauses, outer_path, inner_path,
								   outersortkeys, innersortkeys, 0,
								   &extra);
			if (workspace.total_cost < min_cost)
				min_cost = workspace.total_cost;
		}

		/* Cleanup */
		list_free(hashclauses);
		list_free(merge_candidates);
		list_free(mergeclauses);

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


RelOptInfo *
make_rel(PlannerInfo *root, RelOptInfo *left, RelOptInfo *right)
{
	RelOptInfo *joinrel = make_join_rel(root, left, right);

	if (joinrel)
	{
		generate_partitionwise_join_paths(root, joinrel);
		if (!bms_equal(joinrel->relids, root->all_query_rels))
		{
			generate_useful_gather_paths(root, joinrel, false);
		}
		set_cheapest(joinrel);
	}

	return joinrel;

}

/**
 * @brief Contract anchor zones into pre-planned virtual vertices.
 *
 * Identifies anchors (small rows relative to neighbours), groups them
 * with 1-hop neighbours into zones, plans each zone via
 * standard_join_search, and rebuilds the join graph with virtual
 * vertices replacing zones. Zones whose plan exceeds
 * CONTRACTION_ROW_LIMIT rows are left uncontracted.
 *
 * @param root      PlannerInfo context.
 * @param component Topology with form=COMPONENT (vertexes consumed
 *                  on success, unchanged on no-op).
 * @return Same Topology pointer with (possibly) fewer vertices.
 */
Topology *
contract_anchors(PlannerInfo *root, Topology * component)
{
	int			nv = list_length(component->vertexes);
	bool	   *in_zone;
	bool	   *visited;
	List	   *all_rels = NIL;
	ListCell   *lc;
	int			zone_count = 0;
	int			marked = 0;

	if (nv <= 2)
		return component;

	update_indices(component);

	in_zone = (bool *) palloc0(nv * sizeof(bool));

	foreach(lc, component->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		Cardinality max_nbr_rows = 0;
		ListCell   *lc2;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (nbr->rel->rows > max_nbr_rows)
				max_nbr_rows = nbr->rel->rows;
		}
		if (v->rel->rows < ANCHOR_ABS_MAX &&
			v->rel->rows * ANCHOR_RATIO < max_nbr_rows)
		{
			in_zone[v->index] = true;

			foreach(lc2, v->adj)
			{
				Vertex	   *nbr = (Vertex *) lfirst(lc2);

				in_zone[nbr->index] = true;
			}
		}
	}

	for (int i = 0; i < nv; i++)
	{
		if (in_zone[i])
			marked++;
	}

	if (marked == 0)
	{
		pfree(in_zone);
		return component;
	}

	visited = (bool *) palloc0(nv * sizeof(bool));

	foreach(lc, component->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		List	   *zone_verts;
		List	   *queue;
		int			qi;
		ListCell   *lc2;

		if (!in_zone[v->index] || visited[v->index])
			continue;

		/* BFS restricted to zone subgraph */
		queue = list_make1(v);
		visited[v->index] = true;
		qi = 0;

		while (qi < list_length(queue))
		{
			Vertex	   *cur = (Vertex *) lfirst(list_nth_cell(queue, qi));

			qi++;
			foreach(lc2, cur->adj)
			{
				Vertex	   *nbr = (Vertex *) lfirst(lc2);

				if (in_zone[nbr->index] && !visited[nbr->index])
				{
					visited[nbr->index] = true;
					queue = lappend(queue, nbr);
				}
			}
		}
		zone_verts = queue;

		if (list_length(zone_verts) >= 2)
		{
			List	   *zone_rels = NIL;
			RelOptInfo *zone_plan;

			foreach(lc2, zone_verts)
			{
				Vertex	   *zv = (Vertex *) lfirst(lc2);

				zone_rels = lappend(zone_rels, zv->rel);
			}

			list_free(root->join_rel_list);
			root->join_rel_list = NIL;
			zone_plan = standard_join_search(root, list_length(zone_rels), zone_rels);

			list_free(zone_rels);

			if (zone_plan != NULL && zone_plan->rows <= CONTRACTION_ROW_LIMIT)
			{
				/* print_topology(component,ANCHORS); */
				all_rels = lappend(all_rels, zone_plan);
				zone_count++;
			}
			else
			{
				foreach(lc2, zone_verts)
				{
					Vertex	   *zv = (Vertex *) lfirst(lc2);

					all_rels = lappend(all_rels, zv->rel);
				}
			}
		}
		else
		{
			/* Single-vertex zone — keep as base rel */
			Vertex	   *zv = (Vertex *) linitial(zone_verts);

			all_rels = lappend(all_rels, zv->rel);
		}
		list_free(zone_verts);
	}

	pfree(visited);

	if (zone_count == 0)
	{
		pfree(in_zone);
		list_free(all_rels);
		return component;
	}

	foreach(lc, component->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!in_zone[v->index])
			all_rels = lappend(all_rels, v->rel);
	}

	pfree(in_zone);

	list_free(component->vertexes);
	component->vertexes = build_join_graph(root, all_rels);
	set_complexity_topology(root, component);
	list_free(all_rels);

	return component;
}
