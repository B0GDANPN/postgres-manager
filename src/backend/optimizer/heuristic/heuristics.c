#include "optimizer/heuristic/heuristics.h"
#include "optimizer/heuristic/graph_utils.h"
#include "nodes/pathnodes.h"
#include "optimizer/paths.h"
#include <float.h>
#include <limits.h>
#include <string.h>

/**
 * @brief Greedy join ordering with mixed cost/cardinality criterion.
 *
 * Iteratively picks the best pair from the remaining relations and
 * merges them.  For "small" pairs (both ≤ 2 base rels) compares by
 * cheapest_total_path cost; for larger composites compares by
 * estimated result size (width × rows).  Produces bushy trees.
 * Falls back to cross-joins if clauseless=true and no edge found.
 *
 * @param root         PlannerInfo context.
 * @param initial_rels List of RelOptInfo* (consumed in-place).
 * @param clauseless   If true, allow cross-joins as last resort.
 * @return Single fully-joined RelOptInfo*, or NULL if no plan found.
 */
RelOptInfo *
goo_cost_cardinality(PlannerInfo *root, List *initial_rels,
					 bool clauseless)
{
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cost		best_cost = DBL_MAX;
		Cardinality best_size = DBL_MAX;
		ListCell   *i = NULL;
		int			first;
		int			second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;
				RelOptInfo *rel = NULL;
				bool		is_simple_pair;
				Cost		cost;
				Cardinality size;

				rel2 = (RelOptInfo *) lfirst(j);
				if (!clauseless && !has_edge(root, rel1, rel2))
					continue;
				if (clauseless && !has_edge(root, rel1, rel2))
				{
					/*
					 * Clauseless mode: allow cross-joins, but only consider
					 * them if no normal edge was found yet. Skip for now —
					 * handled below if best_lc1 stays NULL.
					 */
					continue;
				}

				rel = make_rel(root, rel1, rel2);
				if (rel == NULL || rel->cheapest_total_path == NULL)
					continue;

				cost = rel->cheapest_total_path->total_cost;
				size = rel->reltarget->width * rel->rows;

				if (best_lc1 == NULL)
				{
					best_cost = cost;
					best_size = size;
					best_rel = rel;
					best_lc1 = i;
					best_lc2 = j;
					continue;
				}

				is_simple_pair = (bms_num_members(rel1->relids) <= 2) &&
					(bms_num_members(rel2->relids) <= 2);
				if (is_simple_pair)
				{
					if (cost < best_cost)
					{
						best_cost = cost;
						best_size = size;
						best_rel = rel;
						best_lc1 = i;
						best_lc2 = j;
					}
					continue;
				}
				if (size < best_size)
				{
					best_cost = cost;
					best_size = size;
					best_rel = rel;
					best_lc1 = i;
					best_lc2 = j;
				}
			}
		}

		if (best_lc1 == NULL || best_lc2 == NULL)
		{
			if (!clauseless || list_length(initial_rels) <= 1)
				break;

			/*
			 * No edge-connected pair found, but clauseless mode is on and
			 * multiple rels remain.  Force a cross-join between the cheapest
			 * pair (by cost).
			 */
			foreach(i, initial_rels)
			{
				RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
				ListCell   *j;

				for_each_cell(j, initial_rels, lnext(initial_rels, i))
				{
					RelOptInfo *rel2 = (RelOptInfo *) lfirst(j);
					RelOptInfo *rel = make_rel(root, rel1, rel2);

					if (rel == NULL || rel->cheapest_total_path == NULL)
						continue;
					if (rel->cheapest_total_path->total_cost < best_cost)
					{
						best_cost = rel->cheapest_total_path->total_cost;
						best_rel = rel;
						best_lc1 = i;
						best_lc2 = j;
					}
				}
			}
			if (best_lc1 == NULL)
				break;
		}

		first = list_cell_number(initial_rels, best_lc1);
		second = list_cell_number(initial_rels, best_lc2);
		initial_rels = lappend(initial_rels, best_rel);
		initial_rels = list_delete_nth_cell(initial_rels, first);
		if (first < second)
			second--;
		initial_rels = list_delete_nth_cell(initial_rels, second);
	}


	return (RelOptInfo *) linitial(initial_rels);
}


RelOptInfo *
standard_planning_wrapper(PlannerInfo *root, Topology * topology)
{
	List	   *topology_rels = NIL;
	RelOptInfo *result = NULL;
	ListCell   *lc2 = NULL;

	foreach(lc2, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc2);

		topology_rels = lappend(topology_rels, v->rel);
	}
	result = standard_join_search(root, list_length(topology_rels), topology_rels);
	list_free(topology_rels);
	return result;

}

RelOptInfo *
goo_wrapper(PlannerInfo *root, Topology * topology, bool clauseless)
{
	List	   *topology_rels = NIL;
	RelOptInfo *result = NULL;
	ListCell   *lc2 = NULL;

	foreach(lc2, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc2);

		topology_rels = lappend(topology_rels, v->rel);
	}
	result = goo_cost_cardinality(root, topology_rels, clauseless);
	list_free(topology_rels);
	return result;

}
