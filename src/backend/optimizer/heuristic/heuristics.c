#include "optimizer/heuristic/heuristics.h"
#include "optimizer/heuristic/graph_utils.h"
#include "nodes/pathnodes.h"
#include "optimizer/paths.h"
#include "port/pg_bitutils.h"
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
				if (!has_edge(root, rel1, rel2))
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
goo_card(PlannerInfo *root, List *initial_rels)
{
	while (list_length(initial_rels) > 1)
	{
		RelOptInfo *best_rel = NULL;
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		Cardinality best_size = DBL_MAX;
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = (RelOptInfo *) lfirst(j);
				Cardinality size;
				RelOptInfo *rel = NULL;

				if (!has_edge(root, rel1, rel2))
				{
					continue;
				}
				rel = make_rel(root, rel1, rel2);
				size = rel->reltarget->width * rel->rows;
				if (size < best_size)
				{
					best_lc1 = i;
					best_lc2 = j;
					best_size = size;
					best_rel = rel;
				}
			}
		}
		if (best_rel == NULL)
		{
			return NULL;
		}
		first = list_cell_number(initial_rels, best_lc1);
		second = list_cell_number(initial_rels, best_lc2);
		initial_rels = lappend(initial_rels, best_rel);
		initial_rels = list_delete_nth_cell(initial_rels, first);
		if (first < second)
		{
			second--;
		}
		initial_rels = list_delete_nth_cell(initial_rels, second);
	}

	return (RelOptInfo *) linitial(initial_rels);
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

RelOptInfo *
dp_sub(PlannerInfo *root, List *initial_rels)
{
	RelOptInfo **best_plans = NULL;
	Cost	   *best_costs = NULL;
	size_t		n = list_length(initial_rels);
	size_t		total_sets = ((size_t) 1) << n;
	RelOptInfo *result = NULL;

	best_plans = (RelOptInfo **) palloc0(total_sets * sizeof(RelOptInfo *));
	best_costs = (Cost *) palloc0(total_sets * sizeof(Cost));
	for (size_t i = 0; i < total_sets; i++)
	{
		best_costs[i] = DBL_MAX;
	}
	for (size_t i = 0; i < n; i++)
	{
		size_t		mask = ((size_t) 1) << i;
		ListCell   *lc = list_nth_cell(initial_rels, i);
		RelOptInfo *rel = (RelOptInfo *) lfirst(lc);

		best_plans[mask] = rel;
		best_costs[mask] = rel->cheapest_total_path->total_cost;
	}

	for (size_t join_bm = 1; join_bm < total_sets; join_bm++)
	{
		size_t		left_bm = (-join_bm) & join_bm;

		if (pg_popcount64(join_bm) <= 1)
		{
			continue;
		}

		/*
		 * if (!is_connected(topology->vertexes, join_bm)) { continue; }
		 */
		while (join_bm != left_bm)
		{
			size_t		right_bm = join_bm - left_bm;
			RelOptInfo *left_plan = best_plans[left_bm];
			RelOptInfo *right_plan = best_plans[right_bm];
			RelOptInfo *join = NULL;
			Cost		cost;

			/* Cost		join_cost; */

			if (left_bm >= right_bm || left_plan == NULL || right_plan == NULL)
			{
				left_bm = (left_bm - join_bm) & join_bm;
				continue;
			}

			if (!has_edge(root, left_plan, right_plan)) /* Maybe unnesesary */
			{
				left_bm = (left_bm - join_bm) & join_bm;
				continue;
			}
			join = make_rel(root, left_plan, right_plan);
			if (join == NULL)
			{
				left_bm = (left_bm - join_bm) & join_bm;
				continue;
			}
			cost = join->cheapest_total_path->total_cost;
			if (cost < best_costs[join_bm])
			{
				best_costs[join_bm] = cost;
				best_plans[join_bm] = join;
			}
			left_bm = (left_bm - join_bm) & join_bm;
		}
	}

	result = best_plans[total_sets - 1];
	pfree(best_plans);
	pfree(best_costs);
	return result;
}
