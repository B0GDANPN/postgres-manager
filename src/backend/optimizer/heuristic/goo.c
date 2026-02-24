#include "postgres.h"
#include "c.h"
#include "optimizer/heuristic/goo.h"
#include <float.h>
#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/heuristic/heuristic_manager.h"
/**
 * @brief Greedy operator ordering (GOO) join ordering.
 *
 * Repeatedly joins the cheapest pair, optionally requiring a join clause.
 *
 * @param root Planner context.
 * @param initial_rels Relations to join.
 * @param clauseless If false, only joins with a simple inner edge.
 *
 * @return Final join plan.
 */
List *
goo_init_cost_init_result(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force)
{
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cost		best_cost = DBL_MAX;
		Cardinality      best_size = DBL_MAX;
        bool        best_is_base_pair = false;
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;
				bool        is_base_pair;
				Cost		prel_join_cost;

				rel2 = (RelOptInfo *) lfirst(j);
				if (!clauseless && !has_edge(root, rel1, rel2))
				{
					continue;
				}
				prel_join_cost = cost_edge(root, rel1, rel2);

				if (!force && (root->spent_budget + prel_join_cost >
							   root->topology_budget * budget_soft_limit))
				{
					return initial_rels;
				}
				/*
                 * A "base pair" is one where both inputs are single
                 * base relations — cost_edge is accurate here.
                 * For composite rels, use estimated result size instead.
                 */
                is_base_pair = (bms_num_members(rel1->relids) == 1 &&
                                bms_num_members(rel2->relids) == 1);

                if (best_lc1 == NULL)
                {
                    /* First viable pair — always accept */
                    best_cost = prel_join_cost;
                    best_size = rel1->rows * rel2->rows *
                        get_selectivity(root, rel1, rel2);
                    best_is_base_pair = is_base_pair;
                    best_lc1 = i;
                    best_lc2 = j;
                }
                else if (is_base_pair && best_is_base_pair)
                {
                    /* Both are base pairs — compare by cost */
                    if (prel_join_cost < best_cost)
                    {
                        best_cost = prel_join_cost;
                        best_size = rel1->rows * rel2->rows *
                            get_selectivity(root, rel1, rel2);
                        best_lc1 = i;
                        best_lc2 = j;
                    }
                }
                else if (!is_base_pair && !best_is_base_pair)
                {
                    /* Both are composite — compare by result size */
                    Selectivity sel = get_selectivity(root, rel1, rel2);
                    double      size = rel1->rows * rel2->rows * sel;

                    if (size < best_size)
                    {
                        best_cost = prel_join_cost;
                        best_size = size;
                        best_lc1 = i;
                        best_lc2 = j;
                    }
                }
                else if (is_base_pair && !best_is_base_pair)
                {
                    /*
                     * Prefer base-pair joins over composite joins:
                     * base pairs have accurate costs and produce
                     * smaller intermediates that improve later joins.
                     */
                    best_cost = prel_join_cost;
                    best_size = rel1->rows * rel2->rows *
                        get_selectivity(root, rel1, rel2);
                    best_is_base_pair = true;
                    best_lc1 = i;
                    best_lc2 = j;
                }
                /* else: current best is base_pair, candidate is composite
				 *       — keep the base pair, skip this candidate */
			}
		}
		if (best_lc1 == NULL || best_lc2 == NULL)
		{
			return initial_rels;
		}
		{
            RelOptInfo *best_rel1 = (RelOptInfo *) lfirst(best_lc1);
            RelOptInfo *best_rel2 = (RelOptInfo *) lfirst(best_lc2);

            best_rel = make_rel(root, best_rel1, best_rel2);
        }
		root->spent_budget += best_cost;	/* best_rel->cheapest_total_path->total_cost */
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

	return initial_rels;
}

List * goo_final_cost_final_result(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force){
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cost		best_cost = DBL_MAX;
		Cardinality      best_size = DBL_MAX;
        bool        best_is_base_pair = false;
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;
				RelOptInfo *rel = NULL;
				bool        is_base_pair;
				Cost	cost;
				Cardinality size;

				rel2 = (RelOptInfo *) lfirst(j);
				if (!clauseless && !has_edge(root, rel1, rel2))
				{
					continue;
				}
				rel = make_rel(root, rel1, rel2);
				cost = rel->cheapest_total_path->total_cost;
				size =  rel->reltarget->width * rel->rows;
				if (!force && (root->spent_budget + cost >
							   root->topology_budget * budget_soft_limit))
				{
					return initial_rels;
				}
				/*
                 * A "base pair" is one where both inputs are single
                 * base relations — cost_edge is accurate here.
                 * For composite rels, use estimated result size instead.
                 */
                is_base_pair = (bms_num_members(rel1->relids) == 1 &&
                                bms_num_members(rel2->relids) == 1);

                if (best_lc1 == NULL)
                {
                    /* First viable pair — always accept */
                    best_cost = cost;
                    best_size = size;
					best_rel = rel;
                    best_is_base_pair = is_base_pair;
                    best_lc1 = i;
                    best_lc2 = j;
					continue;
                }
                if (is_base_pair && best_is_base_pair)
                {
                    /* Both are base pairs — compare by cost */
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
                if (!is_base_pair && !best_is_base_pair)
                {
                    if (size < best_size)
                    {
                        best_cost = cost;
                        best_size = size;
						best_rel = rel;
                        best_lc1 = i;
                        best_lc2 = j;
                    }
					continue;
                }
				if (cost < best_cost)
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
			return initial_rels;
		}
		root->spent_budget += best_cost;	/* best_rel->cheapest_total_path->total_cost */
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

	return initial_rels;
}

List *goo_init_result(PlannerInfo *root, List *initial_rels,
				 bool clauseless){
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cardinality      best_size = DBL_MAX;
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
				Selectivity sel;
				Cardinality size;

				if (!clauseless && !has_edge(root, rel1, rel2))
				{
					continue;
				}
				
				sel = get_selectivity(root, rel1, rel2);
				size = rel1->rows * rel2->rows * sel;

				if (size < best_size)
				{
					best_size = size;
					best_lc1 = i;
					best_lc2 = j;
				}
			}
		}
		if (best_lc1 == NULL || best_lc2 == NULL)
		{
			return initial_rels;
		}
		{
            RelOptInfo *best_rel1 = (RelOptInfo *) lfirst(best_lc1);
            RelOptInfo *best_rel2 = (RelOptInfo *) lfirst(best_lc2);

            best_rel = make_rel(root, best_rel1, best_rel2);
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

	return initial_rels;
}

List *goo_final_result(PlannerInfo *root, List *initial_rels,
				 bool clauseless){
	while (list_length(initial_rels) > 1)
	{
		RelOptInfo *best_rel = NULL;
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		Cardinality      best_size = DBL_MAX;
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
				if (!clauseless && !has_edge(root, rel1, rel2))
				{
					continue;
				}
				rel =make_rel( root, rel1, rel2);
				size = rel->reltarget->width * rel->rows;
				if (size < best_size)
				{
					best_lc1=i;
					best_lc2=j;
					best_size = size;
					best_rel =rel;
				}
			}
		}
		if (best_rel == NULL)
		{
			return initial_rels;
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

	return initial_rels;
}

List *
goo_init_cost(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force)	/* TODO cost (1), select(2), sizes(3+) */
{
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel1 = NULL;
		RelOptInfo *best_rel2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cost		best_cost = DBL_MAX;
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;

				rel2 = (RelOptInfo *) lfirst(j);
				if (clauseless || has_edge(root, rel1, rel2))
				{
					Cost		prel_join_cost = cost_edge(root, rel1, rel2);

					if (!force && (root->spent_budget + prel_join_cost >
								   root->topology_budget * budget_soft_limit))
					{
						return initial_rels;
					}
					if (prel_join_cost < best_cost)
					{
						best_cost = prel_join_cost;
						best_lc1 = i;
						best_lc2 = j;
					}
				}
			}
		}
		if (best_lc1 == NULL || best_lc2 == NULL)
		{
			return initial_rels;
		}
		best_rel1 = (RelOptInfo *) lfirst(best_lc1);
		best_rel2 = (RelOptInfo *) lfirst(best_lc2);
		best_rel = make_rel(root, best_rel1, best_rel2);
		root->spent_budget += best_rel->cheapest_total_path->total_cost;
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

	return initial_rels;
}

List *
goo_final_cost(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force)	/* TODO cost (1), select(2), sizes(3+) */
{
	while (list_length(initial_rels) > 1)
	{
		ListCell   *best_lc1 = NULL;
		ListCell   *best_lc2 = NULL;
		RelOptInfo *best_rel = NULL;
		Cost		best_cost = DBL_MAX;
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;

				rel2 = (RelOptInfo *) lfirst(j);
				if (clauseless || has_edge(root, rel1, rel2))
				{	
					RelOptInfo* rel =make_rel(root,rel1,rel2);
					Cost cost = rel->cheapest_total_path->total_cost;

					if (!force && (root->spent_budget + cost >
								   root->topology_budget * budget_soft_limit))
					{
						return initial_rels;
					}
					if (cost < best_cost)
					{
						best_cost = cost;
						best_rel = rel;
						best_lc1 = i;
						best_lc2 = j;
					}
				}
			}
		}
		if (best_lc1 == NULL || best_lc2 == NULL)
		{
			return initial_rels;
		}
		root->spent_budget += best_cost;
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

	return initial_rels;
}

List * dummy(PlannerInfo *root, List *initial_rels){
	while (list_length(initial_rels) > 1)
	{
		ListCell   *i = NULL;
		int			first,
					second;

		foreach(i, initial_rels)
		{
			RelOptInfo *rel1 = (RelOptInfo *) lfirst(i);
			ListCell   *j = NULL;

			for_each_cell(j, initial_rels, lnext(initial_rels, i))
			{
				RelOptInfo *rel2 = NULL;
				RelOptInfo* rel;
				rel2 = (RelOptInfo *) lfirst(j);
				if (!has_edge(root, rel1, rel2))
				{
					continue;
				}	
				rel =make_rel(root,rel1,rel2);
				first = list_cell_number(initial_rels, i);
				second = list_cell_number(initial_rels, j);
				initial_rels = lappend(initial_rels, rel);
				initial_rels = list_delete_nth_cell(initial_rels, first);
				if (first < second)
				{
					second--;
				}
				initial_rels = list_delete_nth_cell(initial_rels, second);
			}
		}
	}
	return initial_rels;
}