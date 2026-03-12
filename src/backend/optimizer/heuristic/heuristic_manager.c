#include "postgres.h"
#include "c.h"
#include "common/fe_memutils.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/heuristic/graph_utils.h"
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include "optimizer/heuristic/heuristic_manager.h"
#include "optimizer/heuristic/heuristics.h"


static void split_budget_among_topologies(List *topologies, Cost budget, ListCell *init_cell);

/**
 * @brief Distribute a budget across topologies by estimated complexity.
 *
 * Uses a weighted mix of topology CCP and selectivity to split the budget for
 * the remaining list cells.
 *
 * @param topologies List of Topology items to receive budgets.
 * @param budget Total budget to distribute.
 * @param init_cell Starting cell for partial iteration (or NULL for full list).
 */
static void
split_budget_among_topologies(List *topologies, Cost budget, ListCell *init_cell)
{
	Cost		sum_complexities = 0;
	ListCell   *lc = NULL;
	int			from = 0;
	double		w_ccp,
				w_sel,
				w_vol;

	if (init_cell)
	{
		from = list_cell_number(topologies, init_cell);
	}
	for_each_from(lc, topologies, from)
	{
		Topology   *topology = (Topology *) lfirst(lc);

		if (list_length(topology->vertexes) <= 1)
		{
			topology->budget = 0;
			continue;
		}
		w_ccp = log(1.0 + topology->ccp);
		w_sel = log(1.0 + 1.0 / topology->sel);
		w_vol = log(1.0 + topology->vol);
		sum_complexities += k1 * w_ccp + k2 * w_sel + k3 * w_vol;
	}
	for_each_from(lc, topologies, from)
	{
		Topology   *topology = (Topology *) lfirst(lc);
		double		cur_complexity;

		if (list_length(topology->vertexes) <= 1)
		{
			continue;
		}
		w_ccp = log(1.0 + topology->ccp);
		w_sel = log(1.0 + 1.0 / topology->sel);
		w_vol = log(1.0 + topology->vol);
		cur_complexity = k1 * w_ccp + k2 * w_sel + k3 * w_vol;
		topology->budget = cur_complexity * budget / sum_complexities;
	}
}

/**
 * @brief Heuristic join search over a join graph with a budget.
 *
 * Splits the graph into components, plans each component with topology-specific
 * heuristics and DP, then merges component plans using a greedy join order.
 *
 * @param root Planner context.
 * @param initial_rels Base relations to join.
 *
 * @return Final join plan for all relations.
 */
RelOptInfo *
heuristic_join_search(PlannerInfo *root, List *initial_rels)
{
	List	   *graph = build_join_graph(root, initial_rels);	/* List* of Vertex* */
	List	   *components = split_components(root, graph); /* list of
															 * Topology(COMPONENT)* */
	List	   *component_plans = NIL;
	ListCell   *lc = NULL;

	/* List	   *partial_plans = NULL; */
	RelOptInfo *final_plan = NULL;

	root->last_topology_id = 0;
	root->global_budget = 0;
	root->topology_budget = 0;
	root->spent_budget = 0;
	root->global_budget = DBL_MAX;	/* DEBUG */
	/* split_budget_among_topologies(components, root->global_budget, NULL); */
	foreach(lc, components)
	{
		Topology   *component = (Topology *) lfirst(lc);
		Vertex	   *v = NULL;
		RelOptInfo *comp_plan = NULL;
		Cost		component_budget;
		Cost		current_budget;
		bool		first_iter = true;

		/* split_budget_among_topologies(components, root->global_budget, lc); */

		component_budget = component->budget;
		current_budget = component_budget * b1;

		while (list_length(component->vertexes) > 1)
		{
			bool	   *used_vertexes = NULL;
			List	   *topologies = NIL;	/* List* of Topology*  */
			List	   *dense_subgraphs = NIL;
			List	   *cycles = NIL;
			List	   *stars = NIL;
			List	   *remaining_chains = NIL;
			List	   *topology_plans = NIL;
			ListCell   *lc2 = NULL;

			update_indices(component);
			/* print_topology(component); */
			used_vertexes =
				(bool *) palloc0(list_length(component->vertexes) * sizeof(bool));

			dense_subgraphs = find_dense_subgraphs(root, component->vertexes, used_vertexes);
			topologies = list_concat(topologies, dense_subgraphs);

			stars = find_stars(root, component->vertexes, used_vertexes);
			topologies = list_concat(topologies, stars);

			cycles = find_cycles(root, component->vertexes, used_vertexes);
			topologies = list_concat(topologies, cycles);

			remaining_chains = find_chains(root, component->vertexes, used_vertexes);
			topologies = list_concat(topologies, remaining_chains);

			/* split_budget_among_topologies(topologies, current_budget,
			 * NULL); */

			foreach(lc2, topologies)
			{
				Topology   *topology = (Topology *) lfirst(lc2);
				RelOptInfo *plan;

				root->spent_budget = 0;
				root->topology_budget = topology->budget;
				plan = plan_topology(root, topology);

				/* print_trace(plan); */

				topology_plans = lappend(topology_plans, plan);
				current_budget -= root->spent_budget;
			}
			component_budget += current_budget; /* maybe remain budget */
			current_budget = component_budget * q;

			if (first_iter)
			{
				list_free(component->vertexes); /* spine only — Vertex*
												 * owned by component */
				first_iter = false;
			}
			else
			{
				free_join_graph(component->vertexes);
			}
			list_free(topologies);
			component->vertexes = build_join_graph(root, topology_plans);
			list_free(topology_plans);
			pfree(used_vertexes);
		}
		v = (Vertex *) linitial(component->vertexes);
		comp_plan = v->rel;
		component_plans = lappend(component_plans, comp_plan);
		root->global_budget -= (component->budget - component_budget);
	}
	root->spent_budget = 0;
	root->topology_budget = root->global_budget;
	final_plan = goo_cost_cardinality(root, component_plans, true);
	if (root->global_budget >= root->spent_budget)
	{
		root->global_budget -= root->spent_budget;
	}
	list_free(component_plans);
	list_free(components);
	list_free(graph);
	return final_plan;
}
