#include "postgres.h"
#include "nodes/pg_list.h"
#include "c.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include <limits.h>
#include <float.h>
#include <stdbool.h>
#include <string.h>
#include "optimizer/pathnode.h"
#include "optimizer/heuristic/heuristic_manager.h"
#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/paths.h"
#include "optimizer/optimizer.h"
#include "optimizer/geqo.h"
static double b1 = 3 / 4;
static double q = 1 / 4;
static double k1 = 0.5;
static double k2 = 0.5;
typedef enum { STANDARD, GOO, GEQO } TypeHeuristic;
static List *choose_min_cost_cover(List *partial_plans);
static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan);

static RelOptInfo *goo(PlannerInfo *root, List *component_plans, bool clauseless);
static List *plan_chain_dp(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static void split_budget_among_topologies(List *topologies, uint64 budget, ListCell *init_cell);
///////////////////////////////////////////////////////////////////////////////////

static void split_budget_among_topologies(List *topologies, uint64 budget, ListCell *init_cell)
{
	uint64 sum_complexities = 0;
	ListCell *lc;
	for_each_cell (lc, topologies, init_cell) {
		Topology *topology = (Topology *)lfirst(lc);
		double k_sel = 1 / topology->sel;
		sum_complexities += k1 * topology->ccp + k2 * k_sel;
	}
	for_each_cell (lc, topologies, init_cell) {
		Topology *topology = (Topology *)lfirst(lc);
		topology->budget = topology->ccp * budget / sum_complexities;
	}
}

RelOptInfo *heuristic_join_search(PlannerInfo *root, List *initial_rels, int budget)
{
	List *graph = build_join_graph(root, initial_rels); // List* of Vertex*
	List *components = split_components(root, graph);   // list of Topology(COMPONENT)*
	split_budget_among_topologies(components, budget, NULL);
	List *component_plans = NIL;
	ListCell *lc = NULL;
	uint64 component_budget = 0;
	foreach (lc, components) {
		if (component_budget > 0) {
			split_budget_among_topologies(components, budget, lc);
		}
		Topology *component = (Topology *)lfirst(lc);

		List *comp_vertexes = component->vertexes; // List* of Vertex*

		component_budget = component->budget;
		uint64 current_budget = component_budget * b1;
		while (list_length(comp_vertexes) > 1) {
			update_indices(component);
			bool *used_vertexes =
				(bool *)palloc0(list_length(comp_vertexes) * sizeof(bool));

			List *topologies = NIL; // List* of Topology*
			List *dense_subgraphs =
				find_dense_subgraphs(root, comp_vertexes, used_vertexes);
			topologies = list_concat(topologies, dense_subgraphs);
			List *cycles = find_cycles(root, comp_vertexes, used_vertexes);
			topologies = list_concat(topologies, cycles);
			List *stars = find_stars(root, comp_vertexes, used_vertexes);
			topologies = list_concat(topologies, stars);
			List *remaining_chains = find_chains(root, comp_vertexes, used_vertexes);
			topologies = list_concat(topologies, remaining_chains);
			split_budget_among_topologies(topologies, current_budget, NULL);

			List *topology_plans = NIL;
			foreach (lc, topologies) {
				Topology *topology = (Topology *)lfirst(lc);
				Cost cost_plan = 0;
				RelOptInfo *plan = plan_subgraph(root, topology, &cost_plan);
				topology_plans = lappend(topology_plans, plan);
				current_budget -= cost_plan;
			}
			component_budget += current_budget; // maybe remain budget
			current_budget = component_budget * q;
			list_free(comp_vertexes);
			comp_vertexes = build_join_graph(root, topology_plans);
			pfree(used_vertexes);
		}
		Vertex *v = (Vertex *)linitial(comp_vertexes);
		RelOptInfo *comp_plan = v->rel;
		component_plans = lappend(component_plans, comp_plan);
	}
	RelOptInfo *final_plan = goo(root, component_plans, true);
	list_free(graph);
	return final_plan;
}

static RelOptInfo *goo(PlannerInfo *root, List *initial_rels, bool clauseless)
{
	while (list_length(initial_rels) > 1) {
		RelOptInfo *parent1 = NULL, *parent2 = NULL;
		Selectivity best_sel = 1;
		Cost best_cost = DBL_MAX;
		ListCell *i, *j;

		foreach (i, initial_rels) {
			foreach (j, initial_rels) {
				if (i == j) {
					continue;
				}
				RelOptInfo *r_i = (RelOptInfo *)lfirst(i);
				RelOptInfo *r_j = (RelOptInfo *)lfirst(j);
				if (!clauseless && !has_simple_inner_edge(root, r_i, r_j)) {
					continue;
				}
				Selectivity tmp_sel = get_selectivity(root, r_i, r_j);
				if (tmp_sel < best_sel) {
					best_sel = tmp_sel;
					parent1 = r_i;
					parent2 = r_j;
				}
			}
		}
		RelOptInfo *best_rel = make_join_rel(root, parent1, parent2);
		set_cheapest(best_rel);
		initial_rels = lappend(initial_rels, best_rel);
		initial_rels = list_delete_cell(initial_rels, parent1);
		initial_rels = list_delete_cell(initial_rels, parent2);
	}

	RelOptInfo *plan = (RelOptInfo *)linitial(initial_rels);
	return plan;
}

/*
 * choose_min_cost_cover
 *
 * Greedy set cover that selects the cheapest combination of partial plans
 * whose relids together cover all relids present in the input list. The
 * heuristic prefers plans with the lowest cost per newly covered rel and, in
 * case of ties, the cheapest plan overall.
 */
static List *choose_min_cost_cover(List *partial_plans)
{
	Bitmapset *uncovered = NULL;
	ListCell *lc;

	foreach (lc, partial_plans) {
		RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
		uncovered = bms_add_members(uncovered, rel->relids);
	}

	List *coverage = NIL;
	List *remaining = list_copy(partial_plans);

	while (!bms_is_empty(uncovered)) {
		RelOptInfo *best_rel = NULL;
		ListCell *best_cell = NULL;
		double best_score = DBL_MAX;
		Cost best_cost = DBL_MAX;

		foreach (lc, remaining) {
			RelOptInfo *candidate = (RelOptInfo *)lfirst(lc);
			Bitmapset *newly = bms_intersect(uncovered, candidate->relids);
			int newly_covered = bms_num_members(newly);
			bms_free(newly);
			if (newly_covered == 0) {
				continue;
			}

			Cost cost = candidate->cheapest_total_path->total_cost;
			double score = cost / (double)newly_covered;

			if (score < best_score || (score == best_score && cost < best_cost)) {
				best_score = score;
				best_cost = cost;
				best_rel = candidate;
				best_cell = lc;
			}
		}

		if (best_rel == NULL) {
			break;
		}

		coverage = lappend(coverage, best_rel);
		uncovered = bms_del_members(uncovered, best_rel->relids);
		remaining = list_delete_cell(remaining, best_cell);
	}

	bms_free(uncovered);
	list_free(remaining);

	return coverage;
}

static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	// cost_plan -- final cost plannitg this topology
	RelOptInfo *plan = NULL;
	List *partial_plans = NIL;
	Cost cost_tmp_plan = 0;
	switch (topology->form) {
	case CHAIN:
		partial_plans = plan_chain_dp(root, topology, &cost_tmp_plan);
	case CYCLE:
		partial_plans = plan_cycle(root, topology, &cost_tmp_plan);
	case STAR:
		partial_plans = plan_star(root, topology, &cost_tmp_plan);
	case DENSITY_GRAPH:
	case COMPONENT:
		break;
	}
	topology->budget -= cost_tmp_plan;
	*cost_plan += cost_tmp_plan;
	cost_tmp_plan = 0;
	if (list_length(partial_plans) == 1) {
		plan = (RelOptInfo *)linitial(partial_plans);
		return plan;
	}

	//  fail planning DP, very expensive, so try cheaper.
	List *initial_rels = choose_min_cost_cover(partial_plans);

	partial_plans = standard_join_search(root,
					     list_length(initial_rels),
					     initial_rels,
					     topology->budget,
					     &cost_tmp_plan);

	topology->budget -= cost_tmp_plan;
	*cost_plan += cost_tmp_plan;
	cost_tmp_plan = 0;
	if (list_length(partial_plans) == 1) {
		plan = (RelOptInfo *)linitial(partial_plans);
		return plan;
	}

	// specialized heuristis very expensive, so GOO.
	initial_rels = choose_min_cost_cover(partial_plans);
	plan = goo(root, initial_rels, false, cost_tmp_plan);
	topology->budget -= cost_tmp_plan;
	*cost_plan += cost_tmp_plan;
	cost_tmp_plan = 0;
	// RelOptInfo *plan = geqo(root, list_length(initial_rels), initial_rels);
	return plan;
}

static List *plan_chain_dp(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	int n = list_length(topology->vertexes);
	int i, j, k;
	if (n == 0) {
		*cost_plan = 0;
		return NIL;
	}

	RelOptInfo ***dp = (RelOptInfo ***)palloc0(n * sizeof(RelOptInfo **));
	for (i = 0; i < n; i++) {
		dp[i] = (RelOptInfo **)palloc0(n * sizeof(RelOptInfo *));
	}

	for (i = 0; i < n; i++) {
		for (j = 0; j < n; j++) {
			if (i == j) {
				Vertex *v_i = (Vertex *)list_nth_cell(topology->vertexes, i);
				dp[i][i] = v_i->rel;
				continue;
			}
			dp[i][j] = NULL;
		}
	}

	for (int len = 2; len <= n; len++) {
		for (int i = 0; i <= n - len; i++) {
			j = i + len - 1;

			for (k = i; k < j; k++) {
				if (dp[i][k] == NULL || dp[k + 1][j] == NULL) {
					continue;
				}
				Cost prel_join_cost =
					cost_simple_edge(root, dp[i][k], dp[k + 1][j]);
				if (*cost_plan + prel_join_cost > topology->budget) {
					break;
				}
				RelOptInfo *join = make_join_rel(root, dp[i][k], dp[k + 1][j]);
				if (join == NULL) {
					continue;
				}
				set_cheapest(join);
				if (join->cheapest_total_path == NULL) {
					continue;
				}

				Cost join_cost = join->cheapest_total_path->total_cost;
				*cost_plan += join_cost;
				if (join_cost < dp[i][j]->cheapest_total_path->total_cost) {
					dp[i][j] = join;
				}
			}
		}
	}

	RelOptInfo *full_plan = dp[0][n - 1];
	if (full_plan != NULL &&
	    dp[0][n - 1]->cheapest_total_path->total_cost <= topology->budget) {
		*cost_plan = dp[0][n - 1]->cheapest_total_path->total_cost;
		return list_make1(full_plan);
	}

	List *plans = NIL;
	for (i = 0; i < n; i++) {
		Cost best_cost = DBL_MAX;
		int best_j = i;

		for (j = i; j < n; j++) {
			if (dp[i][j] != NULL &&
			    dp[i][j]->cheapest_total_path->total_cost < best_cost) {
				best_cost = dp[i][j]->cheapest_total_path->total_cost;
				best_j = j;
			}
		}

		plans = lappend(plans, dp[i][best_j]);
		i = best_j;
	}

	return plans;
}
