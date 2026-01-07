#include "optimizer/heuristic/heuristic_manager.h"
#include "c.h"
#include "common/fe_memutils.h"
#include "nodes/bitmapset.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "port/pg_bitutils.h"
#include "postgres.h"
#include <float.h>
#include <limits.h>
#include <stdbool.h>
#include <string.h>
static const double b1 = 0.75;
static const double q = 0.25;
static const double budget_soft_limit = 0.9;
static const double k1 = 0.5;
static const double k2 = 0.5;
static List *choose_min_cost_cover(List *partial_plans);
static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan);

static RelOptInfo *goo(PlannerInfo *root, List *initial_rels, bool clauseless, Cost *cost_plan);
static List *plan_chain_dp(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_cycle(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_star(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_star2(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_dp_sub(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static bool bitmap_connected(List *top_vertexes, uint64 bitmap);
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
static void split_budget_among_topologies(List *topologies, Cost budget, ListCell *init_cell)
{
	Cost sum_complexities = 0;
	ListCell *lc = NULL;
	int from = 0;
	if (init_cell) {
		from = list_cell_number(topologies, init_cell);
	}
	for_each_from(lc, topologies, from)
	{
		Topology *topology = (Topology *)lfirst(lc);
		if (list_length(topology->vertexes)) {
			topology->budget = 0;
			continue;
		}
		double k_sel = 1 / topology->sel;
		sum_complexities += k1 * topology->ccp + k2 * k_sel;
	}
	for_each_from(lc, topologies, from)
	{
		Topology *topology = (Topology *)lfirst(lc);
		if (list_length(topology->vertexes)) {
			continue;
		}
		topology->budget = topology->ccp * budget / sum_complexities;
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
 * @param budget Planning budget for all components.
 *
 * @return Final join plan for all relations.
 */
RelOptInfo *heuristic_join_search(PlannerInfo *root, List *initial_rels, Cost budget)
{
	List *graph = build_join_graph(root, initial_rels); // List* of Vertex*
	List *components = split_components(root, graph);   // list of Topology(COMPONENT)*
	split_budget_among_topologies(components, budget, NULL);
	List *component_plans = NIL;
	ListCell *lc = NULL;
	Cost component_budget = 0;
	foreach (lc, components) {
		if (component_budget > 0) { // remaining budget from prev iteration of planning
			split_budget_among_topologies(components, budget, lc);
		}
		Topology *component = (Topology *)lfirst(lc);

		List *comp_vertexes = component->vertexes; // List* of Vertex*

		component_budget = component->budget;
		Cost current_budget = component_budget * b1;
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
			ListCell *lc2 = NULL;
			foreach (lc2, topologies) {
				Topology *topology = (Topology *)lfirst(lc2);
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
	RelOptInfo *final_plan = goo(root, component_plans, true, NULL);
	list_free(graph);
	return final_plan;
	// переполнение
	// и звезда не присоединяет.
}
/**
 * @brief Greedy operator ordering (GOO) join ordering.
 *
 * Repeatedly joins the cheapest pair, optionally requiring a join clause.
 *
 * @param root Planner context.
 * @param initial_rels Relations to join.
 * @param clauseless If false, only joins with a simple inner edge.
 * @param cost_plan Accumulates the chosen join costs.
 *
 * @return Final join plan.
 */
static RelOptInfo *goo(PlannerInfo *root, List *initial_rels, bool clauseless, Cost *cost_plan)
{
	while (list_length(initial_rels) > 1) {
		ListCell *best_lc1 = NULL;
		ListCell *best_lc2 = NULL;
		Cost best_cost = DBL_MAX;
		ListCell *i = NULL;
		foreach (i, initial_rels) {
			RelOptInfo *rel1 = (RelOptInfo *)lfirst(i);
			ListCell *j = NULL;
			for_each_cell (j, initial_rels, lnext(initial_rels, i)) {
				RelOptInfo *rel2 = (RelOptInfo *)lfirst(j);
				if (!clauseless && !has_simple_inner_edge(root, rel1, rel2)) {
					continue;
				}
				Cost prel_join_cost = cost_simple_edge(root, rel1, rel2);
				if (prel_join_cost < best_cost) {
					best_cost = prel_join_cost;
					best_lc1 = i;
					best_lc2 = j;
				}
			}
		}
		RelOptInfo *best_rel1 = (RelOptInfo *)lfirst(best_lc1);
		RelOptInfo *best_rel2 = (RelOptInfo *)lfirst(best_lc2);
		RelOptInfo *best_rel = make_join_rel(root, best_rel1, best_rel2);
		set_cheapest(best_rel);
		*cost_plan += best_rel->cheapest_total_path->total_cost;
		int a = list_cell_number(initial_rels, best_lc1);
		int b = list_cell_number(initial_rels, best_lc2);
		initial_rels = lappend(initial_rels, best_rel);
		initial_rels = list_delete_nth_cell(initial_rels, a);
		if (a < b) {
			b--;
		}
		initial_rels = list_delete_nth_cell(initial_rels, b);
	}

	RelOptInfo *plan = (RelOptInfo *)linitial(initial_rels);
	return plan;
}
/**
 * @brief Given a list of partial plans, choose a subset of them to cover all
 * relids with the minimum cost.
 *
 * @param partial_plans List of partial plans.
 *
 * @return List of chosen partial plans.
 */
static List *choose_min_cost_cover(List *partial_plans)
{
	Bitmapset *uncovered = NULL;
	ListCell *lc = NULL;
	foreach (lc, partial_plans) {
		RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
		uncovered = bms_add_members(uncovered, rel->relids);
	}

	List *coverage = NIL;

	while (!bms_is_empty(uncovered)) {
		RelOptInfo *best_rel = NULL;
		ListCell *best_cell = NULL;
		double best_score = DBL_MAX;
		Cost best_cost = DBL_MAX;
		lc = NULL;
		foreach (lc, partial_plans) {
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
		partial_plans = list_delete_cell(partial_plans, best_cell);
	}

	bms_free(uncovered);
	list_free(partial_plans);

	return coverage;
}

/**
 * @brief Plans a topology using dynamic programming, specialized heuristics,
 *and the GOO fallback.
 *
 * First, it tries to apply a specialized algorithm to the topology. If the
 *budget for this is insufficient, it switches (while preserving the results) to
 *dynamic programming. If the budget for dynamic programming is insufficient, it
 *uses a greedy approach.
 * @param root The planner context.
 * @param topology The topology to plan.
 * @param cost_plan An output parameter for the total cost of the returned
 *plans.
 *
 * @return A list of resulting plans, either a single completed plan or partial
 *plans.
 **/
static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	print_topology(topology);
	RelOptInfo *plan = NULL;
	List *partial_plans = NIL;
	Cost cost_tmp_plan = 0;
	switch (topology->form) {
	case CHAIN:
		partial_plans = plan_chain_dp(root, topology, &cost_tmp_plan);
		break;
	case CYCLE:
		partial_plans = plan_cycle(root, topology, &cost_tmp_plan);
		break;
	case STAR:
		partial_plans = plan_star(root, topology, &cost_tmp_plan);
		break;
	case DENSITY_GRAPH:
		partial_plans = plan_dp_sub(root, topology, &cost_tmp_plan);
		break;
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
	List *saved_rels = root->initial_rels;
	root->initial_rels = initial_rels;
	partial_plans = standard_join_search(root,
					     list_length(initial_rels),
					     initial_rels,
					     topology->budget,
					     &cost_tmp_plan);
	root->initial_rels = saved_rels;

	topology->budget -= cost_tmp_plan;
	*cost_plan += cost_tmp_plan;
	cost_tmp_plan = 0;
	if (list_length(partial_plans) == 1) {
		plan = (RelOptInfo *)linitial(partial_plans);
		return plan;
	}

	// specialized heuristis very expensive, so GOO.
	initial_rels = choose_min_cost_cover(partial_plans);
	plan = goo(root, initial_rels, false, &cost_tmp_plan);
	topology->budget -= cost_tmp_plan;
	*cost_plan += cost_tmp_plan;
	return plan;
}

/**
 * @brief Dynamic programming join order for a chain topology.
 *
 * Builds best subplans for intervals, stopping early if the budget soft limit
 * is exceeded, and returns a full plan or partial segments.
 *
 * @param root Planner context.
 * @param topology Chain topology to plan.
 * @param cost_plan Accumulates total cost of chosen joins.
 *
 * @return Single full plan or list of partial plans.
 */
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
				Vertex *v_i =
					(Vertex *)lfirst(list_nth_cell(topology->vertexes, i));
				dp[i][i] = v_i->rel;
				continue;
			}
			dp[i][j] = NULL;
		}
	}
	bool success = true;
	for (int len = 2; len <= n; len++) {
		for (int i = 0; i <= n - len; i++) {
			j = i + len - 1;

			for (k = i; k < j; k++) {
				if (dp[i][k] == NULL || dp[k + 1][j] == NULL) {
					continue;
				}
				Cost prel_join_cost =
					cost_simple_edge(root, dp[i][k], dp[k + 1][j]);
				if (*cost_plan + prel_join_cost >
				    topology->budget * budget_soft_limit) {
					success = false;
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
	if (success && dp[0][n - 1] != NULL) {
		RelOptInfo *full_plan = dp[0][n - 1];
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

/**
 * @brief Plan a cycle by removing the most expensive edge and planning a chain.
 *
 * Converts the cycle into a chain by removing the edge with maximal estimated
 * cardinality, then tries to reattach the removed vertex within budget.
 *
 * @param root Planner context.
 * @param topology Cycle topology to plan.
 * @param cost_plan Accumulates total cost of chosen joins.
 *
 * @return Single full plan or list of partial plans.
 */
static List *plan_cycle(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	int n = list_length(topology->vertexes);

	Cardinality max_card = -1;
	int removed_idx = 0;
	for (int i = 0; i < n; i++) {
		int nxt = (i + 1) % n;
		Vertex *v_i = (Vertex *)lfirst(list_nth_cell(topology->vertexes, i));
		RelOptInfo *rel_i = v_i->rel;
		Vertex *v_nxt = (Vertex *)lfirst(list_nth_cell(topology->vertexes, nxt));
		RelOptInfo *rel_nxt = v_nxt->rel;
		Selectivity sel = get_selectivity(root, rel_i, rel_nxt);
		Cardinality card = sel * rel_i->rows * rel_i->rows;

		if (card > max_card) {
			max_card = card;
			removed_idx = nxt;
		}
	}
	List *chain_vertexes = NIL;
	for (int i = 1; i < n; i++) {
		int idx = (removed_idx + i) % n;
		Vertex *v_idx = (Vertex *)lfirst(list_nth_cell(topology->vertexes, idx));
		chain_vertexes = lappend(chain_vertexes, v_idx);
	}
	Topology *chain_topology = (Topology *)palloc0(sizeof(Topology));
	chain_topology->vertexes = chain_vertexes;
	chain_topology->budget = topology->budget;
	chain_topology->form = CHAIN;
	Vertex *v_removed = (Vertex *)lfirst(list_nth_cell(topology->vertexes, removed_idx));
	List *chain_plans = plan_chain_dp(root, chain_topology, cost_plan);
	if (list_length(chain_plans) == 1) {
		RelOptInfo *chain_plan = (RelOptInfo *)linitial(chain_plans);
		RelOptInfo *removed_rel = v_removed->rel;
		Cost tmp = cost_simple_edge(root, chain_plan, removed_rel);
		if (*cost_plan + tmp <= topology->budget * budget_soft_limit) {
			RelOptInfo *join = make_join_rel(root, chain_plan, removed_rel);
			if (join != NULL) {
				set_cheapest(join);
				if (join->cheapest_total_path != NULL) {
					Cost join_cost = join->cheapest_total_path->total_cost;
					if (*cost_plan + join_cost <=
					    topology->budget * budget_soft_limit) {
						*cost_plan += join_cost;
						return list_make1(join);
					}
				}
			}
		}
	}
	return lappend(chain_plans, v_removed->rel);
}

/**
 * @brief Greedy planning for a star topology from the center out.
 *
 * Joins rays to the center in order of minimal estimated cardinality until the
 * budget is hit, then returns remaining relations as partials.
 *
 * @param root Planner context.
 * @param topology Star topology to plan.
 * @param cost_plan Accumulates total cost of chosen joins.
 *
 * @return Single full plan or list of partial plans.
 */
static List *plan_star(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	Vertex *center_vertex = (Vertex *)linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List *rays = (List *)topology->extended_info; /* List* of List* of Vertex* */
	int *ind_array = palloc0(list_length(rays) * sizeof(int));
	bool was_join = false;
	do {
		was_join = false;
		Cardinality min_card = DBL_MAX;
		int best_ind_ray = -1;
		ListCell *ray = NULL;
		foreach (ray, rays) {
			List *ray_vertices = (List *)lfirst(ray); /* List* of Vertex* */
			int ind_ray = list_cell_number(rays, ray);
			int ind_head_ray = ind_array[ind_ray];
			if (list_length(ray_vertices) ==
			    ind_head_ray) { // all vertexes in that ray have been joined
				continue;
			}
			Vertex *head_vertex =
				(Vertex *)lfirst(list_nth_cell(ray_vertices, ind_head_ray));
			Selectivity sel = get_selectivity(root, center_rel, head_vertex->rel);
			Cardinality card = sel * center_rel->rows * head_vertex->rel->rows;
			if (card < min_card) {
				min_card = card;
				best_ind_ray = ind_ray;
			}
		}
		if (best_ind_ray != -1) {
			int ind_head_ray = ind_array[best_ind_ray];
			List *best_ray = (List *)lfirst(list_nth_cell(rays, best_ind_ray));
			Vertex *v_rel = (Vertex *)lfirst(list_nth_cell(best_ray, ind_head_ray));
			RelOptInfo *rel = v_rel->rel;
			Cost prel_join_cost = cost_simple_edge(root, center_rel, rel);
			if (*cost_plan + prel_join_cost <= topology->budget * budget_soft_limit) {
				was_join = true;
				RelOptInfo *new_center = make_join_rel(root, center_rel, rel);
				set_cheapest(new_center);
				ind_array[best_ind_ray]++;
				Cost join_cost = new_center->cheapest_total_path->total_cost;
				*cost_plan += join_cost;
				center_rel = new_center;
			}
		}
	} while (was_join);
	List *partials = list_make1(center_rel);
	ListCell *ray = NULL;
	foreach (ray, rays) {
		List *ray_vertices = (List *)lfirst(ray); /* List* of Vertex* */
		int ind_ray = list_cell_number(rays, ray);
		int ind_head_ray = ind_array[ind_ray];
		if (list_length(ray_vertices) == ind_head_ray) {
			continue;
		}
		ListCell *init_cell = list_nth_cell(ray_vertices, ind_head_ray);
		ListCell *lc = NULL;
		for_each_cell (lc, ray_vertices, init_cell) {
			Vertex *v = (Vertex *)lfirst(lc);
			partials = lappend(partials, v->rel);
		}
	}
	return partials;
}
/**
 * @brief Plan star topology by chaining rays, then joining to the center.
 *
 * First plans each ray as a chain; if all succeed, it greedily joins the ray
 * plans to the center by cheapest edge within budget.
 *
 * @param root Planner context.
 * @param topology Star topology to plan.
 * @param cost_plan Accumulates total cost of chosen joins.
 *
 * @return Single full plan or list of partial plans.
 */
static List *plan_star2(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	Vertex *center_vertex = (Vertex *)linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List *rays = (List *)topology->extended_info; /* List* of List* of Vertex* */
	List *partials = NIL;
	List *chains_plans = NIL;
	/* Plan each ray as an independent chain. */
	ListCell *lc = NULL;
	foreach (lc, rays) {
		List *ray_vertices = (List *)lfirst(lc); /* List* of Vertex* */
		Topology chain_topology;
		List *chain_plans = NIL;
		chain_topology.vertexes = ray_vertices;
		chain_topology.form = CHAIN;
		chain_topology.budget = topology->budget;
		chain_plans = plan_chain_dp(root, &chain_topology, cost_plan);
		if (list_length(chain_plans) > 1) {
			partials = lappend(partials, center_rel);
			partials = list_concat(partials, chain_plans);
			ListCell *lc2 = NULL;
			for_each_cell (lc2, rays, lnext(rays, lc)) {
				List *ray_vertices2 = (List *)lfirst(lc2);
				ListCell *lc3 = NULL;
				foreach (lc3, ray_vertices2) {
					RelOptInfo *rel = (RelOptInfo *)lfirst(lc3);
					partials = lappend(partials, rel);
				}
			}
			return partials;
		}
		RelOptInfo *chain_plan = (RelOptInfo *)linitial(chain_plans);
		chains_plans = lappend(chains_plans, chain_plan);
	}

	/* Greedily join rays by the cheapest edge to the current center. */
	while (chains_plans != NIL) {
		RelOptInfo *best_rel = NULL;
		ListCell *best_cell = NULL;
		Cost best_edge_cost = DBL_MAX;
		lc = NULL;
		foreach (lc, chains_plans) {
			RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
			Cost edge_cost = cost_simple_edge(root, center_rel, rel);

			if (edge_cost < best_edge_cost) {
				best_edge_cost = edge_cost;
				best_rel = rel;
				best_cell = lc;
			}
		}

		if (*cost_plan + best_edge_cost > topology->budget * budget_soft_limit) {
			partials = lappend(partials, center_rel);
			lc = NULL;
			foreach (lc, chains_plans) {
				RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
				partials = lappend(partials, rel);
			}
			return partials;
		}

		RelOptInfo *join = make_join_rel(root, center_rel, best_rel);
		set_cheapest(join);
		Cost join_cost = join->cheapest_total_path->total_cost;
		*cost_plan += join_cost;
		center_rel = join;
		chains_plans = list_delete_cell(partials, best_cell);
	}
	return list_make1(center_rel);
}
/**
 * @brief Check whether a bitmap-selected subgraph is connected.
 *
 * Builds the vertex subset from the bitmap and verifies connectivity with DFS.
 *
 * @param top_vertexes All vertices in the topology.
 * @param bitmap Bitmask selecting a subset of vertices.
 *
 * @return True if the selected subgraph is connected.
 */
static bool bitmap_connected(List *top_vertexes, uint64 bitmap)
{
	Bitmapset *bms = NULL;
	for (int i = 1; (uint64)1 << i <= bitmap; i++) {
		if (bitmap & ((uint64)1 << i)) {
			bms = bms_add_member(bms, i);
		}
	}
	// need select nesessary vertexes from top_vertexes
	List *vertexes = NIL;
	ListCell *lc = NULL;
	foreach (lc, top_vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		RelOptInfo *rel = v->rel;
		Bitmapset *relids = rel->relids;
		if (bms_is_subset(relids, bms)) {
			vertexes = lappend(vertexes, v);
		}
	}

	// check that vertexes are connected
	bool *used = (bool *)palloc0(list_length(vertexes) * sizeof(bool));
	MemSet(used, true, list_length(vertexes) * sizeof(bool));
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		used[v->index] = false;
	}
	bool connected = true;
	foreach (lc, vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		if (!used[v->index]) {
			dfs_check(vertexes, v, used);
		}
	}
	for (int i = 0; i < list_length(vertexes); i++) {
		if (!used[i]) {
			connected = false;
			break;
		}
	}
	list_free(vertexes);
	pfree(used);
	return connected;
}
/**
 * @brief DP over connected subsets for a general topology.
 *
 * Enumerates connected subsets, joining compatible subplans within budget and
 * returning the best plan built.
 *
 * @param root Planner context.
 * @param topology Topology to plan.
 * @param cost_plan Accumulates total cost of chosen joins.
 *
 * @return Single full plan or list containing the best plan found.
 */
static List *plan_dp_sub(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	int n = list_length(topology->vertexes);
	RelOptInfo **best_plans = NULL;
	Cost *best_costs = NULL;
	uint64 total_sets = ((uint64)1) << n;
	best_plans = (RelOptInfo **)palloc0(total_sets * sizeof(RelOptInfo *));
	best_costs = (Cost *)palloc0(total_sets * sizeof(Cost));
	List *partials = NIL;
	update_indices(topology);

	memset(best_costs, DBL_MAX, total_sets);

	for (int i = 0; i < n; i++) {
		uint64 mask = ((uint64)1) << i;
		ListCell *lc_v = list_nth_cell(topology->vertexes, i);
		Vertex *v = (Vertex *)lfirst(lc_v);
		best_plans[mask] = v->rel;
		partials = lappend(partials, v->rel);
		best_costs[mask] = best_plans[mask]->cheapest_total_path->total_cost;
	}

	for (uint64 join_bm = 1; join_bm < total_sets; join_bm++) {
		uint64 members = pg_popcount64(join_bm);

		if (members == 1) {
			continue;
		}

		if (!bitmap_connected(topology->vertexes, join_bm)) {
			continue;
		}
		uint64 left_bm = (-join_bm) & join_bm;
		while (join_bm != left_bm) {
			uint64 right_bm = join_bm - left_bm;
			if (left_bm >= right_bm) {
				continue;
			}
			if (best_plans[left_bm] == NULL || best_plans[right_bm] == NULL) {
				continue;
			}

			if (!bitmap_connected(topology->vertexes, left_bm)) {
				continue;
			}
			if (!bitmap_connected(topology->vertexes, right_bm)) {
				continue;
			}
			RelOptInfo *left_plan = best_plans[left_bm];
			RelOptInfo *right_plan = best_plans[right_bm];
			if (!has_simple_inner_edge(root, left_plan, right_plan)) {
				continue;
			}

			Cost prel_join_cost = cost_simple_edge(root, left_plan, right_plan);
			if (*cost_plan + prel_join_cost > topology->budget * budget_soft_limit) {
				return partials;
			}
			RelOptInfo *join = make_join_rel(root, left_plan, right_plan);
			if (join == NULL) {
				continue;
			}
			set_cheapest(join);
			Cost join_cost = join->cheapest_total_path->total_cost;
			*cost_plan += join_cost;
			if (join->cheapest_total_path->total_cost < best_costs[join_bm]) {
				best_costs[join_bm] = join->cheapest_total_path->total_cost;
				best_plans[join_bm] = join;
			}
			partials = lappend(partials, join);
			left_bm = (left_bm - join_bm) & join_bm;
		}
	}
	RelOptInfo *best_plan = (RelOptInfo *)llast(partials);
	return list_make1(best_plan);
}