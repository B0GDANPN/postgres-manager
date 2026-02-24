#include "postgres.h"
#include "c.h"
#include "common/fe_memutils.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "port/pg_bitutils.h"
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include "optimizer/heuristic/heuristic_manager.h"
#include "optimizer/heuristic/goo.h"

static List *choose_min_cost_cover(List *partial_plans);
static List *chain_dp_optimal_cover(RelOptInfo ***dp, int n);
static List *dp_sub_optimal_cover(RelOptInfo **best_plans, Cost *best_costs, int n);
static RelOptInfo *plan_topology(PlannerInfo *root, Topology * topology);

static List *plan_chain_dp(PlannerInfo *root, Topology * topology);
static List *plan_cycle(PlannerInfo *root, Topology * topology);
static List *plan_star(PlannerInfo *root, Topology * topology);
static List *plan_star2(PlannerInfo *root, Topology * topology);
static List *plan_dp_sub(PlannerInfo *root, Topology * topology);

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
	List	   *partial_plans = NULL;
	RelOptInfo *final_plan = NULL;

	root->last_topology_id = 0;
	root->global_budget = 0;
	root->topology_budget = 0;
	root->spent_budget = 0;
	root->global_budget = DBL_MAX;	/* DEBUG */
	split_budget_among_topologies(components, root->global_budget, NULL);
	foreach(lc, components)
	{
		Topology   *component = (Topology *) lfirst(lc);
		Vertex	   *v = NULL;
		RelOptInfo *comp_plan = NULL;
		Cost		component_budget;
		Cost		current_budget;
		bool		first_iter = true;

		split_budget_among_topologies(components, root->global_budget, lc);

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
			//print_topology(component);
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

			split_budget_among_topologies(topologies, current_budget, NULL);

			foreach(lc2, topologies)
			{
				Topology   *topology = (Topology *) lfirst(lc2);
				RelOptInfo *plan;

				root->spent_budget = 0;
				root->topology_budget = topology->budget;
				plan = plan_topology(root, topology);

				//print_trace(plan);

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
				free_join_graph(component->vertexes);	/* full cleanup of
														 * build_join_graph
														 * output */
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
	partial_plans = goo_init_cost_init_result(root, component_plans, true, true);
	final_plan = (RelOptInfo *) linitial(partial_plans);
	if (root->global_budget >= root->spent_budget)
	{
		root->global_budget -= root->spent_budget;
	}
	list_free(component_plans);
	list_free(components);
	list_free(graph);
	return final_plan;
}


/*
 * Optimal interval cover for a partially-filled chain DP table.
 *
 * cover_cost[i] = minimum total cost to cover positions [0, i-1].
 * cover_from[i] = start index of the last interval in that optimal cover.
 *
 * Recurrence:
 *   cover_cost[0] = 0   (empty prefix, nothing to cover)
 *   cover_cost[i] = min over j in [0, i-1] where dp[j][i-1] != NULL:
 *                     cover_cost[j] + dp[j][i-1]->cheapest_total_path->total_cost
 */
static List *
chain_dp_optimal_cover(RelOptInfo ***dp, int n)
{
	int		   *cover_pieces = (int *) palloc((n + 1) * sizeof(int));
	Cost	   *cover_cost = (Cost *) palloc((n + 1) * sizeof(Cost));
	int		   *cover_from = (int *) palloc((n + 1) * sizeof(int));
	List	   *plans = NIL;
	int			pos;

	cover_pieces[0] = 0;
	cover_cost[0] = 0.0;
	cover_from[0] = -1;

	for (int i = 1; i <= n; i++)
	{
		cover_pieces[i] = INT_MAX;
		cover_cost[i] = DBL_MAX;
		cover_from[i] = -1;

		for (int j = i - 1; j >= 0; j--)
		{
			int			cand_pieces;
			Cost		cand_cost;

			if (dp[j][i - 1] == NULL)
				continue;

			if (cover_pieces[j] == INT_MAX)
				continue;

			cand_pieces = cover_pieces[j] + 1;
			cand_cost = cover_cost[j] +
				dp[j][i - 1]->cheapest_total_path->total_cost;

			if (cand_pieces < cover_pieces[i] ||
				(cand_pieces == cover_pieces[i] &&
				 cand_cost < cover_cost[i]))
			{
				cover_pieces[i] = cand_pieces;
				cover_cost[i] = cand_cost;
				cover_from[i] = j;
			}
		}
	}

	if (cover_pieces[n] == INT_MAX)
	{
		pfree(cover_pieces);
		pfree(cover_cost);
		pfree(cover_from);
		return NIL;
	}

	/* Backtrack to reconstruct the partition. */
	pos = n;
	while (pos > 0)
	{
		int			start = cover_from[pos];

		plans = lcons(dp[start][pos - 1], plans);
		pos = start;
	}

	pfree(cover_pieces);
	pfree(cover_cost);
	pfree(cover_from);
	return plans;
}

/**
 * @brief Optimal minimum-cost cover of all vertices using computed subplans.
 *
 * Given the best_plans[] and best_costs[] arrays from dp_sub (indexed by
 * bitmask), find a partition of the full vertex set into non-overlapping
 * subsets such that each subset has a computed plan and the total cost
 * is minimized.
 *
 * Uses subset-DP: cover_cost[mask] = min cost to cover exactly the
 * vertices in mask.  Enumerates all submasks of each mask.
 *
 * @param best_plans  Array indexed by bitmask; best_plans[m] is the best
 *                    RelOptInfo for vertex set m, or NULL if not computed.
 * @param best_costs  Parallel cost array.
 * @param n           Number of vertices (must be <= ~15 for tractability).
 *
 * @return List of RelOptInfo* forming an optimal non-overlapping cover,
 *         or NIL if no complete cover exists.
 */
static List *
dp_sub_optimal_cover(RelOptInfo **best_plans, Cost *best_costs,
					 int n)
{
	size_t		total_sets = ((size_t) 1) << n;
	size_t		full_mask = total_sets - 1;
	int		   *cover_pieces;	/* min pieces to cover this mask */
	Cost	   *cover_cost;		/* min cost among covers with that many pieces */
	size_t	   *cover_from;		/* which submask was chosen last */
	List	   *result = NIL;
	size_t		mask;

	cover_pieces = (int *) palloc(total_sets * sizeof(int));
	cover_cost = (Cost *) palloc(total_sets * sizeof(Cost));
	cover_from = (size_t *) palloc(total_sets * sizeof(size_t));

	cover_pieces[0] = 0;
	cover_cost[0] = 0.0;
	cover_from[0] = 0;

	for (mask = 1; mask < total_sets; mask++)
	{
		size_t		sub;

		cover_pieces[mask] = INT_MAX;
		cover_cost[mask] = DBL_MAX;
		cover_from[mask] = 0;

		/* Enumerate all non-empty submasks of mask. */
		for (sub = mask; sub > 0; sub = (sub - 1) & mask)
		{
			size_t		complement = mask ^ sub;
			int			cand_pieces;
			Cost		cand_cost;

			if (best_plans[sub] == NULL)
				continue;

			if (cover_pieces[complement] == INT_MAX)
				continue;		/* can't cover the rest */

			cand_pieces = cover_pieces[complement] + 1;
			cand_cost = cover_cost[complement] + best_costs[sub];

			/*
			 * Lexicographic: prefer fewer pieces first, then cheaper cost
			 * among same piece count.
			 */
			if (cand_pieces < cover_pieces[mask] ||
				(cand_pieces == cover_pieces[mask] &&
				 cand_cost < cover_cost[mask]))
			{
				cover_pieces[mask] = cand_pieces;
				cover_cost[mask] = cand_cost;
				cover_from[mask] = sub;
			}
		}
	}

	if (cover_pieces[full_mask] == INT_MAX)
	{
		pfree(cover_pieces);
		pfree(cover_cost);
		pfree(cover_from);
		return NIL;
	}

	/* Backtrack to reconstruct the partition. */
	mask = full_mask;
	while (mask != 0)
	{
		size_t		chosen = cover_from[mask];

		Assert(chosen != 0);
		Assert(best_plans[chosen] != NULL);

		result = lappend(result, best_plans[chosen]);
		mask ^= chosen;
	}

	pfree(cover_pieces);
	pfree(cover_cost);
	pfree(cover_from);
	return result;
}

/**
 * @brief Given a list of partial plans, choose a subset of them to cover all
 * relids with the minimum cost.
 *
 * @param partial_plans List of partial plans.
 *
 * @return List of chosen partial plans.
 */
static List *
choose_min_cost_cover(List *partial_plans)
{
	Bitmapset  *uncovered = NULL;
	ListCell   *lc = NULL;
	List	   *coverage = NIL;

	foreach(lc, partial_plans)
	{
		RelOptInfo *rel = (RelOptInfo *) lfirst(lc);

		uncovered = bms_add_members(uncovered, rel->relids);
	}

	while (!bms_is_empty(uncovered))
	{
		RelOptInfo *best_rel = NULL;
		int			best_covered = 0;
		Cost		best_cost = DBL_MAX;

		lc = NULL;
		foreach(lc, partial_plans)
		{
			RelOptInfo *candidate = (RelOptInfo *) lfirst(lc);
			Bitmapset  *newly = bms_intersect(uncovered, candidate->relids);
			int			newly_covered = bms_num_members(newly);
			Cost		cost;

			bms_free(newly);
			if (newly_covered == 0)
			{
				continue;
			}

			cost = candidate->cheapest_total_path->total_cost;

			/*
			 * Prefer the plan that covers the most uncovered relids (= fewest
			 * pieces overall).  Break ties by lower cost.
			 */
			if (newly_covered > best_covered ||
				(newly_covered == best_covered && cost < best_cost))
			{
				best_covered = newly_covered;
				best_cost = cost;
				best_rel = candidate;
			}
		}

		if (best_rel == NULL)
		{
			break;
		}

		coverage = lappend(coverage, best_rel);
		uncovered = bms_del_members(uncovered, best_rel->relids);
		foreach(lc, partial_plans)
		{
			RelOptInfo *candidate = (RelOptInfo *) lfirst(lc);

			if (bms_overlap(candidate->relids, best_rel->relids))
				partial_plans = foreach_delete_current(partial_plans, lc);
		}
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
 *budget for this is insufficient, it switches to
 *dynamic programming. If the budget for dynamic programming is insufficient, it
 *uses a greedy approach.
 * @param root The planner context.
 * @param topology The topology to plan.
 *
 * @return A list of resulting plans, either a single completed plan or partial
 *plans.
 **/
static RelOptInfo *
plan_topology(PlannerInfo *root, Topology * topology)
{
	RelOptInfo *plan = NULL;
	List	   *partial_plans = NIL;
	List	   *initial_rels = NIL;
	List	   *saved_rels = NIL;
	Cost		spent_plan = 0;

	root->topology_budget = DBL_MAX;	/* debug */
	//print_topology(topology);
	list_free(root->join_rel_list);
	root->join_rel_list = NIL;
	switch (topology->form)
	{
		case CHAIN:
			partial_plans = plan_chain_dp(root, topology);
			break;
		case CYCLE:
			partial_plans = plan_cycle(root, topology);
			break;
		case STAR:
			partial_plans = plan_star(root, topology);
			break;
		case DENSITY_GRAPH:
			partial_plans = plan_dp_sub(root, topology);
			break;
		case COMPONENT:
			break;
	}
	spent_plan += root->spent_budget;
	root->topology_budget -= root->spent_budget;
	if (list_length(partial_plans) == 1)
	{
		root->spent_budget += spent_plan;
		plan = (RelOptInfo *) linitial(partial_plans);
		return plan;
	}

	if (topology->form != CHAIN && topology->form != DENSITY_GRAPH)
	{
		initial_rels = choose_min_cost_cover(partial_plans);
	}
	else
	{
		initial_rels = partial_plans;
	}
	saved_rels = root->initial_rels;
	root->initial_rels = initial_rels;
	root->spent_budget = 0;
	list_free(root->join_rel_list);
	root->join_rel_list = NIL;
	partial_plans = standard_join_search(root,
										 list_length(initial_rels),
										 initial_rels);
	root->initial_rels = saved_rels;
	spent_plan += root->spent_budget;
	root->topology_budget -= root->spent_budget;
	if (list_length(partial_plans) == 1)
	{
		root->spent_budget += spent_plan;
		plan = (RelOptInfo *) linitial(partial_plans);
		return plan;
	}

	/* specialized heuristis very expensive, so GOO. */
	initial_rels = choose_min_cost_cover(partial_plans);
	root->spent_budget = 0;
	list_free(root->join_rel_list);
	root->join_rel_list = NIL;
	partial_plans = goo_final_cost_final_result(root, initial_rels, false, true);
	plan = (RelOptInfo *) linitial(partial_plans);
	if (root->topology_budget >= root->spent_budget)
	{
		root->topology_budget -= root->spent_budget;
	}
	root->spent_budget += spent_plan;
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
 *
 * @return Single full plan or list of partial plans.
 */
static List *
plan_chain_dp(PlannerInfo *root, Topology * topology)
{
	int			n = list_length(topology->vertexes);
	int			i,
				j,
				k;
	bool		success;
	List	   *plans = NIL;
	RelOptInfo ***dp = (RelOptInfo ***) palloc0(n * sizeof(RelOptInfo **));

	for (i = 0; i < n; i++)
	{
		dp[i] = (RelOptInfo **) palloc0(n * sizeof(RelOptInfo *));
	}

	for (i = 0; i < n; i++)
	{
		for (j = 0; j < n; j++)
		{
			if (i == j)
			{
				Vertex	   *v_i =
					(Vertex *) lfirst(list_nth_cell(topology->vertexes, i));

				dp[i][i] = v_i->rel;
				continue;
			}
			dp[i][j] = NULL;
		}
	}
	success = true;
	for (int len = 2; len <= n; len++)
	{
		for (int i = 0; i <= n - len; i++)
		{
			if (!success)
			{
				break;
			}
			j = i + len - 1;

			for (k = i; k < j; k++)
			{
				/*Cost		prel_join_cost;*/
				Cost		join_cost;
				RelOptInfo *join = NULL;

				if (dp[i][k] == NULL || dp[k + 1][j] == NULL)
				{
					continue;
				}
				join = make_rel(root, dp[i][k], dp[k + 1][j]);
				if (join == NULL)
				{
					continue;
				}
				if (join->cheapest_total_path == NULL)
				{
					continue;
				}
				join_cost = join->cheapest_total_path->total_cost;
				if (root->spent_budget + join_cost >
					root->topology_budget * budget_soft_limit)
				{
					success = false;
					break;
				}
				root->spent_budget += join_cost;	/* join_cost; */
				if (dp[i][j] == NULL ||
					join_cost < dp[i][j]->cheapest_total_path->total_cost)
				{
					dp[i][j] = join;
				}
			}
		}
	}
	if (success && dp[0][n - 1] != NULL)
	{
		RelOptInfo *full_plan = dp[0][n - 1];

		for (i = 0; i < n; i++)
		{
			pfree(dp[i]);
		}
		pfree(dp);
		return list_make1(full_plan);
	}

	plans = chain_dp_optimal_cover(dp, n);

	if (plans == NIL)
	{
		/* Fallback: shouldn't happen, but use singleton rels. */
		for (i = 0; i < n; i++)
			plans = lappend(plans, dp[i][i]);
	}
	for (i = 0; i < n; i++)
	{
		pfree(dp[i]);
	}
	pfree(dp);
	return plans;
}

/**
 * @brief Plan a cycle by removing the most cardinal edge and planning a chain.
 *
 * Converts the cycle into a chain by removing the edge with maximal estimated
 * cardinality, then tries to reattach the removed vertex within budget.
 *
 * @param root Planner context.
 * @param topology Cycle topology to plan.
 *
 * @return Single full plan or list of partial plans.
 */
static List *
plan_cycle(PlannerInfo *root, Topology * topology)
{
	int			n = list_length(topology->vertexes);
	List	   *chain_vertexes = NIL;
	Topology   *chain_topology = NULL;
	List	   *chain_plans = NIL;
	Vertex	   *v_removed = NULL;
	Cardinality max_card = -1;
	int			removed_idx = 0;

	for (int i = 0; i < n; i++)
	{
		int			nxt = (i + 1) % n;
		Vertex	   *v_i = (Vertex *) lfirst(list_nth_cell(topology->vertexes, i));
		RelOptInfo *rel_i = v_i->rel;
		Vertex	   *v_nxt = (Vertex *) lfirst(list_nth_cell(topology->vertexes, nxt));
		RelOptInfo *rel_nxt = v_nxt->rel;
		Selectivity sel = get_selectivity(root, rel_i, rel_nxt);
		Cardinality card = sel * rel_i->rows * rel_nxt->rows;

		if (card > max_card)
		{
			max_card = card;
			removed_idx = nxt;
		}
	}
	for (int i = 1; i < n; i++)
	{
		int			idx = (removed_idx + i) % n;
		Vertex	   *v_idx = (Vertex *) lfirst(list_nth_cell(topology->vertexes, idx));

		chain_vertexes = lappend(chain_vertexes, v_idx);
	}
	chain_topology = (Topology *) palloc0(sizeof(Topology));
	chain_topology->vertexes = chain_vertexes;
	chain_topology->budget = topology->budget;
	chain_topology->form = CHAIN;
	v_removed = (Vertex *) lfirst(list_nth_cell(topology->vertexes, removed_idx));
	chain_plans = plan_chain_dp(root, chain_topology);
	if (list_length(chain_plans) == 1)
	{
		RelOptInfo *chain_plan = (RelOptInfo *) linitial(chain_plans);
		RelOptInfo *removed_rel = v_removed->rel;
		RelOptInfo *join = make_rel(root, chain_plan, removed_rel);
		Cost		cost = join->cheapest_total_path->total_cost;

		if (root->spent_budget + cost <= root->topology_budget * budget_soft_limit)
		{
			if (join != NULL)
			{

				if (root->spent_budget + cost /* join_cost */ <=
					root->topology_budget * budget_soft_limit)
				{
					root->spent_budget += cost /* join_cost */ ;
					pfree(chain_topology);
					return list_make1(join);
				}
			}
		}
	}
	pfree(chain_topology);
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
 *
 * @return Single full plan or list of partial plans.
 */
static List *
plan_star(PlannerInfo *root, Topology * topology)
{
	Vertex	   *center_vertex = (Vertex *) linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List	   *rays = (List *) topology->extended_info;	/* List* of List* of
															 * Vertex* */
	int		   *ind_array = palloc0(list_length(rays) * sizeof(int));
	bool		was_join = false;
	List	   *partials = NIL;
	ListCell   *ray = NULL;

	do
	{
		Cardinality min_card = DBL_MAX;
		int			best_ind_ray = -1;
		ListCell   *ray = NULL;

		was_join = false;
		ray = NULL;
		foreach(ray, rays)
		{
			List	   *ray_vertices = (List *) lfirst(ray);	/* List* of Vertex* */
			int			ind_ray = list_cell_number(rays, ray);
			int			ind_head_ray = ind_array[ind_ray];
			Vertex	   *head_vertex = NULL;
			Selectivity sel;
			Cardinality card;

			if (list_length(ray_vertices) ==
				ind_head_ray)
			{					/* all vertexes in that ray have been joined */
				continue;
			}
			head_vertex =
				(Vertex *) lfirst(list_nth_cell(ray_vertices, ind_head_ray));
			sel = get_selectivity(root, center_rel, head_vertex->rel);
			card = sel * center_rel->rows * head_vertex->rel->rows;
			if (card < min_card)
			{
				min_card = card;
				best_ind_ray = ind_ray;
			}
		}
		if (best_ind_ray != -1)
		{
			int			ind_head_ray = ind_array[best_ind_ray];
			List	   *best_ray = (List *) lfirst(list_nth_cell(rays, best_ind_ray));
			Vertex	   *v_rel = (Vertex *) lfirst(list_nth_cell(best_ray, ind_head_ray));
			RelOptInfo *rel = v_rel->rel;
			RelOptInfo *new_center = make_rel(root, center_rel, rel);
			Cost		cost = new_center->cheapest_total_path->total_cost;

			if (root->spent_budget + cost <= root->topology_budget * budget_soft_limit)
			{
				was_join = true;
				ind_array[best_ind_ray]++;
				/* join_cost = new_center->cheapest_total_path->total_cost; */
				root->spent_budget += cost /* join_cost */ ;
				center_rel = new_center;
			}
		}
	} while (was_join);
	partials = list_make1(center_rel);
	ray = NULL;
	foreach(ray, rays)
	{
		List	   *ray_vertices = (List *) lfirst(ray);	/* List* of Vertex* */
		ListCell   *init_cell = NULL;
		ListCell   *lc = NULL;
		int			ind_ray = list_cell_number(rays, ray);
		int			ind_head_ray = ind_array[ind_ray];

		if (list_length(ray_vertices) == ind_head_ray)
		{
			continue;
		}
		init_cell = list_nth_cell(ray_vertices, ind_head_ray);
		for_each_cell(lc, ray_vertices, init_cell)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

			partials = lappend(partials, v->rel);
		}
	}
	pfree(ind_array);
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
 *
 * @return Single full plan or list of partial plans.
 */
static List *
plan_star2(PlannerInfo *root, Topology * topology)
{
	Vertex	   *center_vertex = (Vertex *) linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List	   *rays = (List *) topology->extended_info;	/* List* of List* of
															 * Vertex* */
	List	   *partials = NIL;
	List	   *chains_plans = NIL;

	/* Plan each ray as an independent chain. */
	ListCell   *lc = NULL;

	foreach(lc, rays)
	{
		List	   *ray_vertices = (List *) lfirst(lc); /* List* of Vertex* */
		Topology	chain_topology;
		List	   *chain_plans = NIL;
		RelOptInfo *chain_plan = NULL;

		chain_topology.vertexes = ray_vertices;
		chain_topology.form = CHAIN;
		chain_topology.budget = topology->budget;
		chain_plans = plan_chain_dp(root, &chain_topology);
		if (list_length(chain_plans) > 1)
		{
			ListCell   *lc2 = NULL;

			partials = list_concat(partials, chain_plans);
			for_each_cell(lc2, rays, lnext(rays, lc))
			{
				List	   *ray_vertices2 = (List *) lfirst(lc2);
				ListCell   *lc3 = NULL;

				foreach(lc3, ray_vertices2)
				{
					Vertex	   *v = (Vertex *) lfirst(lc3);

					partials = lappend(partials, v->rel);
				}
			}
			partials = lappend(partials, center_rel);
			return partials;
		}
		chain_plan = (RelOptInfo *) linitial(chain_plans);
		chains_plans = lappend(chains_plans, chain_plan);
	}

	/* Greedily join rays by the cheapest edge to the current center. */
	while (chains_plans != NIL)
	{
		RelOptInfo *best_rel = NULL;
		RelOptInfo *join = NULL;
		ListCell   *best_cell = NULL;
		Cost		best_edge_cost = DBL_MAX;

		/* Cost		join_cost; */

		lc = NULL;
		foreach(lc, chains_plans)
		{
			RelOptInfo *rel = (RelOptInfo *) lfirst(lc);
			Cost		edge_cost = cost_edge(root, center_rel, rel);

			if (edge_cost < best_edge_cost)
			{
				best_edge_cost = edge_cost;
				best_rel = rel;
				best_cell = lc;
			}
		}

		if (root->spent_budget + best_edge_cost > root->topology_budget * budget_soft_limit)
		{
			lc = NULL;
			foreach(lc, chains_plans)
			{
				RelOptInfo *rel = (RelOptInfo *) lfirst(lc);

				partials = lappend(partials, rel);
			}
			partials = lappend(partials, center_rel);
			return partials;
		}

		join = make_rel(root, center_rel, best_rel);
		/* join_cost = join->cheapest_total_path->total_cost; */
		root->spent_budget += best_edge_cost /* join_cost */ ;
		center_rel = join;
		chains_plans = list_delete_cell(chains_plans, best_cell);
	}
	return list_make1(center_rel);
}

/**
 * @brief DP over connected subsets for a general topology.
 *
 * Enumerates connected subsets, joining compatible subplans within budget and
 * returning the best plan built.
 *
 * @param root Planner context.
 * @param topology Topology to plan.
 *
 * @return Single full plan or list containing the best plan found.
 */
static List *
plan_dp_sub(PlannerInfo *root, Topology * topology)
{
	RelOptInfo **best_plans = NULL;
	Cost	   *best_costs = NULL;
	List	   *partials = NIL;
	size_t		n = list_length(topology->vertexes);
	size_t		total_sets = ((size_t) 1) << n;
	bool		force_exit = false;

	best_plans = (RelOptInfo **) palloc0(total_sets * sizeof(RelOptInfo *));
	best_costs = (Cost *) palloc0(total_sets * sizeof(Cost));
	update_indices(topology);

	for (size_t i = 0; i < total_sets; i++)
	{
		best_costs[i] = DBL_MAX;
	}

	for (size_t i = 0; i < n; i++)
	{
		size_t		mask = ((size_t) 1) << i;
		ListCell   *lc_v = list_nth_cell(topology->vertexes, i);
		Vertex	   *v = (Vertex *) lfirst(lc_v);

		best_plans[mask] = v->rel;
		best_costs[mask] = best_plans[mask]->cheapest_total_path->total_cost;
	}

	for (size_t join_bm = 1; join_bm < total_sets; join_bm++)
	{
		size_t		left_bm = (-join_bm) & join_bm;

		if (force_exit)
		{
			break;
		}
		if (pg_popcount64(join_bm) <= 1)
		{
			continue;
		}

		if (!is_connected(topology->vertexes, join_bm))
		{
			continue;
		}
		while (join_bm != left_bm)
		{
			size_t		right_bm = join_bm - left_bm;
			RelOptInfo *left_plan = NULL;
			RelOptInfo *right_plan = NULL;
			RelOptInfo *join = NULL;
			Cost		cost;

			/* Cost		join_cost; */

			if (left_bm >= right_bm)
			{
				left_bm = (left_bm - join_bm) & join_bm;
				continue;
			}
			if (best_plans[left_bm] == NULL || best_plans[right_bm] == NULL)
			{
				left_bm = (left_bm - join_bm) & join_bm;
				continue;
			}
			left_plan = best_plans[left_bm];
			right_plan = best_plans[right_bm];
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
			cost =join->cheapest_total_path->total_cost;
			if (root->spent_budget + cost > root->topology_budget * budget_soft_limit)
			{
				force_exit = true;
				break;
			}
			/* join_cost = join->cheapest_total_path->total_cost; */
			if (cost < best_costs[join_bm])
			{
				best_costs[join_bm] = cost;
				best_plans[join_bm] = join;
				root->spent_budget += cost;
			}
			left_bm = (left_bm - join_bm) & join_bm;
		}
	}
	{
		List	   *optimal = dp_sub_optimal_cover(best_plans, best_costs, n);

		if (optimal != NIL)
		{
			pfree(best_plans);
			pfree(best_costs);
			return optimal;		/* may be list_length==1 (full plan) or a
								 * partition */
		}
	}

	/* Fallback: return raw partials for greedy cover. */
	for (size_t k = 0; k < n; k++)
		partials = lappend(partials, best_plans[((size_t) 1) << k]);
	pfree(best_plans);
	pfree(best_costs);
	return partials;
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
