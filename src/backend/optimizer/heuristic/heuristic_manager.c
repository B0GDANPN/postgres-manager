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
static double b1 = 3 / 4;
static double q = 1 / 4;
static double k1 = 0.5;
static double k2 = 0.5;
typedef enum { STANDARD, GOO, GEQO } TypeHeuristic;
static List *choose_min_cost_cover(List *partial_plans);
static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan);

static RelOptInfo *goo(PlannerInfo *root, List *component_plans, bool clauseless);
static List *plan_chain_dp(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_cycle(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_star(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_star2(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static List *plan_dp_sub(PlannerInfo *root, Topology *topology, Cost *cost_plan);
static bool bitmaps_adjacent(Vertex **vertexes, int n, uint64 left_bm, uint64 right_bm);
static bool bitmap_connected(Vertex **vertexes, int n, uint64 bitmap, bool *visited, int *queue);
static int bitmap_popcount64(uint64 bitmap);
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
	Cost component_budget = 0;
	foreach (lc, components) {
		if (component_budget > 0) {
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
		partial_plans = plan_dp_sub(root, topology, &cost_tmp_plan);
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
static List *plan_cycle(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	int n = list_length(topology->vertexes);
	int i;

	if (n == 0) {
		*cost_plan = 0;
		return NIL;
	}
	Vertex **vertexes = (Vertex **)palloc(n * sizeof(Vertex *));
	ListCell *lc;
	i = 0;
	foreach (lc, topology->vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		vertexes[i++] = v;
	}

	double max_card = -1;
	int removed_idx = 0;
	for (i = 0; i < n; i++) {
		int nxt = (i + 1) % n;
		Selectivity sel = get_selectivity(root, vertexes[i]->rel, vertexes[nxt]->rel);
		double card = sel * vertexes[i]->rel->rows * vertexes[nxt]->rel->rows;

		if (card > max_card) {
			max_card = card;
			removed_idx = nxt;
		}
	}
	List *chain_vertexes = NIL;
	for (i = 1; i < n; i++) {
		int idx = (removed_idx + i) % n;
		chain_vertexes = lappend(chain_vertexes, vertexes[idx]);
	}
	Topology *chain_topology = (Topology *)palloc0(sizeof(Topology));
	chain_topology->vertexes = chain_vertexes;
	chain_topology->budget = topology->budget;
	chain_topology->form = CHAIN;
	List *chain_plans = plan_chain_dp(root, chain_topology, cost_plan);
	if (list_length(chain_plans) == 1) {
		RelOptInfo *chain_plan = (RelOptInfo *)linitial(chain_plans);
		RelOptInfo *removed_rel = vertexes[removed_idx]->rel;
		Cost tmp = cost_simple_edge(root, chain_plan, removed_rel);
		if (*cost_plan + tmp <= topology->budget) {
			RelOptInfo *join = make_join_rel(root, chain_plan, removed_rel);
			if (join != NULL) {
				set_cheapest(join);
				if (join->cheapest_total_path != NULL) {
					Cost join_cost = join->cheapest_total_path->total_cost;
					if (*cost_plan + join_cost <= topology->budget) {
						*cost_plan += join_cost;
						return list_make1(join);
					}
				}
			}
		}
	}
	return lappend(chain_plans, vertexes[removed_idx]->rel);
}

static List *plan_star(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	Vertex *center_vertex = (Vertex *)linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List *rays = (List *)topology->extended_info; /* List* of List* of Vertex* */
	int *ind_array = palloc0(list_length(rays) * sizeof(int));
	bool was_join = false;
	do {
		Cardinality min_card = DBL_MAX;
		int best_ind_ray = -1;
		ListCell *ray = NULL;
		foreach (ray, rays) {
			List *ray_vertices = (List *)lfirst(ray); /* List* of Vertex* */
			int ind_ray = list_cell_number(rays, ray);
			int ind_head_ray = ind_array[ind_ray];
			if (list_length(ray_vertices) == ind_head_ray) {
				continue;
			}
			Vertex *head_vertex = (Vertex *)list_nth_cell(ray_vertices, ind_head_ray);
			Selectivity sel = get_selectivity(root, center_rel, head_vertex->rel);
			Cardinality card = sel * center_rel->rows * head_vertex->rel->rows;
			if (card < min_card) {
				min_card = card;
				best_ind_ray = ind_ray;
			}
		}
		if (best_ind_ray != -1) {
			List *best_ray = (List *)list_nth_cell(rays, best_ind_ray);
			Vertex *v_rel = (Vertex *)list_nth_cell(best_ray, ind_array[best_ind_ray]);
			RelOptInfo *rel = v_rel->rel;
			Cost prel_join_cost = cost_simple_edge(root, center_rel, rel);
			if (*cost_plan + prel_join_cost <= topology->budget) {
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

static List *plan_star2(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	Vertex *center_vertex = (Vertex *)linitial(topology->vertexes);
	RelOptInfo *center_rel = center_vertex->rel;
	List *rays = (List *)topology->extended_info; /* List* of List* of Vertex* */
	List *partials = NIL;
	List *chains_plans = NIL;
	/* Plan each ray as an independent chain. */
	ListCell *lc;
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
			ListCell *lc2;
			for_each_cell (lc2, rays, lnext(rays, lc)) {
				List *ray_vertices2 = (List *)lfirst(lc2);
				ListCell *lc3;
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

		foreach (lc, chains_plans) {
			RelOptInfo *rel = (RelOptInfo *)lfirst(lc);
			Cost edge_cost = cost_simple_edge(root, center_rel, rel);

			if (edge_cost < best_edge_cost) {
				best_edge_cost = edge_cost;
				best_rel = rel;
				best_cell = lc;
			}
		}

		if (*cost_plan + best_edge_cost > topology->budget) {
			partials = lappend(partials, center_rel);

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

static int bitmap_popcount64(uint64 bitmap)
{
	int count = 0;

	while (bitmap != 0) {
		bitmap &= (bitmap - 1);
		count++;
	}

	return count;
}

static bool bitmap_connected(Vertex **vertexes, int n, uint64 bitmap, bool *visited, int *queue)
{
	int subset_size;
	int head = 0;
	int tail = 0;
	int start = -1;
	uint64 tmp;

	if (bitmap == 0) {
		return false;
	}

	memset(visited, 0, n * sizeof(bool));

	tmp = bitmap;
	while (tmp != 0) {
		start++;
		if ((tmp & 1) != 0) {
			break;
		}
		tmp >>= 1;
	}

	if (start < 0 || start >= n) {
		return false;
	}

	queue[tail++] = start;
	visited[start] = true;
	subset_size = bitmap_popcount64(bitmap);

	while (head < tail) {
		int idx = queue[head++];
		Vertex *v = vertexes[idx];
		ListCell *lc;

		foreach (lc, v->adj) {
			Vertex *nbr = (Vertex *)lfirst(lc);
			int nbr_idx = nbr->index;

			if (nbr_idx < 0 || nbr_idx >= n) {
				continue;
			}

			if (((bitmap >> nbr_idx) & 1) == 0) {
				continue;
			}

			if (visited[nbr_idx]) {
				continue;
			}

			visited[nbr_idx] = true;
			queue[tail++] = nbr_idx;

			if (tail >= subset_size) {
				break;
			}
		}
	}

	return tail == subset_size;
}

static bool bitmaps_adjacent(Vertex **vertexes, int n, uint64 left_bm, uint64 right_bm)
{
	int i;

	for (i = 0; i < n; i++) {
		Vertex *v;
		ListCell *lc;

		if (((left_bm >> i) & 1) == 0) {
			continue;
		}

		v = vertexes[i];
		foreach (lc, v->adj) {
			Vertex *nbr = (Vertex *)lfirst(lc);
			int nbr_idx = nbr->index;

			if (nbr_idx < 0 || nbr_idx >= n) {
				continue;
			}

			if (((right_bm >> nbr_idx) & 1) != 0) {
				return true;
			}
		}
	}

	return false;
}

static List *plan_dp_sub(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	int n = list_length(topology->vertexes);
	Vertex **vertexes;
	RelOptInfo **best_plans;
	Cost *best_costs;
	uint64 total_sets;
	bool *visited;
	int *queue;
	int i;

	if (n == 0) {
		*cost_plan = 0;
		return NIL;
	}

	if (n >= (int)(sizeof(uint64) * CHAR_BIT)) {
		*cost_plan = 0;
		return NIL;
	}

	total_sets = ((uint64)1) << n;
	vertexes = (Vertex **)palloc0(n * sizeof(Vertex *));
	best_plans = (RelOptInfo **)palloc0(total_sets * sizeof(RelOptInfo *));
	best_costs = (Cost *)palloc0(total_sets * sizeof(Cost));
	visited = (bool *)palloc0(n * sizeof(bool));
	queue = (int *)palloc0(n * sizeof(int));

	for (i = 0; i < n; i++) {
		Vertex *v = (Vertex *)list_nth(topology->vertexes, i);

		vertexes[i] = v;
		vertexes[i]->index = i;
	}

	for (i = 0; i < total_sets; i++) {
		best_costs[i] = DBL_MAX;
	}

	for (i = 0; i < n; i++) {
		uint64 mask = ((uint64)1) << i;

		best_plans[mask] = vertexes[i]->rel;
		set_cheapest(best_plans[mask]);
		if (best_plans[mask]->cheapest_total_path != NULL) {
			best_costs[mask] = best_plans[mask]->cheapest_total_path->total_cost;
		}
	}

	for (uint64 join_bm = 1; join_bm < total_sets; join_bm++) {
		uint64 left_bm;
		int members = bitmap_popcount64(join_bm);

		if (members == 1) {
			continue;
		}

		if (!bitmap_connected(vertexes, n, join_bm, visited, queue)) {
			continue;
		}

		for (left_bm = (join_bm - 1) & join_bm; left_bm > 0;
		     left_bm = (left_bm - 1) & join_bm) {
			uint64 right_bm = join_bm ^ left_bm;
			RelOptInfo *left_plan;
			RelOptInfo *right_plan;
			RelOptInfo *join_rel;

			if (right_bm == 0) {
				continue;
			}

			if (best_plans[left_bm] == NULL || best_plans[right_bm] == NULL) {
				continue;
			}

			if (!bitmap_connected(vertexes, n, left_bm, visited, queue)) {
				continue;
			}
			if (!bitmap_connected(vertexes, n, right_bm, visited, queue)) {
				continue;
			}
			if (!bitmaps_adjacent(vertexes, n, left_bm, right_bm)) {
				continue;
			}

			left_plan = best_plans[left_bm];
			right_plan = best_plans[right_bm];
			join_rel = make_join_rel(root, left_plan, right_plan);

			if (join_rel == NULL) {
				continue;
			}

			set_cheapest(join_rel);
			if (join_rel->cheapest_total_path == NULL) {
				continue;
			}

			if (join_rel->cheapest_total_path->total_cost < best_costs[join_bm]) {
				best_costs[join_bm] = join_rel->cheapest_total_path->total_cost;
				best_plans[join_bm] = join_rel;
			}
		}
	}

	{
		List *result;

		if (best_plans[total_sets - 1] != NULL) {
			*cost_plan = best_costs[total_sets - 1];
			result = list_make1(best_plans[total_sets - 1]);
		} else {
			*cost_plan = 0;
			result = NIL;
		}

		pfree(queue);
		pfree(visited);
		pfree(best_costs);
		pfree(best_plans);
		pfree(vertexes);

		return result;
	}
}