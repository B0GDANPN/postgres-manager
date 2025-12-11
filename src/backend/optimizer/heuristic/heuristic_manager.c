#include "postgres.h"
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

static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan);

static RelOptInfo *goo(PlannerInfo *root, List *component_plans, bool clauseless);

static void split_budget_among_topologies(List *topologies, uint64 budget, ListCell *init_cell);
static uint64 get_cost_heuristic(Topology *topology, TypeHeuristic type_heuristic);
///////////////////////////////////////////////////////////////////////////////////
static uint64 get_cost_heuristic(Topology *topology, TypeHeuristic type_heuristic)
{
	return 0;
	if (topology->topology == CHAIN) {
	}
	if (topology->topology == CYCLE) {
	}
	if (topology->topology == STAR) {
	}
	if (topology->topology == DENSITY_GRAPH) {
	}
}

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
static RelOptInfo *plan_subgraph(PlannerInfo *root, Topology *topology, Cost *cost_plan)
{
	// cost_plan -- final cost plannitg this topology
	List *initial_rels = NIL; // List* of RelOptInfo*
	ListCell *lc;
	foreach (lc, topology->vertexes) {
		Vertex *v = (Vertex *)lfirst(lc);
		RelOptInfo *rel = v->rel;
		initial_rels = lappend(initial_rels, rel);
	}

	RelOptInfo *plan = NULL;
	plan = standard_join_search(root,
				    list_length(initial_rels),
				    initial_rels,
				    topology->budget,
				    cost_plan);
	if (plan) {
		return plan;
	}
	// fail planning DP, very expensive, so try cheaper.
	*cost_plan = 0;
	switch (topology->form) {
	case CHAIN:
		plan = plan_chain(root, topology, cost_plan);
	case CYCLE:
		plan = plan_cycle(root, topology, cost_plan);
	case STAR:
		plan = plan_star(root, topology, cost_plan);
	case DENSITY_GRAPH:
		plan = plan_density(root, topology, cost_plan);
	case COMPONENT:
		plan = NULL;
	}
	if (plan) {
		return plan;
	}
	// specialized heuristis very expensive, so GOO.
	*cost_plan = 0;
	plan = goo(root, initial_rels, false, cost_plan);

	// RelOptInfo *plan = geqo(root, list_length(initial_rels), initial_rels);
	return plan;
}
