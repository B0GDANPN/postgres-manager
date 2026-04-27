#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/heuristic/heuristic_manager.h"
#include "optimizer/heuristic/heuristics.h"
#include <stdbool.h>

/**
 * @brief Entry point: adaptive join ordering via csg-driven routing.
 *
 * Builds a join graph, splits it into connected components, and routes
 * each through a complexity cascade:
 *   1. csg ≤ threshold  → standard DPsize (exact)
 *   2. contract anchors → recheck csg → DPsize if now tractable
 *   3. still too large  → GOO heuristic
 * Disconnected components are merged with GOO (clauseless mode).
 *
 * @param root         PlannerInfo context.
 * @param initial_rels List of base RelOptInfo* to join.
 * @return Single fully-joined RelOptInfo* covering all relations.
 */
RelOptInfo *
heuristic_join_search(PlannerInfo *root, List *initial_rels)
{
	List       *graph = build_join_graph(root, initial_rels);
	List       *components = split_components(root, graph);
	List       *component_plans = NIL;
	ListCell   *lc = NULL;
	RelOptInfo *final_plan = NULL;
 
	foreach(lc, components)
	{
		Topology   *component = (Topology *) lfirst(lc);
		RelOptInfo *component_plan = NULL;

		set_complexity_topology(root, component); 
		if (component->csg <= csg_threshold)
		{
			/* print_topology(component,DP); */
			component_plan = standard_planning_wrapper(root, component);
			component_plans = lappend(component_plans, component_plan);
			continue;
		}
 
		for (int iter = 0; iter < MAX_CONTRACTION_ITERATIONS; iter++)
		{
			int		old_nv = list_length(component->vertexes);
			int     new_nv;
			component = contract_anchors(root, component);
			set_complexity_topology(root, component);
 
			new_nv = list_length(component->vertexes);
 
			if (new_nv >= old_nv)
				break;
 
			if (component->csg <= csg_threshold)
				break;
		}
 
		if (component->csg <= csg_threshold)
		{
			component_plan = standard_planning_wrapper(root, component);
			component_plans = lappend(component_plans, component_plan);
			continue;
		}
		component_plan = goo_wrapper(root, component, true);
		component_plans = lappend(component_plans, component_plan);
	}
	/* print_list(component_plans,GOO); */
	final_plan = goo_cost_cardinality(root, component_plans, true);
	list_free(components);
	list_free(graph);
	return final_plan;
}
