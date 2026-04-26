#ifndef HEURISTICS_H
#define HEURISTICS_H
#include "postgres.h"
#include "nodes/pathnodes.h"
#include "optimizer/heuristic/graph_utils.h"

extern RelOptInfo * goo_cost_cardinality(PlannerInfo *root, List *initial_rels,
	bool clauseless);
extern RelOptInfo* standard_planning_wrapper(PlannerInfo *root, Topology * topology);
extern RelOptInfo* goo_wrapper(PlannerInfo *root, Topology * topology, bool clauseless);
extern RelOptInfo * dp_sub(PlannerInfo *root, List *initial_rels);
extern RelOptInfo * goo_card(PlannerInfo *root, List *initial_rels);
#endif
