#ifndef HEURISTICS_H
#define HEURISTICS_H
#include "postgres.h"
#include "nodes/pathnodes.h"
#include "optimizer/heuristic/graph_utils.h"
#include <fcntl.h>
static const double budget_soft_limit = 0.9;
extern RelOptInfo * goo_cost_cardinality(PlannerInfo *root, List *initial_rels,
	bool clauseless);
extern RelOptInfo *plan_topology(PlannerInfo *root, Topology * topology);
extern List *plan_chain_dp(PlannerInfo *root, Topology * topology);
extern List *plan_cycle(PlannerInfo *root, Topology * topology);
extern List *plan_star(PlannerInfo *root, Topology * topology);
extern List *plan_star2(PlannerInfo *root, Topology * topology);
extern List *plan_dp_sub(PlannerInfo *root, Topology * topology);
extern RelOptInfo * dp_sub(PlannerInfo *root, List * initial_rels);
#endif