#ifndef HEURISTIC_MANAGER_H
#define HEURISTIC_MANAGER_H
#include "postgres.h"
#include "nodes/pg_list.h"
#include "nodes/pathnodes.h"
static const double b1 = 0.75;
static const double q = 0.25;
static const double budget_soft_limit = 0.9;
static const double k1 = 0.6;
static const double k2 = 0.25;
static const double k3 = 0.15;
extern RelOptInfo *heuristic_join_search(PlannerInfo *root, List *initial_rels);
RelOptInfo * dp_sub(PlannerInfo *root, List * initial_rels);
#endif
