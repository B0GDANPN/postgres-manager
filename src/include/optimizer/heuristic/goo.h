#ifndef GOO_H
#define GOO_H
#include "postgres.h"
#include "nodes/pathnodes.h"
extern List *goo_init_cost_init_result(PlannerInfo *root, List *initial_rels,
				 bool clauseless, bool force);
extern List *goo_init_result(PlannerInfo *root, List *initial_rels,
				 bool clauseless);
extern List *goo_final_result(PlannerInfo *root, List *initial_rels,
				 bool clauseless);
				 
extern List * goo_init_cost(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force);

extern List * goo_final_cost(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force);
extern List * goo_final_cost_final_result(PlannerInfo *root, List *initial_rels,
	bool clauseless, bool force);
extern List * dummy(PlannerInfo *root, List *initial_rels);
#endif
