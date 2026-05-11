#ifndef GRAPH_UTILS_H
#define GRAPH_UTILS_H
#include "c.h"
#include "postgres.h"
static const uint64 MAX_CONTRACTION_ITERATIONS = 3;
typedef struct Vertex
{
	RelOptInfo *rel;
	List	   *adj;
	size_t		index;
}			Vertex;

typedef enum
{
	CHAIN, CYCLE, STAR, DENSITY_GRAPH, COMPONENT,DP,DP_SUB,GOO,ANCHORS
}			TypeTopology;
typedef struct Topology
{
	List	   *vertexes;
	uint64		csg;
	void	   *extended_info;
	TypeTopology form;
}			Topology;

extern int mark_anchor_zones(List *vertexes, bool *used_vertexes);
extern bool has_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern List *build_join_graph(PlannerInfo *root, List *initial_rels);
extern List *split_components(PlannerInfo *root, List *vertexes);
extern void update_indices(Topology * component);
extern Selectivity get_selectivity(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern Cost cost_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern RelOptInfo *make_rel(PlannerInfo *root, RelOptInfo *left, RelOptInfo *right);
extern void print_topology(Topology * topology,TypeTopology type);
extern void print_list(List* rels,TypeTopology type);
extern void print_trace(RelOptInfo *rel);
void free_join_graph(List *graph);
extern Topology *contract_anchors(PlannerInfo *root, Topology *component);
extern void set_complexity_topology(PlannerInfo *root, Topology * topology);
#endif
