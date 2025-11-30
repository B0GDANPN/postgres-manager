#ifndef GRAPH_UTILS_H
#define GRAPH_UTILS_H
#include "postgres.h"
#include "nodes/nodes.h"

#include "nodes/pathnodes.h"
typedef struct Vertex {
	RelOptInfo *rel;
	List *adj;
	size_t index;
} Vertex;

typedef enum { CHAIN, CYCLE, STAR, DENSITY_GRAPH, COMPONENT } TypeTopology;
typedef struct Topology {
	List *vertexes;
	uint64 ccp;
	uint64 budget;
	TypeTopology topology;
	Selectivity sel;
	Cardinality vol;
} Topology;

extern bool has_simple_inner_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern List *build_join_graph(PlannerInfo *root, List *initial_rels);
extern List *split_components(PlannerInfo *root, List *vertexes);
extern List *find_cycles(PlannerInfo *root, List *vertexes, bool *used_vertexes_comp);
extern List *find_stars(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern List *find_chains(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern List *find_dense_subgraphs(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern void update_indices(Topology *component);
extern Selectivity get_selectivity(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern void set_sel_topology(PlannerInfo *root, Topology *topology);
extern void set_vol_topology(PlannerInfo *root, Topology *topology);
#endif