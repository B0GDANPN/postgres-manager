#ifndef GRAPH_UTILS_H
#define GRAPH_UTILS_H
#include "postgres.h"
#include "nodes/nodes.h"

#include "nodes/pathnodes.h"
typedef struct Vertex
{
	RelOptInfo *rel;
	List	   *adj;
	size_t		index;
	int			topology_id;
}			Vertex;

typedef enum
{
	CHAIN, CYCLE, STAR, DENSITY_GRAPH, COMPONENT
}			TypeTopology;
typedef struct Topology
{
	int			id;
	List	   *vertexes;
	uint64		ccp;
	Cost		budget;
	TypeTopology form;
	Selectivity sel;
	Cardinality vol;
	void	   *extended_info;
}			Topology;

extern bool has_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern bool is_connected(List *all_vertexes, size_t bitmap);
extern List *build_join_graph(PlannerInfo *root, List *initial_rels);
extern List *split_components(PlannerInfo *root, List *vertexes);
extern List *find_cycles(PlannerInfo *root, List *vertexes, bool *used_vertexes_comp);
extern List *find_stars(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern List *find_chains(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern List *find_dense_subgraphs(PlannerInfo *root, List *vertexes, bool *used_vertexes);
extern void update_indices(Topology * component);
extern Selectivity get_selectivity(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern void set_id(PlannerInfo *root, Topology * topology);
extern void set_sel_topology(PlannerInfo *root, Topology * topology);
extern void set_vol_topology(PlannerInfo *root, Topology * topology);
extern Cost cost_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2);
extern void print_topology(Topology * topology);
#endif
