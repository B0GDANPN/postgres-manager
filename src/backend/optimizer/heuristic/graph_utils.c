#include "optimizer/heuristic/graph_utils.h"
#include "optimizer/heuristic/counter.h"
#include "c.h"
#include "lib/stringinfo.h"
#include "nodes/bitmapset.h"
#include "nodes/nodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "optimizer/joininfo.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/restrictinfo.h"
#include "postgres.h"
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/palloc.h"
#include <float.h>
#include <limits.h>
#include <optimizer/cost.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static const uint64 dphyp_geqo_cc_threshold = 10000;
static const double THRESH = 0.7;
static const Selectivity border_selectivity = 0.26;
static const int max_ray_length = 5;
static const int min_length_cycle = 3;

/*
 * Anchor zone protection.
 *
 * A vertex is an "anchor" when its estimated rows are tiny relative
 * to its heaviest neighbour (dimension table with a selective filter
 * next to a large fact table).  Separating an anchor from its
 * neighbours during topology decomposition prevents the planner
 * from building index-driven chains that start from the anchor.
 *
 * mark_anchor_zones() sets used_vertexes[i]=true for every anchor
 * and all its immediate neighbours.  The caller must save/restore
 * these bits so that find_chains() later picks them up as one
 * connected component.
 */
static const double ANCHOR_RATIO   = 100.0;   /* rows < max_nbr / 100 */
static const double ANCHOR_ABS_MAX = 50000.0;  /* absolute cap          */
static void set_complexity_topology(PlannerInfo *root, Topology * topology);
static List *bfs_component(Vertex * start, bool *used_vertexes);
static bool dfs_cycle(PlannerInfo *root, Vertex * prev, Vertex * cur,
					  List **stack, bool *visited,
					  bool *used_vertexes_comp);	/* stack is list of Vertex*  */
static bool is_star(Vertex * center, const bool *used_vertexes);
static List *find_star(PlannerInfo *root, Vertex * center, bool *used_vertexes,
					   List **chains);
static Vertex * find_min_degree_vertex_cached(Selectivity *sel_cache, int nv, List *sub);
static double density_cached(Selectivity *sel_cache, int nv, List *sub);
static int	count_edges_cached(Selectivity *sel_cache, int nv, List *sub);
static List *peel_dense(Selectivity *sel_cache, int nv, List *candidate);



/**
 * @brief Mark anchor zones with 2-hop protection.
 *
 * An anchor is a vertex whose filtered rows are tiny relative to its
 * heaviest neighbour.  We protect the anchor, its immediate neighbours
 * (1-hop) and their neighbours (2-hop).  This ensures that topology
 * detectors (dense, star, cycle) cannot separate the selective anchor
 * from the join paths that exploit its selectivity.
 *
 * 2-hop is necessary because star/cycle detectors operate on the
 * UNMARKED subgraph.  With only 1-hop protection, the anchor's
 * neighbour-of-neighbour can become a star center and pull away
 * tables that should be planned together with the anchor.
 */
int
mark_anchor_zones(List *vertexes, bool *used_vertexes)
{
    int         marked = 0;
    ListCell   *lc;
    List       *hop1_vertices = NIL;  /* 1-hop neighbours to expand */

    /* Pass 1: find anchors, mark them + their immediate neighbours */
    foreach(lc, vertexes)
    {
        Vertex     *v = (Vertex *) lfirst(lc);
        Cardinality max_nbr_rows = 0;
        int         unused_nbrs = 0;
        ListCell   *lc2;

        if (used_vertexes[v->index])
            continue;

        foreach(lc2, v->adj)
        {
            Vertex *nbr = (Vertex *) lfirst(lc2);
            if (!used_vertexes[nbr->index])
            {
                unused_nbrs++;
                if (nbr->rel->rows > max_nbr_rows)
                    max_nbr_rows = nbr->rel->rows;
            }
        }

        if (unused_nbrs == 0)
            continue;

        if (v->rel->rows < ANCHOR_ABS_MAX &&
            v->rel->rows * ANCHOR_RATIO < max_nbr_rows)
        {
            /* Mark anchor itself */
            if (!used_vertexes[v->index])
            {
                used_vertexes[v->index] = true;
                marked++;
            }

            /* Mark 1-hop neighbours and collect them for 2-hop */
            foreach(lc2, v->adj)
            {
                Vertex *nbr = (Vertex *) lfirst(lc2);
                if (!used_vertexes[nbr->index])
                {
                    used_vertexes[nbr->index] = true;
                    marked++;
                    hop1_vertices = lappend(hop1_vertices, nbr);
                }
            }
        }
    }

    /* Pass 2: mark 2-hop (neighbours of 1-hop vertices) */
    foreach(lc, hop1_vertices)
    {
        Vertex     *v = (Vertex *) lfirst(lc);
        ListCell   *lc2;

        foreach(lc2, v->adj)
        {
            Vertex *nbr = (Vertex *) lfirst(lc2);
            if (!used_vertexes[nbr->index])
            {
                used_vertexes[nbr->index] = true;
                marked++;
            }
        }
    }

    list_free(hop1_vertices);
    return marked;
}

/**
 * @brief Check whether two relations have a legal simple join edge.
 *
 * Uses join clause and join order restriction checks while excluding overlap.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return True if a simple inner edge exists between the relations.
 */
bool
has_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	bool		result = !bms_overlap(rel1->relids, rel2->relids) &&
		(have_relevant_joinclause(root, rel1, rel2) || have_join_order_restriction(root, rel1, rel2));

	return result;
}

/**
 * @brief Emit a debug representation of the join graph.
 *
 * Logs each vertex, its cost, and adjacent edge costs.
 *
 * @param root Planner context.
 * @param graph List of Vertex items.
 */
static void
print_graph(PlannerInfo *root, List *graph)
{
	StringInfoData buf;
	ListCell   *lc = NULL;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_GRAPH\n");
	foreach(lc, graph)
	{
		Vertex	   *vertex = (Vertex *) lfirst(lc);
		ListCell   *lc2 = NULL;
		Cost		cost_rel = vertex->rel->cheapest_total_path->total_cost;

		appendStringInfo(&buf, "%zu(%lf):", vertex->index, cost_rel);
		foreach(lc2, vertex->adj)
		{
			Vertex	   *neighbor = (Vertex *) lfirst(lc2);
			Cost		prel_join_cost = cost_edge(root, vertex->rel, neighbor->rel);
			Selectivity selectivity = get_selectivity(root, vertex->rel, neighbor->rel);

			appendStringInfo(&buf, " %zu(%.3lf, %.9lf)", neighbor->index, prel_join_cost, selectivity);
		}
		appendStringInfo(&buf, "\n");
	}
	appendStringInfo(&buf, "\n");
	foreach(lc, graph)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			i = -1;

		appendStringInfo(&buf, "bitmap v_%zu: ", v->index);
		while ((i = bms_next_member(v->rel->relids, i)) >= 0)
		{
			appendStringInfo(&buf, "%d ", i);
		}
		appendStringInfo(&buf, "\n");
	}
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Debug print a topology.
 *
 * Prints the type of the topology, selectivity, count connected pairs of
 * subgraphs, volume, and budget. If the topology is a star, prints the center
 * and chains of the star (each chain on a new line).
 *
 * Also prints Bitmapset of each vertex in the topology.
 * @param topology Topology to print.
 */
void
print_topology(Topology * topology)
{
	StringInfoData buf;
	ListCell   *lc = NULL;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_TOPOLOGY\n");
	switch (topology->form)
	{
		case CHAIN:
			{
				appendStringInfo(&buf, "Chain\n");
				break;
			}
		case CYCLE:
			{
				appendStringInfo(&buf, "Cycle\n");
				break;
			}
		case DENSITY_GRAPH:
			{
				appendStringInfo(&buf, "Density graph\n");
				break;
			}
		case STAR:
			{
				appendStringInfo(&buf, "Star\n");
				break;
			}
		case COMPONENT:
			{
				appendStringInfo(&buf, "Component\n");
				break;
			}
	}
	appendStringInfo(&buf, "sel: %.10lf\n", topology->sel);
	appendStringInfo(&buf, "ccp: %lu\n", topology->ccp);
	appendStringInfo(&buf, "vol: %lf\n", topology->vol);
	appendStringInfo(&buf, "budget: %lf\n", topology->budget);
	appendStringInfo(&buf, "vertexes: ");

	if (topology->form == STAR)
	{
		Vertex	   *center = (Vertex *) linitial(topology->vertexes);
		ListCell   *lc = NULL;

		appendStringInfo(&buf, "Center: %zu\n", center->index);
		foreach(lc, topology->extended_info)
		{
			List	   *chain = (List *) lfirst(lc);
			ListCell   *lc2 = NULL;

			appendStringInfo(&buf, "Chain: ");
			foreach(lc2, chain)
			{
				Vertex	   *v = (Vertex *) lfirst(lc2);

				appendStringInfo(&buf, "%zu ", v->index);
			}
			appendStringInfo(&buf, "\n");
		}
	}
	else
	{
		ListCell   *lc = NULL;

		foreach(lc, topology->vertexes)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

			appendStringInfo(&buf, "%zu ", v->index);
		}
		appendStringInfo(&buf, "\n");
	}
	/* print bitmap each vertex */
	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			i = -1;

		appendStringInfo(&buf, "bitmap v_%zu: ", v->index);
		while ((i = bms_next_member(v->rel->relids, i)) >= 0)
		{
			appendStringInfo(&buf, "%d ", i);
		}
		appendStringInfo(&buf, "\n");
	}
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Build a join graph from initial relations.
 *
 * Creates a vertex per relation and adds edges for simple inner joins.
 *
 * @param root Planner context.
 * @param initial_rels Base relations to include.
 *
 * @return List of Vertex items representing the join graph.
 */
List *
build_join_graph(PlannerInfo *root, List *initial_rels)
{
	List	   *vertexes = NIL;
	size_t		index = 0;
	ListCell   *lc = NULL;
	ListCell   *i = NULL;
	ListCell   *j = NULL;

	foreach(lc, initial_rels)
	{
		RelOptInfo *rel = (RelOptInfo *) lfirst(lc);
		Vertex	   *v = (Vertex *) palloc0(sizeof(Vertex));

		v->rel = rel;
		v->adj = NIL;
		v->index = index++;
		vertexes = lappend(vertexes, v);
	}
	foreach(i, vertexes)
	{
		Vertex	   *v_i = (Vertex *) lfirst(i);

		for_each_cell(j, vertexes, lnext(vertexes, i))
		{
			Vertex	   *v_j = (Vertex *) lfirst(j);

			if (has_edge(root, v_i->rel, v_j->rel))
			{
				v_i->adj = lappend(v_i->adj, v_j);
				v_j->adj = lappend(v_j->adj, v_i);
			}
		}
	}
	print_graph(root, vertexes);
	return vertexes;
}

/**
 * @brief BFS to collect a connected component.
 *
 * Marks visited vertices and returns the component list.
 *
 * @param v Start vertex.
 * @param comp Current component list.
 * @param used_vertexes Visited marker array.
 *
 * @return Updated component list.
 */
static List *
bfs_component(Vertex * start, bool *used_vertexes)
{
	List	   *queue = list_make1(start);
	int			begin_queue = 0;

	used_vertexes[start->index] = true;
	while (begin_queue < list_length(queue))
	{
		Vertex	   *v = (Vertex *) lfirst(list_nth_cell(queue, begin_queue));
		ListCell   *lc = NULL;

		begin_queue++;
		foreach(lc, v->adj)
		{
			Vertex	   *next = (Vertex *) lfirst(lc);

			if (!used_vertexes[next->index])
			{
				used_vertexes[next->index] = true;
				queue = lappend(queue, next);
			}
		}
	}
	return queue;
}

/**
 * @brief Split a join graph into connected components.
 *
 * Builds Topology objects and computes selectivity, volume, and complexity.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 *
 * @return List of Topology components.
 */
List *
split_components(PlannerInfo *root, List *vertexes)
{
	List	   *comps = NIL;	/* List* of Component*   */
	int			number_of_rels = list_length(vertexes);
	bool	   *used_vertexes = (bool *) palloc0(number_of_rels * sizeof(bool));
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used_vertexes[v->index])
		{
			Topology   *component = (Topology *) palloc0(sizeof(Topology));
			List	   *sub = bfs_component(v, used_vertexes);

			component->vertexes = sub;
			component->form = COMPONENT;
			/*set_id(root, component);
			set_sel_topology(root, component);
			set_vol_topology(root, component);
			set_complexity_topology(root, component);*/
			comps = lappend(comps, component);
		}
	}
	pfree(used_vertexes);
	return comps;
}

/* find cycle */
static bool
dfs_cycle(PlannerInfo *root, Vertex * prev, Vertex * cur,
		  List **stack, bool *visited, bool *used_vertexes_comp)
{
	ListCell   *lc = NULL;

	visited[cur->index] = true;
	*stack = lappend(*stack, cur);
	foreach(lc, cur->adj)
	{
		Vertex	   *nbr = (Vertex *) lfirst(lc);
		Selectivity sel;

		if (nbr == prev)
		{
			continue;
		}
		sel = get_selectivity(root, cur->rel, nbr->rel);
		if (sel > border_selectivity)
		{
			continue;
		}
		if (visited[nbr->index] && (*stack)->length >= min_length_cycle)
		{
			List	   *cycle = NIL;
			ListCell   *lc2 = NULL;
			ListCell   *lc3 = NULL;

			foreach(lc2, *stack)
			{
				Vertex	   *it = (Vertex *) lfirst(lc2);

				if (it->index == nbr->index)
				{
					break;
				}
			}
			for_each_cell(lc3, *stack, lc2)
			{
				Vertex	   *it = (Vertex *) lfirst(lc3);

				cycle = lappend(cycle, it);
				used_vertexes_comp[it->index] = true;
			}
			list_free(*stack);
			*stack = cycle;
			return true;
		}
		if (!visited[nbr->index] && !used_vertexes_comp[nbr->index])
		{
			bool		was_cycle =
				dfs_cycle(root, cur, nbr, stack, visited, used_vertexes_comp);

			if (was_cycle)
			{
				return true;
			}
		}
	}
	visited[cur->index] = false;
	*stack = list_delete_last(*stack);
	return false;
}

/**
 * @brief Check whether a -selected subgraph is connected.
 *
 * Builds the vertex subset from the bitmap and verifies connectivity with BFS.
 *
 * @param all_vertexes All vertices in the topology.
 * @param bitmap Bitmask selecting a subset of vertices.
 *
 * @return True if the selected subgraph is connected.
 */
bool
is_connected(List *all_vertexes, size_t bitmap)
{
	List	   *vertices = NIL;
	bool	   *used = NULL;
	Vertex	   *start = NULL;
	size_t		topology_id;
	List	   *queue = NIL;
	int			begin_queue = 0;
	ListCell   *lc = NULL;
	bool		connected = true;

	for (uint64 i = 0; ((uint64) 1 << i) <= bitmap; i++)
	{
		if (bitmap & ((uint64) 1 << i))
		{
			Vertex	   *v = (Vertex *) list_nth(all_vertexes, i);

			vertices = lappend(vertices, v);
		}
	}
	/* check that vertexes are connected */
	used = (bool *) palloc0(list_length(all_vertexes) * sizeof(bool));
	start = (Vertex *) linitial(vertices);
	topology_id = start->topology_id;
	queue = list_make1(start);
	used[start->index] = true;
	while (begin_queue < list_length(queue))
	{
		Vertex	   *v = (Vertex *) lfirst(list_nth_cell(queue, begin_queue));

		begin_queue++;
		foreach(lc, v->adj)
		{
			Vertex	   *next = (Vertex *) lfirst(lc);

			if (!used[next->index] && next->topology_id == topology_id)
			{
				used[next->index] = true;
				queue = lappend(queue, next);
			}
		}
	}
	list_free(queue);
	foreach(lc, vertices)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used[v->index])
		{
			connected = false;
			break;
		}
	}
	list_free(vertices);
	pfree(used);
	return connected;
}

/* find non intersecting cycles */
List *
find_cycles(PlannerInfo *root, List *vertexes, bool *used_vertexes_comp)
{
	int			n_local = list_length(vertexes);
	List	   *cycles = NIL;	/* List* of List* of Vertex*  */
	bool	   *visited = (bool *) palloc0(n_local * sizeof(bool));
	ListCell   *lc = NULL;
	List	   *cyclic_topologies = NIL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		List	   *stack = NIL;

		if (used_vertexes_comp[v->index])
		{
			continue;
		}
		memset(visited, false, n_local * sizeof(bool));
		dfs_cycle(root, NULL, v, &stack, visited, used_vertexes_comp);
		if (stack)
		{
			cycles = lappend(cycles, stack);
		}
	}
	foreach(lc, cycles)
	{
		List	   *cycle = (List *) lfirst(lc);
		Topology   *topology = (Topology *) palloc0(sizeof(Topology));

		topology->vertexes = cycle;
		topology->form = CYCLE;
		/*set_id(root, topology);
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);*/
		cyclic_topologies = lappend(cyclic_topologies, topology);
		/* print_topology(topology); */
	}
	pfree(visited);
	return cyclic_topologies;
}

/**
 * @brief Decide whether a vertex can be treated as a star center.
 *
 * Checks degree and relative volume of neighbors.
 *
 * @param center Candidate center vertex.
 * @param used_vertexes Used marker array.
 *
 * @return True if the vertex qualifies as a star center.
 */
static bool
is_star(Vertex *center, const bool *used_vertexes)
{
    double center_rows = center->rel->rows;
    int count_unused = 0;
    double sum_neighbor_rows = 0;
	ListCell   *lc = NULL;
    foreach(lc, center->adj) {
        Vertex *nbr = lfirst(lc);
        if (!used_vertexes[nbr->index]) {
            count_unused++;
            sum_neighbor_rows += nbr->rel->rows;
        }
    }
    
    if (count_unused < 3)
        return false;
    
    if (center_rows > sum_neighbor_rows / count_unused)
        return false;
    
    return true;
}

/**
 * @brief Build a star topology around a center vertex.
 *
 * Grows rays up to a maximum length by selectivity.
 *
 * @param root Planner context.
 * @param center Star center vertex.
 * @param used_vertexes Used marker array.
 * @param chains Output list of ray chains.
 *
 * @return List of vertices that form the star.
 */
static List *
find_star(PlannerInfo *root, Vertex * center, bool *used_vertexes,
		  List **chains)
{
	List	   *star = NIL;
	ListCell   *lc = NULL;

	star = lappend(star, center);
	used_vertexes[center->index] = true;
	foreach(lc, center->adj)
	{
		int			ray_len = 0;
		Vertex	   *curr = (Vertex *) lfirst(lc);
		List	   *chain = NIL;

		if (used_vertexes[curr->index])
		{
			continue;
		}
		while (ray_len < max_ray_length)
		{
			Selectivity sel;
			Vertex	   *new_neighbor = NULL;
			ListCell   *lc2 = NULL;

			chain = lappend(chain, curr);
			used_vertexes[curr->index] = true;
			ray_len += 1;
			sel = border_selectivity;
			foreach(lc2, curr->adj)
			{
				Selectivity tmp_sel;
				Vertex	   *tmp = (Vertex *) lfirst(lc2);

				if (used_vertexes[tmp->index] || is_star(tmp, used_vertexes))
				{
					continue;
				}
				tmp_sel = get_selectivity(root, curr->rel, tmp->rel);
				if (tmp_sel < sel)
				{
					new_neighbor = tmp;
					sel = tmp_sel;
				}
			}
			if (new_neighbor == NULL)
			{
				break;
			}
			curr = new_neighbor;
		}
		star = list_concat(star, chain);
		*chains = lappend(*chains, chain);
	}
	return star;
}

/**
 * @brief Find star topologies among unused vertices.
 *
 * Detects star centers and builds star topologies with ray chains.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used_vertexes Used marker array.
 *
 * @return List of STAR topologies.
 */
List *
find_stars(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List	   *stars = NIL;
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Topology   *topology = NULL;
		Vertex	   *v = (Vertex *) lfirst(lc);
		List	   *chains = NIL;
		List	   *star = NIL;

		if (used_vertexes[v->index] || !is_star(v, used_vertexes))
		{
			continue;
		}
		star = find_star(root, v, used_vertexes,
						 &chains);	/* List* of {star_vertex, List1 of chain
									 * vertex, List_n of chain vertex} */
		topology = (Topology *) palloc0(sizeof(Topology));
		topology->vertexes = star;
		topology->form = STAR;
		topology->extended_info = chains;
		/*set_id(root, topology);
		set_sel_topology(root, topology);
		set_vol_topology(root, topology);
		set_complexity_topology(root, topology);*/
		stars = lappend(stars, topology);
		/* print_topology(topology); */
	}
	return stars;
}

/**
 * @brief Count "good" internal edges in a vertex subset using cached selectivities.
 *
 * An edge is counted only when its cached selectivity does not
 * exceed border_selectivity.
 *
 * @param sel_cache  Flat nv*nv selectivity matrix; -1.0 = no edge.
 * @param nv         Dimension of the cache (total vertices in component).
 * @param sub        Vertex subset.
 *
 * @return Number of good internal edges.
 */
static int
count_edges_cached(Selectivity *sel_cache, int nv, List *sub)
{
	int			m = 0;
	ListCell   *lc = NULL;

	foreach(lc, sub)
	{
		Vertex	   *v1 = (Vertex *) lfirst(lc);
		ListCell   *lc2 = NULL;

		foreach(lc2, v1->adj)
		{
			Vertex	   *v2 = (Vertex *) lfirst(lc2);

			if (v1->index < v2->index && list_member_ptr(sub, v2))
			{
				Selectivity sel = sel_cache[v1->index * nv + v2->index];

				if (sel >= 0 && sel <= border_selectivity)
				{
					m++;
				}
			}
		}
	}
	return m;
}

/**
 * @brief Reassign indices for topology vertices.
 *
 * @param component Topology to update.
 */
void
update_indices(Topology * component)
{
	size_t		i = 0;
	ListCell   *lc = NULL;

	foreach(lc, component->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		v->index = i;
		i++;
	}
}

/**
 * @brief Compute edge density for a vertex subset using cached selectivities.
 *
 * @param sel_cache  Flat nv*nv selectivity matrix.
 * @param nv         Cache dimension.
 * @param sub        Vertex subset.
 *
 * @return Density in [0,1], or 0 for small sets.
 */
static double
density_cached(Selectivity *sel_cache, int nv, List *sub)
{
	int			n = list_length(sub);
	int			m;
	double		d;

	if (n < 4)
		return 0.0;

	m = count_edges_cached(sel_cache, nv, sub);
	d = (double) m / ((double) n * (n - 1) / 2.0);
	return d;
}

/**
 * @brief Find the vertex with minimum "good" degree using cached selectivities.
 *
 * Only edges with cached selectivity <= border_selectivity are counted
 * toward a vertex's degree, consistent with the density metric.
 *
 * @param sel_cache  Flat nv*nv selectivity matrix.
 * @param nv         Cache dimension.
 * @param sub        Vertex subset.
 *
 * @return Vertex with the lowest good-edge degree.
 */
static Vertex *
find_min_degree_vertex_cached(Selectivity *sel_cache, int nv, List *sub)
{
	int			best_deg = INT_MAX;
	Vertex	   *best_v = NULL;
	ListCell   *lc = NULL;

	foreach(lc, sub)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		int			deg = 0;
		ListCell   *lc2 = NULL;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (list_member_ptr(sub, nbr))
			{
				Selectivity sel = sel_cache[v->index * nv + nbr->index];

				if (sel >= 0 && sel <= border_selectivity)
				{
					deg++;
				}
			}
		}

		if (deg < best_deg)
		{
			best_deg = deg;
			best_v = v;
		}
	}
	return best_v;
}

/**
 * @brief Attempt to peel a candidate vertex set down to a dense core.
 *
 * Iteratively removes the vertex with the lowest good-edge degree until
 * the remaining subgraph has density >= THRESH, or the candidate becomes
 * too small.
 *
 * @param sel_cache  Flat nv*nv selectivity matrix.
 * @param nv         Cache dimension.
 * @param candidate  List of Vertex* to peel (consumed — caller loses ownership).
 *
 * @return The peeled dense core (List of Vertex*), or NIL if peeling failed.
 *         On failure the candidate list is freed.
 */
static List *
peel_dense(Selectivity *sel_cache, int nv, List *candidate)
{
	while (list_length(candidate) >= 4)
	{
		Vertex	   *vmin = NULL;
		double		cur_d = density_cached(sel_cache, nv, candidate);

		if (cur_d >= THRESH)
			return candidate;

		vmin = find_min_degree_vertex_cached(sel_cache, nv, candidate);
		if (vmin == NULL)
			break;

		candidate = list_delete_ptr(candidate, vmin);
	}

	/* Check once more after the loop exits (size may be exactly 4) */
	if (list_length(candidate) >= 4 &&
		density_cached(sel_cache, nv, candidate) >= THRESH)
	{
		return candidate;
	}

	list_free(candidate);
	return NIL;
}

/**
 * @brief Find dense subgraphs and return them as topologies.
 *
 * Builds a selectivity cache once for the entire component,
 * then on each iteration splits unused vertices into connected
 * components using only good edges (sel <= border_selectivity)
 * and tries to peel each component independently.
 *
 * This avoids the bug where a single failed peeling of the full
 * unused vertex set prevents discovery of dense subgraphs that
 * exist in independent sub-components of the graph.
 *
 * @param root     Planner context.
 * @param vertexes Join graph vertices (indices must be 0..nv-1).
 * @param used     Used marker array (size >= nv, updated in-place).
 *
 * @return List of DENSITY_GRAPH topologies.
 */
List *
find_dense_subgraphs(PlannerInfo *root, List *vertexes, bool *used)
{
	List	   *dense_sets = NIL;
	int			nv = list_length(vertexes);
	Selectivity *sel_cache;
	ListCell   *lc;

	/*
	 * Build selectivity cache — one get_selectivity() call per edge,
	 * instead of n * edges calls during repeated density/peeling passes. -1.0
	 * = no adjacency between these vertices.
	 */
	sel_cache = (Selectivity *) palloc(nv * nv * sizeof(Selectivity));
	for (int i = 0; i < nv * nv; i++)
		sel_cache[i] = -1.0;

	foreach(lc, vertexes)
	{
		Vertex	   *v1 = (Vertex *) lfirst(lc);
		ListCell   *lc2;

		foreach(lc2, v1->adj)
		{
			Vertex	   *v2 = (Vertex *) lfirst(lc2);

			if (v1->index < v2->index)
			{
				Selectivity s = get_selectivity(root, v1->rel, v2->rel);

				sel_cache[v1->index * nv + v2->index] = s;
				sel_cache[v2->index * nv + v1->index] = s;
			}
		}
	}

	/*
	 * Main loop: on each iteration, collect unused vertices, split them into
	 * connected components (good-edge-only), and try peeling each. Re-enter
	 * only if at least one dense subgraph was found (remaining fragments of a
	 * large component may form new dense cores).
	 */
	while (true)
	{
		List	   *all_unused = NIL;
		bool	   *comp_visited;
		bool		found_any = false;

		foreach(lc, vertexes)
		{
			Vertex	   *v = (Vertex *) lfirst(lc);

			if (!used[v->index])
				all_unused = lappend(all_unused, v);
		}

		if (list_length(all_unused) < 4)
		{
			list_free(all_unused);
			break;
		}

		/*
		 * Split unused vertices into connected components, following only
		 * "good" edges (sel <= border_selectivity).  This ensures that two
		 * clusters connected only by near-Cartesian joins are treated
		 * independently.
		 */
		comp_visited = (bool *) palloc0(nv * sizeof(bool));
		for (int i = 0; i < nv; i++)
			comp_visited[i] = used[i];

		foreach(lc, all_unused)
		{
			Vertex	   *start = (Vertex *) lfirst(lc);
			List	   *component;
			List	   *dense_core;
			int			begin_q;
			ListCell   *lc2;

			if (comp_visited[start->index])
				continue;

			/* BFS: follow only edges with selectivity <= border_selectivity */
			comp_visited[start->index] = true;
			component = list_make1(start);
			begin_q = 0;

			while (begin_q < list_length(component))
			{
				Vertex	   *v = (Vertex *) lfirst(list_nth_cell(component, begin_q));

				begin_q++;
				foreach(lc2, v->adj)
				{
					Vertex	   *nbr = (Vertex *) lfirst(lc2);
					Selectivity s;

					if (comp_visited[nbr->index])
						continue;

					s = sel_cache[v->index * nv + nbr->index];
					if (s >= 0 && s <= border_selectivity)
					{
						comp_visited[nbr->index] = true;
						component = lappend(component, nbr);
					}
				}
			}

			if (list_length(component) < 4)
			{
				list_free(component);
				continue;
			}

			/* Try peeling this connected component to a dense core. */
			dense_core = peel_dense(sel_cache, nv, list_copy(component));
			list_free(component);

			if (dense_core != NIL)
			{
				Topology   *topology = (Topology *) palloc0(sizeof(Topology));

				topology->vertexes = dense_core;
				topology->form = DENSITY_GRAPH;
				/*set_id(root, topology);
				set_sel_topology(root, topology);
				set_vol_topology(root, topology);
				set_complexity_topology(root, topology);*/
				dense_sets = lappend(dense_sets, topology);

				foreach(lc2, dense_core)
				{
					Vertex	   *v = (Vertex *) lfirst(lc2);

					used[v->index] = true;
				}
				found_any = true;
			}
		}

		pfree(comp_visited);
		list_free(all_unused);

		if (!found_any)
			break;
	}

	pfree(sel_cache);
	return dense_sets;
}

/**
 * @brief Estimate topology complexity via connected subgraph counting.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
static void
set_complexity_topology(PlannerInfo *root, Topology * topology)
{
	DPHypContext context = {0};
	List	   *initial_rels = NIL;
	ListCell   *lc = NULL;
	uint64		subgraphs_count;

	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		initial_rels = lappend(initial_rels, v->rel);
	}
	context.initial_rels = initial_rels;
	context.root = root;
	context.simple_hypernodes = NIL;

	initialize_edges(root, initial_rels, &context);

	subgraphs_count = count_cc(&context, dphyp_geqo_cc_threshold);
	topology->ccp = subgraphs_count;
	list_free(context.initial_rels);
	list_free(context.simple_hypernodes);
	pfree(context.simple_edges);
	pfree(context.complex_edges);
	hash_destroy(context.dptable);
}

/**
 * @brief Compute join selectivity for a relation pair.
 *
 * Builds a dummy join rel and evaluates clause selectivity.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return Estimated selectivity for joining rel1 and rel2.
 */
Selectivity
get_selectivity(PlannerInfo *root, RelOptInfo *rel1,
				RelOptInfo *rel2)
{
	RelOptInfo	joinrel = {0};
	SpecialJoinInfo sjinfo;
	List	   *clauses;
	List	   *unique_clauses = NIL;
	Selectivity result;
	Relids		base_relids = bms_union(rel1->relids, rel2->relids);
	List	   *seen_ecs = NIL;
	ListCell   *lc;

	init_dummy_sjinfo(&sjinfo, rel1->relids, rel2->relids);
	joinrel.relids =
		add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);
	clauses =
		build_joinrel_restrictlist(root, &joinrel, rel1, rel2, &sjinfo);

	/*
	 * Deduplicate clauses that belong to the same EquivalenceClass. When rel1
	 * is composite (e.g., {1,4,6} joined on t1.id=t4.id=t6.id), joining with
	 * rel2 on t1.id=t2.id AND t4.id=t2.id AND t6.id=t2.id produces three
	 * clauses that are functionally redundant. They all share the same
	 * EquivalenceClass.  Keep only one per EC.
	 */
	foreach(lc, clauses)
	{
		RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

		if (rinfo->parent_ec != NULL)
		{
			if (list_member_ptr(seen_ecs, rinfo->parent_ec))
				continue;		/* redundant — same EC already counted */

			seen_ecs = lappend(seen_ecs, rinfo->parent_ec);
		}
		unique_clauses = lappend(unique_clauses, rinfo);
	}

	result = clauselist_selectivity(root, unique_clauses, 0,
									JOIN_INNER, &sjinfo);

	list_free(seen_ecs);
	list_free(unique_clauses);
	if (joinrel.relids != base_relids)
		bms_free(base_relids);
	bms_free(joinrel.relids);
	return result;
}

/**
 * @brief Compute topology volume as product of row counts.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
void
set_vol_topology(PlannerInfo *root, Topology * topology)
{
	Cardinality vol = 1;
	List	   *vertexes = topology->vertexes;
	ListCell   *i = NULL;

	foreach(i, vertexes)
	{
		RelOptInfo *rel = ((Vertex *) lfirst(i))->rel;

		vol *= rel->rows;
	}
	topology->vol = vol;
}

void
set_id(PlannerInfo *root, Topology * topology)
{
	ListCell   *lc = NULL;

	topology->id = root->last_topology_id++;
	foreach(lc, topology->vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		v->topology_id = topology->id;
	}
}

/**
 * @brief Compute topology selectivity from join clauses.
 *
 * Aggregates join clauses fully contained in the topology and applies
 * selectivity estimation.
 *
 * @param root Planner context.
 * @param topology Topology to update.
 */
void
set_sel_topology(PlannerInfo *root, Topology * topology)
{
	Selectivity sel = 1.0;
	List	   *vertexes = topology->vertexes;
	ListCell   *lc;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);
		ListCell   *lc2;

		foreach(lc2, v->adj)
		{
			Vertex	   *nbr = (Vertex *) lfirst(lc2);

			if (v->index < nbr->index &&
				nbr->topology_id == v->topology_id)
			{
				sel *= get_selectivity(root, v->rel, nbr->rel);
			}
		}
	}

	topology->sel = sel;
}

/**
 * @brief Estimate the cheapest join cost between two relations.
 *
 * Considers nestloop, hashjoin, and mergejoin initial costs.
 *
 * @param root Planner context.
 * @param rel1 First relation.
 * @param rel2 Second relation.
 *
 * @return Minimum estimated join cost.
 */
Cost
cost_edge(PlannerInfo *root, RelOptInfo *rel1, RelOptInfo *rel2)
{
	Cost		min_cost = DBL_MAX;
	RelOptInfo *outer_rels[2] = {rel1, rel2};
	RelOptInfo *inner_rels[2] = {rel2, rel1};

	for (int i = 0; i < 2; i++)
	{
		RelOptInfo *outer_rel = outer_rels[i];
		RelOptInfo *inner_rel = inner_rels[i];
		Path	   *outer_path = outer_rel->cheapest_total_path;
		Path	   *inner_path = inner_rel->cheapest_total_path;
		JoinCostWorkspace workspace;
		JoinPathExtraData extra = {0};
		SpecialJoinInfo sjinfo;
		RelOptInfo	joinrel = {0};
		List	   *restrictlist = NIL;
		List	   *hashclauses = NIL;
		List	   *merge_candidates = NIL;
		List	   *mergeclauses = NIL;
		ListCell   *lc = NULL;
		Relids		base_relids = NULL;

		if (PATH_PARAM_BY_REL(outer_path, inner_rel) ||
			PATH_PARAM_BY_REL(inner_path, outer_rel))
		{
			continue;
		}

		base_relids = bms_union(outer_rel->relids, inner_rel->relids);

		init_dummy_sjinfo(&sjinfo, outer_rel->relids, inner_rel->relids);
		joinrel.relids =
			add_outer_joins_to_relids(root, base_relids, &sjinfo, NULL);

		restrictlist = build_joinrel_restrictlist(root, &joinrel, outer_rel,
												  inner_rel, &sjinfo);

		extra.restrictlist = restrictlist;
		extra.mergeclause_list = NIL;
		extra.inner_unique = false;
		extra.sjinfo = &sjinfo;
		extra.param_source_rels = joinrel.relids;

		/* ---- Nestloop ---- */
		initial_cost_nestloop(root, &workspace, JOIN_INNER,
							  outer_path, inner_path, &extra);
		if (workspace.total_cost < min_cost)
			min_cost = workspace.total_cost;

		/* ---- Hashjoin ---- */
		foreach(lc, restrictlist)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (!rinfo->can_join ||
				rinfo->hashjoinoperator == InvalidOid)
				continue;

			if (!clause_sides_match_join(rinfo, outer_rel->relids,
										 inner_rel->relids))
				continue;

			if (!rinfo->outer_is_left &&
				!OidIsValid(
							get_commutator(castNode(OpExpr,
													rinfo->clause)->opno)))
				continue;

			hashclauses = lappend(hashclauses, rinfo);
		}

		if (hashclauses != NIL)
		{
			initial_cost_hashjoin(root, &workspace, JOIN_INNER,
								  hashclauses, outer_path, inner_path,
								  &extra, false);
			if (workspace.total_cost < min_cost)
				min_cost = workspace.total_cost;
		}

		/* ---- Mergejoin ---- */

		/*
		 * Pre-filter: only clauses with mergeopfamilies can participate
		 * in a merge join.  find_mergeclauses_for_outer_pathkeys() calls
		 * update_mergeclause_eclasses() which asserts mergeopfamilies != NIL,
		 * so passing unfiltered restrictlist causes an assertion failure.
		 */
		foreach(lc, restrictlist)
		{
			RestrictInfo *rinfo = (RestrictInfo *) lfirst(lc);

			if (rinfo->mergeopfamilies != NIL)
				merge_candidates = lappend(merge_candidates, rinfo);
		}

		if (merge_candidates != NIL)
		{
			mergeclauses = find_mergeclauses_for_outer_pathkeys(
															   root, outer_path->pathkeys,
															   merge_candidates);
		}

		if (mergeclauses != NIL)
		{
			List	   *outersortkeys = outer_path->pathkeys;
			List	   *innersortkeys =
				make_inner_pathkeys_for_merge(root, mergeclauses,
											  outersortkeys);

			if (outersortkeys &&
				pathkeys_contained_in(outersortkeys, outer_path->pathkeys))
				outersortkeys = NIL;

			if (innersortkeys &&
				pathkeys_contained_in(innersortkeys, inner_path->pathkeys))
				innersortkeys = NIL;

			initial_cost_mergejoin(root, &workspace, JOIN_INNER,
								   mergeclauses, outer_path, inner_path,
								   outersortkeys, innersortkeys, 0,
								   &extra);
			if (workspace.total_cost < min_cost)
				min_cost = workspace.total_cost;
		}

		/* Cleanup */
		list_free(hashclauses);
		list_free(merge_candidates);
		list_free(mergeclauses);

		if (joinrel.relids != base_relids)
			bms_free(base_relids);
		bms_free(joinrel.relids);
	}

	return min_cost;
}

void
print_trace(RelOptInfo *rel)
{
	StringInfoData buf;

	initStringInfo(&buf);
	appendStringInfo(&buf, "\n----------------------PRINT_TRACE\n");
	appendStringInfo(&buf, "%s\n", rel->trace);
	ereport(NOTICE, (errmsg("%s\n", buf.data)));
	pfree(buf.data);
}

/**
 * @brief Free a join graph built by build_join_graph().
 *
 * Frees each Vertex's adjacency list spine, the Vertex struct itself,
 * and the outer list.  Does NOT touch the RelOptInfo* that each Vertex
 * references (those belong to the planner's join_rel_list).
 *
 * @param graph  List of Vertex* to free.  Must have been created by
 *               build_join_graph(); do NOT pass component->vertexes.
 */
void
free_join_graph(List *graph)
{
	ListCell   *lc;

	foreach(lc, graph)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		list_free(v->adj);		/* spine only — neighbors are in the same
								 * list */
		pfree(v);
	}
	list_free(graph);
}


RelOptInfo *
make_rel(PlannerInfo *root, RelOptInfo *left, RelOptInfo *right)
{
	RelOptInfo *joinrel = make_join_rel(root, left, right);

	if (joinrel)
	{
		generate_partitionwise_join_paths(root, joinrel);
		if (!bms_equal(joinrel->relids, root->all_query_rels))
		{
			generate_useful_gather_paths(root, joinrel, false);
		}
		set_cheapest(joinrel);
	}

	return joinrel;

}

/**
 * @brief Check whether a list of vertices forms a true path graph.
 *
 * A path graph on n vertices has exactly n-1 edges (among vertices
 * in the list) and every vertex has internal degree <= 2.
 * Triangles or shortcut edges disqualify it.
 *
 * @param vertexes  List of Vertex* forming the subgraph.
 * @return true if the subgraph is a genuine path (chain).
 */
static bool
is_path_graph(List *vertexes)
{
    int     n = list_length(vertexes);
    int     edge_count = 0;
    bool   *in_sub = NULL;
    int     max_idx = 0;
    ListCell *lc;

    if (n <= 2)
        return true;    /* trivially a path */

    /* Find max index for the membership array */
    foreach(lc, vertexes)
    {
        Vertex *v = (Vertex *) lfirst(lc);
        if ((int) v->index > max_idx)
            max_idx = (int) v->index;
    }

    in_sub = (bool *) palloc0((max_idx + 1) * sizeof(bool));
    foreach(lc, vertexes)
    {
        Vertex *v = (Vertex *) lfirst(lc);
        in_sub[v->index] = true;
    }

    foreach(lc, vertexes)
    {
        Vertex *v = (Vertex *) lfirst(lc);
        int     degree = 0;
        ListCell *lc2;

        foreach(lc2, v->adj)
        {
            Vertex *nbr = (Vertex *) lfirst(lc2);

            if (in_sub[nbr->index])
            {
                degree++;
                if (v->index < nbr->index)
                    edge_count++;
            }
        }

        if (degree > 2)
        {
            pfree(in_sub);
            return false;
        }
    }

    pfree(in_sub);
    return (edge_count == n - 1);
}


/**
 * @brief Find chain components among unused vertices.
 *
 * Each connected component is treated as a chain topology.
 *
 * @param root Planner context.
 * @param vertexes Join graph vertices.
 * @param used_vertexes Used marker array.
 *
 * @return List of CHAIN topologies.
 */
List *
find_chains(PlannerInfo *root, List *vertexes, bool *used_vertexes)
{
	List	   *chains = NIL;	/* List* of Topology*  */
	ListCell   *lc = NULL;

	foreach(lc, vertexes)
	{
		Vertex	   *v = (Vertex *) lfirst(lc);

		if (!used_vertexes[v->index])
		{
			List	   *sub = bfs_component(v, used_vertexes);
			Topology   *topology = (Topology *) palloc0(sizeof(Topology));

			topology->vertexes = sub;
			topology->form = is_path_graph(sub) ? CHAIN : DENSITY_GRAPH;;
			/*set_id(root, topology);
			set_sel_topology(root, topology);
			set_vol_topology(root, topology);
			set_complexity_topology(root, topology);*/
			chains = lappend(chains, topology);
		}
	}
	return chains;
}
