/*-------------------------------------------------------------------------
 *
 * gt_inject.c
 *      Inject ground-truth cardinalities into PostgreSQL planner via
 *      set_joinrel_size_estimates_hook.
 *
 * Reads cardinalities from public.ground_truth at first use for a given
 * query_id and caches them keyed by sorted comma-separated alias list
 * (matching subplan_key produced by joboracle.py).
 *
 * Usage:
 *   LOAD 'gt_inject';
 *   SET gt_inject.query_id = '1a';
 *   EXPLAIN SELECT ...;          -- planner uses ground-truth on joinrels
 *   SET gt_inject.query_id = ''; -- disable
 *
 * Behaviour:
 *   - If gt_inject.query_id is empty/NULL → no override, planner default.
 *   - If the joinrel's subplan_key is not in ground_truth → no override.
 *   - If found → rel->rows is replaced with the true value.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "fmgr.h"
#include "miscadmin.h"
#include "access/xact.h"
#include "executor/spi.h"
#include "lib/stringinfo.h"
#include "nodes/bitmapset.h"
#include "nodes/parsenodes.h"
#include "nodes/pathnodes.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/hsearch.h"
#include "utils/memutils.h"
#include "utils/snapmgr.h"

PG_MODULE_MAGIC;

void _PG_init(void);
void _PG_fini(void);

/* ------------------------------------------------------------------------
 * GUC variables
 * ------------------------------------------------------------------------
 */
static char *gt_query_id = NULL;
static bool  gt_enable_debug = false;
static bool  gt_enabled = true;

/* ------------------------------------------------------------------------
 * Cache state
 * ------------------------------------------------------------------------
 */

#define GT_KEY_MAXLEN  4096

typedef struct GTCacheKey
{
    char    key[GT_KEY_MAXLEN];   /* sorted comma-separated aliases */
} GTCacheKey;

typedef struct GTCacheEntry
{
    GTCacheKey  key;              /* must be first for HASH_BLOBS */
    double      true_rows;
} GTCacheEntry;

static HTAB        *gt_cache = NULL;
static MemoryContext gt_cache_ctx = NULL;
static char        *gt_cached_query_id = NULL;

/* ------------------------------------------------------------------------
 * Saved previous hook value
 * ------------------------------------------------------------------------
 */
static set_joinrel_size_estimates_hook_type prev_joinrel_hook = NULL;

static void gt_invalidate_cache(void);
static void gt_load_cache_for_query(const char *query_id);
static char *build_subplan_key(PlannerInfo *root, Relids relids);
static void gt_set_joinrel_size_estimates_hook(PlannerInfo *root,
                                                RelOptInfo *rel,
                                                RelOptInfo *outer_rel,
                                                RelOptInfo *inner_rel,
                                                SpecialJoinInfo *sjinfo,
                                                List *restrictlist);
static void gt_query_id_assign_hook(const char *newval, void *extra);


/* ------------------------------------------------------------------------
 * Cache management
 * ------------------------------------------------------------------------
 */

static void
gt_invalidate_cache(void)
{
    if (gt_cache != NULL)
    {
        hash_destroy(gt_cache);
        gt_cache = NULL;
    }
    if (gt_cache_ctx != NULL)
    {
        MemoryContextDelete(gt_cache_ctx);
        gt_cache_ctx = NULL;
    }
    if (gt_cached_query_id != NULL)
    {
        pfree(gt_cached_query_id);
        gt_cached_query_id = NULL;
    }
}

static void
gt_query_id_assign_hook(const char *newval, void *extra)
{
    /*
     * GUC change → drop cache. Fresh load happens lazily on next lookup.
     */
    gt_invalidate_cache();
}

static void
gt_load_cache_for_query(const char *query_id)
{
    int          ret;
    Oid          argtypes[1] = {TEXTOID};
    Datum        values[1];
    MemoryContext old_ctx;
    uint64       i;

    if (!IsTransactionState())
    {
        elog(WARNING, "gt_inject: not in transaction state, cannot load cache");
        return;
    }

    /* Dedicated long-lived context so cache survives across statements */
    gt_cache_ctx = AllocSetContextCreate(TopMemoryContext,
                                          "gt_inject cache",
                                          ALLOCSET_DEFAULT_SIZES);

    old_ctx = MemoryContextSwitchTo(gt_cache_ctx);

    {
        HASHCTL ctl;
        memset(&ctl, 0, sizeof(ctl));
        ctl.keysize = sizeof(GTCacheKey);
        ctl.entrysize = sizeof(GTCacheEntry);
        ctl.hcxt = gt_cache_ctx;
        gt_cache = hash_create("gt_inject cache",
                                4096,
                                &ctl,
                                HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);
    }

    gt_cached_query_id = pstrdup(query_id);

    MemoryContextSwitchTo(old_ctx);

    if (SPI_connect() != SPI_OK_CONNECT)
    {
        elog(WARNING, "gt_inject: SPI_connect failed");
        return;
    }

    values[0] = CStringGetTextDatum(query_id);
    ret = SPI_execute_with_args(
        "SELECT subplan_key, true_rows FROM public.ground_truth "
        "WHERE query_id = $1",
        1, argtypes, values, NULL,
        true,   /* read_only */
        0       /* no row limit */
    );

    if (ret != SPI_OK_SELECT)
    {
        elog(WARNING, "gt_inject: SPI_execute returned %d", ret);
        SPI_finish();
        return;
    }

    for (i = 0; i < SPI_processed; i++)
    {
        HeapTuple  tup = SPI_tuptable->vals[i];
        TupleDesc  tdesc = SPI_tuptable->tupdesc;
        bool       isnull;
        Datum      key_datum, rows_datum;
        char      *key_str;
        int64      true_rows;
        GTCacheKey  cache_key;
        GTCacheEntry *entry;
        bool        found;

        key_datum = SPI_getbinval(tup, tdesc, 1, &isnull);
        if (isnull) continue;
        rows_datum = SPI_getbinval(tup, tdesc, 2, &isnull);
        if (isnull) continue;

        key_str = TextDatumGetCString(key_datum);
        true_rows = DatumGetInt64(rows_datum);

        memset(&cache_key, 0, sizeof(cache_key));
        strncpy(cache_key.key, key_str, GT_KEY_MAXLEN - 1);

        old_ctx = MemoryContextSwitchTo(gt_cache_ctx);
        entry = (GTCacheEntry *) hash_search(gt_cache, &cache_key,
                                              HASH_ENTER, &found);
        entry->true_rows = (double) true_rows;
        MemoryContextSwitchTo(old_ctx);

        pfree(key_str);
    }

    if (gt_enable_debug)
        elog(NOTICE, "gt_inject: loaded %lu entries for query_id='%s'",
             (unsigned long) SPI_processed, query_id);

    SPI_finish();
}


/* ------------------------------------------------------------------------
 * Subplan key generation — must match joboracle.py format:
 *   sorted aliases joined with comma
 * ------------------------------------------------------------------------
 */

static int
str_compare(const void *a, const void *b)
{
    const char *sa = *(const char *const *) a;
    const char *sb = *(const char *const *) b;
    return strcmp(sa, sb);
}

static char *
build_subplan_key(PlannerInfo *root, Relids relids)
{
    int         x = -1;
    int         count = 0;
    int         capacity = 16;
    char      **names = (char **) palloc(capacity * sizeof(char *));
    StringInfoData buf;
    int         i;

    while ((x = bms_next_member(relids, x)) >= 0)
    {
        RangeTblEntry *rte;

        if (x <= 0 || x >= root->simple_rel_array_size)
            continue;

        rte = root->simple_rte_array[x];
        if (rte == NULL || rte->rtekind != RTE_RELATION)
            continue;
        if (rte->eref == NULL || rte->eref->aliasname == NULL)
            continue;

        if (count == capacity)
        {
            capacity *= 2;
            names = (char **) repalloc(names, capacity * sizeof(char *));
        }
        names[count++] = rte->eref->aliasname;
    }

    if (count == 0)
    {
        pfree(names);
        return NULL;
    }

    qsort(names, count, sizeof(char *), str_compare);

    initStringInfo(&buf);
    for (i = 0; i < count; i++)
    {
        if (i > 0)
            appendStringInfoChar(&buf, ',');
        appendStringInfoString(&buf, names[i]);
    }

    pfree(names);
    return buf.data;
}


/* ------------------------------------------------------------------------
 * The hook itself
 * ------------------------------------------------------------------------
 */

static void
gt_set_joinrel_size_estimates_hook(PlannerInfo *root,
                                    RelOptInfo *rel,
                                    RelOptInfo *outer_rel,
                                    RelOptInfo *inner_rel,
                                    SpecialJoinInfo *sjinfo,
                                    List *restrictlist)
{
    char           *subplan_key;
    GTCacheKey      lookup_key;
    GTCacheEntry   *entry;
    bool            found;

    /* Chain — call previous hook first */
    if (prev_joinrel_hook)
        prev_joinrel_hook(root, rel, outer_rel, inner_rel, sjinfo, restrictlist);

    if (!gt_enabled)
        return;
    if (gt_query_id == NULL || gt_query_id[0] == '\0')
        return;

    /* Lazy load on first lookup */
    if (gt_cache == NULL ||
        gt_cached_query_id == NULL ||
        strcmp(gt_cached_query_id, gt_query_id) != 0)
    {
        gt_invalidate_cache();
        gt_load_cache_for_query(gt_query_id);
        if (gt_cache == NULL)
            return;
    }

    subplan_key = build_subplan_key(root, rel->relids);
    if (subplan_key == NULL)
        return;

    if (strlen(subplan_key) >= GT_KEY_MAXLEN)
    {
        elog(WARNING, "gt_inject: subplan_key exceeds %d chars: %s",
             GT_KEY_MAXLEN, subplan_key);
        pfree(subplan_key);
        return;
    }

    memset(&lookup_key, 0, sizeof(lookup_key));
    strncpy(lookup_key.key, subplan_key, GT_KEY_MAXLEN - 1);

    entry = (GTCacheEntry *) hash_search(gt_cache, &lookup_key,
                                          HASH_FIND, &found);
    if (found)
    {
        if (gt_enable_debug)
            elog(NOTICE, "gt_inject: %s: %.0f -> %.0f",
                 subplan_key, rel->rows, entry->true_rows);
        rel->rows = clamp_row_est(entry->true_rows);
    }
    else if (gt_enable_debug)
    {
        elog(DEBUG1, "gt_inject: no entry for %s", subplan_key);
    }

    pfree(subplan_key);
}


/* ------------------------------------------------------------------------
 * Module init / fini
 * ------------------------------------------------------------------------
 */

void
_PG_init(void)
{
    DefineCustomStringVariable(
        "gt_inject.query_id",
        "Identifier of the query in public.ground_truth to inject from.",
        "Empty string disables the override.",
        &gt_query_id,
        "",
        PGC_USERSET,
        0,
        NULL,
        gt_query_id_assign_hook,
        NULL
    );

    DefineCustomBoolVariable(
        "gt_inject.enabled",
        "Globally enable/disable cardinality injection.",
        NULL,
        &gt_enabled,
        true,
        PGC_USERSET,
        0,
        NULL, NULL, NULL
    );

    DefineCustomBoolVariable(
        "gt_inject.debug",
        "Print NOTICE for every overridden estimate.",
        NULL,
        &gt_enable_debug,
        false,
        PGC_USERSET,
        0,
        NULL, NULL, NULL
    );

    MarkGUCPrefixReserved("gt_inject");

    prev_joinrel_hook = set_joinrel_size_estimates_hook;
    set_joinrel_size_estimates_hook = gt_set_joinrel_size_estimates_hook;

    elog(LOG, "gt_inject: initialized");
}

void
_PG_fini(void)
{
    set_joinrel_size_estimates_hook = prev_joinrel_hook;
    gt_invalidate_cache();
}
