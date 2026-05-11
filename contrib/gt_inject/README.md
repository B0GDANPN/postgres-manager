# gt_inject — Ground-truth cardinality injection for PostgreSQL

Extension that overrides the PostgreSQL planner's joinrel cardinality
estimates with values from the `public.ground_truth` table. Designed
for "oracle planner" experiments: PG sees true cardinalities on every
joined subset and selects plans accordingly.

## Prerequisites

PostgreSQL **must** be patched to expose the cardinality hooks
(`set_baserel_size_estimates_hook`, `set_joinrel_size_estimates_hook`).
The patch was applied to your PG 18.2 build during the previous step.

Verify:

```bash
nm /path/to/postgres | grep set_joinrel_size_estimates_hook
# Expected: B set_joinrel_size_estimates_hook
```

## Schema requirement

The extension reads from `public.ground_truth` with this layout
(matches `joboracle.py`):

```sql
CREATE TABLE ground_truth (
    query_id     text NOT NULL,
    subplan_key  text NOT NULL,    -- sorted aliases joined with comma
    aliases      text[] NOT NULL,
    true_rows    bigint NOT NULL,
    computed_at  timestamptz DEFAULT now(),
    PRIMARY KEY (query_id, subplan_key)
);
```

`subplan_key` must be the comma-separated, alphabetically sorted alias
list produced by `joboracle.py`.

## Build

```bash
PG_CONFIG=/home/b-pyanzin/Manager/postgres-manager/build/bin/pg_config

make PG_CONFIG=$PG_CONFIG
make install PG_CONFIG=$PG_CONFIG
```

This installs:

- `<pglib>/gt_inject.so`
- `<pgshare>/extension/gt_inject.control`
- `<pgshare>/extension/gt_inject--1.0.sql`

## Configuration (postgresql.conf)

Two ways to load:

### Per-session (recommended for testing)

```sql
LOAD 'gt_inject';
```

### Global

```conf
shared_preload_libraries = 'gt_inject'
```

Requires PG restart. Once loaded, hook is registered for every backend.

## Usage

```sql
LOAD 'gt_inject';                       -- or via shared_preload_libraries
SET gt_inject.query_id = '1a';          -- set active query
EXPLAIN SELECT MIN(...) FROM ...;       -- planner uses true cardinalities
SET gt_inject.query_id = '';            -- restore default behaviour
```

Diagnostic GUCs:

```sql
SET gt_inject.debug = on;     -- prints NOTICE for each override
SET gt_inject.enabled = off;  -- emergency global off-switch
SET client_min_messages = NOTICE;
```

Example debug output:

```
NOTICE:  gt_inject: loaded 47 entries for query_id='1a'
NOTICE:  gt_inject: ct,mc: 4523930 -> 28657
NOTICE:  gt_inject: ct,mc,t: 4523930 -> 28657
...
```

## Scope

- **Joinrels only** (≥2 tables). Baserel hook is exposed by the patch
  but not yet used by this extension. Per-table cardinalities remain
  PostgreSQL's default selectivity-based estimates. To enable for
  baserels, add a separate hook handler keyed on single-alias
  subplan_key.
- **No transitive enrichment.** If `ground_truth` lacks a particular
  subset, the planner uses its own estimate for that subset.
- **Cache lifetime.** Loaded on first lookup per `query_id`. Cleared
  on `SET gt_inject.query_id = ...`. Lives in `TopMemoryContext`,
  i.e. per-backend.

## Caveats

- Cache uses fixed-size 1024-byte keys. Subplan with very many
  long-named aliases could overflow. For JOB / JOB-Complex (aliases
  ≤4 chars, ≤17 tables) this is well within bounds.
- `ground_truth.true_rows` is `bigint`. PG stores `rel->rows` as
  `double`. Conversion is exact for values up to 2^53; JOB/JOB-Complex
  cardinalities fit easily.
