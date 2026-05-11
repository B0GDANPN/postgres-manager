-- gt_inject extension SQL.
-- The extension hooks into the planner via shared library; no SQL-level
-- objects are required. This file exists for CREATE EXTENSION compatibility.
\echo Use "CREATE EXTENSION gt_inject" to load this file. \quit

-- Nothing here — all functionality is C-level via _PG_init() hook.
