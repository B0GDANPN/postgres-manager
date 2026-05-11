# Makefile for gt_inject extension
#
# Build:
#   make PG_CONFIG=/path/to/pg_config
# Install:
#   make install PG_CONFIG=/path/to/pg_config

MODULE_big = gt_inject
OBJS = gt_inject.o

EXTENSION = gt_inject
DATA = gt_inject--1.0.sql
PGFILEDESC = "gt_inject - inject ground-truth cardinalities into PG planner"

# Use pg_config from environment (or default)
PG_CONFIG ?= pg_config

PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
