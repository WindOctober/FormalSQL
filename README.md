# FormalSQL

FormalSQL is a Rocq library for executable, compositional semantics of a
realistic SQL fragment. Queries denote possible ordered row-list outcomes,
including modeled SQL runtime errors; bag reasoning is exposed as a proved
local abstraction of that exact semantics.

FormalSQL's design is informed by
[SQLFormalSemantics](https://framagit.org/formaldata/sqlformalsemantics) and
uses foundational collection, logic, tuple, and bag libraries published by
the [FormalData](https://framagit.org/formaldata) project. On top of those
foundations, FormalSQL provides a new ordered, PostgreSQL-oriented query and
value semantics used by [Logos](https://github.com/WindOctober/Logos).

## Status

The `master` branch is tested with Rocq 9.2. FormalSQL is a research library,
not a complete formalization of ISO SQL or every PostgreSQL feature. Its public
semantics is planner-independent: physical join strategies, aggregate spill,
worker scheduling, and storage order do not define query meaning.

## Semantic Scope

FormalSQL provides:

- typed scalar and aggregate syntax with SQL NULL and three-valued Boolean
  results;
- one compositional query syntax for filtering, projection, joins, grouping,
  grouping sets, duplicate elimination, ordering, offset, fetch, rank, and
  supported cumulative windows;
- possible ordered outcomes at every nesting depth, including legal Boolean
  operand schedules and tie-dependent orderings;
- outer `SqlError` outcomes for modeled language-level failures;
- a possible-bag abstraction with proved `BagClosed` recovery conditions;
- concrete PostgreSQL-oriented value domains for integers, numeric/decimal,
  floating point, strings, dates, times, timestamps, and timestamps with time
  zone;
- database conformance for types, `NOT NULL`, primary and unique keys,
  `MATCH SIMPLE` foreign keys, three-valued `CHECK` constraints, and supported
  partial or expression unique indexes.

The ordered evaluator and the bag abstraction are not competing SQL
semantics. Order-sensitive operators always consume exact lists. Bag theory is
available only where a proved abstraction boundary permits forgetting order.

## Requirements

The opam package declares the supported dependency range:

- `rocq-core` 9.2;
- `rocq-stdlib` 9.1;
- Flocq 4.2.2 or later;
- Zarith 1.14 or later.

Install dependencies into an existing opam switch:

```bash
opam install . --deps-only
```

## Build

Build all modules with the active switch:

```bash
opam exec -- make JOBS=1
```

Or select a switch explicitly:

```bash
opam exec --switch=/path/to/rocq-switch -- make JOBS=1
```

The top-level Makefile regenerates `src/Makefile.rocq` from
`src/_CoqProject` when needed. The generated makefile is intentionally not
version-controlled.

Additional targets are:

```bash
# Install the SQLFS library into the active switch
opam exec -- make install JOBS=1

# Remove generated Rocq objects
opam exec -- make clean
```

FormalSQL uses the logical Rocq namespace `SQLFS`. After installation, a
client can import the query layer with:

```coq
From SQLFS Require Import
  SqlOutcome
  SqlQuerySyntax
  SqlQuerySemantics
  SqlQueryWellFormed
  SqlBagAbstraction
  SqlQueryFacts.
```

## Architecture

```text
common/                    finite collections, bags, sets, lists, order
logic/                     Bool3 and formula foundations
data/flat/                 tuples, environments, scalar and aggregate terms
data/sql/                  exact query syntax, outcomes, semantics, facts
data/proof_of_concept/     concrete PostgreSQL-oriented instance
```

The primary SQL modules are:

| Module | Responsibility |
| --- | --- |
| `SqlOutcome.v` | Successful values and modeled SQL error outcomes |
| `SqlErrorSemantics.v` | Runtime-error interpretation for expressions |
| `SqlOrder.v` | Sort keys and exact ordered-row comparison |
| `SqlQuerySyntax.v` | Typed scalar/query syntax and query operators |
| `SqlQuerySemantics.v` | Scheduled exact ordered-outcome relation |
| `SqlQueryWellFormed.v` | Conservative structural and typing obligations |
| `SqlBagAbstraction.v` | `alpha`, possible bags, and `BagClosed` |
| `SqlQueryFacts.v` | Ordered/list facts and bag-reuse bridges |
| `SqlQueryContexts.v` | Typed context substitution and congruence |
| `SqlQueryRenameTransport.v` | Renaming transport across query contexts |
| `SchemaConstraints.v` | Concrete integrity constraints and conformance |
| `Values.v` | Concrete scalar and aggregate interpretation |

`SqlQuerySemantics.v` exposes the exact relation for a fixed Boolean schedule.
Public SQL equivalence quantifies over every legal schedule. This permits
declarative PostgreSQL-style Boolean reordering without weakening row order or
turning physical execution plans into logical semantics.

## PostgreSQL-Oriented Details

The concrete instance models the supported PostgreSQL behavior rather than
leaving scalar and aggregate functions uninterpreted. Important examples
include:

- checked int32/int64 arithmetic without wraparound;
- finite and special numeric values, typmods, rounding, division, and selected
  aggregate finalization rules;
- distinct binary32 and binary64 floating-point carriers;
- string typmods and selected deterministic-collation operations;
- finite temporal ranges and supported temporal infinities;
- NULL-sensitive predicates and aggregate behavior.

Unsupported behavior is not assigned an approximate successful meaning by the
library. A frontend must establish that emitted terms belong to the modeled
fragment and satisfy `SqlQueryWellFormed` obligations.

## License

FormalSQL is a mixed-license repository. FormalData foundational modules are
distributed under `LGPL-3.0-only`; FormalSQL-authored query, value, and
supporting modules are distributed under MIT. FormalSQL modifications to
FormalData-derived library modules remain under `LGPL-3.0-only`.

The authoritative path-level allocation and complete license texts are in
[`LICENSES/README.md`](LICENSES/README.md). No repository-wide license should
be inferred from the license of an individual directory or file.

## Citation

If you use FormalSQL, cite the Logos paper:

```bibtex
@misc{ke2026logos,
  title = {Logos: Certified Order-Sensitive SQL Rewrites with Mechanized
           Semantics and LLM Guidance},
  author = {Jingyu Ke and Jingyang Li and Guoqiang Li},
  year = {2026},
  eprint = {2608.15709},
  archivePrefix = {arXiv},
  primaryClass = {cs.DB},
  url = {https://arxiv.org/abs/2608.15709}
}
```
