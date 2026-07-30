# SQLFormalSemantics

A Coq mechanized executable formal semantics for realistic SQL queries

This repository is forked from
[formaldata/sqlformalsemantics](https://framagit.org/formaldata/sqlformalsemantics).
The `master` branch of this fork tracks the Rocq modernization work while
retaining the original tuple, value, and bag foundations under the unified
exact query semantics described below.


## Compilation
The `master` branch is currently tested with Rocq 9.2:
```
opam exec --switch=/path/to/rocq-switch -- make JOBS=1
```

The top-level makefile regenerates `src/Makefile.rocq` from `_CoqProject` when
needed; no generated Rocq makefile is version-controlled.

## Exact declarative PostgreSQL query extensions

The Logos fork contains one exact ordered row-list query syntax and outcome
semantics. Bag operators and possible bags are proof abstractions over that
syntax rather than a second embedded query language or evaluator. Query
meaning is independent of planner and executor choices.
Logical filtering, joins, grouping, grouping sets,
order-preserving deterministic row mapping, duplicate elimination, ordering,
offset, and fetch are compositional at every nesting depth. Rank and cumulative
window semantics range over every ordering permitted by the SQL partition and
order keys. Runtime errors are SQL
expression-level outcomes of that logical structure, never observations of a
particular execution plan.

PostgreSQL fixed-scale NUMERIC AVG is represented by one aggregate-owned
`numeric_avg_scale_state`, not by composing SUM, a checked COUNT, and scalar
division. `avg_numeric_scale_2` serves every schema-authoritative
`DECIMAL(p,2)` input: declared precision is enforced by schema conformance and
does not alter the transition. It retains exact nonnegative counters and an
exact fixed-scale coefficient sum, with numeric range/division errors delayed
until aggregate finalization.

`src/data/proof_of_concept/SchemaConstraints.v` defines the concrete
PostgreSQL integrity contract for stored database states. It covers typing,
`NOT NULL`, primary and unique keys, `MATCH SIMPLE` foreign keys, three-valued
`CHECK` constraints, and the supported partial or expression unique indexes.
Frontends may transport and instantiate these declarations, but their meaning
and the database-conformance relation are owned by FormalSQL.

`src/data/sql/SqlQueryWellFormed.v` states the conservative schema, ordering,
join-projection, and positional-IN obligations directly on the exact query
syntax. `src/data/sql/SqlQueryFacts.v` proves reusable ordered/list and
possible-bag bridges. No frontend correctness is inferred from these
theorems: emitters must separately justify PostgreSQL typing and declarative
SQL translation.


## License

This code is released under the terms of the [Creative Common
Attribution-NonCommercial-NoDerivatives 4.0 International
license](https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode);
see LICENSE for details.


## Companion paper
[A Coq mechanised formal semantics for realistic SQL queries: formally reconciling SQL and bag relational algebra](https://hal.archives-ouvertes.fr/hal-01955433), Benzaken, Véronique; Contejean, Évelyne, [CPP - 8th ACM SIGPLAN International Conference on Certified Programs and Proofs](https://popl19.sigplan.org/track/cpp-2019) - 2019
