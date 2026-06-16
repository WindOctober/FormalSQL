# SQLFormalSemantics

A Coq mechanized executable formal semantics for realistic SQL queries

This repository is forked from
[formaldata/sqlformalsemantics](https://framagit.org/formaldata/sqlformalsemantics).
The `master` branch of this fork tracks the Rocq modernization work while
preserving the original formal semantics.


## Compilation
The upstream version compiles with Coq 8.11.2:
```
make
make install
```

The `master` branch is currently tested with Rocq 9.2:
```
cd src
opam exec --switch=../.opam-rocq -- make -f Makefile.rocq -j1
```


## License

This code is released under the terms of the [Creative Common
Attribution-NonCommercial-NoDerivatives 4.0 International
license](https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode);
see LICENSE for details.


## Companion paper
[A Coq mechanised formal semantics for realistic SQL queries: formally reconciling SQL and bag relational algebra](https://hal.archives-ouvertes.fr/hal-01955433), Benzaken, Véronique; Contejean, Évelyne, [CPP - 8th ACM SIGPLAN International Conference on Certified Programs and Proofs](https://popl19.sigplan.org/track/cpp-2019) - 2019
