# FormalSQL Licensing

FormalSQL contains code from several independently licensed sources. There is
no repository-wide license grant. The applicable license is determined by the
path allocation below and, where present, by a more specific notice in a file.

## MIT-licensed FormalSQL work

The following paths were introduced by the FormalSQL modernization and are
licensed under the [MIT License](MIT.txt):

- `src/common/comparison/DecidableEquality.v`;
- `src/data/sql/`;
- `src/data/proof_of_concept/SchemaConstraints.v`;
- `src/data/proof_of_concept/ValueCore.v`;
- `src/data/proof_of_concept/ValueDomain.v`;
- `src/data/proof_of_concept/ValueFloat.v`;
- `src/data/proof_of_concept/ValueInteger.v`;
- `src/data/proof_of_concept/ValueNumeric.v`;
- `src/data/proof_of_concept/ValueNumericTypmod.v`;
- `src/data/proof_of_concept/ValuePredicates.v`;
- `src/data/proof_of_concept/ValueString.v`;
- `src/data/proof_of_concept/ValueTemporal.v`;
- `src/data/proof_of_concept/ValueTextInteger.v`;
- repository build and documentation metadata, except where it reproduces an
  upstream notice.

The MIT grant covers only contributions whose copyright is held by the
FormalSQL contributors. It does not relicense code inherited from another
project.

## LGPL-licensed FormalData foundations

The following paths use the shared FormalData collection, logic, tuple, and
bag foundations and are distributed under
[LGPL-3.0-only](LGPL-3.0-only.txt):

- `src/common/`, except `src/common/comparison/DecidableEquality.v`;
- `src/logic/`;
- `src/data/flat/`;
- `src/data/proof_of_concept/GenericInstance.v`;
- `src/data/proof_of_concept/SqlSyntax.v`;
- `src/data/proof_of_concept/TuplesImpl.v`;
- `src/data/proof_of_concept/Values.v`.

FormalSQL modifications to these library modules are distributed under the
same LGPL terms. Their source headers retain the FormalData copyright notice.
Equivalent foundational modules were published by FormalData in projects
including [ProvCert](https://framagit.org/formaldata/provcert) and
[SQLEngines](https://framagit.org/formaldata/sqlengines).

## Attribution

The SQLFormalSemantics development and the shared FormalData foundations are
copyright 2016-2022 FormalData and were authored principally by Veronique
Benzaken and Evelyne Contejean, with other contributors recorded in Git
history. FormalSQL additions are copyright their respective contributors.
Modifications to LGPL modules remain available under `LGPL-3.0-only`.

This allocation records repository provenance; it is not legal advice. If a
file is moved or substantially rewritten, update this allocation in the same
change.
