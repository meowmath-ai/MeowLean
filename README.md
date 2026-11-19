# Lean formalizations for the Justin Sun Prize

| Problem | Main theorem | Mathematical evidence |
|---|---|---|
| JSP-000492 / Erdős 605 | `JSP000492.erdos_605` | [Spherical repeated distances](solutions/JSP-000492.md) |
| JSP-001010 / Erdős 1205 | `Erdos1205.erdos1205` | [Residue-class coverage](solutions/JSP-001010.md) |
| JSP-000377 / Erdős 465 | `JSP000377.erdos_465` | [Planar distances away from integers](solutions/JSP-000377.md) |
| JSP-000733 / Erdős 882 | `JSP000733.erdos_882` | [Primitive subset sums](solutions/JSP-000733.md) |

The project uses Lean 4.36.0 and Mathlib 4.36.0. The toolchain is specified in `lean-toolchain`. Mathlib and its transitive dependencies are pinned in `lake-manifest.json`.

With Git and Elan installed, run the following from a fresh checkout at the proof commit.

~~~sh
lake env lean --version
lake exe cache get Mathlib
lake env lean JustinPrize/JSP000492.lean
lake env lean JustinPrize/Erdos1205.lean
lake env lean JustinPrize/JSP000377.lean
lake env lean JustinPrize/JSP000733.lean
~~~

The cache command retrieves precompiled Mathlib artifacts. Run the proof commands one at a time, waiting for a successful exit before starting the next. Each command elaborates and kernel-checks its source file and prints its axiom audits. The expected axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

## Supplementary formalization

[JSP-000060 / Erdős 27](solutions/JSP-000060.md) formalizes the fixed-ratio uniform density theorem of Filaseta, Ford, Konyagin, Pomerance, and Yu. The main theorem is `JSP000060.erdos27_fixed_ratio_uniform`.

## Attribution

[@meowmath-ai](https://github.com/meowmath-ai) led the Lean contributions developed in this repository. AI tools assisted with proof drafting, revision, and build diagnostics.
