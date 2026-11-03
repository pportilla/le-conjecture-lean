# Third-party notices

The files of this repository are under the MIT license (see [`LICENSE`](LICENSE)), with the
following exceptions, which are under the Apache License, Version 2.0. Each exception keeps its
original license and attribution.

## Vendored libraries

The directory [`OnLeConjecture/External`](OnLeConjecture/External) contains parts of four
libraries. Each subdirectory contains the library's Apache 2.0 `LICENSE` file. The provenance
records (`*-provenance.json`) give, for each vendored file, the upstream repository, commit,
path and SHA-256, and list the changes made in this repository.

| Directory | Upstream | Commit | Copyright | License |
| --- | --- | --- | --- | --- |
| `External/TauCeti` | <https://github.com/TauCetiProject/TauCeti> | `eb4dd2412a1cd62f73128361bfd3cb422df32e37` | The Tau Ceti contributors | Apache-2.0 |
| `External/LocalComplexGeometry` | <https://github.com/BochaoKong/nullstellensatz> | `029697242294aea7989bf5d391199696a43490df` | the authors of the upstream repository | Apache-2.0 |
| `External/ClassicalComplexWPT` | <https://github.com/BochaoKong/classical-complex-wpt> | `b4a7273fe5c9752753c52e10494097569089642d` | the authors of the upstream repository | Apache-2.0 |
| `External/OpenAIMath` | <https://github.com/openai/math> | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` | the authors of the upstream repository | Apache-2.0 |

Changes made in this repository to the vendored files are stated in the file headers and in
the provenance records. They consist mainly of module and import-path adaptations to this
project and Lean version, and a small number of proof compatibility edits. The edits are
recorded in:

* `External/LocalComplexGeometry/patches/ruckert-compatibility.patch`,
  `ruckert-full-port.patch` and `nullstellensatz-full-port.patch`;
* `External/OpenAIMath/mayer-vietoris-compatibility.patch`.

Some provenance records refer to `source_snapshot` copies of the upstream files under
`verification/2026-10-29/upstream/`. These local copies are not part of this repository; the
upstream files are identified by the repository, commit, path and SHA-256 given in the same
records. Some vendored files have no individual copyright header; they are covered by the
`LICENSE` file of their directory.

## Files adapted from Tau Ceti

The following files outside `External` contain code adapted from Tau Ceti together with new
code by Pablo Portilla Cuadrado. They are under the Apache License 2.0 (see
[`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt)), and their headers name both copyright
holders.

* `OnLeConjecture/KnotFloer/GridFullCommutationCyclic.lean`
* `OnLeConjecture/KnotFloer/GridFullCommutationHexagon.lean`
* `OnLeConjecture/KnotFloer/GridFullCommutationPentagon.lean`
* `OnLeConjecture/KnotFloer/GridFullDifferentialBasic.lean`
* `OnLeConjecture/KnotFloer/GridFullDifferentialOffDiagonal.lean`
* `OnLeConjecture/KnotFloer/GridFullMaslovComplex.lean`
* `OnLeConjecture/KnotFloer/GridFullReflectedCycles.lean`
* `OnLeConjecture/KnotFloer/GridFullReflection.lean`
* `OnLeConjecture/KnotFloer/GridFullTwoByTwo.lean`
* `OnLeConjecture/KnotFloer/GridStabilizationSourceRectangle.lean`
* `OnLeConjecture/KnotFloer/GridWeightedCurvature.lean`
* `OnLeConjecture/KnotFloer/MatchingContraction.lean` (adapted from
  `TauCeti/Algebra/Homology/SquareZero/Contraction.lean`; see
  `External/TauCeti/matching-contraction-adaptation-provenance.json`)

## File adapted from lean-SCV

The file `OnLeConjecture/Analytic/FiniteDimensionalFactorization.lean` contains code adapted
from lean-SCV, <https://github.com/bjbraams/lean-SCV>, commit
`336759b3964011aa0d6e1111e32276b1476fb7f0`, files
`SeveralComplexVariables/AnalyticGerm/Polynomial.lean` and
`SeveralComplexVariables/Polynomial/OfFn.lean`, Copyright (c) 2026 Bastiaan J Braams, together
with new code by Pablo Portilla Cuadrado. The polynomial reconstruction and
distinguished-divisor arguments were adapted to the germ rings of this project. The file is
under the Apache License 2.0 (see [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt)), and
its header names both copyright holders.

## Dependencies

[Mathlib](https://github.com/leanprover-community/mathlib4) and the Lean toolchain are
dependencies, fetched by Lake and not included in this repository. Both are under the Apache
License 2.0.
