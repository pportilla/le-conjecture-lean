# Third-party Lean sources

Original Lean code is licensed under the [MIT License](LICENSE). Third-party
code retains its applicable license and attribution. The [third-party
notices](THIRD_PARTY_NOTICES.md) identify all recorded exceptions, including
adaptations outside the vendored directories.

The files under `OnLeConjecture/External` are vendored source dependencies.
They are compiled as part of this project. Their upstream copyright notices,
license files, and provenance records are retained.

| Directory | Upstream | License and provenance |
| --- | --- | --- |
| `OnLeConjecture/External/TauCeti` | [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | [License](OnLeConjecture/External/TauCeti/LICENSE), `*-provenance.json` in that directory |
| `OnLeConjecture/External/LocalComplexGeometry` | [BochaoKong/nullstellensatz](https://github.com/BochaoKong/nullstellensatz) | [License](OnLeConjecture/External/LocalComplexGeometry/LICENSE), [Nullstellensatz provenance](OnLeConjecture/External/LocalComplexGeometry/nullstellensatz-port-provenance.json), [Rückert dependency provenance](OnLeConjecture/External/LocalComplexGeometry/ruckert-port-provenance.json) |
| `OnLeConjecture/External/ClassicalComplexWPT` | [BochaoKong/classical-complex-wpt](https://github.com/BochaoKong/classical-complex-wpt) | [License](OnLeConjecture/External/ClassicalComplexWPT/LICENSE), file headers and the [shared Rückert dependency provenance](OnLeConjecture/External/LocalComplexGeometry/ruckert-port-provenance.json) |
| `OnLeConjecture/External/OpenAIMath` | [openai/math](https://github.com/openai/math) | [License](OnLeConjecture/External/OpenAIMath/LICENSE), `*-provenance.json` in that directory |

All four included license texts are Apache License 2.0. The provenance records
identify upstream commits, files, and local adaptations. Consult each record
for its retrieval date and scope rather than assuming a whole upstream library
is included or that all files came from one commit.

The original patch records are included under
[`External/LocalComplexGeometry/patches`](OnLeConjecture/External/LocalComplexGeometry/patches):

- [Rückert compatibility changes](OnLeConjecture/External/LocalComplexGeometry/patches/ruckert-compatibility.patch).
- [Full Rückert port](OnLeConjecture/External/LocalComplexGeometry/patches/ruckert-full-port.patch).
- [Full Nullstellensatz port](OnLeConjecture/External/LocalComplexGeometry/patches/nullstellensatz-full-port.patch).

Twelve files under `OnLeConjecture/KnotFloer` contain adaptations from Tau Ceti.
`OnLeConjecture/Analytic/FiniteDimensionalFactorization.lean` contains adaptations
from [lean-SCV](https://github.com/bjbraams/lean-SCV). These files retain the
[Apache License 2.0](LICENSES/Apache-2.0.txt), as recorded in their headers and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The notices give the file list,
upstream references, and attribution.

Mathlib and its transitive Lake dependencies are fetched separately. Their
exact revisions are recorded in [lake-manifest.json](lake-manifest.json), and
their own licenses apply. The `.lake` directory is not distributed in this
repository.
