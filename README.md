# Lê’s conjecture in Lean 4

This repository contains a Lean 4 formalization of the following statement of **Lê’s conjecture**:

> Every germ of a holomorphic map `(ℂ², 0) → (ℂ³, 0)` with a representative that is injective on a neighbourhood of the origin has a nonzero differential at the origin.

The final theorem is [`OnLeConjecture.Analytic.leConjecture_native`](OnLeConjecture/Analytic/LeConjectureNative.lean). Its recorded axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The repository includes the Lean source, pinned dependencies, written mathematical notes, and verification records.

The companion manuscript, [*Injective analytic mappings of low order*](https://github.com/pportilla/le-conjecture-cases-2-3-4), contains the written case analysis for orders 2, 3, and 4, with its LaTeX source and PDF. Those cases are formalized here in [`Case234.lean`](OnLeConjecture/Case234.lean) and the `DTwo`, `DThree`, and `DFour` directories. The Lean development also supplies the reduction arguments needed to reach those cases.

## The formal statement

In the namespace `OnLeConjecture.Analytic`, the proposition is defined by

```lean
def LeConjecture : Prop :=
  ∀ g : PointedMapGerm 2 3,
    g.HasInjectiveRepresentative → g.differential ≠ 0
```

and the final declaration has type

```lean
OnLeConjecture.Analytic.leConjecture_native :
  OnLeConjecture.Analytic.LeConjecture
```

| Definition | Meaning | Source |
| --- | --- | --- |
| `Source n` | `Fin n → ℂ`, the complex vector space `ℂⁿ` | [`Germ.lean`](OnLeConjecture/Analytic/Germ.lean) |
| `MapGerm n m` | Germs at zero of maps `ℂⁿ → ℂᵐ` satisfying Mathlib’s `AnalyticAt ℂ` at zero | [`MapGerm.lean`](OnLeConjecture/Analytic/MapGerm.lean) |
| `PointedMapGerm n m` | Analytic map germs whose value at zero is zero | [`MapGerm.lean`](OnLeConjecture/Analytic/MapGerm.lean) |
| `g.differential` | The complex Fréchet derivative `fderiv ℂ f 0`, independent of the representative `f` | [`MapGerm.lean`](OnLeConjecture/Analytic/MapGerm.lean) |
| `g.HasInjectiveRepresentative` | An analytic representative is injective on some neighbourhood of zero | [`MapGerm.lean`](OnLeConjecture/Analytic/MapGerm.lean) |

Germs use Mathlib’s quotient `Filter.Germ` by equality on a neighbourhood of zero. Lean checks the proof of the proposition expressed by these definitions, and the axiom audit checks the theorem’s transitive axiom dependencies. Mathematical review includes checking that the definitions express the intended conjecture.

## Check the proof

Install [elan](https://github.com/leanprover/elan), the Lean toolchain manager, and Git. Then run:

```bash
git clone https://github.com/pportilla/le-conjecture-lean.git
cd le-conjecture-lean
lake exe cache get
lake build
lake env lean AuditLeConjectureNative.lean
```

[`lean-toolchain`](lean-toolchain) selects Lean `v4.33.1`. [`lakefile.toml`](lakefile.toml) selects Mathlib `v4.33.1`, and [`lake-manifest.json`](lake-manifest.json) records the exact revisions of all Lake dependencies. Keep these files together. TeX is optional and is needed only to compile the written notes.

The audit prints the proposition, the final theorem’s type, and its axiom dependencies. Its expected final line is:

```text
'OnLeConjecture.Analytic.leConjecture_native' depends on axioms: [propext, Classical.choice, Quot.sound]
```

[`AuditLeConjectureNative.lean`](AuditLeConjectureNative.lean) also fails if it finds an axiom outside that allowlist. In particular, it rejects a dependency on `sorryAx` or an axiom introduced by native evaluation. The audit covers the final theorem and its dependencies. The word `native` in the theorem’s name refers to the proof’s grid-complex construction.

The [verification script](scripts/verify.sh) runs the build and audit together and records the environment and source checksums. See [the build guide](docs/BUILDING.md) for its usage, verification records, resource considerations, a minimal use example, and troubleshooting.

## Proof structure

The proof proceeds by contradiction from a locally injective germ with zero differential.

1. The analytic development constructs resolution data and plane sections associated with the germ.
2. Chain maps between grid complexes and bounds for their spectral thresholds give numerical bounds on the critical Jacobian multiplicities.
3. These bounds supply the common reduction data used in the case analysis. The coordinate order is then 2, 3, or 4, and each case is excluded.
4. The final assembly discharges the remaining chain-map construction through a finite event factorization and marked inverse cancellation.

[`docs/PROOF_GUIDE.md`](docs/PROOF_GUIDE.md) gives the intermediate theorem names, explains how the conditional reductions are discharged, and maps the written notes to the source. In [`Case234.lean`](OnLeConjecture/Case234.lean), the intermediate theorem `leConjecture_of_general_resolution_reduction` states the reduction hypothesis used in the case analysis.

## Relation to the written proofs

The formalization follows the reduction to orders 2, 3, and 4 in [*A reduction theorem for Lê’s conjecture*](https://arxiv.org/abs/2610.10418v1), followed by the exclusions in [*Injective analytic mappings of low order*](https://github.com/pportilla/le-conjecture-cases-2-3-4/blob/main/cases_234_codex.pdf). Two substantial parts of the argument are developed differently.

**The Floer-theoretic estimates are proved through explicit grid complexes.** Grid homology is a combinatorial formulation of knot Floer homology. The classical correspondence is established by Manolescu, Ozsváth, and Sarkar in [*A combinatorial description of knot Floer homology*, Theorem 3.3](https://arxiv.org/abs/math/0607691). In this formalization, the numerical estimates are derived directly from the grid definitions. A general identification with the classical knot Floer complex or its Upsilon invariant lies outside this formal argument.

The [Laurent grid complexes](OnLeConjecture/KnotFloer/GridFullLaurent.lean) have coefficients in $\mathbb{F}_2[T,T^{-1}]$. Their differentials count rectangles whose interiors contain no grid-state points, with weights determined by the O markings. For each weighted combination of the two filtrations, the [spectral threshold](OnLeConjecture/KnotFloer/SpectralThreshold.lean) of a [canonical degree-zero homology class](OnLeConjecture/KnotFloer/GridCanonicalClass.lean) is the infimum of filtration levels admitting a cycle representative of that class. The comparison with the reduction paper is as follows.

| Step in the reduction paper | Construction used in Lean |
| --- | --- |
| Corollary 3.19 constructs a knot cobordism. Lemma 4.3 and Corollary 4.4 apply the Upsilon cobordism inequality and connected-sum additivity. | [Explicit filtered chain maps](OnLeConjecture/Analytic/ResolutionSectionNativeAssembly.lean) compose a braid map, an exterior map, and a comparison with a finite tensor product of local grid complexes. Their composite transports the canonical class and has a filtration shift computed from delta invariants. |
| Theorem 4.5 uses the initial linear segment of Upsilon for algebraic knots. | A [spectral-threshold lower bound](OnLeConjecture/KnotFloer/GridFactorLowerBound.lean) is proved for the positive-word grids arising from the local factors. |
| Theorem 4.5 uses two inequalities obtained from the torus-knot Upsilon formula. | [Two explicit reflected-torus cycle estimates](OnLeConjecture/KnotFloer/GridReflectedTorusComparison.lean), combined with the local factor bounds and the finite-tensor comparison, give the required numerical inequalities. |

The [formal reduction](OnLeConjecture/Analytic/ResolutionSectionFloerReduction.lean) obtains

$$
M\le t_J,\qquad S+M\le 3t_J,
\qquad M=\sum_p m_p,\quad S=\sum_p m_p^2,
$$

where $p$ runs over the vertices of the resolution tree and $m_p$ is its multiplicity at $p$. The integer $t_J$ is defined [algebraically](OnLeConjecture/Analytic/CriticalJacobianDivisor.lean): factor the greatest common divisor of the coordinate Jacobians, add one to each irreducible factor's exponent, and take the maximum, with value zero for empty support. The subsequent case reduction uses these algebraic quantities directly.

**The order-two quadratic-pencil argument uses analytic coordinates and a cyclic normal form.** In the cases manuscript, Proposition 6.8 applies the obstruction from semicontinuity of the singularity spectrum in Lemma 6.6. For a quadratic pencil with no common projective zero, the [formal proof](OnLeConjecture/DTwo/BasepointFreePencilExclusion.lean) uses the nonunit common divisor of the Jacobian minors supplied by the reduction to construct a smooth critical factor and choose compatible analytic node coordinates. It then applies a [cyclic normal-form noninjectivity theorem](OnLeConjecture/DTwo/CyclicSmallExponentExclusion.lean). This supplies the particular exclusion needed at that step of the order-two proof.

## Repository layout

| Path | Contents |
| --- | --- |
| [`OnLeConjecture/Analytic`](OnLeConjecture/Analytic) | Analytic germs, resolution trees, sections, levels, braid monodromy, reductions, and the final theorem |
| [`OnLeConjecture/KnotFloer`](OnLeConjecture/KnotFloer) | Grid complexes, filtrations, canonical classes, grid moves, torus representatives, tensor products, seams, and the exterior map |
| [`OnLeConjecture/KnotTheory`](OnLeConjecture/KnotTheory) | Braid words, word grids, braid relations, and marked cancellation |
| [`OnLeConjecture/DTwo`](OnLeConjecture/DTwo), [`DThree`](OnLeConjecture/DThree), [`DFour`](OnLeConjecture/DFour) | The order 2, 3, and 4 case analyses |
| [`OnLeConjecture/PlaneCurve`](OnLeConjecture/PlaneCurve) | Plane curve invariants and local constructions |
| [`OnLeConjecture/Polynomial`](OnLeConjecture/Polynomial), [`Numerical`](OnLeConjecture/Numerical), [`DifferentialTopology`](OnLeConjecture/DifferentialTopology) | Supporting algebra, numerical estimates, and topology |
| [`OnLeConjecture/External`](OnLeConjecture/External) | Vendored dependencies, licenses, and provenance records |
| [`OnLeConjecture.lean`](OnLeConjecture.lean) | Aggregate import for the development |
| [`AuditLeConjectureNative.lean`](AuditLeConjectureNative.lean) | Axiom audit of the final theorem |
| [`docs`](docs) | Build guide, proof guide, and written mathematical notes |
| [`verification`](verification) | Recorded build and axiom-audit output |

## Written mathematical notes

The notes in [`docs/written-proofs`](docs/written-proofs) document arguments used during the formalization. The `J` identifiers in their filenames identify development tasks.

| Note (PDF) | Topics |
| --- | --- |
| [Seven obligations: J05, J06, J07, J21, J10, J15, J14](docs/written-proofs/written-proofs-J05-J06-J07-J21-J10-J15-J14.pdf) ([source](docs/written-proofs/written-proofs-J05-J06-J07-J21-J10-J15-J14.tex)) | Seam parity, a second torus representative, letter deletion, discriminant counts, and full-twist factorization |
| [J03–J04](docs/written-proofs/J03-J04-finite-tensor-iterated-seam.pdf) ([source](docs/written-proofs/J03-J04-finite-tensor-iterated-seam.tex)) | Finite tensor algebra and the iterated seam comparison |
| [J08](docs/written-proofs/J08-coxeter-conjugacy.pdf) ([source](docs/written-proofs/J08-coxeter-conjugacy.tex)) | Full-twist centrality and Coxeter-word conjugacy |
| [J09](docs/written-proofs/J09-word-grid-moves.pdf) ([source](docs/written-proofs/J09-word-grid-moves.tex)) | Braid word relations as grid moves |
| [J11](docs/written-proofs/J11-torus-word-grid.pdf) ([source](docs/written-proofs/J11-torus-word-grid.tex)) | Torus word grids and reflected torus grids |
| [Factor lower bound](docs/written-proofs/factor-lower-bound.pdf) ([source](docs/written-proofs/factor-lower-bound.tex)) | Spectral-threshold bounds for torus grids and positive word grids |
| [Statement E](docs/written-proofs/statement-E-complete-proof.pdf) ([source](docs/written-proofs/statement-E-complete-proof.tex)) | Construction of the exterior map |

These development documents retain references to problem briefs, proposed Lean names, earlier interfaces, and gaps recorded at the time of writing. Some statements were narrowed or replaced during formalization. The [proof guide](docs/PROOF_GUIDE.md#written-notes-and-the-final-source) explains the changes. The final Lean declarations and their hypotheses determine the formal result’s scope.

The separate [cases repository](https://github.com/pportilla/le-conjecture-cases-2-3-4) provides the low-order manuscript in a form intended for mathematical reading and citation.

## Dependencies and attribution

The original code was developed by Pablo Portilla Cuadrado using ChatGPT Astra and Opus 5.5. The source retains individual authorship and copyright headers. Mathlib and its dependencies are obtained through Lake. Four additional collections are vendored under [`OnLeConjecture/External`](OnLeConjecture/External):

| Collection | Material used |
| --- | --- |
| [`TauCeti`](OnLeConjecture/External/TauCeti) | Grid diagrams, grid homology, grid moves, and smooth isotopy tools |
| [`LocalComplexGeometry`](OnLeConjecture/External/LocalComplexGeometry) | Local complex geometry and the Rückert Nullstellensatz |
| [`ClassicalComplexWPT`](OnLeConjecture/External/ClassicalComplexWPT) | Weierstrass preparation |
| [`OpenAIMath`](OnLeConjecture/External/OpenAIMath) | Homology and related geometric results |

The [third-party source guide](THIRD_PARTY.md) links upstream repositories, licenses, and provenance records. Each vendored collection includes its license. Provenance records in the vendored directories describe the imported or adapted files. Preserve these records and source headers when redistributing the code.

## Reporting issues and citing the development

Use the [issue tracker](https://github.com/pportilla/le-conjecture-lean/issues) for build failures, discrepancies between the formal statement and the mathematics, or documentation corrections. Include the commit, the command, and the relevant error output for a build report. For a mathematical report, name the declaration and the assumption or conclusion at issue.

Machine-readable citation metadata is in [`CITATION.cff`](CITATION.cff). When citing the formalization, use that metadata and identify the exact commit or release used. A description of the development should acknowledge the use of ChatGPT Astra and Opus 5.5. Cite the [companion manuscript](https://github.com/pportilla/le-conjecture-cases-2-3-4) separately when referring to the written case proofs.

## License

Original Lean code is licensed under the [MIT License](LICENSE). Vendored code and the adapted files listed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) retain the [Apache License 2.0](LICENSES/Apache-2.0.txt) and their attribution. The exceptions include the four vendored collections, twelve files adapted from Tau Ceti, and `Analytic/FiniteDimensionalFactorization.lean`, adapted from lean-SCV. Consult the individual source headers and notices for the applicable terms.
