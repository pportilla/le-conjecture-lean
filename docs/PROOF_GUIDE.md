# Guide to the formal proof

This guide locates the statements and constructions used by the final theorem. It is a reading map for the Lean source. The written low-order arguments are in the companion repository, [*Injective analytic mappings of low order*](https://github.com/pportilla/le-conjecture-cases-2-3-4).

## Read the statement first

[`Analytic/Germ.lean`](../OnLeConjecture/Analytic/Germ.lean) defines `Source n := Fin n → ℂ`. [`Analytic/MapGerm.lean`](../OnLeConjecture/Analytic/MapGerm.lean) defines analytic germs, pointed germs, their differential, and existence of an injective representative. These determine the meaning of `LeConjecture`.

[`Analytic/LeConjectureNative.lean`](../OnLeConjecture/Analytic/LeConjectureNative.lean) contains the final proof:

```lean
theorem leConjecture_native : LeConjecture :=
  leConjecture_of_markedFactorCleanup
    OnLeConjecture.KnotTheory.MarkedCancel.markedFactorCleanup
```

The right-hand side combines a reduction theorem with a proof of its remaining hypothesis. Following that reduction and its imports gives the path through the development. Intermediate names containing `of_`, `Remaining`, or `Frontier` record steps of this construction. Their names alone do not indicate a hypothesis left open in the final declaration.

## The case analysis and its reduction hypothesis

For a finite pointed map germ, [`Analytic/CoordinateOrder.lean`](../OnLeConjecture/Analytic/CoordinateOrder.lean) defines the order of its coordinate ideal using powers of the maximal ideal. This is the order used in the cases 2, 3, and 4.

[`Case234.lean`](../OnLeConjecture/Case234.lean) proves `leConjecture_of_general_resolution_reduction`. Its hypothesis supplies `GeneralResolutionReductionData g` for every germ `g` with zero differential and an injective representative. The proof derives finiteness, reduces the possible coordinate orders to 2, 3, and 4, and applies the corresponding exclusions.

| Case | Entry file |
| --- | --- |
| Order 2 | [`DTwo/CoordinateOrderTwoExclusion.lean`](../OnLeConjecture/DTwo/CoordinateOrderTwoExclusion.lean) |
| Order 3 | [`DThree/GeneralResolutionReductionExclusion.lean`](../OnLeConjecture/DThree/GeneralResolutionReductionExclusion.lean) |
| Order 4 | [`DFour/GenericProjectiveReductionExclusion.lean`](../OnLeConjecture/DFour/GenericProjectiveReductionExclusion.lean) |

`Case234.lean` deliberately states the common reduction hypothesis. The rest of the final proof supplies it. The companion manuscript should be read with its own stated reduction assumptions, independently of the fact that the full Lean development discharges them.

## From analytic sections to the numerical bounds

The relevant sequence of interfaces is:

| Declaration | What it supplies | Entry file |
| --- | --- | --- |
| `leConjecture_of_criticalJacobian_floer_data` | Constructs common reduction data from the critical-Jacobian bounds furnished by Floer comparison data | [`CriticalJacobianFloerReduction.lean`](../OnLeConjecture/Analytic/CriticalJacobianFloerReduction.lean) |
| `ResolutionSectionFloerData` | A chain map, filtration shifts, a second torus representative, factor lower bounds, and compatibility of homology classes for an assembled section and level | [`ResolutionSectionFloerReduction.lean`](../OnLeConjecture/Analytic/ResolutionSectionFloerReduction.lean) |
| `leConjecture_of_resolutionSection_floer_data` | Reduces the conjecture to existence of that comparison data | [`ResolutionSectionFloerReduction.lean`](../OnLeConjecture/Analytic/ResolutionSectionFloerReduction.lean) |
| `exists_resolutionSectionFloerData_of_nativeRouteInputs` | Builds the comparison data from the five fields of `NativeRouteInputs` | [`ResolutionSectionNativeAssembly.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeAssembly.lean) |

For an assembled section `A`, write `mₚ` for the multiplicity of a vertex `p` of `A.tree`, and `T` for the maximum multiplicity of the critical-Jacobian factorization of the hypothetical injective germ. The conclusion `ResolutionSectionFloerData.criticalJacobian_bounds` is

```text
Σₚ mₚ ≤ T,
Σₚ mₚ² + Σₚ mₚ ≤ 3T.
```

The source records the finite index types, natural-number conventions, and all hypotheses. The section and level determine the numerical parameters used by the chain maps and their filtration shifts.

## The five grid-complex inputs

[`ResolutionSectionNativeAssembly.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeAssembly.lean) defines `NativeRouteInputs` with five fields:

| Field | Content | Current proof or construction |
| --- | --- | --- |
| `parity` | Seam positive-path comparisons | [`GridConnectedSumSeamParity.lean`](../OnLeConjecture/KnotFloer/GridConnectedSumSeamParity.lean), `seamPositivePathComparisons` |
| `second` | The second reflected-torus representative in the specified strict range | [`GridReflectedTorusSecondCycle.lean`](../OnLeConjecture/KnotFloer/GridReflectedTorusSecondCycle.lean), `reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt` |
| `braid` | The braid map between the required grid complexes | [`PositiveWordGridBraidRelation.lean`](../OnLeConjecture/KnotTheory/PositiveWordGridBraidRelation.lean), `braidNativeMapStatement_holds` |
| `factor` | Lower bounds for the factor word grids | [`GridFactorLowerBound.lean`](../OnLeConjecture/KnotFloer/GridFactorLowerBound.lean), `factorWordLowerBound` |
| `exterior` | The exterior map, called Statement E in the written notes | [`ExteriorNativeMapReduction.lean`](../OnLeConjecture/Analytic/ExteriorNativeMapReduction.lean) and the assembly below |

The comparison map is composed from a braid map, an exterior map, and an iterated seam comparison into a finite tensor product. [`ResolutionSectionNativeRemaining.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeRemaining.lean) supplies the first four fields and reduces the conjecture to the exterior statement.

## How Statement E is discharged

[`ResolutionSectionNativeFrontier.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeFrontier.lean) constructs the exterior input from event factorization, signed word-grid relations, and the scissor cleanup.

[`ResolutionSectionNativeLevelFamily.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeLevelFamily.lean) then proves the level root-family and event-factorization statements. It reduces the scissor endpoint cleanup to `MarkedFactorCleanupStatement`. Finally, [`GridMarkedCancelCleanup.lean`](../OnLeConjecture/KnotFloer/GridMarkedCancelCleanup.lean) proves that statement as `MarkedCancel.markedFactorCleanup`. This is the argument passed to the final theorem.

For a closer reading, follow these declarations in order:

1. `leConjecture_native`.
2. `leConjecture_of_markedFactorCleanup` and `leConjecture_of_endpointCleanup`.
3. `leConjecture_of_rootFamily_frontier`.
4. `leConjecture_of_remaining_inputs`.
5. `leConjecture_of_nativeRouteInputs`.
6. `leConjecture_of_resolutionSection_floer_data`.
7. `leConjecture_of_criticalJacobian_floer_data`.
8. `leConjecture_of_general_resolution_reduction`.

This order follows the reduction chain backward from the final assembly to the case exclusions. Each declaration’s arguments specify what that particular step still needs.

## Written notes and the final source

The [written notes](written-proofs) retain the development’s job identifiers and historical status statements. They are useful mathematical explanations, but they have not been rewritten into a uniform exposition of the finished Lean dependency chain. In particular, headings such as “Remaining gap” and “Exact missing native identifications” describe the document’s development stage. They should be read together with the current declarations, rather than treated as a current axiom-audit report.

| Identifier or note | Topic | Source entry |
| --- | --- | --- |
| J03–J04 | Finite tensor algebra and the iterated seam comparison | [`ResolutionSectionNativeAssembly.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeAssembly.lean), the call to `exists_iteratedSeam_finiteTensor_map` |
| J05–J07 | Seam parity | [`GridConnectedSumSeamParity.lean`](../OnLeConjecture/KnotFloer/GridConnectedSumSeamParity.lean) |
| J08 | Full-twist centrality and Coxeter conjugacy | [`PositiveWordCoxeterConjugacy.lean`](../OnLeConjecture/KnotTheory/PositiveWordCoxeterConjugacy.lean) |
| J09 | Braid word relations as grid moves | [`PositiveWordGridBraidRelation.lean`](../OnLeConjecture/KnotTheory/PositiveWordGridBraidRelation.lean) |
| J10 | Letter deletion as an X switch | [`PositiveWordGridLetterSwitch.lean`](../OnLeConjecture/KnotTheory/PositiveWordGridLetterSwitch.lean) |
| J11 | Torus word grids | [`TorusWordGridMoves.lean`](../OnLeConjecture/KnotTheory/TorusWordGridMoves.lean) |
| J21 | Second torus representative | [`GridReflectedTorusSecondCycle.lean`](../OnLeConjecture/KnotFloer/GridReflectedTorusSecondCycle.lean) |
| Factor lower bound | Bounds for positive word grids | [`GridFactorLowerBound.lean`](../OnLeConjecture/KnotFloer/GridFactorLowerBound.lean) |
| Statement E | Exterior map and cleanup | [`ResolutionSectionNativeLevelFamily.lean`](../OnLeConjecture/Analytic/ResolutionSectionNativeLevelFamily.lean) |

Some hypotheses matter especially when moving between the notes and the source:

- The full-twist positive-word conjugacy lemmas in `PositiveWordCoxeterConjugacy.lean` impose a strand-count hypothesis where required.
- The J11 note states a torus-word comparison for `q ≥ 1`. The formal theorem `wordGrid_torusWord_movesTo` requires `a ≥ 2` and `q ≥ 2`. Its application to `a = S`, `q = S + 1`, with `S ≥ 2`, satisfies these hypotheses.
- The seven-obligation notes discuss a proposed full-twist interface that is false without additional assumptions.

Read the current formal hypotheses before using any statement from those notes.

Finite grid-move certificates are combined with formal soundness arguments in the source. Finding a sequence by computation and proving that it has the required effect are different steps. The theorem’s axiom audit checks the completed proof dependencies, including the dependencies used to justify such certificates.

## Verification and review

Follow [BUILDING.md](BUILDING.md) to build the source and run the axiom audit. A successful audit establishes the permitted axiom dependencies of the formal theorem. Mathematical review should additionally check that the definitions of analytic germs, local injectivity, and differential express the intended conjecture. Review of the written notes is a separate task from the Lean build.
