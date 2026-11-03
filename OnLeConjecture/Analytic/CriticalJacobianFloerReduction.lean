/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalJacobianStaircaseReduction
public import OnLeConjecture.KnotFloer.GridReflectedTorusComparison
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondRange
public import Mathlib.Algebra.Field.ZMod

/-!
# The finite grid comparison implies the canonical critical-divisor bounds

This verifies the connection from the explicit torus class and finite tensor
map to the conjecture reduction. The first source representative and all
exceptional size conditions are discharged internally. Constructing the
remaining data is open. The second representative is required only when
`2*t_J < S`, since the first representative also supplies its weighted bound
in the complementary range. In particular, this module does not identify a grid
with the geometric knot or construct the manuscript's cobordism.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open TauCeti CategoryTheory HomologicalComplex KnotFloer KnotFloer.GridFull KnotFloer.Staircase

/-- Exact remaining inputs to the finite grid route for a fixed resolution tree.
They are supplied by the Floer data of `ResolutionSectionFloerReduction.lean`. -/
structure CriticalJacobianFloerData (g : PointedMapGerm 2 3)
    (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (T : RawProjectiveWeakBlowupTree g.1.component) where
  count : ℕ
  sizes : Fin count → ℕ
  diagrams : ∀ j, GridDiagram (sizes j)
  cobordismGenus : ℝ
  genera : Fin count → ℝ
  map : laurentMaslovComplex (reflectedTorusGrid ((∑ p, (T.multiplicity p) ^ 2) - 1))
      (ZMod 2) ⟶ laurentFiniteMaslovComplex (K := ZMod 2) diagrams
  shift : (laurentMaslovBifiltration
      (reflectedTorusGrid ((∑ p, (T.multiplicity p) ^ 2) - 1)) (ZMod 2)).Shifts
    (laurentFiniteMaslovBifiltration diagrams) map 0 cobordismGenus
  secondRepresentative :
    2 * (g.criticalJacobianFactorization hi).maxMultiplicity < ∑ p, (T.multiplicity p) ^ 2 →
    ((laurentMaslovBifiltration
      (reflectedTorusGrid ((∑ p, (T.multiplicity p) ^ 2) - 1)) (ZMod 2)).weighted
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).RepresentedBelow 0
    (reflectedTorusAnchorClass ((∑ p, (T.multiplicity p) ^ 2) - 1) (ZMod 2))
    (consecutiveWeight ((∑ p, (T.multiplicity p) ^ 2) - 1)
      (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))
      ⟨2, by have := T.four_le_square_sum_of_differential_eq_zero hd; omega⟩)
  cycles : ∀ j, (laurentMaslovComplex (diagrams j) (ZMod 2)).cycles 0
  lowerBounds : ∀ j,
    ((genera j * (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ)) / 2 : ℝ) :
        EReal) ≤
      ((laurentMaslovBifiltration (diagrams j) (ZMod 2)).weighted
        (2 / ((g.criticalJacobianFactorization hi).maxMultiplicity : ℝ))).spectralThreshold 0
        ((laurentMaslovComplex (diagrams j) (ZMod 2)).homologyπ 0 (cycles j))
  mapClass : homologyMap map 0
      (reflectedTorusAnchorClass ((∑ p, (T.multiplicity p) ^ 2) - 1) (ZMod 2)) =
    laurentFiniteNativeClass diagrams cycles
  genusIdentity :
    (((∑ p, (T.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) *
        ((((∑ p, (T.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) / 2 -
      (∑ j, genera j) + cobordismGenus =
        ((((∑ p, (T.multiplicity p) ^ 2) - 1 : ℕ) : ℝ) + 1) -
          ((∑ p, T.multiplicity p : ℕ) : ℝ)

/-- The package gives exactly the two bounds consumed by the canonical reduction. -/
theorem criticalJacobian_bounds_of_floer_data
    (g : PointedMapGerm 2 3) (hd : g.differential = 0)
    (hi : g.HasInjectiveRepresentative) (T : RawProjectiveWeakBlowupTree g.1.component)
    (D : CriticalJacobianFloerData g hd hi T) :
    (∑ p, T.multiplicity p) ≤ (g.criticalJacobianFactorization hi).maxMultiplicity ∧
      (∑ p, (T.multiplicity p) ^ 2) + (∑ p, T.multiplicity p) ≤
        3 * (g.criticalJacobianFactorization hi).maxMultiplicity := by
  have hS := T.four_le_square_sum_of_differential_eq_zero hd
  have hm := (g.criticalJacobianFactorization hi).two_le_maxMultiplicity_of_differential_eq_zero
    hi hd
  have h := estimates_of_reflected_torus_and_finite_tensor_map
    ((∑ p, (T.multiplicity p) ^ 2) - 1) (∑ p, T.multiplicity p)
    (g.criticalJacobianFactorization hi).maxMultiplicity (by omega) (by omega)
    D.diagrams D.map D.cobordismGenus D.shift (by
      by_cases hbig : 2 * (g.criticalJacobianFactorization hi).maxMultiplicity <
          ∑ p, (T.multiplicity p) ^ 2
      · exact D.secondRepresentative hbig
      · exact reflectedTorusAnchorClass_representedBelow_second_vertex_of_le
          ((∑ p, (T.multiplicity p) ^ 2) - 1) (ZMod 2)
          (g.criticalJacobianFactorization hi).maxMultiplicity (by omega) (by omega) (by omega))
    D.cycles D.genera D.lowerBounds D.mapClass D.genusIdentity
  simpa only [Nat.sub_add_cancel (show 1 ≤ ∑ p, (T.multiplicity p) ^ 2 by omega)] using h

end OnLeConjecture.Analytic

namespace OnLeConjecture

open Analytic Analytic.Germ

/-- Reduction through the finite grid comparison. The displayed data are supplied by
`ResolutionSectionFloerData` (see `leConjecture_of_resolutionSection_floer_data`). No full
staircase computation is required. -/
theorem leConjecture_of_criticalJacobian_floer_data
    (hdata : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative),
        ∃ T : RawProjectiveWeakBlowupTree g.1.component,
          Nonempty (CriticalJacobianFloerData g hd hi T)) :
    LeConjecture := by
  apply leConjecture_of_general_resolution_reduction
  intro g hd hi
  obtain ⟨T, ⟨D⟩⟩ := hdata g hd hi
  obtain ⟨hM, hglobal⟩ := criticalJacobian_bounds_of_floer_data g hd hi T D
  obtain ⟨q₀, _, hq₀⟩ := T.exists_exact_coefficients Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨R⟩ := exists_constructedResolutionRemainingData_of_criticalJacobian_bounds
    g hd hi T q₀ hq₀ hM hglobal
  exact R.exists_generalResolutionReductionData

end OnLeConjecture
