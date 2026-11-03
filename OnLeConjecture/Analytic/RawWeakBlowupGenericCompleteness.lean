/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupProximityData
public import OnLeConjecture.Analytic.ExceptionalPolynomialFamily
public import OnLeConjecture.Analytic.SimpleExceptionalRoot
public import OnLeConjecture.Analytic.ProjectivePointBasisCompleteness
public import OnLeConjecture.Polynomial.GenericSquarefreeOpen

/-!
# Generic members whose singular transforms are recorded

A single coefficient row can give squarefree residual exceptional
polynomials in both projective charts at every vertex of the finite
weak-transform tree. Every singular transform then lies at a common weak
zero, hence at a recorded child. The coefficient row can be selected
inside any prescribed nonempty open set.

The conclusion holds throughout a constructed nonempty open coefficient
set. This file does not identify branch counts with proximity excesses.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- Pullback preserves a constant linear combination with its original
coefficient row. -/
theorem pullback_germLinearCombination {ι : Type*} [Fintype ι]
    (e : PointedMapGerm 2 2) (F : ι → Germ 2) (q : ι → ℂ) :
    e.pullbackRingHom (germLinearCombination F q) =
      germLinearCombination (fun i => e.pullbackRingHom (F i)) q := by
  simp only [germLinearCombination, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, PointedMapGerm.pullback_complex_smul]

/-- A squarefree residual exceptional polynomial makes the member exact
of the prescribed order and confines singular transforms to common weak
zeros of the original generators. -/
theorem singular_transforms_common_zero_of_squarefree_residual
    {ι : Type*} [Fintype ι] (F : ι → Germ 2) (m : ℕ)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) (P : ι → ℂ[X])
    (hrestriction : ∀ (i : ι) (c : ℂ),
      pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m (F i) (hF i)) =
        oneVariablePolynomialEvaluation ((P i).comp (X + C c)))
    (q : ι → ℂ) (G R : ℂ[X]) (hG : G ≠ 0) (hR : Squarefree R)
    (hfactor : OnLeConjecture.Polynomial.polynomialLinearCombination P q = G * R)
    (hzero : ∀ z, G.eval z = 0 ↔ ∀ i, (P i).eval z = 0) :
    germLinearCombination F q ∉ maximalIdeal 2 ^ (m + 1) ∧
      ∀ (c : ℂ) (H : Germ 2),
        (pointBlowupChartGerm c).pullbackRingHom (germLinearCombination F q) =
          coordinate (1 : Fin 2) ^ m * H →
        H ∈ maximalIdeal 2 ^ 2 →
        ∀ i, pointBlowupTransform c m (F i) (hF i) ∈ maximalIdeal 2 := by
  have hcomb : (∑ i, C (q i) * P i) = G * R := by
    simpa only [OnLeConjecture.Polynomial.polynomialLinearCombination,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_C_mul] using hfactor
  have hmember (c : ℂ) :
      pointBlowupExceptionalLine.pullbackRingHom
        (pointBlowupTransform c m (germLinearCombination F q)
          (germLinearCombination_mem _ _ hF q)) =
        oneVariablePolynomialEvaluation ((G * R).comp (X + C c)) := by
    rw [exceptional_restriction_linearCombination m F hF P hrestriction q c, hcomb]
  constructor
  · apply not_mem_succ_of_pointBlowupTransform_exceptionalRestriction_ne_zero
      0 m _ (germLinearCombination_mem _ _ hF q)
    rw [hmember]
    apply vanishingOrder_eq_top_iff.not.mp
    rw [vanishingOrder_polynomial_translation (G * R) (mul_ne_zero hG hR.ne_zero) 0]
    exact ENat.natCast_ne_top _
  · intro c H htransform hsingular i
    have hH : H = pointBlowupTransform c m (germLinearCombination F q)
        (germLinearCombination_mem _ _ hF q) :=
      pointBlowupTransform_unique c m _ _ _ htransform (pointBlowupTransform_factor _ _ _ _)
    have hGzero := common_factor_vanishes_of_singular_exceptional_transform
      H G R c hR (by rw [hH]; exact hmember c) hsingular
    exact (mem_maximalIdeal_iff_exceptional_polynomial_root _ (P i) c
      (hrestriction i c)).mpr ((hzero c).mp hGzero i)

/-- The singular-transform conclusion holds throughout a nonempty open
subset of any supplied nonempty open coefficient set. -/
theorem exists_open_coefficients_singular_transforms_common_zero
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → Germ 2) (m : κ → ℕ)
    (hF : ∀ k i, F k i ∈ maximalIdeal 2 ^ m k)
    (hexact : ∀ k, ∃ i, F k i ∉ maximalIdeal 2 ^ (m k + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ k, germLinearCombination (F k) q ∉ maximalIdeal 2 ^ (m k + 1)) ∧
        ∀ (k : κ) (c : ℂ) (H : Germ 2),
          (pointBlowupChartGerm c).pullbackRingHom (germLinearCombination (F k) q) =
            coordinate (1 : Fin 2) ^ m k * H →
          H ∈ maximalIdeal 2 ^ 2 →
          ∀ i, pointBlowupTransform c (m k) (F k i) (hF k i) ∈ maximalIdeal 2 := by
  classical
  let := Fintype.ofFinite κ
  choose P hdegree hPne hrestriction using
    fun k => exists_exceptional_restriction_polynomial_family (m k) (F k) (hF k) (hexact k)
  obtain ⟨G, A, V, hVopen, hVne, hVU, hG, hV⟩ :=
    OnLeConjecture.Polynomial.exists_open_squarefree_coprime_residual_combinations P hPne U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro q hq
  have hfactor (k : κ) : OnLeConjecture.Polynomial.polynomialLinearCombination (P k) q =
      G k * OnLeConjecture.Polynomial.polynomialLinearCombination (A k) q := by
    simp only [OnLeConjecture.Polynomial.polynomialLinearCombination,
      LinearMap.coe_mk, AddHom.coe_mk, (hG k).2.1, Finset.mul_sum, smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgood (k : κ) := singular_transforms_common_zero_of_squarefree_residual
    (F k) (m k) (hF k) (P k) (hrestriction k) q (G k)
    (OnLeConjecture.Polynomial.polynomialLinearCombination (A k) q)
    (hG k).1 (hV q hq k).1 (hfactor k) (hG k).2.2.2
  exact ⟨fun k => (hgood k).1, fun k => (hgood k).2⟩

/-- One common coefficient row can be selected inside any prescribed
nonempty open set. -/
theorem exists_coefficients_singular_transforms_common_zero_mem_open
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → Germ 2) (m : κ → ℕ)
    (hF : ∀ k i, F k i ∈ maximalIdeal 2 ^ m k)
    (hexact : ∀ k, ∃ i, F k i ∉ maximalIdeal 2 ^ (m k + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ k, germLinearCombination (F k) q ∉ maximalIdeal 2 ^ (m k + 1)) ∧
      ∀ (k : κ) (c : ℂ) (H : Germ 2),
        (pointBlowupChartGerm c).pullbackRingHom (germLinearCombination (F k) q) =
          coordinate (1 : Fin 2) ^ m k * H →
        H ∈ maximalIdeal 2 ^ 2 →
        ∀ i, pointBlowupTransform c (m k) (F k i) (hF k i) ∈ maximalIdeal 2 := by
  obtain ⟨V, _, hVne, hVU, hV⟩ :=
    exists_open_coefficients_singular_transforms_common_zero F m hF hexact U hU hUne
  obtain ⟨q, hq⟩ := hVne
  exact ⟨q, hVU hq, hV q hq⟩

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- Every row in a constructed nonempty open coefficient subset has exact
order at every vertex and no unrecorded singular transform in either
projective chart. The conclusion holds at every vertex. -/
theorem exists_open_member_singular_complete
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
      (∀ p, germLinearCombination (T.generators p) q ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      ∀ (p : T.Vertex) (t : Option ℂ) (H : Germ 2),
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) q)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * H →
        H ∈ maximalIdeal 2 ^ 2 →
        ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t := by
  classical
  let e : Bool → PointedEquivGerm 2 := fun b =>
    if b then coordinateSwapPointedEquiv (1 : Fin 2) else PointedEquivGerm.identity 2
  let A : T.Vertex × Bool → ι → Germ 2 := fun k i =>
    (e k.2).forward.pullbackRingHom (T.generators k.1 i)
  let m : T.Vertex × Bool → ℕ := fun k => T.multiplicity k.1
  have hA (k : T.Vertex × Bool) (i : ι) : A k i ∈ maximalIdeal 2 ^ m k :=
    (e k.2).forward.pullback_mem_maximalIdeal_pow (T.generator_mem k.1 i)
  have hAexact (k : T.Vertex × Bool) : ∃ i, A k i ∉ maximalIdeal 2 ^ (m k + 1) := by
    obtain ⟨i, hi⟩ := T.generator_exact k.1
    refine ⟨i, fun h => hi ?_⟩
    exact ((e k.2).pullback_mem_maximalIdeal_pow_iff _).mp h
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_coefficients_singular_transforms_common_zero A m hA hAexact U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro q hqV
  obtain ⟨hq, hsing⟩ := hV q hqV
  have hmember (p : T.Vertex) (b : Bool) : germLinearCombination (A (p, b)) q =
      (e b).forward.pullbackRingHom (germLinearCombination (T.generators p) q) := by
    rw [pullback_germLinearCombination]
  constructor
  · intro p
    have h := hq (p, false)
    rw [hmember] at h
    simpa only [e, Bool.false_eq_true, ↓reduceIte, PointedEquivGerm.identity_forward,
      PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply, m] using h
  · intro p t H htransform hsingular
    apply T.realizes_common_zero p t
    intro i
    cases t with
    | none =>
        have h := hsing (p, true) 0 H (by
          rw [hmember]
          simpa only [e, ↓reduceIte, m,
            projectiveChartCenter, projectiveChartSource] using htransform) hsingular i
        simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
          A, e, ↓reduceIte, m] using h
    | some c =>
        have h := hsing (p, false) c H (by
          rw [hmember]
          simpa only [e, Bool.false_eq_true, ↓reduceIte, m,
            projectiveChartCenter, projectiveChartSource] using htransform) hsingular i
        simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
          A, e, Bool.false_eq_true, ↓reduceIte, m] using h

/-- A member with complete singular transforms can be selected from any
nonempty open coefficient set. -/
theorem exists_member_singular_complete_mem_open
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (T.generators p) q ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      ∀ (p : T.Vertex) (t : Option ℂ) (H : Germ 2),
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) q)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * H →
        H ∈ maximalIdeal 2 ^ 2 →
        ∃ r, r ≠ T.root ∧ T.predecessor r = p ∧ T.chartPoint r = t := by
  obtain ⟨V, _, hVne, hVU, hV⟩ := T.exists_open_member_singular_complete U hU hUne
  obtain ⟨q, hq⟩ := hVne
  exact ⟨q, hVU hq, hV q hq⟩

/-- The selected member's constructed point basis has the two-chart
singular completeness required in the general reduction record. -/
theorem exists_terminal_complete_member_mem_open
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (q : ι → ℂ), q ∈ U ∧
      ∃ hq : ∀ p, germLinearCombination (T.generators p) q ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1),
        TerminalTwoChartSingularCompleteness (T.pointBasis q hq) := by
  obtain ⟨q, hqU, hq, hcomplete⟩ := T.exists_member_singular_complete_mem_open U hU hUne
  refine ⟨q, hqU, hq, ⟨?_⟩⟩
  intro p _ _ t H htransform _ hsingular
  obtain ⟨r, hr, hpred, hchart⟩ :=
    hcomplete (T.indexEquiv.symm p) t H htransform hsingular
  refine ⟨T.indexEquiv r, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    exact hr (T.indexEquiv.injective h)
  · change T.indexEquiv (T.predecessor (T.indexEquiv.symm (T.indexEquiv r))) = p
    rw [Equiv.symm_apply_apply, hpred, Equiv.apply_symm_apply]
  · change projectiveChartCenter (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r))) = _
    rw [Equiv.symm_apply_apply, hchart]
  · change (projectiveChartSource (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r)))).forward = _
    rw [Equiv.symm_apply_apply, hchart]

/-- A nonempty open subset makes the singular completeness assertion
hold for every chosen member of the original weak-generator data. -/
theorem exists_open_weakData_terminal_complete
    (T : RawProjectiveWeakBlowupTree F) (q₀ : ι → ℂ)
    (hq₀ : ∀ p, germLinearCombination (T.generators p) q₀ ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        ∀ hq : ∀ p,
          germLinearCombination ((T.weakData q₀ hq₀).generators p) q ∈
            maximalIdeal 2 ^ (T.pointBasis q₀ hq₀).multiplicity p ∧
          germLinearCombination ((T.weakData q₀ hq₀).generators p) q ∉
            maximalIdeal 2 ^ ((T.pointBasis q₀ hq₀).multiplicity p + 1),
          TerminalTwoChartSingularCompleteness
            ((T.weakData q₀ hq₀).pointBasisOfLinearCombination q hq) := by
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ := T.exists_open_member_singular_complete U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro q hqV hq
  refine ⟨?_⟩
  intro p _ _ t H htransform _ hsingular
  obtain ⟨r, hr, hpred, hchart⟩ :=
    (hV q hqV).2 (T.indexEquiv.symm p) t H htransform hsingular
  refine ⟨T.indexEquiv r, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    exact hr (T.indexEquiv.injective h)
  · change T.indexEquiv (T.predecessor (T.indexEquiv.symm (T.indexEquiv r))) = p
    rw [Equiv.symm_apply_apply, hpred, Equiv.apply_symm_apply]
  · change projectiveChartCenter (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r))) = _
    rw [Equiv.symm_apply_apply, hchart]
  · change (projectiveChartSource (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r)))).forward = _
    rw [Equiv.symm_apply_apply, hchart]

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
