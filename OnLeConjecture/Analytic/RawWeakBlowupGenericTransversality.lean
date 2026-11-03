/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupProximityIntersectionExact
public import OnLeConjecture.Analytic.ExceptionalResidualBranchCount

/-!
# Transverse branches at unrecorded projective points

The common-factor and squarefree-residual polynomial construction gives
more than singular completeness. At every unrecorded projective point, a
nonunit transformed member has exceptional intersection one and exactly
one irreducible branch. The same coefficient row works at every vertex and
both projective charts, throughout a nonempty open coefficient set.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- Away from the common factor, a nonunit transform with squarefree
residual exceptional polynomial has exceptional order and branch count one. -/
theorem exceptional_order_and_branchCount_one_of_squarefree_residual
    (H : Germ 2) (G R : ℂ[X]) (c : ℂ) (hR : Squarefree R)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom H =
      oneVariablePolynomialEvaluation ((G * R).comp (X + C c)))
    (hG : G.eval c ≠ 0) (hunit : ¬ IsUnit H) :
    (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom H)).toNat = 1 ∧
      PlaneCurve.irreducibleBranchCount H = 1 := by
  have hH : H ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    by_contra hz
    exact hunit (isUnit_of_valueRingHom_ne_zero hz)
  have hprod := (mem_maximalIdeal_iff_exceptional_polynomial_root H (G * R) c hrestriction).mp hH
  have hRroot : R.IsRoot c := by
    change (G * R).eval c = 0 at hprod
    rw [eval_mul] at hprod
    exact (mul_eq_zero.mp hprod).resolve_left hG
  have hGne : G ≠ 0 := by intro hz; exact hG (by rw [hz, eval_zero])
  have hGorder : G.rootMultiplicity c = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hG ((rootMultiplicity_pos hGne).mp hpos)
  have hRorder : R.rootMultiplicity c = 1 := by
    have hpos := (rootMultiplicity_pos hR.ne_zero).mpr hRroot
    have hle := rootMultiplicity_le_one_of_separable
      (PerfectField.separable_iff_squarefree.mpr hR) c
    omega
  refine ⟨?_, (smooth_branch_of_squarefree_residual_exceptional_polynomial
    H G R c hR hrestriction hG hRroot).2.2.2.2⟩
  rw [hrestriction, vanishingOrder_polynomial_translation (G * R)
    (mul_ne_zero hGne hR.ne_zero), rootMultiplicity_mul (mul_ne_zero hGne hR.ne_zero),
    hGorder, hRorder, zero_add, ENat.toNat_natCast]

/-- Common finite analytic generator families have uniformly transverse
members away from their common weak zeros. -/
theorem exists_open_coefficients_transverse_off_common_zero
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
          (∃ i, pointBlowupTransform c (m k) (F k i) (hF k i) ∉ maximalIdeal 2) →
          ¬ IsUnit H →
          (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom H)).toNat = 1 ∧
            PlaneCurve.irreducibleBranchCount H = 1 := by
  classical
  choose P hdegree hPne hrestriction using
    fun k => exists_exceptional_restriction_polynomial_family (m k) (F k) (hF k) (hexact k)
  obtain ⟨G, A, V, hVopen, hVne, hVU, hG, hV⟩ :=
    OnLeConjecture.Polynomial.exists_open_squarefree_coprime_residual_combinations
      P hPne U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro q hq
  let R : κ → ℂ[X] := fun k => OnLeConjecture.Polynomial.polynomialLinearCombination (A k) q
  have hfactor (k : κ) : OnLeConjecture.Polynomial.polynomialLinearCombination (P k) q =
      G k * R k := by
    simp only [R, OnLeConjecture.Polynomial.polynomialLinearCombination,
      LinearMap.coe_mk, AddHom.coe_mk, (hG k).2.1, Finset.mul_sum, smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgood (k : κ) := singular_transforms_common_zero_of_squarefree_residual
    (F k) (m k) (hF k) (P k) (hrestriction k) q (G k) (R k)
    (hG k).1 (hV q hq k).1 (hfactor k) (hG k).2.2.2
  refine ⟨fun k => (hgood k).1, ?_⟩
  intro k c H htransform hnotcommon hunit
  have hH : H = pointBlowupTransform c (m k) (germLinearCombination (F k) q)
      (germLinearCombination_mem _ _ (hF k) q) :=
    pointBlowupTransform_unique c (m k) _ _ _ htransform (pointBlowupTransform_factor _ _ _ _)
  have hcomb : (∑ i, C (q i) * P k i) = G k * R k := by
    simpa only [OnLeConjecture.Polynomial.polynomialLinearCombination,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_C_mul] using hfactor k
  have hHrestriction : pointBlowupExceptionalLine.pullbackRingHom H =
      oneVariablePolynomialEvaluation ((G k * R k).comp (X + C c)) := by
    rw [hH, exceptional_restriction_linearCombination (m k) (F k) (hF k) (P k)
      (hrestriction k) q c, hcomb]
  have hGvalue : (G k).eval c ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hnotcommon
    exact hi ((mem_maximalIdeal_iff_exceptional_polynomial_root _ (P k i) c
      (hrestriction k i c)).mpr (((hG k).2.2.2 c).mp hz i))
  exact exceptional_order_and_branchCount_one_of_squarefree_residual H (G k) (R k) c
    (hV q hq k).1 hHrestriction hGvalue hunit

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- The analytic transform of the selected member at any projective
point, whether or not that point is a recorded child. -/
@[expose] noncomputable def projectiveMemberTransform
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) (t : Option ℂ) : Germ 2 :=
  germLinearCombination (projectiveWeakGenerators (T.multiplicity p)
    (T.generators p) (T.generator_mem p) t) q

theorem projectiveMemberTransform_factor
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) (t : Option ℂ) :
    (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom
        (germLinearCombination (T.generators p) q)) =
      coordinate (1 : Fin 2) ^ T.multiplicity p * T.projectiveMemberTransform q p t :=
  T.linearCombination_projective_transform_identity q p t

theorem projectiveMemberTransform_eq_child
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p r : T.Vertex)
    (hr : r ∈ T.childFinset p) :
    T.projectiveMemberTransform q p (T.chartPoint r) =
      germLinearCombination (T.generators r) q := by
  obtain ⟨hrne, hrpred⟩ := (T.mem_childFinset p r).mp hr
  apply pointBlowupTransform_unique _ _ _ _ _
    (T.projectiveMemberTransform_factor q p (T.chartPoint r))
  simpa only [hrpred] using T.linearCombination_transform q r hrne

/-- At every unrecorded point in either projective chart, a nonunit
member transform is one smooth transverse branch, uniformly on a nonempty
open coefficient set. -/
theorem exists_open_unrecorded_transverse_members
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
        ∀ (p : T.Vertex) (t : Option ℂ),
          t ∉ (T.childFinset p).image T.chartPoint →
          ¬ IsUnit (T.projectiveMemberTransform q p t) →
          (vanishingOrder (pointBlowupExceptionalLine.pullbackRingHom
            (T.projectiveMemberTransform q p t))).toNat = 1 ∧
            PlaneCurve.irreducibleBranchCount (T.projectiveMemberTransform q p t) = 1 := by
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
    exact ⟨i, fun h => hi (((e k.2).pullback_mem_maximalIdeal_pow_iff _).mp h)⟩
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_coefficients_transverse_off_common_zero A m hA hAexact U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro q hqV
  obtain ⟨hq, htransverse⟩ := hV q hqV
  have hmember (p : T.Vertex) (b : Bool) : germLinearCombination (A (p, b)) q =
      (e b).forward.pullbackRingHom (germLinearCombination (T.generators p) q) := by
    rw [pullback_germLinearCombination]
  refine ⟨?_, ?_⟩
  · intro p
    have h := hq (p, false)
    rw [hmember] at h
    simpa only [e, Bool.false_eq_true, ↓reduceIte, PointedEquivGerm.identity_forward,
      PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply, m] using h
  · intro p t ht hunit
    have hnotcommon : ∃ i, projectiveWeakGenerators (T.multiplicity p)
        (T.generators p) (T.generator_mem p) t i ∉ maximalIdeal 2 := by
      by_contra! h
      exact ht ((T.mem_image_chartPoint_childFinset_iff p t).mpr h)
    have htransform := T.projectiveMemberTransform_factor q p t
    cases t with
    | none =>
        apply htransverse (p, true) 0 _ _ _ hunit
        · rw [hmember]
          simpa only [e, ↓reduceIte, m,
            projectiveChartCenter, projectiveChartSource] using htransform
        · simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
            A, e, ↓reduceIte, m] using hnotcommon
    | some c =>
        apply htransverse (p, false) c _ _ _ hunit
        · rw [hmember]
          simpa only [e, Bool.false_eq_true, ↓reduceIte, m,
            projectiveChartCenter, projectiveChartSource] using htransform
        · simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
            A, e, Bool.false_eq_true, ↓reduceIte, m] using hnotcommon

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
