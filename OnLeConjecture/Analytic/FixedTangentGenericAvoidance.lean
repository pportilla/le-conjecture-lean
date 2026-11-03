/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisMember

/-!
# Finite generic avoidance at fixed exceptional directions

At a fixed tangent direction, evaluation of the weak transform is a linear
form in the target coefficients. Avoiding its kernel whenever the form is
nonzero ensures that a zero of the member is a common zero of all weak
generators. A finite collection of these conditions is constructible by
the existing coefficient-choice theorem, together with exact recorded orders.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace WeakTransformIdealData

variable {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}

@[expose] noncomputable def rootWeakTransform
    (d : WeakTransformIdealData c ι) (ζ : ℂ) (i : ι) : Germ 2 :=
  pointBlowupTransform ζ (c.multiplicity c.root) (d.generators c.root i)
    (d.generator_mem_pow c.root i)

theorem rootWeakTransform_factor (d : WeakTransformIdealData c ι) (ζ : ℂ) (i : ι) :
    (pointBlowupChartGerm ζ).pullbackRingHom (d.generators c.root i) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root * d.rootWeakTransform ζ i :=
  pointBlowupTransform_factor ζ (c.multiplicity c.root) (d.generators c.root i)
    (d.generator_mem_pow c.root i)

@[expose] noncomputable def rootWeakValueLinearForm [Fintype ι]
    (d : WeakTransformIdealData c ι) (ζ : ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun q := ∑ i, q i * valueRingHom 2 (d.rootWeakTransform ζ i)
  map_add' q r := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a q := by simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Finset.mul_sum]

theorem rootWeakValueLinearForm_single [Fintype ι] [DecidableEq ι]
    (d : WeakTransformIdealData c ι) (ζ : ℂ) (i : ι) :
    d.rootWeakValueLinearForm ζ (Pi.single i 1) = valueRingHom 2 (d.rootWeakTransform ζ i) := by
  simp [rootWeakValueLinearForm, Pi.single_apply]

/-- A nonzero evaluation linear form is required not to vanish on the
chosen coefficients. If all generator values are zero, no condition is imposed. -/
@[expose] def AvoidsRootTangentCancellation [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (ζ : ℂ) : Prop :=
  d.rootWeakValueLinearForm ζ = 0 ∨ d.rootWeakValueLinearForm ζ q ≠ 0

/-- Any finite prescribed collection of tangent directions can be
avoided simultaneously with exact order at every recorded center. -/
theorem exists_coefficients_exact_orders_and_tangent_avoidance
    [Fintype ι] {κ : Type*} [Finite κ]
    (d : WeakTransformIdealData c ι) (directions : κ → ℂ) :
    ∃ q : ι → ℂ,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      ∀ j, d.AvoidsRootTangentCancellation q (directions j) := by
  classical
  let K := {j : κ // d.rootWeakValueLinearForm (directions j) ≠ 0}
  obtain ⟨q, horder, havoid⟩ := d.exists_coefficients_exact_orders_and_linear_conditions
    (fun j : K => d.rootWeakValueLinearForm (directions j.1)) (fun j => j.2)
  refine ⟨q, horder, ?_⟩
  intro j
  by_cases hz : d.rootWeakValueLinearForm (directions j) = 0
  · exact Or.inl hz
  · exact Or.inr (havoid ⟨j, hz⟩)

theorem rootWeakTransform_linearCombination [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (ζ : ℂ) :
    (pointBlowupChartGerm ζ).pullbackRingHom
        (germLinearCombination (d.generators c.root) q) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root *
        germLinearCombination (d.rootWeakTransform ζ) q := by
  change (pointBlowupChartGerm ζ).pullbackRingHom (∑ i, q i • d.generators c.root i) =
    coordinate (1 : Fin 2) ^ c.multiplicity c.root * ∑ i, q i • d.rootWeakTransform ζ i
  simp only [map_sum, PointedMapGerm.pullback_complex_smul, d.rootWeakTransform_factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_smul_comm _ _ _).symm

theorem rootWeakValueLinearForm_eq_value [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (ζ : ℂ) :
    d.rootWeakValueLinearForm ζ q =
      valueRingHom 2 (germLinearCombination (d.rootWeakTransform ζ) q) := by
  change (∑ i, q i * valueRingHom 2 (d.rootWeakTransform ζ i)) =
    valueRingHom 2 (∑ i, q i • d.rootWeakTransform ζ i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change q i * valueRingHom 2 (d.rootWeakTransform ζ i) =
    valueRingHom 2 (constRingHom 2 (q i) * d.rootWeakTransform ζ i)
  rw [map_mul, valueRingHom_const]

/-- The avoidance condition has the asserted geometric meaning for any
strict transform of the specified constant-coefficient member. -/
theorem rootWeakTransforms_mem_maximalIdeal_of_member_zero [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (ζ : ℂ)
    (havoid : d.AvoidsRootTangentCancellation q ζ)
    (v V : Germ 2) (hmember : v = germLinearCombination (d.generators c.root) q)
    (htransform : (pointBlowupChartGerm ζ).pullbackRingHom v =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root * V)
    (hV : V ∈ maximalIdeal 2) : ∀ i, d.rootWeakTransform ζ i ∈ maximalIdeal 2 := by
  classical
  have hVeq : V = germLinearCombination (d.rootWeakTransform ζ) q := by
    apply mul_left_cancel₀ (pow_ne_zero _ (coordinate_ne_zero (1 : Fin 2)))
    rw [← htransform, hmember, d.rootWeakTransform_linearCombination]
  have hvalue : d.rootWeakValueLinearForm ζ q = 0 := by
    rw [d.rootWeakValueLinearForm_eq_value, ← hVeq]
    exact mem_maximalIdeal_iff.mp hV
  have hzero : d.rootWeakValueLinearForm ζ = 0 := havoid.resolve_right (not_not_intro hvalue)
  intro i
  rw [mem_maximalIdeal_iff, ← d.rootWeakValueLinearForm_single ζ i, hzero]
  rfl

/-- Completeness records a root child of entry one when the member's
first transform is smooth. The original point basis and its source
coordinates remain unchanged. -/
theorem exists_root_child_entry_one_of_tangent_avoidance [Fintype ι]
    (d : WeakTransformIdealData c ι) (hcomplete : FiniteWeakBasepointCompleteness d)
    (q : ι → ℂ) (ζ : ℂ)
    (hmember : c.germ c.root = germLinearCombination (d.generators c.root) q)
    (havoid : d.AvoidsRootTangentCancellation q ζ)
    (V : Germ 2)
    (htransform : (pointBlowupChartGerm ζ).pullbackRingHom (c.germ c.root) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root * V)
    (hV : V ∈ maximalIdeal 2) (hVnext : V ∉ maximalIdeal 2 ^ 2) :
    ∃ p, c.ParentRelation p c.root ∧ c.multiplicity p = 1 := by
  have hzero := d.rootWeakTransforms_mem_maximalIdeal_of_member_zero q ζ havoid
    (c.germ c.root) V hmember htransform hV
  obtain ⟨p, hp, hcenter, hpreserve⟩ := hcomplete.realizes_common_zero c.root ζ
    (d.rootWeakTransform ζ) (d.rootWeakTransform_factor ζ) hzero
  have hvfix : (c.sourceCoordinates p).forward.pullbackRingHom (c.germ c.root) =
      c.germ c.root := by
    rw [hmember]
    change (c.sourceCoordinates p).forward.pullbackRingHom
      (∑ i, q i • d.generators c.root i) = ∑ i, q i • d.generators c.root i
    simp only [map_sum, PointedMapGerm.pullback_complex_smul, hpreserve]
  have hchart := c.transform_identity p hp.1
  rw [hp.2, hcenter, hvfix] at hchart
  have hVequal : c.germ p = V := by
    apply mul_left_cancel₀ (pow_ne_zero _ (coordinate_ne_zero (1 : Fin 2)))
    rw [← hchart, htransform]
  refine ⟨p, hp, ?_⟩
  have hbound : c.multiplicity p ≤ 1 := by
    by_contra hn
    apply hVnext
    rw [← hVequal]
    exact (Ideal.pow_le_pow_right (by omega)) (c.germ_mem p)
  have hpos := c.multiplicity_pos p
  omega

end WeakTransformIdealData

end OnLeConjecture.Analytic
