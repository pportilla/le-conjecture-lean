/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisGeometryTransport
public import OnLeConjecture.Analytic.ProjectiveCriticalFirstBlowup

/-!
# Generic avoidance and weak basepoints in both root charts

Completeness refers to the fixed weak generators in the finite and
complementary charts. A fixed projective direction determines a linear
condition on the coefficients. Its avoidance, together with a smooth
member transform, constructs a recorded child of multiplicity one.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Coverage of common zeros of the root weak generators in both charts.
The recorded source coordinate map must agree on each generator with
the indicated finite or complementary parent chart. -/
structure RootTwoChartWeakBasepointCompleteness
    {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}
    (d : WeakTransformIdealData c ι) : Prop where
  realizes_common_zero : ∀ (t : Option ℂ) (G : ι → Germ 2),
    (∀ i, (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom (d.generators c.root i)) =
        coordinate (1 : Fin 2) ^ c.multiplicity c.root * G i) →
    (∀ i, G i ∈ maximalIdeal 2) →
    ∃ p, c.ParentRelation p c.root ∧ c.chartCenter p = projectiveChartCenter t ∧
      ∀ i, (c.sourceCoordinates p).forward.pullbackRingHom (d.generators c.root i) =
        (projectiveChartSource t).forward.pullbackRingHom (d.generators c.root i)

namespace WeakTransformIdealData

variable {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}

@[expose] noncomputable def rootProjectiveWeakTransform
    (d : WeakTransformIdealData c ι) (t : Option ℂ) (i : ι) : Germ 2 :=
  pointBlowupTransform (projectiveChartCenter t) (c.multiplicity c.root)
    ((projectiveChartSource t).forward.pullbackRingHom (d.generators c.root i))
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow
      (d.generator_mem_pow c.root i))

theorem rootProjectiveWeakTransform_factor
    (d : WeakTransformIdealData c ι) (t : Option ℂ) (i : ι) :
    (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom (d.generators c.root i)) =
        coordinate (1 : Fin 2) ^ c.multiplicity c.root *
          d.rootProjectiveWeakTransform t i :=
  pointBlowupTransform_factor _ _ _ _

@[expose] noncomputable def rootProjectiveWeakValueLinearForm [Fintype ι]
    (d : WeakTransformIdealData c ι) (t : Option ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun q := ∑ i, q i * valueRingHom 2 (d.rootProjectiveWeakTransform t i)
  map_add' q r := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a q := by simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Finset.mul_sum]

@[expose] def AvoidsRootProjectiveTangentCancellation [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (t : Option ℂ) : Prop :=
  d.rootProjectiveWeakValueLinearForm t = 0 ∨ d.rootProjectiveWeakValueLinearForm t q ≠ 0

theorem exists_coefficients_exact_orders_projective_tangent_avoidance_mem_open
    [Fintype ι] {κ : Type*} [Finite κ]
    (d : WeakTransformIdealData c ι) (directions : κ → Option ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      ∀ j, d.AvoidsRootProjectiveTangentCancellation q (directions j) := by
  classical
  let K := {j : κ // d.rootProjectiveWeakValueLinearForm (directions j) ≠ 0}
  obtain ⟨q, hqU, horder, havoid⟩ :=
    d.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun j : K => d.rootProjectiveWeakValueLinearForm (directions j.1))
      (fun j => j.2) U hU hUne
  refine ⟨q, hqU, horder, ?_⟩
  intro j
  by_cases hz : d.rootProjectiveWeakValueLinearForm (directions j) = 0
  · exact Or.inl hz
  · exact Or.inr (havoid ⟨j, hz⟩)

theorem rootProjectiveWeakTransform_linearCombination [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (t : Option ℂ) :
    (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom
        (germLinearCombination (d.generators c.root) q)) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root *
        germLinearCombination (d.rootProjectiveWeakTransform t) q := by
  change (pointBlowupChartGerm _).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom (∑ i, q i • d.generators c.root i)) =
    coordinate (1 : Fin 2) ^ c.multiplicity c.root *
      ∑ i, q i • d.rootProjectiveWeakTransform t i
  simp only [map_sum, PointedMapGerm.pullback_complex_smul,
    d.rootProjectiveWeakTransform_factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_smul_comm _ _ _).symm

theorem rootProjectiveWeakValueLinearForm_eq_value [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ) (t : Option ℂ) :
    d.rootProjectiveWeakValueLinearForm t q =
      valueRingHom 2 (germLinearCombination (d.rootProjectiveWeakTransform t) q) := by
  change (∑ i, q i * valueRingHom 2 (d.rootProjectiveWeakTransform t i)) =
    valueRingHom 2 (∑ i, q i • d.rootProjectiveWeakTransform t i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change q i * valueRingHom 2 (d.rootProjectiveWeakTransform t i) =
    valueRingHom 2 (constRingHom 2 (q i) * d.rootProjectiveWeakTransform t i)
  rw [map_mul, valueRingHom_const]

theorem exists_root_child_entry_one_of_projective_tangent_avoidance [Fintype ι]
    (d : WeakTransformIdealData c ι) (hcomplete : RootTwoChartWeakBasepointCompleteness d)
    (q : ι → ℂ) (t : Option ℂ)
    (hmember : c.germ c.root = germLinearCombination (d.generators c.root) q)
    (havoid : d.AvoidsRootProjectiveTangentCancellation q t)
    (V : Germ 2)
    (htransform : (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
      ((projectiveChartSource t).forward.pullbackRingHom (c.germ c.root)) =
        coordinate (1 : Fin 2) ^ c.multiplicity c.root * V)
    (hV : V ∈ maximalIdeal 2) (hVnext : V ∉ maximalIdeal 2 ^ 2) :
    ∃ p, c.ParentRelation p c.root ∧ c.multiplicity p = 1 := by
  classical
  have hVeq : V = germLinearCombination (d.rootProjectiveWeakTransform t) q := by
    apply mul_left_cancel₀ (pow_ne_zero _ (coordinate_ne_zero (1 : Fin 2)))
    rw [← htransform, hmember, d.rootProjectiveWeakTransform_linearCombination]
  have hvalue : d.rootProjectiveWeakValueLinearForm t q = 0 := by
    rw [d.rootProjectiveWeakValueLinearForm_eq_value, ← hVeq]
    exact mem_maximalIdeal_iff.mp hV
  have hzero : d.rootProjectiveWeakValueLinearForm t = 0 :=
    havoid.resolve_right (not_not_intro hvalue)
  have hzeroEach (i : ι) : d.rootProjectiveWeakTransform t i ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    have hz := LinearMap.congr_fun hzero (Pi.single i 1)
    simpa [rootProjectiveWeakValueLinearForm, Pi.single_apply] using hz
  obtain ⟨p, hp, hcenter, hpreserve⟩ := hcomplete.realizes_common_zero t
    (d.rootProjectiveWeakTransform t) (d.rootProjectiveWeakTransform_factor t) hzeroEach
  have hvfix : (c.sourceCoordinates p).forward.pullbackRingHom (c.germ c.root) =
      (projectiveChartSource t).forward.pullbackRingHom (c.germ c.root) := by
    rw [hmember]
    change (c.sourceCoordinates p).forward.pullbackRingHom
      (∑ i, q i • d.generators c.root i) =
      (projectiveChartSource t).forward.pullbackRingHom (∑ i, q i • d.generators c.root i)
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

theorem rootTwoChartWeakBasepointCompleteness_linearCombination [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1))
    (hcomplete : RootTwoChartWeakBasepointCompleteness d) :
    RootTwoChartWeakBasepointCompleteness (d.weakDataOfLinearCombination q hq) where
  realizes_common_zero := hcomplete.realizes_common_zero

theorem avoidsRootProjectiveTangentCancellation_linearCombination [Fintype ι]
    (d : WeakTransformIdealData c ι) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
      germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1))
    (t : Option ℂ) (havoid : d.AvoidsRootProjectiveTangentCancellation q t) :
    (d.weakDataOfLinearCombination q hq).AvoidsRootProjectiveTangentCancellation q t := havoid

end WeakTransformIdealData

end OnLeConjecture.Analytic
