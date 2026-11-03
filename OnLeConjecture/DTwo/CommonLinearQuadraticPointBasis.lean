/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakTransformIdealData
public import OnLeConjecture.Analytic.CoordinatePermutation
public import OnLeConjecture.DTwo.CommonLinearQuadraticBlowup
public import OnLeConjecture.Numerical.SmallPointBasisCounts
public import OnLeConjecture.Numerical.PointBasisCountIdentities
import Mathlib.Tactic

/-!
# Point-basis counts for the common-linear quadratic jet

Weak-transform generator identities bound every immediate root child by
one. Analytic multiplicity monotonicity then bounds every nonroot point.
Completeness at common zeros of the weak ideal records the explicitly
constructed common base point, proving that at least one entry is one.
Neither count nor a coverage conclusion is a hypothesis.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The recorded root edges use the common finite coordinates or their
coordinate interchange, on all weak generators. -/
structure RootWeakChartCompatibility {N : ℕ} {c : AnalyticPointBasis N}
    (d : WeakTransformIdealData c (Fin 3)) : Prop where
  charts : ∀ q, c.ParentRelation q c.root →
    (∀ i, (c.sourceCoordinates q).forward.pullbackRingHom (d.generators c.root i) =
      d.generators c.root i) ∨
    (∀ i, (c.sourceCoordinates q).forward.pullbackRingHom (d.generators c.root i) =
      (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (d.generators c.root i))

private theorem swap_pullback_coordinate_one :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      (coordinate (1 : Fin 2)) = coordinate (0 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv]
  apply Subtype.ext
  change ((MapGerm.ofFunction (coordinateSwapEquiv (1 : Fin 2))
    ((coordinateSwapEquiv (1 : Fin 2)).analyticAt 0)).component 1).1 = (coordinate (0 : Fin 2)).1
  rw [MapGerm.component_ofFunction, coe_coordinate]
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) z) 1 = z 0
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) z 0
  simpa using h

private theorem coordinateSwap_preserves_xy_tail (g : Germ 2)
    (hg : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3) :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom g -
      coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3 := by
  have h := PointedMapGerm.pullback_mem_maximalIdeal_pow
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward hg
  rw [map_sub, map_mul, swap_pullback_coordinate_one, PointedMapGerm.pullback_coordinate,
    coordinateSwapPointedEquiv_component_zero] at h
  change (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom g -
    coordinate (1 : Fin 2) * coordinate (0 : Fin 2) ∈ maximalIdeal 2 ^ 3 at h
  rwa [mul_comm (coordinate (1 : Fin 2)) (coordinate (0 : Fin 2))] at h

/-- A root child contains the transformed `xy` generator, whose linear
exceptional term proves that the recorded ideal order is at most one. -/
theorem common_linear_root_child_multiplicity_le_one
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hroot : c.multiplicity c.root = 2)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (q : Fin N) (hq : c.ParentRelation q c.root) : c.multiplicity q ≤ 1 := by
  let g := (c.sourceCoordinates q).forward.pullbackRingHom (d.generators c.root 1)
  have hgt : g - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈ maximalIdeal 2 ^ 3 := by
    rcases hcharts.charts q hq with hfinite | hswap
    · simpa only [g, hfinite 1] using hg
    · simpa only [g, hswap 1] using coordinateSwap_preserves_xy_tail _ hg
  obtain ⟨G, hG, _hres, hGnot, _hvalue⟩ :=
    exists_common_linear_quadratic_second_transform g hgt (c.chartCenter q)
  have hedge := d.transform_identity q hq.1 (1 : Fin 3)
  rw [hq.2, hroot] at hedge
  have hGeq : G = d.generators q 1 :=
    pointBlowupTransform_unique (c.chartCenter q) 2 g G (d.generators q 1) hG hedge
  exact d.multiplicity_le_of_generator_not_mem_pow q 1 1 (by rwa [← hGeq])

/-- Every nonroot entry is one. Root paths supply the necessary coverage. -/
theorem common_linear_nonroot_multiplicity_eq_one
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hroot : c.multiplicity c.root = 2)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (q : Fin N) (hq : q ≠ c.root) : c.multiplicity q = 1 := by
  have hle := c.nonroot_multiplicity_le_of_root_children 1
    (common_linear_root_child_multiplicity_le_one d hcharts hroot hg) q hq
  have hpos := c.multiplicity_pos q
  omega

/-- The origin is the unique order-two entry. -/
theorem common_linear_count_two_eq_one
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hroot : c.multiplicity c.root = 2)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 := by
  classical
  have hset : Finset.univ.filter (fun q ↦ c.multiplicity q = 2) = {c.root} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro htwo
      by_contra hq
      have := common_linear_nonroot_multiplicity_eq_one d hcharts hroot hg q hq
      omega
    · rintro rfl
      exact hroot
  rw [Numerical.MultiplicityCounts.valueCount, hset, Finset.card_singleton]

/-- Base-ideal completeness records the explicitly constructed common
zero. This proves existence of an order-one entry despite smoothness of
the generic member there. -/
theorem common_linear_exists_entry_one_of_basepoint_completeness
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : d.generators c.root 2 -
      (constRingHom 2 α * d.generators c.root 0 + constRingHom 2 β * d.generators c.root 1) ∈
        maximalIdeal 2 ^ 3) :
    ∃ q, c.ParentRelation q c.root ∧ c.multiplicity q = 1 := by
  obtain ⟨F, G, W, hF, hG, hW, hmax, _hnot⟩ :=
    exists_common_linear_quadratic_weak_ideal_order_one
      (d.generators c.root 0) (d.generators c.root 1) (d.generators c.root 2) hf hg α β hw
  have htrans : ∀ i : Fin 3, (pointBlowupChartGerm 0).pullbackRingHom (d.generators c.root i) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root * (![F, G, W] : Fin 3 → Germ 2) i := by
    intro i
    rw [hroot]
    fin_cases i
    · exact hF
    · exact hG
    · exact hW
  have hzero : ∀ i : Fin 3, (![F, G, W] : Fin 3 → Germ 2) i ∈ maximalIdeal 2 := by
    intro i
    apply hmax
    apply Ideal.subset_span
    fin_cases i <;> simp
  obtain ⟨q, hq, _hcenter, _hcoordinates⟩ :=
    hcomplete.realizes_common_zero c.root 0 ![F, G, W] htrans hzero
  exact ⟨q, hq, common_linear_nonroot_multiplicity_eq_one d hcharts hroot hg q hq.1⟩

/-- Both counts and both numerical sums follow from the weak-generator
chart identities and basepoint completeness. -/
theorem common_linear_complete_point_basis_counts
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : d.generators c.root 2 -
      (constRingHom 2 α * d.generators c.root 0 + constRingHom 2 β * d.generators c.root 1) ∈
        maximalIdeal 2 ^ 3) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 ∧
      1 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.sum c.multiplicity =
        2 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity =
        4 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
  classical
  have htwo := common_linear_count_two_eq_one d hcharts hroot hg
  obtain ⟨q, _hq, hone⟩ := common_linear_exists_entry_one_of_basepoint_completeness
    d hcharts hcomplete hroot hf hg α β hw
  have hcount : 1 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
    exact Finset.card_pos.mpr ⟨q, by simp [hone]⟩
  have hsum := c.toPointBasisCertificate.S_eq_two_mul_count_two_add_count_one
    hroot c.multiplicity_pos
  have hsq := c.toPointBasisCertificate.M_eq_four_mul_count_two_add_count_one
    hroot c.multiplicity_pos
  change Numerical.MultiplicityCounts.sum c.multiplicity =
    2 * Numerical.MultiplicityCounts.valueCount c.multiplicity 2 +
      Numerical.MultiplicityCounts.valueCount c.multiplicity 1 at hsum
  change Numerical.MultiplicityCounts.squareSum c.multiplicity =
    4 * Numerical.MultiplicityCounts.valueCount c.multiplicity 2 +
      Numerical.MultiplicityCounts.valueCount c.multiplicity 1 at hsq
  exact ⟨htwo, hcount, by simpa only [htwo, mul_one] using hsum,
    by simpa only [htwo, mul_one] using hsq⟩

/-- Ideal membership of the supplied generic member forces its quadratic
jet into the common-linear pencil. Analytic coefficients are replaced by
their values only modulo the proved cubic remainder. -/
theorem common_linear_generic_member_quadratic_tail
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : d.generators c.root 2 -
      (constRingHom 2 α * d.generators c.root 0 + constRingHom 2 β * d.generators c.root 1) ∈
        maximalIdeal 2 ^ 3) :
    ∃ a b : ℂ, c.germ c.root - coordinate (0 : Fin 2) *
      (constRingHom 2 a * coordinate (0 : Fin 2) +
        constRingHom 2 b * coordinate (1 : Fin 2)) ∈ maximalIdeal 2 ^ 3 := by
  have hv := d.generic_member_mem c.root
  change c.germ c.root ∈ Submodule.span (Germ 2) (Set.range (d.generators c.root)) at hv
  rw [Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨z, hz⟩ := hv
  simp only [Fin.sum_univ_three, smul_eq_mul] at hz
  let A := z 0 + z 2 * constRingHom 2 α
  let B := z 1 + z 2 * constRingHom 2 β
  have hco (q : Germ 2) : q - constRingHom 2 (valueRingHom 2 q) ∈ maximalIdeal 2 := by
    simp [mem_maximalIdeal_iff]
  have hmem (i : Fin 3) : d.generators c.root i ∈ maximalIdeal 2 ^ 2 := by
    simpa only [hroot] using d.generator_mem_pow c.root i
  have hA : (A - constRingHom 2 (valueRingHom 2 A)) * d.generators c.root 0 ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul (hco A) (hmem 0)
  have hB : (B - constRingHom 2 (valueRingHom 2 B)) * d.generators c.root 1 ∈
      maximalIdeal 2 ^ 3 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul (hco B) (hmem 1)
  have hW := Ideal.mul_mem_left (maximalIdeal 2 ^ 3) (z 2) hw
  have hconst : c.germ c.root -
      (constRingHom 2 (valueRingHom 2 A) * d.generators c.root 0 +
        constRingHom 2 (valueRingHom 2 B) * d.generators c.root 1) ∈ maximalIdeal 2 ^ 3 := by
    have heq : c.germ c.root -
        (constRingHom 2 (valueRingHom 2 A) * d.generators c.root 0 +
          constRingHom 2 (valueRingHom 2 B) * d.generators c.root 1) =
        (A - constRingHom 2 (valueRingHom 2 A)) * d.generators c.root 0 +
        (B - constRingHom 2 (valueRingHom 2 B)) * d.generators c.root 1 +
        z 2 * (d.generators c.root 2 -
          (constRingHom 2 α * d.generators c.root 0 +
            constRingHom 2 β * d.generators c.root 1)) := by
      rw [← hz]
      dsimp only [A, B]
      ring
    rw [heq]
    exact Ideal.add_mem _ (Ideal.add_mem _ hA hB) hW
  refine ⟨valueRingHom 2 A, valueRingHom 2 B, ?_⟩
  have hft := Ideal.mul_mem_left (maximalIdeal 2 ^ 3) (constRingHom 2 (valueRingHom 2 A)) hf
  have hgt := Ideal.mul_mem_left (maximalIdeal 2 ^ 3) (constRingHom 2 (valueRingHom 2 B)) hg
  convert Ideal.add_mem _ (Ideal.add_mem _ hconst hft) hgt using 1
  ring

/-- The complete common-linear branch, conditional only on the weak-ideal
resolution inputs and the displayed reduction inequalities. The branch
number lower bound `b≥2` is retained explicitly. -/
theorem common_linear_quadratic_excluded_of_complete_weak_point_basis
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcharts : RootWeakChartCompatibility d) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
    (hg : d.generators c.root 1 - coordinate (0 : Fin 2) * coordinate (1 : Fin 2) ∈
      maximalIdeal 2 ^ 3)
    (α β : ℂ)
    (hw : d.generators c.root 2 -
      (constRingHom 2 α * d.generators c.root 0 + constRingHom 2 β * d.generators c.root 1) ∈
        maximalIdeal 2 ^ 3)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2) (t b i : ℕ) (hb : 2 ≤ b)
    (hMt : Numerical.MultiplicityCounts.sum c.multiplicity ≤ t)
    (hNoether : i = Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hdiv : h ^ (t - 1) ∣ jacobian (d.generators c.root 0) (d.generators c.root 1))
    (hfinite : PlaneCurve.HasFiniteIntersection h (c.germ c.root))
    (hpolar : PlaneCurve.intersectionMultiplicity h (c.germ c.root) hfinite * (t - 1) +
      Numerical.MultiplicityCounts.sum c.multiplicity + b ≤ 2 * i) : False := by
  obtain ⟨_htwo, hone, hsum, hsq⟩ := common_linear_complete_point_basis_counts
    d hcharts hcomplete hroot hf hg α β hw
  obtain ⟨a, b', htail⟩ := common_linear_generic_member_quadratic_tail d hroot hf hg α β hw
  apply common_linear_quadratic_excluded_of_point_counts
    (d.generators c.root 0) (d.generators c.root 1) h (c.germ c.root) hf hg hh t
    (Numerical.MultiplicityCounts.valueCount c.multiplicity 1) hone
    (by rwa [← hsum]) hdiv a b' htail hfinite
  rw [hNoether, hsq, hsum] at hpolar
  omega

end OnLeConjecture.DTwo
