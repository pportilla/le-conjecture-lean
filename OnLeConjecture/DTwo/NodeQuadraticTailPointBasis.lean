/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.RankOneNodePointBasis
public import OnLeConjecture.Analytic.NodeQuadraticTail
public import OnLeConjecture.Analytic.OrdinaryIntersectionBound

/-!
# Point-basis counts from a node quadratic jet

The generic member and weak generators remain the recorded analytic germs.
Only their quadratic jets are prescribed. Both exceptional node directions
are common zeros before any target normalization, so completeness and the
analytic transforms supply the counts in the original point basis.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem node_quadratic_tail_nonroot_multiplicity_eq_one
    {N : ℕ} (c : AnalyticPointBasis N) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
    (p : Fin N) (hp : p ≠ c.root) : c.multiplicity p = 1 := by
  have hv' : c.germ c.root -
      (coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2) ∈ maximalIdeal 2 ^ 3 := by
    simpa only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda,
      map_sub, map_pow, coordinatePolynomialAlgHom_X] using hv
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ :=
    exists_transverse_factors_of_differenceSquares_tail (c.germ c.root) hv'
  have hchildren : ∀ q, c.ParentRelation q c.root → c.multiplicity q ≤ 1 := by
    intro q hq
    let e := c.sourceCoordinates q
    have htransform := c.transform_identity q hq.1
    rw [hq.2, hroot, hfactor, map_mul] at htransform
    have hnot := pointBlowup_transverse_product_not_mem_square (c.chartCenter q)
      (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) (c.germ q)
      (e.forward.pullback_mem_maximalIdeal hf) (e.forward.pullback_mem_maximalIdeal hg)
      (jacobian_isUnit_pullback_equiv e f g hjac) htransform
    by_contra hn
    exact hnot ((Ideal.pow_le_pow_right (by omega)) (c.germ_mem q))
  have hle := c.nonroot_multiplicity_le_of_root_children 1 hchildren p hp
  have hpos := c.multiplicity_pos p
  omega

/-- Scalar multiples of the node jet all vanish at both exceptional
directions. Their higher-order terms are retained analytically. -/
theorem exists_weak_common_zero_of_node_scalar_tails
    {ι : Type*} (v : Germ 2)
    (hv : v - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3)
    (F : ι → Germ 2)
    (hF : ∀ i, ∃ b : ℂ, F i - constRingHom 2 b * v ∈ maximalIdeal 2 ^ 3)
    (z : ℂ) (hz : z ^ 2 = 1) :
    ∃ H : ι → Germ 2,
      (∀ i, (pointBlowupChartGerm z).pullbackRingHom (F i) =
        coordinate (1 : Fin 2) ^ 2 * H i) ∧
      ∀ i, H i ∈ maximalIdeal 2 := by
  classical
  obtain ⟨H₀, hH₀, hzero⟩ := exists_rank_one_node_weak_common_zero 0 0
    (Ideal.zero_mem _) (Ideal.zero_mem _) z hz
  choose b hb using hF
  let T : ι → Germ 2 := fun i => F i - constRingHom 2 (b i) *
    coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)
  have hT (i : ι) : T i ∈ maximalIdeal 2 ^ 3 := by
    have hadd := (maximalIdeal 2 ^ 3).add_mem (hb i)
      ((maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 (b i)) hv)
    convert hadd using 1
    dsimp only [T]
    ring
  let W : ι → Germ 2 := fun i => pointBlowupTransform z 3 (T i) (hT i)
  refine ⟨fun i => constRingHom 2 (b i) * H₀ 0 + coordinate (1 : Fin 2) * W i, ?_, ?_⟩
  · intro i
    have hFi : F i = constRingHom 2 (b i) *
        coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) + T i := by dsimp [T]; ring
    rw [hFi, map_add, map_mul, PointedMapGerm.pullback_constRingHom]
    have hphi := hH₀ 0
    change (pointBlowupChartGerm z).pullbackRingHom
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) =
        coordinate (1 : Fin 2) ^ 2 * H₀ 0 at hphi
    rw [hphi, pointBlowupTransform_factor z 3 (T i) (hT i)]
    change constRingHom 2 (b i) * (coordinate (1 : Fin 2) ^ 2 * H₀ 0) +
      coordinate 1 ^ 3 * W i = _
    ring
  · intro i
    exact (maximalIdeal 2).add_mem ((maximalIdeal 2).mul_mem_left _ (hzero 0))
      ((maximalIdeal 2).mul_mem_right _ (coordinate_mem_maximalIdeal 1))

theorem node_quadratic_tail_two_distinct_children
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
    (hjets : ∀ i, ∃ b : ℂ,
      d.generators c.root i - constRingHom 2 b * c.germ c.root ∈ maximalIdeal 2 ^ 3) :
    ∃ p q, c.ParentRelation p c.root ∧ c.ParentRelation q c.root ∧ p ≠ q := by
  have hchild (z : ℂ) (hz : z ^ 2 = 1) :
      ∃ q, c.ParentRelation q c.root ∧ c.chartCenter q = z := by
    obtain ⟨H, hH, hzero⟩ := exists_weak_common_zero_of_node_scalar_tails
      (c.germ c.root) hv (d.generators c.root) hjets z hz
    have htrans : ∀ i, (pointBlowupChartGerm z).pullbackRingHom (d.generators c.root i) =
        coordinate (1 : Fin 2) ^ c.multiplicity c.root * H i := by
      simpa only [hroot] using hH
    obtain ⟨q, hq, hcenter, _⟩ := hcomplete.realizes_common_zero c.root z H htrans hzero
    exact ⟨q, hq, hcenter⟩
  obtain ⟨p, hp, hpz⟩ := hchild 1 (by norm_num)
  obtain ⟨q, hq, hqz⟩ := hchild (-1) (by norm_num)
  refine ⟨p, q, hp, hq, ?_⟩
  intro hpq
  have : (1 : ℂ) = -1 := hpz.symm.trans (hpq ▸ hqz)
  norm_num at this

theorem node_quadratic_tail_complete_point_basis_counts
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
    (hjets : ∀ i, ∃ b : ℂ,
      d.generators c.root i - constRingHom 2 b * c.germ c.root ∈ maximalIdeal 2 ^ 3) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 ∧
      2 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.sum c.multiplicity =
        2 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity =
        4 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
  classical
  have hnonroot := node_quadratic_tail_nonroot_multiplicity_eq_one c hroot hv
  have hset : Finset.univ.filter (fun p => c.multiplicity p = 2) = {c.root} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      by_contra hn
      have := hnonroot p hn
      omega
    · rintro rfl
      exact hroot
  have htwo : Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 := by
    rw [Numerical.MultiplicityCounts.valueCount, hset, Finset.card_singleton]
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    node_quadratic_tail_two_distinct_children d hcomplete hroot hv hjets
  have hone : 2 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
    have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun z => c.multiplicity z = 1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [hnonroot z hp.1]
      · simp [hnonroot z hq.1]
    change 2 ≤ (Finset.univ.filter (fun z => c.multiplicity z = 1)).card
    simpa only [Finset.card_pair hpq] using Finset.card_le_card hsub
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
  exact ⟨htwo, hone, by simpa only [htwo, mul_one] using hsum,
    by simpa only [htwo, mul_one] using hsq⟩

theorem node_quadratic_tail_extremal_reduction_data
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
    (hjets : ∀ i, ∃ b : ℂ,
      d.generators c.root i - constRingHom 2 b * c.germ c.root ∈ maximalIdeal 2 ^ 3)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2) (t : ℕ)
    (hfinite : PlaneCurve.HasFiniteIntersection (c.germ c.root) h)
    (hMt : Numerical.MultiplicityCounts.sum c.multiplicity ≤ t)
    (hpolar : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite * (t - 1) +
      Numerical.MultiplicityCounts.sum c.multiplicity +
      PlaneCurve.irreducibleBranchCount (c.germ c.root) ≤
        2 * Numerical.MultiplicityCounts.squareSum c.multiplicity) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 1 = 2 ∧
      Numerical.MultiplicityCounts.sum c.multiplicity = 4 ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity = 6 ∧
      t = 4 ∧ PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite = 2 ∧
      differential h ≠ 0 ∧ Irreducible h := by
  obtain ⟨htwo, hone, hsum, hsq⟩ :=
    node_quadratic_tail_complete_point_basis_counts d hcomplete hroot hv hjets
  have hbranches : PlaneCurve.irreducibleBranchCount (c.germ c.root) = 2 := by
    apply irreducibleBranchCount_eq_two_of_differenceSquares_tail
    simpa only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda,
      map_sub, map_pow, coordinatePolynomialAlgHom_X] using hv
  have hvorder : c.germ c.root ∈ maximalIdeal 2 ^ 2 := by simpa only [hroot] using c.germ_mem c.root
  have hvnext : c.germ c.root ∉ maximalIdeal 2 ^ 3 := by
    simpa only [hroot] using c.germ_not_mem_succ c.root
  have hai : 2 ≤ PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite := by
    simpa only [mul_one] using ordinary_intersection_lower_bound 2 1 (by omega)
      (c.germ c.root) h hvorder hvnext (by simpa only [pow_one] using hh) hfinite
  rw [hsum] at hMt
  rw [hbranches, hsum, hsq] at hpolar
  let A := Numerical.MultiplicityCounts.valueCount c.multiplicity 1
  let I := PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite
  have htsub : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have hproduct : 2 * (t - 1) ≤ I * (t - 1) := Nat.mul_le_mul_right _ hai
  have hA : A = 2 := by dsimp only [A, I] at *; nlinarith
  have ht : t = 4 := by dsimp only [A] at hA; rw [hA] at hMt hpolar; nlinarith
  have hI : I = 2 := by dsimp only [A] at hA; rw [hA, ht] at hpolar; dsimp only [I]; omega
  obtain ⟨hsmooth, hirred⟩ := smooth_irreducible_of_intersection_lt_twice_order 2 (by omega)
    (c.germ c.root) h hvorder hvnext hh hfinite (by change I < 2 * 2; omega)
  have hA' : Numerical.MultiplicityCounts.valueCount c.multiplicity 1 = 2 := hA
  refine ⟨htwo, hA, ?_, ?_, ht, hI, hsmooth, hirred⟩
  · simpa only [hA'] using hsum
  · simpa only [hA'] using hsq

end OnLeConjecture.DTwo
