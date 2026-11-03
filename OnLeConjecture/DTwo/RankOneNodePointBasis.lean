/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitCubicPreparation
public import OnLeConjecture.Analytic.OrdinaryNodeBlowup
public import OnLeConjecture.Analytic.WeakTransformIdealData
public import OnLeConjecture.Numerical.PointBasisCountIdentities
public import OnLeConjecture.Numerical.SmallPointBasisCounts

/-!
# Point-basis counts for a rank-one ordinary node jet

The node is written in coordinates in which the generic member is `x²-y²`.
Both finite exceptional directions are common zeros of all weak generators,
so base-ideal completeness records two distinct children. Transversality of
the node factors bounds every other entry by one in arbitrary recorded
source coordinates. No count or coverage conclusion is assumed.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

private theorem orbitPhi_germ_eq :
    coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) =
      coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2 := by
  simp only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda, map_sub,
    map_pow, coordinatePolynomialAlgHom_X]

private theorem orbitPhi_factor_jacobian_unit :
    IsUnit (jacobian (coordinate (0 : Fin 2) - coordinate (1 : Fin 2))
      (coordinate (0 : Fin 2) + coordinate (1 : Fin 2))) := by
  apply isUnit_iff_valueRingHom_ne_zero.mpr
  norm_num [jacobian_eq, partialDerivative_sub, partialDerivative_add,
    partialDerivative_coordinate_same, partialDerivative_coordinate_ne]
  norm_num only [map_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

/-- The two transverse analytic factors give the actual irreducible branch
count of the normalized node. -/
theorem orbitPhi_irreducibleBranchCount_eq_two :
    PlaneCurve.irreducibleBranchCount
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) = 2 := by
  let f := coordinate (0 : Fin 2) - coordinate (1 : Fin 2)
  let g := coordinate (0 : Fin 2) + coordinate (1 : Fin 2)
  have hf : f ∈ maximalIdeal 2 :=
    (maximalIdeal 2).sub_mem (coordinate_mem_maximalIdeal 0) (coordinate_mem_maximalIdeal 1)
  have hg : g ∈ maximalIdeal 2 :=
    (maximalIdeal 2).add_mem (coordinate_mem_maximalIdeal 0) (coordinate_mem_maximalIdeal 1)
  have hJac : IsUnit (jacobian f g) := orbitPhi_factor_jacobian_unit
  have hfi := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hf
    (not_mem_square_of_jacobian_isUnit_left f g hJac)).2
  have hgi := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq g hg
    (not_mem_square_of_jacobian_isUnit_right f g hJac)).2
  have hnot : ¬ Associated f g := by
    rintro ⟨u, hu⟩
    apply valueRingHom_ne_zero_of_isUnit hJac
    rw [← hu, jacobian_mul_right, jacobian_self]
    simp only [mul_zero, add_zero, map_mul, mem_maximalIdeal_iff.mp hf, zero_mul]
  apply PlaneCurve.irreducibleBranchCount_eq_two_of_eq_mul _ f g hfi hgi hnot
  rw [orbitPhi_germ_eq]
  dsimp only [f, g]
  ring

/-- Every nonroot entry is one for an actual node generic member. The
recorded child charts may use arbitrary source coordinate equivalences. -/
theorem rank_one_node_nonroot_multiplicity_eq_one
    {N : ℕ} (c : AnalyticPointBasis N) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (p : Fin N) (hp : p ≠ c.root) : c.multiplicity p = 1 := by
  have hchildren : ∀ q, c.ParentRelation q c.root → c.multiplicity q ≤ 1 := by
    intro q hq
    let e := c.sourceCoordinates q
    let f := coordinate (0 : Fin 2) - coordinate (1 : Fin 2)
    let g := coordinate (0 : Fin 2) + coordinate (1 : Fin 2)
    have hf : f ∈ maximalIdeal 2 :=
      (maximalIdeal 2).sub_mem (coordinate_mem_maximalIdeal 0) (coordinate_mem_maximalIdeal 1)
    have hg : g ∈ maximalIdeal 2 :=
      (maximalIdeal 2).add_mem (coordinate_mem_maximalIdeal 0) (coordinate_mem_maximalIdeal 1)
    have hfactor : c.germ c.root = f * g := by rw [hv, orbitPhi_germ_eq]; dsimp [f, g]; ring
    have htransform := c.transform_identity q hq.1
    rw [hq.2, hroot, hfactor, map_mul] at htransform
    have hef : e.forward.pullbackRingHom f ∈ maximalIdeal 2 := by
      have h := e.forward.pullback_mem_maximalIdeal_pow
        (by simpa only [pow_one] using hf : f ∈ maximalIdeal 2 ^ 1)
      simpa only [pow_one] using h
    have heg : e.forward.pullbackRingHom g ∈ maximalIdeal 2 := by
      have h := e.forward.pullback_mem_maximalIdeal_pow
        (by simpa only [pow_one] using hg : g ∈ maximalIdeal 2 ^ 1)
      simpa only [pow_one] using h
    have hnot := pointBlowup_transverse_product_not_mem_square (c.chartCenter q)
      (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g) (c.germ q)
      hef heg
      (jacobian_isUnit_pullback_equiv e f g orbitPhi_factor_jacobian_unit) htransform
    by_contra hn
    exact hnot ((Ideal.pow_le_pow_right (by omega)) (c.germ_mem q))
  have hle := c.nonroot_multiplicity_le_of_root_children 1 hchildren p hp
  have hpos := c.multiplicity_pos p
  omega

/-- At either node direction all the explicitly constructed weak
generators vanish. This includes the two coordinates of order at least three. -/
theorem exists_rank_one_node_weak_common_zero
    (u w : Germ 2) (hu : u ∈ maximalIdeal 2 ^ 3) (hw : w ∈ maximalIdeal 2 ^ 3)
    (z : ℂ) (hz : z ^ 2 = 1) :
    ∃ H : Fin 3 → Germ 2,
      (∀ i, (pointBlowupChartGerm z).pullbackRingHom
          ((![coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ), u, w] : Fin 3 → Germ 2) i) =
        coordinate (1 : Fin 2) ^ 2 * H i) ∧
      ∀ i, H i ∈ maximalIdeal 2 := by
  let U := pointBlowupTransform z 3 u hu
  let W := pointBlowupTransform z 3 w hw
  let H₀ := (coordinate (0 : Fin 2) + constRingHom 2 z) ^ 2 - 1
  refine ⟨![H₀, coordinate (1 : Fin 2) * U, coordinate (1 : Fin 2) * W], ?_, ?_⟩
  · intro i
    fin_cases i
    · change (pointBlowupChartGerm z).pullbackRingHom
        (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) = coordinate (1 : Fin 2) ^ 2 * H₀
      rw [orbitPhi_germ_eq]
      simp only [map_sub, map_pow, pointBlowupChartGerm_pullback_zero,
        pointBlowupChartGerm_pullback_one]
      dsimp only [H₀]
      ring
    · change (pointBlowupChartGerm z).pullbackRingHom u = coordinate (1 : Fin 2) ^ 2 *
        (coordinate (1 : Fin 2) * U)
      simpa only [U, pow_succ, mul_assoc] using pointBlowupTransform_factor z 3 u hu
    · change (pointBlowupChartGerm z).pullbackRingHom w = coordinate (1 : Fin 2) ^ 2 *
        (coordinate (1 : Fin 2) * W)
      simpa only [W, pow_succ, mul_assoc] using pointBlowupTransform_factor z 3 w hw
  · intro i
    fin_cases i
    · apply mem_maximalIdeal_iff.mpr
      simp [H₀, hz]
    · exact (maximalIdeal 2).mul_mem_right U (coordinate_mem_maximalIdeal 1)
    · exact (maximalIdeal 2).mul_mem_right W (coordinate_mem_maximalIdeal 1)

/-- Completeness records the two distinct exceptional node directions. -/
theorem rank_one_node_two_distinct_children
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hf : d.generators c.root 0 = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hu : d.generators c.root 1 ∈ maximalIdeal 2 ^ 3)
    (hw : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3) :
    ∃ p q, c.ParentRelation p c.root ∧ c.ParentRelation q c.root ∧ p ≠ q := by
  have hchild (z : ℂ) (hz : z ^ 2 = 1) :
      ∃ q, c.ParentRelation q c.root ∧ c.chartCenter q = z := by
    obtain ⟨H, hH, hzero⟩ := exists_rank_one_node_weak_common_zero
      (d.generators c.root 1) (d.generators c.root 2) hu hw z hz
    have htrans : ∀ i, (pointBlowupChartGerm z).pullbackRingHom (d.generators c.root i) =
        coordinate (1 : Fin 2) ^ c.multiplicity c.root * H i := by
      intro i
      rw [hroot]
      fin_cases i
      · change (pointBlowupChartGerm z).pullbackRingHom (d.generators c.root 0) =
          coordinate (1 : Fin 2) ^ 2 * H 0
        simpa only [hf, Matrix.cons_val_zero] using hH 0
      · exact hH 1
      · exact hH 2
    obtain ⟨q, hq, hcenter, _⟩ := hcomplete.realizes_common_zero c.root z H htrans hzero
    exact ⟨q, hq, hcenter⟩
  obtain ⟨p, hp, hpz⟩ := hchild 1 (by norm_num)
  obtain ⟨q, hq, hqz⟩ := hchild (-1) (by norm_num)
  refine ⟨p, q, hp, hq, ?_⟩
  intro hpq
  have : (1 : ℂ) = -1 := hpz.symm.trans (hpq ▸ hqz)
  norm_num at this

/-- The actual node member and weak-ideal completeness give `A₂=1`,
`A₁≥2`, and the corresponding numerical sums. -/
theorem rank_one_node_complete_point_basis_counts
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hf : d.generators c.root 0 = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hu : d.generators c.root 1 ∈ maximalIdeal 2 ^ 3)
    (hw : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 1 ∧
      2 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.sum c.multiplicity =
        2 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity =
        4 + Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
  classical
  have hnonroot := rank_one_node_nonroot_multiplicity_eq_one c hroot hv
  have hset : Finset.univ.filter (fun p ↦ c.multiplicity p = 2) = {c.root} := by
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
  obtain ⟨p, q, hp, hq, hpq⟩ := rank_one_node_two_distinct_children d hcomplete hroot hf hu hw
  have hone : 2 ≤ Numerical.MultiplicityCounts.valueCount c.multiplicity 1 := by
    have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun z ↦ c.multiplicity z = 1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [hnonroot z hp.1]
      · simp [hnonroot z hq.1]
    change 2 ≤ (Finset.univ.filter (fun z ↦ c.multiplicity z = 1)).card
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

/-- The knot and polar reduction inequalities force the extremal node
counts and prove smoothness of the chosen maximal critical component.
The branch count and intersection lower bound are analytic conclusions. -/
theorem rank_one_node_extremal_reduction_data
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hcomplete : FiniteWeakBasepointCompleteness d) (hroot : c.multiplicity c.root = 2)
    (hv : c.germ c.root = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hf : d.generators c.root 0 = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hu : d.generators c.root 1 ∈ maximalIdeal 2 ^ 3)
    (hw : d.generators c.root 2 ∈ maximalIdeal 2 ^ 3)
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
    rank_one_node_complete_point_basis_counts d hcomplete hroot hv hf hu hw
  have hbranches : PlaneCurve.irreducibleBranchCount (c.germ c.root) = 2 := by
    rw [hv]
    exact orbitPhi_irreducibleBranchCount_eq_two
  have hfinite' : PlaneCurve.HasFiniteIntersection
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) h := hv ▸ hfinite
  have hbound := orbitPhi_intersection_lower_bound 1 h (by simpa only [pow_one] using hh) hfinite'
  have hai : 2 ≤ PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite := by
    simpa only [hv, mul_one] using hbound
  rw [hsum] at hMt
  rw [hbranches, hsum, hsq] at hpolar
  let A := Numerical.MultiplicityCounts.valueCount c.multiplicity 1
  let I := PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite
  have htsub : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have hproduct : 2 * (t - 1) ≤ I * (t - 1) := Nat.mul_le_mul_right _ hai
  have hA : A = 2 := by dsimp only [A, I] at *; nlinarith
  have ht : t = 4 := by dsimp only [A] at hA; rw [hA] at hMt hpolar; nlinarith
  have hI : I = 2 := by dsimp only [A] at hA; rw [hA, ht] at hpolar; dsimp only [I]; omega
  have hnot : h ∉ maximalIdeal 2 ^ 2 := by
    intro hsquare
    have hlarge := orbitPhi_intersection_lower_bound 2 h hsquare hfinite'
    have hI' : PlaneCurve.intersectionMultiplicity
        (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) h hfinite' = 2 := by
      simpa only [I, hv] using hI
    omega
  obtain ⟨hsmooth, hirred⟩ := smooth_irreducible_of_mem_maximalIdeal_not_mem_sq h hh hnot
  have hA' : Numerical.MultiplicityCounts.valueCount c.multiplicity 1 = 2 := hA
  refine ⟨htwo, hA, ?_, ?_, ht, hI, hsmooth, hirred⟩
  · simpa only [hA'] using hsum
  · simpa only [hA'] using hsq

end OnLeConjecture.DTwo
