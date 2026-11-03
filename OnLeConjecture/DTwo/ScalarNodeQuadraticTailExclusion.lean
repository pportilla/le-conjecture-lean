/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.NodeQuadraticTailExclusion
public import OnLeConjecture.Analytic.PointBasisConstantScaling
public import OnLeConjecture.Analytic.UnitIntersection

/-!
# Node-jet exclusion without normalizing the generic coefficient in advance

The nonzero coefficient of the node jet is removed by a constant target
scaling. The recorded member is scaled by the same constant at every center.
The weak generators, blowup charts and their completeness remain unchanged.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ PlaneCurve

theorem exists_target_first_constant_scaling
    (F : PointedMapGerm 2 3) (a : ℂ) (ha : a ≠ 0) :
    ∃ G : PointedMapGerm 2 3, F.RightLeftEquivalent G ∧
      G.1.component 0 = constRingHom 2 a * F.1.component 0 ∧
      ∀ i : Fin 2, G.1.component i.succ = F.1.component i.succ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := !![a, 0, 0; 0, 1, 0; 0, 0, 1]
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix M
    (by simpa [M, Matrix.det_fin_three] using ha)
  have hcomp (i : Fin 3) : (T.forward.comp F).1.component i =
      ∑ j, constRingHom 2 (M i j) * F.1.component j := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← T.forward.pullback_coordinate i,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, F.pullback_coordinate]
  refine ⟨T.forward.comp F, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · simpa [M, Fin.sum_univ_succ] using hcomp 0
  · intro i
    fin_cases i
    · simpa [M, Fin.sum_univ_succ] using hcomp 1
    · simpa [M, Fin.sum_univ_succ] using hcomp 2

theorem scalar_rank_one_node_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ} {c : AnalyticPointBasis N}
    (d : WeakTransformIdealData c (Fin 3)) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2) (hgeneric : c.germ c.root = F.1.component 0)
    (a : ℂ) (ha : a ≠ 0)
    (hv : F.1.component 0 - constRingHom 2 a *
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3)
    (hweakjets : ∀ i, ∃ b : ℂ,
      d.generators c.root i - constRingHom 2 b * c.germ c.root ∈ maximalIdeal 2 ^ 3)
    (hjets : ∀ i : Fin 2, ∃ b : ℂ,
      F.1.component i.succ - constRingHom 2 b * F.1.component 0 ∈ maximalIdeal 2 ^ 3)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2) (t : ℕ)
    (hfiniteCritical : HasFiniteIntersection (F.1.component 0) h)
    (hMt : Numerical.MultiplicityCounts.sum c.multiplicity ≤ t)
    (hpolar : intersectionMultiplicity (F.1.component 0) h hfiniteCritical * (t - 1) +
      Numerical.MultiplicityCounts.sum c.multiplicity +
      irreducibleBranchCount (F.1.component 0) ≤
        2 * Numerical.MultiplicityCounts.squareSum c.multiplicity)
    (hminors : ∀ i : Fin 2, h ^ (t - 1) ∣ jacobian (F.1.component 0) (F.1.component i.succ))
    (selected : Fin 2)
    (hfinitePair : HasFiniteIntersection (F.1.component 0) (F.1.component selected.succ))
    (hpair : intersectionMultiplicity (F.1.component 0) (F.1.component selected.succ) hfinitePair =
      Numerical.MultiplicityCounts.squareSum c.multiplicity) :
    ¬ F.HasInjectiveRepresentative := by
  let C := constRingHom 2 a⁻¹
  have hC : IsUnit C := isUnit_of_valueRingHom_ne_zero (by simpa [C] using inv_ne_zero ha)
  have hCa : C * constRingHom 2 a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hcoeff (b : ℂ) : constRingHom 2 (b * a) * C = constRingHom 2 b := by
    change constRingHom 2 (b * a) * constRingHom 2 a⁻¹ = _
    rw [← map_mul, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  obtain ⟨G, hFG, hG0, hGi⟩ := exists_target_first_constant_scaling F a⁻¹ (inv_ne_zero ha)
  let c' := c.scaleMember a⁻¹ (inv_ne_zero ha)
  let d' := d.scaleMember a⁻¹ (inv_ne_zero ha)
  have hgeneric' : c'.germ c'.root = G.1.component 0 := by
    change C * c.germ c.root = _
    rw [hgeneric, hG0]
  have hv' : G.1.component 0 - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3 := by
    have ht := (maximalIdeal 2 ^ 3).mul_mem_left C hv
    simpa only [mul_sub, ← mul_assoc, hCa, one_mul, hG0] using ht
  have hweak' (i : Fin 3) : ∃ b : ℂ,
      d'.generators c'.root i - constRingHom 2 b * c'.germ c'.root ∈ maximalIdeal 2 ^ 3 := by
    obtain ⟨b, hb⟩ := hweakjets i
    refine ⟨b * a, ?_⟩
    change d.generators c.root i - constRingHom 2 (b * a) * (C * c.germ c.root) ∈ _
    simpa only [← mul_assoc, hcoeff] using hb
  have hjets' (i : Fin 2) : ∃ b : ℂ,
      G.1.component i.succ - constRingHom 2 b * G.1.component 0 ∈ maximalIdeal 2 ^ 3 := by
    obtain ⟨b, hb⟩ := hjets i
    refine ⟨b * a, ?_⟩
    rw [hGi, hG0]
    change F.1.component i.succ - constRingHom 2 (b * a) * (C * F.1.component 0) ∈ _
    simpa only [← mul_assoc, hcoeff] using hb
  have hfinite' : HasFiniteIntersection (G.1.component 0) h := by
    rw [hG0]
    exact (hasFiniteIntersection_unit_mul_left_iff C _ _ hC).mpr hfiniteCritical
  have hinter : intersectionMultiplicity (G.1.component 0) h hfinite' =
      intersectionMultiplicity (F.1.component 0) h hfiniteCritical := by
    simpa only [hG0] using intersectionMultiplicity_unit_mul_left C _ _ hC
      ((hasFiniteIntersection_unit_mul_left_iff C _ _ hC).mpr hfiniteCritical) hfiniteCritical
  have hbranches : irreducibleBranchCount (G.1.component 0) =
      irreducibleBranchCount (F.1.component 0) := by
    rw [hG0]
    exact irreducibleBranchCount_eq_of_associated (associated_unit_mul_left _ C hC)
  have hminors' (i : Fin 2) : h ^ (t - 1) ∣
      jacobian (G.1.component 0) (G.1.component i.succ) := by
    rw [hG0, hGi, Germ.jacobian_mul_left, Germ.jacobian_const_left]
    simpa only [zero_mul, mul_zero, add_zero, C] using dvd_mul_of_dvd_right (hminors i) C
  have hfinitePair' : HasFiniteIntersection (G.1.component 0) (G.1.component selected.succ) := by
    rw [hG0, hGi]
    exact (hasFiniteIntersection_unit_mul_left_iff C _ _ hC).mpr hfinitePair
  have hpair' : intersectionMultiplicity (G.1.component 0) (G.1.component selected.succ)
      hfinitePair' = Numerical.MultiplicityCounts.squareSum c'.multiplicity := by
    have hi := intersectionMultiplicity_unit_mul_left C _ _ hC
      ((hasFiniteIntersection_unit_mul_left_iff C _ _ hC).mpr hfinitePair) hfinitePair
    simpa only [hG0, hGi, C, c', AnalyticPointBasis.scaleMember] using hi.trans hpair
  intro hinjective
  apply rank_one_node_jet_reduction_not_hasInjectiveRepresentative G d'
    (d.finiteWeakBasepointCompleteness_scaleMember a⁻¹ (inv_ne_zero ha) hcomplete)
    hroot hgeneric' hv' hweak' hjets' h hh t hfinite' hMt ?_ hminors'
    selected hfinitePair' hpair' (hFG.hasInjectiveRepresentative hinjective)
  simpa only [hinter, hbranches, AnalyticPointBasis.scaleMember] using hpolar

end OnLeConjecture.DTwo
