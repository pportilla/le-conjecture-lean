/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.NodeQuadraticTailPointBasis
public import OnLeConjecture.DTwo.SmoothCriticalNodeOrbitExclusion
public import OnLeConjecture.DTwo.SquareJetExtremeReduction
public import OnLeConjecture.PlaneCurve.PairGeneratorChange

/-!
# Rank-one node-jet exclusion with the recorded generic member

The point-basis counts are obtained from the original generic member and
weak generators. Only afterward are scalar quadratic terms removed by an
invertible target change. This preserves the selected pair ideal and its
intersection number, without requiring new point-basis compatibility.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ PlaneCurve

theorem exists_target_last_scalar_subtraction
    (F : PointedMapGerm 2 3) (b c : ℂ) :
    ∃ G : PointedMapGerm 2 3, F.RightLeftEquivalent G ∧
      G.1.component 0 = F.1.component 0 ∧
      G.1.component 1 = F.1.component 1 - constRingHom 2 b * F.1.component 0 ∧
      G.1.component 2 = F.1.component 2 - constRingHom 2 c * F.1.component 0 := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; -b, 1, 0; -c, 0, 1]
  obtain ⟨e, he⟩ := exists_equiv_linear_matrix M (by simp [M, Matrix.det_fin_three])
  have he0 : e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 := by
    simpa [M, Fin.sum_univ_succ] using he 0
  have he1 : e.forward.pullbackRingHom (coordinate (1 : Fin 3)) =
      coordinate 1 - constRingHom 3 b * coordinate 0 := by
    have hh := he 1
    simp [M, Fin.sum_univ_succ] at hh
    simpa only [PointedMapGerm.pullbackRingHom_apply, sub_eq_add_neg, neg_mul, add_comm] using hh
  have he2 : e.forward.pullbackRingHom (coordinate (2 : Fin 3)) =
      coordinate 2 - constRingHom 3 c * coordinate 0 := by
    have hh := he 2
    simp [M, Fin.sum_univ_succ] at hh
    simpa only [PointedMapGerm.pullbackRingHom_apply, sub_eq_add_neg, neg_mul, add_comm] using hh
  refine ⟨e.forward.comp F, ?_, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · rw [PointedMapGerm.component_comp_eq_pullback, ← e.forward.pullback_coordinate 0,
      he0, F.pullback_coordinate]
  · rw [PointedMapGerm.component_comp_eq_pullback, ← e.forward.pullback_coordinate 1,
      he1, map_sub, map_mul, F.pullback_constRingHom, F.pullback_coordinate, F.pullback_coordinate]
  · rw [PointedMapGerm.component_comp_eq_pullback, ← e.forward.pullback_coordinate 2,
      he2, map_sub, map_mul, F.pullback_constRingHom, F.pullback_coordinate, F.pullback_coordinate]

theorem node_quadratic_tail_scalar_jets_intersection_six_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3)
    (hv : F.1.component 0 - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
    (hsecond : ∃ b : ℂ, F.1.component 1 - constRingHom 2 b * F.1.component 0 ∈
      maximalIdeal 2 ^ 3)
    (hthird : ∃ b : ℂ, F.1.component 2 - constRingHom 2 b * F.1.component 0 ∈
      maximalIdeal 2 ^ 3)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2) (hdh : differential h ≠ 0)
    (hfiniteCritical : HasFiniteIntersection (F.1.component 0) h)
    (hcritical : intersectionMultiplicity (F.1.component 0) h hfiniteCritical = 2)
    (hfinitePair : HasFiniteIntersection (F.1.component 0) (F.1.component 1))
    (hpair : intersectionMultiplicity (F.1.component 0) (F.1.component 1) hfinitePair = 6)
    (hminor12 : h ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 1))
    (hminor13 : h ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 2)) :
    ¬ F.HasInjectiveRepresentative := by
  obtain ⟨b, hb⟩ := hsecond
  obtain ⟨c, hc⟩ := hthird
  obtain ⟨G, hFG, hG0, hG1, hG2⟩ := exists_target_last_scalar_subtraction F b c
  have hv' : F.1.component 0 -
      (coordinate (0 : Fin 2) ^ 2 - coordinate (1 : Fin 2) ^ 2) ∈ maximalIdeal 2 ^ 3 := by
    simpa only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda,
      map_sub, map_pow, coordinatePolynomialAlgHom_X] using hv
  obtain ⟨f, g, hfactor, hf, hg, hjac⟩ :=
    exists_transverse_factors_of_differenceSquares_tail (F.1.component 0) hv'
  have hcritFinite : HasFiniteIntersection h (G.1.component 0) := by
    rw [hG0]
    exact (hasFiniteIntersection_comm _ _).mp hfiniteCritical
  have hcrit : intersectionMultiplicity h (G.1.component 0) hcritFinite = 2 := by
    simpa only [hG0] using
      (intersectionMultiplicity_comm _ _ hfiniteCritical).symm.trans hcritical
  have hfiniteG : HasFiniteIntersection (G.1.component 0) (G.1.component 1) := by
    rw [hG0, hG1]
    simpa only [mul_comm] using hfinitePair.sub_mul_right (q := constRingHom 2 b)
  have hpairG : intersectionMultiplicity (G.1.component 0) (G.1.component 1) hfiniteG = 6 := by
    have hi := intersectionMultiplicity_sub_mul_right (q := constRingHom 2 b) hfinitePair
    simpa only [hG0, hG1, mul_comm] using hi.trans hpair
  have hJ (u : Germ 2) (z : ℂ) :
      jacobian (F.1.component 0) (u - constRingHom 2 z * F.1.component 0) =
        jacobian (F.1.component 0) u := by
    rw [Germ.jacobian_sub_right, Germ.jacobian_mul_right,
      Germ.jacobian_const_right, Germ.jacobian_self]
    ring
  intro hinjective
  apply smooth_critical_node_intersection_six_not_hasInjectiveRepresentative G h f g
    (hG0.trans hfactor) hf hg hjac hh hdh hcritFinite hcrit
    (hG1 ▸ hb) (hG2 ▸ hc) hfiniteG hpairG ?_ ?_ (hFG.hasInjectiveRepresentative hinjective)
  · rwa [hG0, hG1, hJ]
  · rwa [hG0, hG2, hJ]

/-- The original node generic member and weak point basis exclude
injectivity. The chosen pair is retained through all target changes. -/
theorem rank_one_node_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ} {c : AnalyticPointBasis N}
    (d : WeakTransformIdealData c (Fin 3)) (hcomplete : FiniteWeakBasepointCompleteness d)
    (hroot : c.multiplicity c.root = 2) (hgeneric : c.germ c.root = F.1.component 0)
    (hv : F.1.component 0 - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      maximalIdeal 2 ^ 3)
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
  have hfiniteRoot : HasFiniteIntersection (c.germ c.root) h := by rwa [hgeneric]
  obtain ⟨_, _, _, hsquares, ht, hi, hsmooth, _⟩ :=
    node_quadratic_tail_extremal_reduction_data d hcomplete hroot
      (by rwa [hgeneric]) hweakjets h hh t hfiniteRoot hMt (by simpa only [hgeneric] using hpolar)
  obtain ⟨G, hFG, hG0, hG1, hothers⟩ := exists_target_selected_second F selected
  have hfiniteG : HasFiniteIntersection (G.1.component 0) (G.1.component 1) := by
    rwa [hG0, hG1]
  have hpairG : intersectionMultiplicity (G.1.component 0) (G.1.component 1) hfiniteG = 6 := by
    simpa only [hG0, hG1, hsquares] using hpair
  have hfiniteCritG : HasFiniteIntersection (G.1.component 0) h := by rwa [hG0]
  have hcritG : intersectionMultiplicity (G.1.component 0) h hfiniteCritG = 2 := by
    simpa only [hG0, hgeneric] using hi
  have hjetsG (i : Fin 2) : ∃ b : ℂ,
      G.1.component i.succ - constRingHom 2 b * G.1.component 0 ∈ maximalIdeal 2 ^ 3 := by
    obtain ⟨j, hj⟩ := hothers i
    simpa only [hj, hG0] using hjets j
  have hminorsG (i : Fin 2) : h ^ 3 ∣ jacobian (G.1.component 0) (G.1.component i.succ) := by
    obtain ⟨j, hj⟩ := hothers i
    simpa only [hj, hG0, ht] using hminors j
  intro hinjective
  exact node_quadratic_tail_scalar_jets_intersection_six_not_hasInjectiveRepresentative G
    (by rwa [hG0]) (hjetsG 0) (hjetsG 1) h hh hsmooth hfiniteCritG hcritG hfiniteG hpairG
    (hminorsG 0) (hminorsG 1) (hFG.hasInjectiveRepresentative hinjective)

end OnLeConjecture.DTwo
