/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAnalyticEndpoint
public import OnLeConjecture.DTwo.QuadraticJetCubicNormalization
public import OnLeConjecture.Analytic.SecondPowerIntersection
public import OnLeConjecture.Analytic.UnitIntersection
public import OnLeConjecture.Analytic.WeightedInitialFormExistence
public import OnLeConjecture.Analytic.DiagonalCoordinates
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Cubic preparation in the squarefree quadratic branch

The first coordinate and the critical coordinate are already aligned here:
the first is `s²-λ²`, and the relevant Jacobian minors are divisible by
`λ³`. An actual intersection number six forces a nonzero cubic term in
the second coordinate. The cubic normal form is then a conclusion of
Jacobian divisibility, not an endpoint assumption.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ
open _root_.Polynomial

theorem orbitPhi_intersection_lower_bound (L : ℕ) (H : Germ 2)
    (hH : H ∈ maximalIdeal 2 ^ L)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) H) :
    2 * L ≤ PlaneCurve.intersectionMultiplicity
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) H hfinite := by
  let P : Polynomial (Germ 1) := X ^ 2 + C (-(coordinate (0 : Fin 1) ^ 2))
  have hP : P.Monic := monic_X_pow_add_C _ (by decide)
  have hPm : P.natDegree = 2 := natDegree_X_pow_add_C
  have hcoeff : ∀ i, i < 2 → P.coeff i ∈ maximalIdeal 1 ^ (1 * (2 - i)) := by
    intro i hi
    interval_cases i
    · simpa only [P, coeff_add, coeff_X_pow, coeff_C, Nat.reduceEqDiff, if_false,
        if_true, zero_add, one_mul, Nat.sub_zero] using
        (maximalIdeal 1 ^ 2).neg_mem (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
    · simp only [P, coeff_add, coeff_X_pow, coeff_C, Nat.reduceEqDiff, if_false,
        zero_add, Ideal.zero_mem]
  have heval : firstCoordinatePolynomialEvaluation P =
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) := by
    simp only [P, firstCoordinatePolynomialEvaluation, eval₂_add, eval₂_pow, eval₂_neg,
      eval₂_X, eval₂_C, map_neg, map_pow, map_add, hyperplaneExtension_coordinate,
      orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda,
      coordinatePolynomialAlgHom_X, sub_eq_add_neg]
    rfl
  have hfinite' : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H :=
    heval ▸ hfinite
  have hbound := weighted_intersection_lower_bound_any_order 1 L 2 (by decide) (by decide)
    P hP hPm hcoeff H (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hH)
    hfinite'
  simpa only [heval] using hbound

/-- In the aligned node coordinates, intersection six rules out order four
for the second analytic coordinate. -/
theorem orbit_second_not_mem_four_of_intersection_six (u : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) u)
    (hi : PlaneCurve.intersectionMultiplicity
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) u hfinite = 6) :
    u ∉ maximalIdeal 2 ^ 4 := by
  intro hu
  have hbound := orbitPhi_intersection_lower_bound 4 u hu hfinite
  omega

theorem orbit_cubic_jacobian_divisibility
    (v u : Germ 2)
    (hv : v - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3)
    (R : OrbitSourceForm) (hR : R.IsHomogeneous 3)
    (hu : u - coordinatePolynomialAlgHom 2 R ∈ maximalIdeal 2 ^ 4)
    (hdiv : coordinate (1 : Fin 2) ^ 3 ∣ jacobian v u) :
    orbitPolynomialLambda ℂ ^ 3 ∣ OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R := by
  have hw : (1 : Fin 2 → ℕ) = ![1, 1] := by ext i; fin_cases i <;> rfl
  have hJ := jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal 1 2 3
    (by decide) (by decide) (by decide) (orbitPolynomialPhi ℂ) R
    (by simpa only [← hw] using orbitPolynomialPhi_isHomogeneous (K := ℂ))
    (by simpa only [MvPolynomial.IsHomogeneous, ← hw] using hR) v u
    (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hv)
    (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hu)
  have hJhom : (OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R).IsHomogeneous 3 := by
    simpa only [MvPolynomial.IsHomogeneous, Pi.one_apply, Nat.reduceSub, Nat.reduceAdd] using
      OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
      (1 : Fin 2 → ℕ) (orbitPolynomialPhi ℂ) R 2 3
      (orbitPolynomialPhi_isHomogeneous (K := ℂ)) hR
      (by simp) (by simp) (by simp) (by simp)
  exact orbitLambdaCube_dvd_initialForm_of_coordinateCube_dvd (jacobian v u) (by decide)
    hJhom (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hJ) hdiv

/-- The analytic minor condition determines the complete cubic initial
form, including the possibility that the cubic is zero. -/
theorem exists_cubic_orbit_coefficient (v u : Germ 2)
    (hv : v - coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3)
    (hu : u ∈ maximalIdeal 2 ^ 3)
    (hdiv : coordinate (1 : Fin 2) ^ 3 ∣ jacobian v u) :
    ∃ a : ℂ, u - constRingHom 2 a * coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      maximalIdeal 2 ^ 4 := by
  obtain ⟨R, hR, htail⟩ := exists_weightedHomogeneous_coordinatePolynomial_mod_succ 1 3
    (by decide) u (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hu)
  have hw : (1 : Fin 2 → ℕ) = ![1, 1] := by ext i; fin_cases i <;> rfl
  have hRhom : R.IsHomogeneous 3 := by simpa only [MvPolynomial.IsHomogeneous, hw] using hR
  have htail' : u - coordinatePolynomialAlgHom 2 R ∈ maximalIdeal 2 ^ 4 := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using htail
  obtain ⟨a, ha⟩ := exists_eq_C_mul_orbitPolynomialPsi_of_cubic_jacobian_dvd hRhom
    (orbit_cubic_jacobian_divisibility v u hv R hRhom htail' hdiv)
  refine ⟨a, ?_⟩
  simpa only [ha, map_mul, coordinatePolynomialAlgHom_C] using htail'

/-- The scalar multiplying `Ψ` is nonzero when the second coordinate has
intersection number six with the exact first coordinate `Φ`. -/
theorem exists_nonzero_cubic_orbit_coefficient_of_intersection_six
    (u : Germ 2) (hu : u ∈ maximalIdeal 2 ^ 3)
    (hdiv : coordinate (1 : Fin 2) ^ 3 ∣
      jacobian (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) u)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) u)
    (hi : PlaneCurve.intersectionMultiplicity
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) u hfinite = 6) :
    ∃ a : ℂ, a ≠ 0 ∧
      u - constRingHom 2 a * coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
        maximalIdeal 2 ^ 4 := by
  obtain ⟨a, ha⟩ := exists_cubic_orbit_coefficient _ u (by simp) hu hdiv
  refine ⟨a, ?_, ha⟩
  intro hzero
  apply orbit_second_not_mem_four_of_intersection_six u hfinite hi
  simpa only [hzero, map_zero, zero_mul, sub_zero] using ha

/-- The orbit endpoint is constructed by an invertible linear scaling and
a third-coordinate subtraction. Finiteness is obtained from the supplied
intersection algebra and transported through the scaling. -/
theorem exists_orbit_endpoint_of_aligned_node_and_intersection_six
    (F : PointedMapGerm 2 3)
    (hfirst : F.1.component 0 = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hsecond : F.1.component 1 ∈ maximalIdeal 2 ^ 3)
    (hthird : F.1.component 2 ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (F.1.component 0) (F.1.component 1))
    (hi : PlaneCurve.intersectionMultiplicity (F.1.component 0) (F.1.component 1) hfinite = 6)
    (hminor12 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 1))
    (hminor13 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 2)) :
    ∃ G : PointedMapGerm 2 3, F.RightLeftEquivalent G ∧ Nonempty (OrbitAnalyticEndpoint G) := by
  have hf : PlaneCurve.HasFiniteIntersection
      (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) (F.1.component 1) := hfirst ▸ hfinite
  obtain ⟨a, ha, hpsi⟩ := exists_nonzero_cubic_orbit_coefficient_of_intersection_six
    (F.1.component 1) hsecond (hfirst ▸ hminor12) hf (by simpa only [hfirst] using hi)
  obtain ⟨b, hthirdPsi⟩ := exists_cubic_orbit_coefficient (F.1.component 0) (F.1.component 2)
    (by simp [hfirst]) hthird hminor13
  let scales : Fin 3 → ℂ := ![1, a⁻¹, 1]
  have hscales : ∀ i, scales i ≠ 0 := by
    intro i
    fin_cases i
    · exact one_ne_zero
    · exact inv_ne_zero ha
    · exact one_ne_zero
  let e := diagonalPointedEquiv scales hscales
  let f := e.forward.comp F
  have he : F.RightLeftEquivalent f := by
    refine ⟨PointedEquivGerm.identity 2, e, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  have hcomponent (i : Fin 3) : f.1.component i = constRingHom 2 (scales i) * F.1.component i := by
    rw [PointedMapGerm.component_comp_eq_pullback, diagonalPointedEquiv_component,
      map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
  have hf0 : f.1.component 0 = F.1.component 0 := by
    rw [hcomponent, show scales 0 = 1 from rfl, map_one, one_mul]
  have hf1 : f.1.component 1 = constRingHom 2 a⁻¹ * F.1.component 1 := hcomponent 1
  have hf2 : f.1.component 2 = F.1.component 2 := by
    rw [hcomponent, show scales 2 = 1 from rfl, map_one, one_mul]
  have hinv : constRingHom 2 a⁻¹ * constRingHom 2 a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hfpsi : f.1.component 1 - coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      maximalIdeal 2 ^ 4 := by
    have h := (maximalIdeal 2 ^ 4).mul_mem_left (constRingHom 2 a⁻¹) hpsi
    convert h using 1
    rw [hf1]
    linear_combination coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) * hinv
  let q : Germ 2 := constRingHom 2 b * coordinate (1 : Fin 2)
  have hq : q ∈ maximalIdeal 2 := (maximalIdeal 2).mul_mem_left _ (coordinate_mem_maximalIdeal 1)
  obtain ⟨G, hG, hG0, hG1, hG2⟩ := f.exists_target_subtraction q hq
  have hpull : f.firstTwo.pullbackRingHom q = constRingHom 2 b * f.1.component 1 := by
    dsimp only [q]
    rw [map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate,
      PointedMapGerm.firstTwo_component]
    rfl
  rw [hpull] at hG2
  have hGpair0 : G.firstTwo.1.component 0 = G.1.component 0 := by
    rw [PointedMapGerm.firstTwo_component]
    rfl
  have hGpair1 : G.firstTwo.1.component 1 = G.1.component 1 := by
    rw [PointedMapGerm.firstTwo_component]
    rfl
  have hfiniteG : G.firstTwo.IsFiniteAtOrigin := by
    apply PointedMapGerm.finiteFiberCriterionAtOrigin_two 2
    change Module.Finite ℂ (Germ 2 ⧸ G.firstTwo.1.coordinateIdeal)
    rw [PlaneCurve.coordinateIdeal_eq_pairIdeal]
    change PlaneCurve.HasFiniteIntersection (G.firstTwo.1.component 0) (G.firstTwo.1.component 1)
    simp only [hGpair0, hGpair1, hG0, hG1, hf0, hf1]
    apply (PlaneCurve.hasFiniteIntersection_comm _ _).mp
    apply (PlaneCurve.hasFiniteIntersection_unit_mul_left_iff _ _ _
      (isUnit_iff_valueRingHom_ne_zero.mpr (by simpa using inv_ne_zero ha))).mpr
    exact (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfinite
  have hdiv12 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (f.1.component 0) (f.1.component 1) := by
    rw [hf0, hf1, jacobian_mul_right, jacobian_const_right, mul_zero, add_zero]
    exact dvd_mul_of_dvd_right hminor12 _
  have hdiv13 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (G.1.component 0) (G.1.component 2) := by
    rw [hG0, hG2, jacobian_sub_right, jacobian_mul_right, jacobian_const_right, mul_zero, add_zero]
    exact dvd_sub (by simpa only [hf0, hf2] using hminor13) (dvd_mul_of_dvd_right hdiv12 _)
  refine ⟨G, he.trans hG, ⟨{
    plane := G.firstTwo
    finite := hfiniteG
    component_zero := hGpair0.symm
    component_one := hGpair1.symm
    phi_tail := ?_
    psi_tail := ?_
    third_order := ?_
    minor_twelve := ?_
    minor_thirteen := ?_
  }⟩⟩
  · simp only [hGpair0, hG0, hf0, hfirst, sub_self, Ideal.zero_mem]
  · simpa only [hGpair1, hG1] using hfpsi
  · have h := (maximalIdeal 2 ^ 4).sub_mem hthirdPsi
      ((maximalIdeal 2 ^ 4).mul_mem_left (constRingHom 2 b) hfpsi)
    convert h using 1
    rw [hG2, hf2]
    ring
  · simpa only [hGpair0, hGpair1, hG0, hG1] using hdiv12
  · simpa only [hGpair0] using hdiv13

/-- The orbit collision excludes the aligned squarefree branch with its
actual intersection and minor data. No prepared endpoint is assumed. -/
theorem aligned_node_intersection_six_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3)
    (hfirst : F.1.component 0 = coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ))
    (hsecond : F.1.component 1 ∈ maximalIdeal 2 ^ 3)
    (hthird : F.1.component 2 ∈ maximalIdeal 2 ^ 3)
    (hfinite : PlaneCurve.HasFiniteIntersection (F.1.component 0) (F.1.component 1))
    (hi : PlaneCurve.intersectionMultiplicity (F.1.component 0) (F.1.component 1) hfinite = 6)
    (hminor12 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 1))
    (hminor13 : coordinate (1 : Fin 2) ^ 3 ∣ jacobian (F.1.component 0) (F.1.component 2)) :
    ¬ F.HasInjectiveRepresentative := by
  obtain ⟨G, hFG, data⟩ := exists_orbit_endpoint_of_aligned_node_and_intersection_six
    F hfirst hsecond hthird hfinite hi hminor12 hminor13
  intro hF
  exact data.some.not_hasInjectiveRepresentative (hFG.hasInjectiveRepresentative hF)

end OnLeConjecture.DTwo
