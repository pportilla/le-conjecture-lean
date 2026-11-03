/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntersectionParametrization
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.Analytic.SmoothPolarCorrection

/-!
# The polar intersection identity

The chain rule on an intersection parametrization computes the intersection
with each irreducible factor of a partial derivative. Additivity then
relates the polar intersection to the Jacobian algebra and the chosen
coordinate axis. The coordinate axis may be tangent to the curve.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- On a curve contained in the first polar, the chain rule has one term. -/
theorem derivative_pullback_of_first_partial_eq_zero
    (γ : PointedMapGerm 1 2) (f : Germ 2)
    (hzero : γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) = 0) :
    partialDerivative (0 : Fin 1) (γ.pullbackRingHom f) =
      γ.pullbackRingHom (partialDerivative (1 : Fin 2) f) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (1 : Fin 2))) := by
  change partialDerivative (0 : Fin 1) (compPointed f γ) = _
  rw [partialDerivative_compPointed_sum, Fin.sum_univ_two]
  change γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) * _ +
    γ.pullbackRingHom (partialDerivative (1 : Fin 2) f) * _ = _
  rw [hzero, zero_mul, zero_add, PointedMapGerm.pullback_coordinate]

/-- The one-variable derivative rule cancels the two order drops. -/
theorem order_eq_add_of_derivative_eq_mul_derivative
    (a b c : Germ 1) (ha : a ∈ maximalIdeal 1) (hc : c ∈ maximalIdeal 1)
    (hane : a ≠ 0) (hbne : b ≠ 0) (hcne : c ≠ 0)
    (hderiv : partialDerivative (0 : Fin 1) a =
      b * partialDerivative (0 : Fin 1) c) :
    (vanishingOrder a).toNat = (vanishingOrder b).toNat + (vanishingOrder c).toNat := by
  obtain ⟨_, hao⟩ := derivative_ne_zero_and_order_add_one a ha hane
  obtain ⟨hcd, hco⟩ := derivative_ne_zero_and_order_add_one c hc hcne
  rw [hderiv, vanishingOrder_mul,
    ENat.toNat_add (vanishingOrder_eq_top_iff.not.mpr hbne)
      (vanishingOrder_eq_top_iff.not.mpr hcd)] at hao
  omega

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- Finiteness survives replacing the first equation by a divisor. -/
theorem HasFiniteIntersection.of_dvd_left {f g p : Germ 2}
    (hfinite : HasFiniteIntersection f g) (hdiv : p ∣ f) : HasFiniteIntersection p g := by
  obtain ⟨a, rfl⟩ := hdiv
  exact (hasFiniteIntersection_mul_left_iff p a g).mp hfinite |>.1

/-- A reduced pointed equation has finite first polar whenever its
intersection with the second coordinate axis is finite. -/
theorem finite_first_partial_polar_of_squarefree_axis_finite
    (f : Germ 2) (_hf : f ∈ maximalIdeal 2) (hsq : Squarefree f)
    (haxis : HasFiniteIntersection f (coordinate (1 : Fin 2))) :
    HasFiniteIntersection f (partialDerivative (0 : Fin 2) f) := by
  apply hasFiniteIntersection_of_no_common_prime_divisor _ _ hsq.ne_zero
  rintro p hp ⟨hpf, hpx⟩
  have hpy : ¬ p ∣ partialDerivative (1 : Fin 2) f :=
    fun h => not_prime_dvd_self_and_partials_of_squarefree f hsq p hp ⟨hpf, hpx, h⟩
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible p hp.irreducible
  have hzero (g : Germ 2) (hpg : p ∣ g) : P.map.pullbackRingHom g = 0 := by
    obtain ⟨a, rfl⟩ := hpg
    rw [map_mul, P.curve_eq_zero, zero_mul]
  have hfyne : P.map.pullbackRingHom (partialDerivative (1 : Fin 2) f) ≠ 0 :=
    P.pullback_ne_zero _ (hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors
      _ _ hp.irreducible hpy)
  have hchain := derivative_pullback_of_first_partial_eq_zero P.map f (hzero _ hpx)
  rw [hzero _ hpf, partialDerivative_zero] at hchain
  have hyzero : P.map.pullbackRingHom (coordinate (1 : Fin 2)) = 0 := by
    apply eq_zero_of_oneVariable_derivative_eq_zero _
      (P.map.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 1))
    exact (mul_eq_zero.mp hchain.symm).resolve_left hfyne
  exact P.pullback_ne_zero _ (haxis.of_dvd_left hpf) hyzero

/-- The coordinate-axis correction also supplies finiteness of the
intersection of that axis with the first partial derivative. -/
theorem first_partial_axis_intersection_add_one
    (f : Germ 2) (hf : f ∈ maximalIdeal 2)
    (haxis : HasFiniteIntersection f (coordinate (1 : Fin 2))) :
    ∃ hpartial : HasFiniteIntersection (partialDerivative (0 : Fin 2) f)
        (coordinate (1 : Fin 2)),
      intersectionMultiplicity (partialDerivative (0 : Fin 2) f)
        (coordinate (1 : Fin 2)) hpartial + 1 =
      intersectionMultiplicity f (coordinate (1 : Fin 2)) haxis := by
  have hynext : coordinate (1 : Fin 2) ∉ maximalIdeal 2 ^ 2 := by
    intro hmem
    have hd := (mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 hmem)).2
    have hv := congrArg (fun L : Source 2 →L[ℂ] ℂ => L (coordinateVector 1)) hd
    simp [coordinateVector] at hv
  obtain ⟨hpolar, horder⟩ := exists_order_one_polar_intersection_add_one
    (coordinate (1 : Fin 2)) f (coordinate_mem_maximalIdeal 1) hynext hf
    ((hasFiniteIntersection_comm _ _).mp haxis)
  have hneg : HasFiniteIntersection (coordinate (1 : Fin 2))
      (-(partialDerivative (0 : Fin 2) f)) := by
    simpa only [hasFinitePolarIntersection_iff_hasFiniteIntersection,
      Germ.jacobian_coordinate_one_left] using hpolar
  have hpos := (hasFiniteIntersection_neg_right_iff _ _).mp hneg
  refine ⟨(hasFiniteIntersection_comm _ _).mp hpos, ?_⟩
  have hpolarEq : polarIntersectionMultiplicity (coordinate (1 : Fin 2)) f hpolar =
      intersectionMultiplicity (coordinate (1 : Fin 2))
        (-(partialDerivative (0 : Fin 2) f)) hneg := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [polarIdeal, Germ.jacobian_coordinate_one_left]
  rw [hpolarEq, intersectionMultiplicity_neg_right _ _ hpos,
    intersectionMultiplicity_comm (coordinate (1 : Fin 2)) _,
    intersectionMultiplicity_comm (coordinate (1 : Fin 2)) f] at horder
  exact horder

/-- On an irreducible component of the first polar, the curve order is
the sum of its second-partial and coordinate orders. -/
theorem polar_factor_intersection_identity
    (f p : Germ 2) (hf : f ∈ maximalIdeal 2) (hp : Irreducible p)
    (hpx : p ∣ partialDerivative (0 : Fin 2) f)
    (hpf : HasFiniteIntersection p f)
    (hpy : HasFiniteIntersection p (partialDerivative (1 : Fin 2) f))
    (haxis : HasFiniteIntersection p (coordinate (1 : Fin 2))) :
    intersectionMultiplicity p f hpf =
      intersectionMultiplicity p (partialDerivative (1 : Fin 2) f) hpy +
        intersectionMultiplicity p (coordinate (1 : Fin 2)) haxis := by
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible p hp
  have hzero : P.map.pullbackRingHom (partialDerivative (0 : Fin 2) f) = 0 := by
    obtain ⟨a, ha⟩ := hpx
    rw [ha, map_mul, P.curve_eq_zero, zero_mul]
  rw [P.intersection_order _ hpf, P.intersection_order _ hpy, P.intersection_order _ haxis]
  exact order_eq_add_of_derivative_eq_mul_derivative _ _ _
    (P.map.pullback_mem_maximalIdeal hf)
    (P.map.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 1))
    (P.pullback_ne_zero _ hpf) (P.pullback_ne_zero _ hpy) (P.pullback_ne_zero _ haxis)
    (derivative_pullback_of_first_partial_eq_zero P.map f hzero)

/-- Factorization with multiplicities sums the identities on the polar
components. Unit partial derivatives are included by the unit case. -/
theorem first_partial_intersection_identity
    (f : Germ 2) (hf : f ∈ maximalIdeal 2)
    (hfx : partialDerivative (0 : Fin 2) f ≠ 0)
    (hpolar : HasFiniteIntersection (partialDerivative (0 : Fin 2) f) f)
    (hjac : HasFiniteIntersection (partialDerivative (0 : Fin 2) f)
      (partialDerivative (1 : Fin 2) f))
    (haxis : HasFiniteIntersection (partialDerivative (0 : Fin 2) f)
      (coordinate (1 : Fin 2))) :
    intersectionMultiplicity (partialDerivative (0 : Fin 2) f) f hpolar =
      intersectionMultiplicity (partialDerivative (0 : Fin 2) f)
        (partialDerivative (1 : Fin 2) f) hjac +
      intersectionMultiplicity (partialDerivative (0 : Fin 2) f)
        (coordinate (1 : Fin 2)) haxis := by
  have hall (a : Germ 2) : a ∣ partialDerivative (0 : Fin 2) f →
      ∀ (haf : HasFiniteIntersection a f)
        (hay : HasFiniteIntersection a (partialDerivative (1 : Fin 2) f))
        (haaxis : HasFiniteIntersection a (coordinate (1 : Fin 2))),
        intersectionMultiplicity a f haf =
          intersectionMultiplicity a (partialDerivative (1 : Fin 2) f) hay +
          intersectionMultiplicity a (coordinate (1 : Fin 2)) haaxis := by
    induction a using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
        intro hdiv
        exact (hfx (zero_dvd_iff.mp hdiv)).elim
    | h₂ a ha =>
        intro _ haf hay haaxis
        simp only [intersectionMultiplicity_eq_zero_of_isUnit_left _ _ ha, zero_add]
    | h₃ a p _ hp ih =>
        intro hdiv hpf hpy hpaxis
        obtain ⟨hpF, haF⟩ := (hasFiniteIntersection_mul_left_iff p a f).mp hpf
        obtain ⟨hpY, haY⟩ := (hasFiniteIntersection_mul_left_iff p a _).mp hpy
        obtain ⟨hpAxis, haAxis⟩ := (hasFiniteIntersection_mul_left_iff p a _).mp hpaxis
        have hpEq := polar_factor_intersection_identity f p hf hp.irreducible
          ((dvd_mul_right p a).trans hdiv) hpF hpY hpAxis
        have haEq := ih ((dvd_mul_left a p).trans hdiv) haF haY haAxis
        rw [intersectionMultiplicity_mul_left p a f hpF haF hpf,
          intersectionMultiplicity_mul_left p a _ hpY haY hpy,
          intersectionMultiplicity_mul_left p a _ hpAxis haAxis hpaxis]
        omega
  exact hall _ dvd_rfl hpolar hjac haxis

/-- Teissier's coordinate-polar identity for every reduced pointed plane
equation meeting the chosen coordinate axis finitely. The Jacobian
dimension formulation includes smooth equations, for which it is zero. -/
theorem exists_first_partial_polar_identity
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f)
    (haxis : HasFiniteIntersection f (coordinate (1 : Fin 2))) :
    ∃ hpolar : HasFiniteIntersection f (partialDerivative (0 : Fin 2) f),
      HasFiniteJacobianAlgebra f ∧
      intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) +
          intersectionMultiplicity f (coordinate (1 : Fin 2)) haxis := by
  have hpolar := finite_first_partial_polar_of_squarefree_axis_finite f hf hsq haxis
  have hJ := hasFiniteJacobianAlgebra_of_squarefree f hf hsq
  have hjac := (hasFiniteJacobianAlgebra_iff_hasFiniteIntersection f).mp hJ
  have hfx : partialDerivative (0 : Fin 2) f ≠ 0 := by
    intro hz
    have hu := isUnit_of_hasFiniteIntersection_zero_right f (hz ▸ hpolar)
    exact (isUnit_iff_valueRingHom_ne_zero.mp hu) (mem_maximalIdeal_iff.mp hf)
  obtain ⟨hpartial, horder⟩ := first_partial_axis_intersection_add_one f hf haxis
  have hi := first_partial_intersection_identity f hf hfx
    ((hasFiniteIntersection_comm _ _).mp hpolar) hjac hpartial
  rw [intersectionMultiplicity_comm (partialDerivative (0 : Fin 2) f) f] at hi
  have hmu : intersectionMultiplicity (partialDerivative (0 : Fin 2) f)
      (partialDerivative (1 : Fin 2) f) hjac =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) := rfl
  exact ⟨hpolar, hJ, by omega⟩

end OnLeConjecture.PlaneCurve
