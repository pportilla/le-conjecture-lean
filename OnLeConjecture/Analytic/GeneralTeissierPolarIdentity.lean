/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TeissierPolarIdentity
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection
public import OnLeConjecture.PlaneCurve.MilnorBranchDefect

/-!
# The polar identity for an arbitrary pointed parameter

The parameter may be singular or tangent to the reduced curve. The
chain rule on each irreducible branch compares its polar with a coordinate
polar. Intersection additivity and a transverse coordinate change remove
the auxiliary coordinate axis from the final identity.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The Jacobian identity along a parametrized zero fibre. -/
theorem pullback_first_partial_mul_derivative_eq_jacobian_mul_derivative
    (γ : PointedMapGerm 1 2) (f g : Germ 2) (hf : γ.pullbackRingHom f = 0) :
    γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom g) =
      γ.pullbackRingHom (jacobian f g) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (1 : Fin 2))) := by
  have hchain (h : Germ 2) : partialDerivative (0 : Fin 1) (γ.pullbackRingHom h) =
      γ.pullbackRingHom (partialDerivative (0 : Fin 2) h) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (0 : Fin 2))) +
      γ.pullbackRingHom (partialDerivative (1 : Fin 2) h) *
        partialDerivative (0 : Fin 1) (γ.pullbackRingHom (coordinate (1 : Fin 2))) := by
    change partialDerivative (0 : Fin 1) (compPointed h γ) = _
    rw [partialDerivative_compPointed_sum, Fin.sum_univ_two,
      PointedMapGerm.pullback_coordinate, PointedMapGerm.pullback_coordinate]
    rfl
  have hfc := hchain f
  rw [hf, partialDerivative_zero] at hfc
  rw [hchain g, jacobian_eq, map_sub, map_mul, map_mul]
  linear_combination -(γ.pullbackRingHom (partialDerivative (0 : Fin 2) g)) * hfc

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- A pointed parameter meeting the curve finitely has nonzero polar
restriction on every branch, provided a finite coordinate polar is fixed. -/
theorem finite_polar_of_finite_first_partial
    (f g : Germ 2) (hf : f ≠ 0) (hg : g ∈ maximalIdeal 2)
    (hfirst : HasFiniteIntersection f (partialDerivative (0 : Fin 2) f))
    (hfg : HasFiniteIntersection f g) : HasFinitePolarIntersection f g := by
  apply hasFiniteIntersection_of_no_common_prime_divisor _ _ hf
  rintro p hp ⟨hpf, hpJ⟩
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible p hp.irreducible
  have hzero (h : Germ 2) (hph : p ∣ h) : P.map.pullbackRingHom h = 0 := by
    obtain ⟨a, rfl⟩ := hph
    rw [map_mul, P.curve_eq_zero, zero_mul]
  have hfxne := P.pullback_ne_zero _ (hfirst.of_dvd_left hpf)
  have hgne := P.pullback_ne_zero _ (hfg.of_dvd_left hpf)
  have hgd := (derivative_ne_zero_and_order_add_one _
    (P.map.pullback_mem_maximalIdeal hg) hgne).1
  have hchain := pullback_first_partial_mul_derivative_eq_jacobian_mul_derivative
    P.map f g (hzero _ hpf)
  rw [hzero _ hpJ, zero_mul] at hchain
  exact mul_ne_zero hfxne hgd hchain

/-- The parameter-polar comparison on one irreducible branch. -/
theorem branch_polar_comparison_identity
    (f g p : Germ 2) (hg : g ∈ maximalIdeal 2) (hp : Irreducible p) (hpf : p ∣ f)
    (hfirst : HasFiniteIntersection p (partialDerivative (0 : Fin 2) f))
    (hpg : HasFiniteIntersection p g)
    (haxis : HasFiniteIntersection p (coordinate (1 : Fin 2)))
    (hpolar : HasFiniteIntersection p (jacobian f g)) :
    intersectionMultiplicity p (jacobian f g) hpolar +
        intersectionMultiplicity p (coordinate (1 : Fin 2)) haxis =
      intersectionMultiplicity p (partialDerivative (0 : Fin 2) f) hfirst +
        intersectionMultiplicity p g hpg := by
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible p hp
  have hzero : P.map.pullbackRingHom f = 0 := by
    obtain ⟨a, ha⟩ := hpf
    rw [ha, map_mul, P.curve_eq_zero, zero_mul]
  obtain ⟨hgd, hgo⟩ := derivative_ne_zero_and_order_add_one _
    (P.map.pullback_mem_maximalIdeal hg) (P.pullback_ne_zero _ hpg)
  obtain ⟨hyd, hyo⟩ := derivative_ne_zero_and_order_add_one _
    (P.map.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 1))
    (P.pullback_ne_zero _ haxis)
  have hchain := congrArg (fun h : Germ 1 => (vanishingOrder h).toNat)
    (pullback_first_partial_mul_derivative_eq_jacobian_mul_derivative P.map f g hzero)
  simp only [vanishingOrder_mul,
    ENat.toNat_add (vanishingOrder_eq_top_iff.not.mpr (P.pullback_ne_zero _ hfirst))
      (vanishingOrder_eq_top_iff.not.mpr hgd),
    ENat.toNat_add (vanishingOrder_eq_top_iff.not.mpr (P.pullback_ne_zero _ hpolar))
      (vanishingOrder_eq_top_iff.not.mpr hyd)] at hchain
  rw [P.intersection_order _ hpolar, P.intersection_order _ haxis,
    P.intersection_order _ hfirst, P.intersection_order _ hpg]
  omega

/-- Intersection additivity sums the branchwise polar comparison. -/
theorem polar_comparison_identity
    (f g : Germ 2) (hf : f ≠ 0) (hg : g ∈ maximalIdeal 2)
    (hfirst : HasFiniteIntersection f (partialDerivative (0 : Fin 2) f))
    (hfg : HasFiniteIntersection f g)
    (haxis : HasFiniteIntersection f (coordinate (1 : Fin 2)))
    (hpolar : HasFinitePolarIntersection f g) :
    polarIntersectionMultiplicity f g hpolar +
        intersectionMultiplicity f (coordinate (1 : Fin 2)) haxis =
      intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hfirst +
        intersectionMultiplicity f g hfg := by
  have hall (a : Germ 2) : a ∣ f →
      ∀ (haFirst : HasFiniteIntersection a (partialDerivative (0 : Fin 2) f))
        (haG : HasFiniteIntersection a g)
        (haAxis : HasFiniteIntersection a (coordinate (1 : Fin 2)))
        (haPolar : HasFiniteIntersection a (jacobian f g)),
        intersectionMultiplicity a (jacobian f g) haPolar +
            intersectionMultiplicity a (coordinate (1 : Fin 2)) haAxis =
          intersectionMultiplicity a (partialDerivative (0 : Fin 2) f) haFirst +
            intersectionMultiplicity a g haG := by
    induction a using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
        intro hdiv
        exact (hf (zero_dvd_iff.mp hdiv)).elim
    | h₂ a ha =>
        intro _ haFirst haG haAxis haPolar
        simp only [intersectionMultiplicity_eq_zero_of_isUnit_left _ _ ha]
    | h₃ a p _ hp ih =>
        intro hdiv hFirst hG hAxis hPolar
        obtain ⟨hpFirst, haFirst⟩ := (hasFiniteIntersection_mul_left_iff p a _).mp hFirst
        obtain ⟨hpG, haG⟩ := (hasFiniteIntersection_mul_left_iff p a g).mp hG
        obtain ⟨hpAxis, haAxis⟩ := (hasFiniteIntersection_mul_left_iff p a _).mp hAxis
        obtain ⟨hpPolar, haPolar⟩ := (hasFiniteIntersection_mul_left_iff p a _).mp hPolar
        have hpEq := branch_polar_comparison_identity f g p hg hp.irreducible
          ((dvd_mul_right p a).trans hdiv) hpFirst hpG hpAxis hpPolar
        have haEq := ih ((dvd_mul_left a p).trans hdiv) haFirst haG haAxis haPolar
        rw [intersectionMultiplicity_mul_left p a _ hpFirst haFirst hFirst,
          intersectionMultiplicity_mul_left p a g hpG haG hG,
          intersectionMultiplicity_mul_left p a _ hpAxis haAxis hAxis,
          intersectionMultiplicity_mul_left p a _ hpPolar haPolar hPolar]
        omega
  exact hall f dvd_rfl hfirst hfg haxis hpolar

/-- The arbitrary-parameter polar identity with one finite auxiliary axis. -/
theorem exists_polar_identity_of_axis_finite
    (f g : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hsq : Squarefree f) (haxis : HasFiniteIntersection f (coordinate (1 : Fin 2)))
    (hfg : HasFiniteIntersection f g) :
    ∃ hpolar : HasFinitePolarIntersection f g,
      HasFiniteJacobianAlgebra f ∧
      polarIntersectionMultiplicity f g hpolar + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + intersectionMultiplicity f g hfg := by
  obtain ⟨hfirst, hJ, hcoord⟩ := exists_first_partial_polar_identity f hf hsq haxis
  have hpolar := finite_polar_of_finite_first_partial f g hsq.ne_zero hg hfirst hfg
  have hcompare := polar_comparison_identity f g hsq.ne_zero hg hfirst hfg haxis hpolar
  exact ⟨hpolar, hJ, by omega⟩

/-- Teissier's identity for a reduced pointed equation and any pointed
parameter meeting it finitely. No smoothness or transversality condition
is imposed on the parameter. -/
theorem exists_polar_intersection_identity
    (f g : Germ 2) (hf : f ∈ maximalIdeal 2) (hg : g ∈ maximalIdeal 2)
    (hsq : Squarefree f) (hfg : HasFiniteIntersection f g) :
    ∃ hpolar : HasFinitePolarIntersection f g,
      HasFiniteJacobianAlgebra f ∧
      polarIntersectionMultiplicity f g hpolar + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + intersectionMultiplicity f g hfg := by
  obtain ⟨e, m, hregular⟩ := exists_linear_equiv_regularInFirstCoordinate hsq.ne_zero
  have heaxis := hasFiniteIntersection_secondCoordinate_of_regular _ m hregular
  have hefg := hfg.pullback e
  obtain ⟨hepolar, heJ, heq⟩ := exists_polar_identity_of_axis_finite
    (e.forward.pullbackRingHom f) (e.forward.pullbackRingHom g)
    (e.forward.pullback_mem_maximalIdeal hf) (e.forward.pullback_mem_maximalIdeal hg)
    (e.squarefree_pullback f hsq) ((hasFiniteIntersection_comm _ _).mp heaxis) hefg
  have hpolar : HasFinitePolarIntersection f g :=
    (hasFinitePolarIntersection_pullback_iff e f g).mp hepolar
  refine ⟨hpolar, hasFiniteJacobianAlgebra_of_squarefree f hf hsq, ?_⟩
  rw [polarIntersectionMultiplicity_pullback e f g hpolar,
    jacobianColength_pullback e f, intersectionMultiplicity_pullback e hfg]
  exact heq

end OnLeConjecture.PlaneCurve
