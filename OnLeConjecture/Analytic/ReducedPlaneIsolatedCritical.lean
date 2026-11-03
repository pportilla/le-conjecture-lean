/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleCurveParametrization
public import OnLeConjecture.Analytic.FinitePlaneJacobian
public import OnLeConjecture.PlaneCurve.Milnor

/-!
# Finite Jacobian algebra of a reduced plane equation

A prime factor common to both partial derivatives is parametrized by a
constructed nonconstant analytic curve. The chain rule and the
one-variable derivative order theorem imply that the original equation
vanishes on this curve. Finite intersection then forces the prime to
divide the equation. Squarefreeness excludes such a common factor.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem eq_zero_of_oneVariable_derivative_eq_zero
    (f : Germ 1) (hf : f ∈ maximalIdeal 1)
    (hderivative : partialDerivative (0 : Fin 1) f = 0) : f = 0 := by
  by_contra hne
  exact (derivative_ne_zero_and_order_add_one f hf hne).1 hderivative

/-- Every irreducible component of the critical locus through the origin
is contained in the zero fibre of a pointed plane equation. -/
theorem dvd_of_irreducible_dvd_both_partials
    (f : Germ 2) (hf : f ∈ maximalIdeal 2)
    (p : Germ 2) (hp : Irreducible p)
    (hp0 : p ∣ partialDerivative 0 f) (hp1 : p ∣ partialDerivative 1 f) : p ∣ f := by
  obtain ⟨γ, hγp, hγnonconstant⟩ := exists_nonconstant_parametrization_of_irreducible p hp
  have hpartial : ∀ i : Fin 2, γ.pullbackRingHom (partialDerivative i f) = 0 := by
    intro i
    have hdiv : p ∣ partialDerivative i f := by
      fin_cases i
      · exact hp0
      · exact hp1
    obtain ⟨a, ha⟩ := hdiv
    rw [ha, map_mul, hγp, zero_mul]
  have hγf : γ.pullbackRingHom f = 0 := by
    apply eq_zero_of_oneVariable_derivative_eq_zero _ (γ.pullback_mem_maximalIdeal hf)
    rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed_sum]
    apply Finset.sum_eq_zero
    intro i hi
    change γ.pullbackRingHom (partialDerivative i f) * _ = 0
    rw [hpartial i, zero_mul]
  by_contra hnot
  have hfinite := PlaneCurve.hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors
    p f hp hnot
  have hall := γ.coordinate_pullbacks_eq_zero_of_finite_pair p f hfinite hγp hγf
  obtain ⟨i, hi⟩ := hγnonconstant
  exact hi (hall i)

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic
open OnLeConjecture.Analytic.Germ

/-- A reduced pointed plane equation has finite Jacobian algebra. -/
theorem hasFiniteJacobianAlgebra_of_squarefree
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (hsquarefree : Squarefree f) :
    HasFiniteJacobianAlgebra f := by
  apply quotient_moduleFinite_of_nonzero_no_prime_divisor (jacobianIdeal f)
  · intro hbot
    obtain ⟨i, hi⟩ := exists_partialDerivative_not_dvd f hf hsquarefree.ne_zero
    have hmem : partialDerivative i f ∈ jacobianIdeal f := by
      rw [jacobianIdeal, pairIdeal]
      apply Ideal.subset_span
      fin_cases i <;> simp
    rw [hbot] at hmem
    exact hi ((Ideal.mem_bot.mp hmem) ▸ dvd_zero f)
  · intro p hp hle
    have hpartials : ∀ i : Fin 2, p ∣ partialDerivative i f := by
      intro i
      apply Ideal.mem_span_singleton.mp
      apply hle
      rw [jacobianIdeal, pairIdeal]
      apply Ideal.subset_span
      fin_cases i <;> simp
    have hpf := dvd_of_irreducible_dvd_both_partials f hf p hp.irreducible
      (hpartials 0) (hpartials 1)
    exact not_prime_dvd_self_and_partials_of_squarefree f hsquarefree p hp
      ⟨hpf, hpartials 0, hpartials 1⟩

/-- A reduced plane equation of order at least two has an isolated
critical point at the origin. -/
theorem hasIsolatedCriticalPoint_of_squarefree_mem_maximalIdeal_sq
    (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ 2) (hsquarefree : Squarefree f) :
    HasIsolatedCriticalPoint f := by
  have hjet := mem_firstOrderIdeal_iff.mp (maximalIdeal_sq_le_firstOrderIdeal 2 hf)
  exact ⟨hjet.2, hasFiniteJacobianAlgebra_of_squarefree f
    (mem_maximalIdeal_iff.mpr hjet.1) hsquarefree⟩

theorem exists_reduced_isolated_pencil_member_mem_open
    (f g : Germ 2) (hf : f ∈ maximalIdeal 2 ^ 2) (hg : g ∈ maximalIdeal 2 ^ 2)
    (hfinite : HasFiniteIntersection f g)
    (U : Set ℂ) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ c ∈ U, Squarefree (f + constRingHom 2 c * g) ∧
      HasIsolatedCriticalPoint (f + constRingHom 2 c * g) := by
  obtain ⟨c, hc, hsquarefree⟩ := exists_squarefree_pointed_pencil_member_mem_open f g
    ((Ideal.pow_le_self (by decide)) hf) ((Ideal.pow_le_self (by decide)) hg) hfinite U hU hUne
  refine ⟨c, hc, hsquarefree,
    hasIsolatedCriticalPoint_of_squarefree_mem_maximalIdeal_sq _ ?_ hsquarefree⟩
  exact (maximalIdeal 2 ^ 2).add_mem hf ((maximalIdeal 2 ^ 2).mul_mem_left _ hg)

end OnLeConjecture.PlaneCurve
