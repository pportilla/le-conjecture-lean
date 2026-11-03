/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.Analytic.JacobianLinearSpan
public import OnLeConjecture.Analytic.GenericFiniteCompanion

/-!
# Reduced members meet common critical divisors properly

For a reduced plane equation, a prime dividing the equation and its
Jacobian with a pointed germ also divides that germ. The proof uses the
constructed nonconstant parametrization and the one-variable chain rule.
Consequently a reduced member of a finite-colength linear system has
finite intersection with every nonzero common divisor of its coordinate
Jacobians.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- A nonconstant parametrization of an irreducible plane equation has
that principal ideal as its kernel. -/
theorem parametrization_pullback_eq_zero_iff_dvd
    (p : Germ 2) (hp : Irreducible p)
    (γ : PointedMapGerm 1 2) (hγp : γ.pullbackRingHom p = 0)
    (hγ : ∃ i : Fin 2, γ.pullbackRingHom (coordinate i) ≠ 0) (f : Germ 2) :
    γ.pullbackRingHom f = 0 ↔ p ∣ f := by
  constructor
  · intro hf
    by_contra hnot
    have hfinite := PlaneCurve.hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors
      p f hp hnot
    have hall := γ.coordinate_pullbacks_eq_zero_of_finite_pair p f hfinite hγp hf
    obtain ⟨i, hi⟩ := hγ
    exact hi (hall i)
  · rintro ⟨a, rfl⟩
    rw [map_mul, hγp, zero_mul]

/-- The tangency expressed by a Jacobian divisor forces a pointed germ
to vanish on that component of a reduced equation. -/
theorem dvd_of_prime_dvd_reduced_and_jacobian
    (f g p : Germ 2) (hf : Squarefree f) (hg : g ∈ maximalIdeal 2)
    (hp : Prime p) (hpf : p ∣ f) (hpJ : p ∣ jacobian f g) : p ∣ g := by
  obtain ⟨γ, hγp, hγ⟩ := exists_nonconstant_parametrization_of_irreducible p hp.irreducible
  have hker := parametrization_pullback_eq_zero_iff_dvd p hp.irreducible γ hγp hγ
  have hγf : γ.pullbackRingHom f = 0 := (hker f).mpr hpf
  have hγJ : γ.pullbackRingHom (jacobian f g) = 0 := (hker _).mpr hpJ
  have hchain (h : Germ 2) : partialDerivative (0 : Fin 1) (γ.pullbackRingHom h) =
      γ.pullbackRingHom (partialDerivative 0 h) * partialDerivative 0 (γ.1.component 0) +
      γ.pullbackRingHom (partialDerivative 1 h) * partialDerivative 0 (γ.1.component 1) := by
    rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed_sum,
      Fin.sum_univ_two]
    rfl
  have hdf := hchain f
  rw [hγf, partialDerivative_zero] at hdf
  rw [jacobian_eq, map_sub, map_mul, map_mul] at hγJ
  obtain ⟨i, hi⟩ := exists_partialDerivative_not_dvd_of_squarefree f hf p hp hpf
  have hpi : γ.pullbackRingHom (partialDerivative i f) ≠ 0 := by
    intro hz
    exact hi ((hker _).mp hz)
  have hdg : partialDerivative (0 : Fin 1) (γ.pullbackRingHom g) = 0 := by
    rw [hchain]
    apply (mul_eq_zero.mp (show γ.pullbackRingHom (partialDerivative i f) *
      (γ.pullbackRingHom (partialDerivative 0 g) * partialDerivative 0 (γ.1.component 0) +
        γ.pullbackRingHom (partialDerivative 1 g) * partialDerivative 0 (γ.1.component 1)) = 0
      from ?_)).resolve_left hpi
    fin_cases i
    · change γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) * _ = 0
      linear_combination γ.pullbackRingHom (partialDerivative 0 g) * (-hdf) +
        partialDerivative 0 (γ.1.component 1) * hγJ
    · change γ.pullbackRingHom (partialDerivative (1 : Fin 2) f) * _ = 0
      linear_combination γ.pullbackRingHom (partialDerivative 1 g) * (-hdf) -
        partialDerivative 0 (γ.1.component 0) * hγJ
  exact (hker g).mp (eq_zero_of_oneVariable_derivative_eq_zero _
    (γ.pullback_mem_maximalIdeal hg) hdg)

/-- Every reduced member of a finite-colength linear system meets a
nonzero common Jacobian divisor in finite intersection. -/
theorem finiteIntersection_commonJacobianDivisor_of_squarefree_linearCombination
    {ι : Type*} [Fintype ι] (F : ι → Germ 2)
    (hpointed : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (d : Germ 2) (hd : d ≠ 0) (hdiv : ∀ i j, d ∣ jacobian (F i) (F j))
    (q : ι → ℂ) (hq : Squarefree (germLinearCombination F q)) :
    PlaneCurve.HasFiniteIntersection d (germLinearCombination F q) := by
  classical
  apply PlaneCurve.hasFiniteIntersection_of_no_common_prime_divisor _ _ hd
  rintro p hp ⟨hpd, hpf⟩
  have hspan : germLinearCombination F q ∈ Submodule.span ℂ (Set.range F) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hpF (i : ι) : p ∣ F i := by
    apply dvd_of_prime_dvd_reduced_and_jacobian (germLinearCombination F q) (F i) p
      hq (hpointed i) hp hpf
    exact hpd.trans (dvd_jacobian_of_mem_linear_span F d hdiv hspan
      (Submodule.subset_span (Set.mem_range_self i)))
  obtain ⟨i, hi⟩ := exists_generator_not_dvd_of_finite_colength F hfinite p hp.not_isUnit
  exact hi (hpF i)

end OnLeConjecture.Analytic.Germ
