/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedPlaneDifferentialFactors
public import OnLeConjecture.Analytic.WeightedPrincipalClosure
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Finite colength from absence of a common prime factor

Every nonzero nonmaximal prime in the two-dimensional regular local ring
of plane analytic germs is principal. Hence a nonzero ideal not contained
in a prime principal ideal has finite complex colength.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_prime_generator_of_nonzero_nonmaximal_prime
    (I : Ideal (Germ 2)) (hI : I.IsPrime) (hne : I ≠ ⊥)
    (hmax : I ≠ maximalIdeal 2) :
    ∃ p : Germ 2, Prime p ∧ I = Ideal.span {p} := by
  let : I.IsPrime := hI
  let : (maximalIdeal 2).IsPrime := (maximalIdeal_isMaximal 2).isPrime
  have hmaxheight : (maximalIdeal 2).height = 2 := by
    apply WithBot.coe_injective (α := ℕ∞)
    rw [maximalIdeal_eq_isLocalRing, IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ringKrullDim_two]
  have hlt : I < maximalIdeal 2 :=
    lt_of_le_of_ne (by
      rw [maximalIdeal_eq_isLocalRing]
      exact IsLocalRing.le_maximalIdeal hI.ne_top) hmax
  have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hmaxheight] at hheight
  have hfinite : I.height ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hheight
    exact (by decide : ¬ (⊤ : ℕ∞) ≤ 2) hheight
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hnle : n + 1 ≤ 2 := by
    rw [← hn] at hheight
    exact_mod_cast hheight
  have hnzero : n ≠ 0 := by
    intro hz
    apply hne
    apply Ideal.height_eq_zero_iff_eq_bot.mp
    simpa only [hz, Nat.cast_zero] using hn.symm
  have hheightone : I.height = 1 := by
    have hn1 : n = 1 := by omega
    simpa only [hn1, Nat.cast_one] using hn.symm
  obtain ⟨p, hpI, hp⟩ := exists_prime_mem_of_nonzero_prime I hne hI
  exact ⟨p, hp, Ideal.eq_span_singleton_of_height_eq_one hheightone hpI hp⟩

theorem quotient_moduleFinite_of_nonzero_no_prime_divisor
    (I : Ideal (Germ 2)) (hne : I ≠ ⊥)
    (hno : ∀ p : Germ 2, Prime p → ¬ I ≤ Ideal.span {p}) :
    Module.Finite ℂ (Germ 2 ⧸ I) := by
  apply (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le I).mpr
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (maximalIdeal_fg 2)
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  rintro J ⟨hIJ, hJ⟩
  by_cases hmax : J = maximalIdeal 2
  · exact hmax ▸ le_rfl
  · have hJne : J ≠ ⊥ := by
      intro hzero
      exact hne (le_bot_iff.mp (hzero ▸ hIJ))
    obtain ⟨p, hp, hJp⟩ :=
      exists_prime_generator_of_nonzero_nonmaximal_prime J hJ hJne hmax
    exact (hno p hp (hJp ▸ hIJ)).elim

theorem finite_tjurinaAlgebra_of_squarefree (f : Germ 2)
    (hne : f ≠ 0) (hf : Squarefree f) :
    Module.Finite ℂ
      (Germ 2 ⧸ Ideal.span {f, partialDerivative 0 f, partialDerivative 1 f}) := by
  apply quotient_moduleFinite_of_nonzero_no_prime_divisor
  · intro hbot
    have hfmem := Ideal.subset_span
      (show f ∈ ({f, partialDerivative 0 f, partialDerivative 1 f} : Set (Germ 2)) by simp)
    rw [hbot] at hfmem
    exact hne (Ideal.mem_bot.mp hfmem)
  · intro p hp hle
    apply not_prime_dvd_self_and_partials_of_squarefree f hf p hp
    refine ⟨?_, ?_, ?_⟩
    all_goals
      apply Ideal.mem_span_singleton.mp
      apply hle
      apply Ideal.subset_span
      simp

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

theorem hasFiniteIntersection_of_no_common_prime_divisor
    (f g : Germ 2) (hf : f ≠ 0)
    (hno : ∀ p : Germ 2, Prime p → ¬ (p ∣ f ∧ p ∣ g)) :
    HasFiniteIntersection f g := by
  apply Germ.quotient_moduleFinite_of_nonzero_no_prime_divisor (pairIdeal f g)
  · intro hzero
    apply hf
    have hmem := Ideal.subset_span (show f ∈ ({f, g} : Set (Germ 2)) by simp)
    change f ∈ pairIdeal f g at hmem
    rwa [hzero, Ideal.mem_bot] at hmem
  · intro p hp hle
    apply hno p hp
    constructor
    all_goals
      apply Ideal.mem_span_singleton.mp
      apply hle
      apply Ideal.subset_span
      simp

theorem hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors
    (f g : Germ 2) (hf : Irreducible f) (hnot : ¬ f ∣ g) :
    HasFiniteIntersection f g := by
  apply hasFiniteIntersection_of_no_common_prime_divisor f g hf.ne_zero
  rintro p hp ⟨hpf, hpg⟩
  exact hnot ((hp.irreducible.associated_of_dvd hf hpf).dvd_iff_dvd_left.mp hpg)

theorem exists_finite_partial_polar_of_irreducible
    (f : Germ 2) (hf : Irreducible f) :
    ∃ i : Fin 2, HasFiniteIntersection f (Germ.partialDerivative i f) := by
  obtain ⟨i, hi⟩ := Germ.exists_partialDerivative_not_dvd_of_irreducible f hf
  exact ⟨i, hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors f _ hf hi⟩

theorem finite_first_partial_polar_of_irreducible_regular
    (f : Germ 2) (hf : Irreducible f) (m : ℕ)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f m) :
    HasFiniteIntersection f (Germ.partialDerivative (0 : Fin 2) f) := by
  apply hasFiniteIntersection_of_irreducible_not_dvd_via_prime_factors f _ hf
  apply Germ.not_dvd_partialDerivative_zero_of_regular f _ m hregular
  rw [Germ.mem_maximalIdeal_iff]
  by_contra h
  exact hf.not_isUnit (Germ.isUnit_of_valueRingHom_ne_zero h)

end OnLeConjecture.PlaneCurve
