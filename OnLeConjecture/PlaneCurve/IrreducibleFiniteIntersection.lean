/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.BranchCountAdditivity

/-!
# Finite intersection of distinct analytic branches

A prime principal ideal in the analytic plane has height one. A prime
ideal containing it and an element outside it must therefore be the
maximal ideal, since the local ring has dimension two. Thus an irreducible
equation has finite intersection with every equation it does not divide.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- An irreducible analytic equation and an equation not divisible by it
have finite local intersection. -/
theorem hasFiniteIntersection_of_irreducible_not_dvd
    (f g : Germ 2) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    HasFiniteIntersection f g := by
  apply (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f g).mpr
  apply Ideal.exists_pow_le_of_le_radical_of_fg ?_ (maximalIdeal_fg 2)
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  rintro P ⟨hpairP, hP⟩
  let : P.IsPrime := hP
  let I : Ideal (Germ 2) := Ideal.span {f}
  let : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr
    (irreducible_iff_prime.mp hf)
  let : (maximalIdeal 2).IsPrime := (maximalIdeal_isMaximal 2).isPrime
  have hIP : I ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpairP (Ideal.subset_span (by simp))
  have hIPne : I ≠ P := by
    intro heq
    apply hfg
    rw [← Ideal.mem_span_singleton]
    change g ∈ I
    rw [heq]
    exact hpairP (Ideal.subset_span (by simp))
  have hIPheight := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne hIP hIPne)
  have hIheight : I.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  rw [hIheight] at hIPheight
  have hPmax : P ≤ maximalIdeal 2 := by
    rw [maximalIdeal_eq_isLocalRing]
    exact IsLocalRing.le_maximalIdeal hP.ne_top
  by_cases hPeq : P = maximalIdeal 2
  · exact hPeq ▸ le_refl _
  exfalso
  have hPheight := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne hPmax hPeq)
  have hthree : (3 : ℕ∞) ≤ (maximalIdeal 2).height := by
    calc
      (3 : ℕ∞) = (1 + 1) + 1 := by norm_num
      _ ≤ P.height + 1 := add_le_add hIPheight le_rfl
      _ ≤ (maximalIdeal 2).height := hPheight
  have hcast : (3 : WithBot ℕ∞) ≤ ((maximalIdeal 2).height : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hthree
  rw [maximalIdeal_eq_isLocalRing, IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ringKrullDim_two] at hcast
  norm_num at hcast

/-- Nonassociated irreducible analytic equations have finite intersection. -/
theorem hasFiniteIntersection_of_irreducible_not_associated
    (f g : Germ 2) (hf : Irreducible f) (hg : Irreducible g)
    (hfg : ¬ Associated f g) : HasFiniteIntersection f g := by
  apply hasFiniteIntersection_of_irreducible_not_dvd f g hf
  intro hdvd
  rcases hg.dvd_iff.mp hdvd with hunit | hass
  · exact hf.not_isUnit hunit
  · exact hfg hass.symm

end OnLeConjecture.PlaneCurve
