/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparationComplete
public import OnLeConjecture.Analytic.WeightedThirdInitialReplacement

/-!
# Normalized odd preparation including a unit third coefficient

The third coefficient may or may not vanish at the origin. In the unit
case a linear target change produces `x^p`. In the other case the proved
mixed-residual exclusion supplies `κ*x^(p+2q)`, and a target scaling
normalizes `κ` to one.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ MvPolynomial

theorem exists_cyclic_normalized_odd_preparation
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 2) (hβ : valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hH : g.1.component 2 = coordinate 1 ^ k * h) :
    ∃ q₀ : ℕ, ∃ g' : PointedMapGerm 2 3, g.RightLeftEquivalent g' ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      g'.1.component 2 - coordinate (0 : Fin 2) ^ (p + 2 * q₀) ∈
        twoWeightOrderIdeal k p (k * (p + 2 * q₀) + 1) := by
  have hp0 : 0 < p := by omega
  have hxhom (N : ℕ) : (X (0 : Fin 2) ^ N : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
      ![k, p] (k * N) := by
    simpa [nsmul_eq_mul, mul_comm] using
      (isWeightedHomogeneous_X ℂ (![k, p] : Fin 2 → ℕ) 0).pow N
  by_cases hh : valueRingHom 2 h = 0
  · obtain ⟨f, κ, q₀, hequiv, _hf, hf0, hf1, hκ, _hq, htail⟩ :=
      cyclic_preparation_pure_odd g hg k p hk hp hodd β hβ hP hQ h
        (mem_maximalIdeal_iff.mpr hh) hH
    have hpair := cyclic_pair_strict_tails f.firstTwo k p hk hp β
      (by simpa using hf0.trans hP) (by simpa using hf1.trans hQ)
    obtain ⟨g', hequiv', hg'0, hg'1, hg'2⟩ :=
      f.exists_weighted_third_initial_replacement k p (k * (p + 2 * q₀)) hk hp0
        (Nat.mul_pos hk (by omega)) ![2 * k, p * k] (cyclicInitialPair k p (valueRingHom 2 β))
        (cyclicInitialPair_homogeneous k p _) hpair
        (C κ * X 0 ^ (p + 2 * q₀)) (X 0 ^ (p + 2 * q₀))
        ((hxhom _).C_mul κ) (hxhom _) κ hκ htail (by exact ⟨0, by simp⟩)
    refine ⟨q₀, g', hequiv.trans hequiv', hg'0.trans hf0, hg'1.trans hf1, ?_⟩
    simpa only [map_pow, coordinatePolynomialAlgHom_X] using hg'2
  · let c := valueRingHom 2 β
    let d := valueRingHom 2 h
    have hpair := cyclic_pair_strict_tails g.firstTwo k p hk hp β
      (by simpa using hP) (by simpa using hQ)
    have hyhom : (C d * X (1 : Fin 2) ^ k : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
        ![k, p] (k * p) := by
      simpa [nsmul_eq_mul] using
        ((isWeightedHomogeneous_X ℂ (![k, p] : Fin 2 → ℕ) 1).pow k).C_mul d
    have hrem : h - constRingHom 2 d ∈ twoWeightOrderIdeal k p 1 := by
      rw [twoWeightOrderIdeal_one_eq_maximalIdeal k p hk hp0, mem_maximalIdeal_iff]
      simp [d]
    have hyk : coordinate (1 : Fin 2) ^ k ∈ twoWeightOrderIdeal k p (k * p) := by
      simpa only [pow_zero, one_mul] using
        monomial_mem_twoWeightOrderIdeal_of_threshold k p (k * p) 0 k hk hp0 (by simp [mul_comm])
    have hthird : g.1.component 2 - coordinatePolynomialAlgHom 2 (C d * X 1 ^ k) ∈
        twoWeightOrderIdeal k p (k * p + 1) := by
      have hmul := twoWeightOrderIdeal_mul_mem k p (k * p) 1 hk hp0 hyk hrem
      rw [hH, map_mul, map_pow, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
      convert hmul using 1
      ring
    have hquotient : C d * X (1 : Fin 2) ^ k - C (-d / c) * X 0 ^ p ∈
        Set.range (MvPolynomial.aeval (cyclicInitialPair k p c) :
          MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) := by
      refine ⟨C (d / c) * X 1, ?_⟩
      rw [map_mul, aeval_C, aeval_X]
      change C (d / c) * (X 0 ^ p + C c * X 1 ^ k) = _
      have hscalar : (C (d / c) * C c : MvPolynomial (Fin 2) ℂ) = C d := by
        rw [← map_mul, div_mul_cancel₀ d hβ]
      rw [mul_add, ← mul_assoc, hscalar, neg_div, map_neg]
      ring
    obtain ⟨g', hequiv, hg'0, hg'1, hg'2⟩ :=
      g.exists_weighted_third_initial_replacement k p (k * p) hk hp0 (Nat.mul_pos hk hp0)
        ![2 * k, p * k] (cyclicInitialPair k p c)
        (cyclicInitialPair_homogeneous k p c) hpair
        (C d * X 1 ^ k) (X 0 ^ p) hyhom (hxhom p) (-d / c)
        (div_ne_zero (neg_ne_zero.mpr hh) hβ) hthird hquotient
    refine ⟨0, g', hequiv, hg'0, hg'1, ?_⟩
    simpa only [mul_zero, add_zero, map_pow, coordinatePolynomialAlgHom_X] using hg'2

end OnLeConjecture.DTwo
