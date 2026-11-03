/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.OddMorseIrreducible
public import OnLeConjecture.Analytic.OrdinaryNodeFactorization
public import OnLeConjecture.DTwo.AnalyticBranchPullback

/-!
# The analytic branch count of `x²+y^k`

For even `k=2a>0`, the two explicit factors `x±iy^a` are smooth
and nonassociated. Together with the odd irreducibility theorem and
source-coordinate invariance, this proves the branch count `gcd(2,k)`
for the actual convergent equation and every equivalent germ.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

private theorem graph_power_irreducible (a : ℕ) (ha : 0 < a) (c : ℂ) :
    Irreducible (coordinate (0 : Fin 2) + constRingHom 2 c * coordinate (1 : Fin 2) ^ a) := by
  let F := coordinate (0 : Fin 2) + constRingHom 2 c * coordinate (1 : Fin 2) ^ a
  have hmem : F ∈ maximalIdeal 2 := (maximalIdeal 2).add_mem (coordinate_mem_maximalIdeal 0)
    ((maximalIdeal 2).mul_mem_left _
      ((maximalIdeal 2).pow_mem_of_mem (coordinate_mem_maximalIdeal 1) a ha))
  have hrestriction : pointBlowupExceptionalLine.pullbackRingHom F = coordinate (0 : Fin 1) := by
    simp only [F, map_add, map_mul, map_pow, pointBlowupExceptionalLine_pullback_zero,
      pointBlowupExceptionalLine_pullback_one, zero_pow ha.ne', mul_zero, add_zero]
  have hnot : F ∉ maximalIdeal 2 ^ 2 := by
    intro hh
    have hr := pointBlowupExceptionalLine.pullback_mem_maximalIdeal_pow hh
    rw [hrestriction, mem_maximalIdeal_one_pow_iff, vanishingOrder_coordinate] at hr
    norm_num at hr
  exact (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq F hmem hnot).2

/-- The two factors for a positive even exponent are irreducible and
not associated. Separation is proved by restriction to one actual
analytic branch, including the case `a=1`. -/
theorem morseCurve_even_irreducible_factorization (a : ℕ) (ha : 0 < a) :
    ∃ f g : Germ 2, morseCurve (2 * a) = f * g ∧
      Irreducible f ∧ Irreducible g ∧ ¬ Associated f g := by
  let f := coordinate (0 : Fin 2) - constRingHom 2 Complex.I * coordinate (1 : Fin 2) ^ a
  let g := coordinate (0 : Fin 2) + constRingHom 2 Complex.I * coordinate (1 : Fin 2) ^ a
  have hf : Irreducible f := by
    simpa only [map_neg, neg_mul, ← sub_eq_add_neg] using graph_power_irreducible a ha (-Complex.I)
  have hg : Irreducible g := graph_power_irreducible a ha Complex.I
  have hI : (constRingHom 2 Complex.I : Germ 2) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hfactor : morseCurve (2 * a) = f * g := by
    dsimp only [f, g, morseCurve]
    rw [sub_mul, mul_add, mul_add]
    have hpow : coordinate (1 : Fin 2) ^ (2 * a) = (coordinate (1 : Fin 2) ^ a) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm a 2]
    rw [hpow]
    linear_combination (coordinate (1 : Fin 2) ^ a) ^ 2 * hI
  let φ := OnLeConjecture.DTwo.Germ.evenQuadraticBranchMapGerm a ha Complex.I
  have hφf : φ.pullbackRingHom f = 0 := by
    simp only [φ, f, map_sub, map_mul, map_pow, PointedMapGerm.pullback_constRingHom,
      OnLeConjecture.DTwo.Germ.evenQuadraticBranchMapGerm_pullback_coordinate_zero,
      OnLeConjecture.DTwo.Germ.evenQuadraticBranchMapGerm_pullback_coordinate_one, sub_self]
  have hφg : φ.pullbackRingHom g ≠ 0 := by
    simp only [φ, g, map_add, map_mul, map_pow, PointedMapGerm.pullback_constRingHom,
      OnLeConjecture.DTwo.Germ.evenQuadraticBranchMapGerm_pullback_coordinate_zero,
      OnLeConjecture.DTwo.Germ.evenQuadraticBranchMapGerm_pullback_coordinate_one]
    rw [← two_mul]
    apply mul_ne_zero (by
      intro hz
      have hv := congrArg (valueRingHom 1) hz
      norm_num only [map_ofNat, map_zero] at hv)
    apply mul_ne_zero
    · intro hz
      have hv := congrArg (valueRingHom 1) hz
      exact Complex.I_ne_zero (by simpa only [valueRingHom_const, map_zero] using hv)
    · exact pow_ne_zero a (coordinate_ne_zero (0 : Fin 1))
  refine ⟨f, g, hfactor, hf, hg, ?_⟩
  intro hassociated
  exact hφg ((hassociated.map φ.pullbackRingHom).eq_zero_iff.mp hφf)

theorem irreducibleBranchCount_morseCurve_even (a : ℕ) (ha : 0 < a) :
    irreducibleBranchCount (morseCurve (2 * a)) = 2 := by
  obtain ⟨f, g, hfactor, hf, hg, hne⟩ := morseCurve_even_irreducible_factorization a ha
  exact irreducibleBranchCount_eq_two_of_eq_mul _ f g hf hg hne hfactor

/-- The parity branch formula for every positive exponent. -/
theorem irreducibleBranchCount_morseCurve (k : ℕ) (hk : 0 < k) :
    irreducibleBranchCount (morseCurve k) = Nat.gcd 2 k := by
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨a, ha⟩ := heven
    have hkEq : k = 2 * a := by omega
    have haPos : 0 < a := by omega
    rw [hkEq, irreducibleBranchCount_morseCurve_even a haPos]
    exact (Nat.gcd_eq_left_iff_dvd.mpr ⟨a, rfl⟩).symm
  · rw [irreducibleBranchCount_morseCurve_of_odd k hk hodd,
      hodd.coprime_two_left.gcd_eq_one]

/-- The constructed normal form determines the branch count of the
original analytic equation. -/
theorem irreducibleBranchCount_of_morse_normalization
    (v : Germ 2) (e : PointedEquivGerm 2) (k : ℕ) (hk : 0 < k)
    (hform : e.forward.pullbackRingHom v = morseCurve k) :
    irreducibleBranchCount v = Nat.gcd 2 k := by
  rw [irreducibleBranchCount_pullback e v, hform]
  exact irreducibleBranchCount_morseCurve k hk

end OnLeConjecture.PlaneCurve
