/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticSmoothIntersection
public import OnLeConjecture.Analytic.OrdinaryIntersectionBound
public import OnLeConjecture.DTwo.SquareJetProximityBounds

/-!
# Intersection two at a maximal critical component in the square branch

The proximity and polar inequalities first bound the intersection by
three. The ordinary intersection inequality proves smoothness. Exponents
at least four exclude intersection three analytically, and exponent three
excludes it using the satellite forced by proximity.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical

private theorem quadratic_power_exact_order_two (k : ℕ) (hk : 2 ≤ k) :
    coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k ∈ maximalIdeal 2 ^ 2 ∧
      coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k ∉ maximalIdeal 2 ^ 3 := by
  constructor
  · exact (maximalIdeal 2 ^ 2).add_mem
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) 2)
      ((Ideal.pow_le_pow_right hk) (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 1) k))
  · intro hnext
    have h := pointBlowupExceptionalLine.pullback_mem_maximalIdeal_pow hnext
    rw [map_add, map_pow, map_pow, pointBlowupExceptionalLine_pullback_zero,
      pointBlowupExceptionalLine_pullback_one, zero_pow (by omega : k ≠ 0), add_zero,
      mem_maximalIdeal_one_pow_iff, vanishingOrder_coordinate_pow] at h
    norm_num at h

/-- The maximal critical component has intersection two and is smooth,
from genuine proximity sums and the supplied reduction inequalities.
The branch and genus identities refer to the same prepared exponent. -/
theorem square_jet_maximal_critical_intersection_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hk : 3 ≤ k) (hbranches : c.branchCount = Nat.gcd 2 k)
    (hgenus : 2 * c.multiplicityCount 2 + 2 = k + c.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) h)
    (t : ℕ) (htransverse : c.totalMultiplicity ≤ t)
    (hpolar : PlaneCurve.intersectionMultiplicity
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) h hfinite * (t - 1) +
        c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity) :
    PlaneCurve.intersectionMultiplicity
      (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) h hfinite = 2 ∧
      differential h ≠ 0 ∧ Irreducible h := by
  let v := coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k
  let I := PlaneCurve.intersectionMultiplicity v h hfinite
  have hbranch : 0 < c.branchCount := by
    rw [hbranches]
    exact Nat.gcd_pos_of_pos_left k (by decide)
  have hIupper : I ≤ 3 := square_jet_maximal_critical_intersection_le_three
    c generation hdecrease hroot hpositive k hk hbranch hgenus t I htransverse hpolar
  obtain ⟨hv, hvnext⟩ := quadratic_power_exact_order_two k (by omega)
  have hIlower : 2 ≤ I := by
    simpa only [mul_one] using ordinary_intersection_lower_bound 2 1 (by omega)
      v h hv hvnext (by simpa only [pow_one] using hh) hfinite
  have hsmooth := smooth_irreducible_of_intersection_lt_twice_order 2 (by omega) v h
    hv hvnext hh hfinite (by change I < 2 * 2; omega)
  have hIne : I ≠ 3 := by
    intro hI3
    by_cases hk3 : k = 3
    · have hb : c.branchCount = 1 := by simp only [hbranches, hk3]; decide
      have hgenus3 : 2 * c.multiplicityCount 2 + 2 = 3 + c.branchCount := by
        simpa only [hk3] using hgenus
      exact square_jet_exponent_three_critical_intersection_ne_three
        c generation hdecrease hroot hpositive hb hgenus3 t I htransverse hpolar hI3
    · have hk4 : 4 ≤ k := by omega
      have hfinite' := (PlaneCurve.hasFiniteIntersection_comm v h).mp hfinite
      have hneq := smooth_intersection_quadratic_power_ne_three h k hk4 hh hsmooth.1 hfinite'
      apply hneq
      exact (PlaneCurve.intersectionMultiplicity_comm v h hfinite).symm.trans hI3
  exact ⟨by change I = 2; omega, hsmooth⟩

end OnLeConjecture.DTwo
