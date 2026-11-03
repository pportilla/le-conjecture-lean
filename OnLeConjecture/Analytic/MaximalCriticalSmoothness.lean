/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryIntersectionBound
public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Numerical.PointBasisCountIdentities
import Mathlib.Tactic.Linarith

/-!
# Smoothness of a maximal critical component in orders three and four

The root order and point-basis bounds here come from actual analytic
strict transforms. The two numerical inequalities are the knot and polar
inequalities supplied by the reduction. The intersection lower bound is
proved for the original analytic germs, so smoothness is a conclusion.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ Numerical.MultiplicityCounts
open scoped BigOperators

/-- The reduction's inequalities force a vanishing critical equation to
be smooth, and bound its intersection with the generic member between
the member's order and four. -/
theorem maximal_critical_equation_smooth
    {N : ℕ} (c : AnalyticPointBasis N) (m t b : ℕ)
    (hm : m = 3 ∨ m = 4) (hroot : c.multiplicity c.root = m)
    (hb : 1 ≤ b) (ht : 2 ≤ t)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (c.germ c.root) h)
    (hglobal : squareSum c.multiplicity + (∑ p, c.multiplicity p) ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite * (t - 1) +
      (∑ p, c.multiplicity p) + b ≤ 2 * squareSum c.multiplicity) :
    m ≤ PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite ∧
    PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite ≤ 4 ∧
    differential h ≠ 0 ∧ Irreducible h := by
  let M := ∑ p, c.multiplicity p
  let S := squareSum c.multiplicity
  let I := PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite
  have hmpos : 0 < m := by omega
  have hf : c.germ c.root ∈ maximalIdeal 2 ^ m := by
    simpa only [hroot] using c.germ_mem c.root
  have hfnext : c.germ c.root ∉ maximalIdeal 2 ^ (m + 1) := by
    simpa only [hroot] using c.germ_not_mem_succ c.root
  have hIlower : m ≤ I := by
    simpa only [mul_one] using ordinary_intersection_lower_bound m 1 hmpos
      (c.germ c.root) h hf hfnext (by simpa only [pow_one] using hh) hfinite
  have hMlower : m ≤ M := by
    rw [← hroot]
    exact Finset.single_le_sum (fun p _ ↦ Nat.zero_le (c.multiplicity p))
      (Finset.mem_univ c.root)
  have hSbound : S ≤ m * M := by
    change (∑ p, c.multiplicity p ^ 2) ≤ m * ∑ p, c.multiplicity p
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    have hp : c.multiplicity p ≤ m := by
      simpa only [hroot] using c.multiplicity_le_root p
    nlinarith
  have hglobal' : S + M ≤ 3 * t := hglobal
  have hpolar' : I * (t - 1) + M + b ≤ 2 * S := hpolar
  have htadd : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have hIupper : I ≤ 4 := by
    by_contra hn
    have hIlarge : 5 ≤ I := by omega
    have hmul : 5 * (t - 1) ≤ I * (t - 1) := Nat.mul_le_mul_right _ hIlarge
    have hineq : 8 * M + 3 * b ≤ S + 15 := by nlinarith
    rcases hm with rfl | rfl <;> nlinarith
  have hsmooth := smooth_irreducible_of_intersection_lt_twice_order m hmpos
    (c.germ c.root) h hf hfnext hh hfinite (by change I < 2 * m; omega)
  exact ⟨hIlower, hIupper, hsmooth⟩

/-- In order four the intersection equals four. No prior transversality
or smoothness hypothesis is needed. -/
theorem quartic_maximal_critical_equation_smooth
    {N : ℕ} (c : AnalyticPointBasis N) (t b : ℕ)
    (hroot : c.multiplicity c.root = 4) (hb : 1 ≤ b) (ht : 2 ≤ t)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (c.germ c.root) h)
    (hglobal : squareSum c.multiplicity + (∑ p, c.multiplicity p) ≤ 3 * t)
    (hpolar : PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite * (t - 1) +
      (∑ p, c.multiplicity p) + b ≤ 2 * squareSum c.multiplicity) :
    PlaneCurve.intersectionMultiplicity (c.germ c.root) h hfinite = 4 ∧
    differential h ≠ 0 ∧ Irreducible h := by
  obtain ⟨hlower, hupper, hsmooth⟩ := c.maximal_critical_equation_smooth
    4 t b (Or.inr rfl) hroot hb ht h hh hfinite hglobal hpolar
  exact ⟨by omega, hsmooth⟩

end OnLeConjecture.Analytic.AnalyticPointBasis
