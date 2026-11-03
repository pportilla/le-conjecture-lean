/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralResolutionReductionData
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Selection of a maximal transverse component before the general member

The input consists of a finite family of analytic equations, transverse
multiplicities, the product divisor of the coordinate minors, and the
full polar sum for each allowed coefficient vector. A maximal index is
selected independently of that vector. Its factor divides every minor,
and its nonnegative polar contribution is bounded by the full sum.

The existence of the component family and the reduction inequalities is
not asserted. In particular, these statements do not construct the
critical locus or prove the polar or knot estimates.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve Numerical
open scoped BigOperators

/-- The all-component form of the transverse reduction estimates. The
coefficient set need not be open or nonempty for component selection. -/
structure CriticalComponentReductionData
    (g : PointedMapGerm 2 3) (M S b : ℕ) (U : Set (Fin 3 → ℂ))
    (ι : Type*) [Fintype ι] where
  component : ι → Germ 2
  transverseMultiplicity : ι → ℕ
  component_mem : ∀ i, component i ∈ maximalIdeal 2
  two_le_multiplicity : ∀ i, 2 ≤ transverseMultiplicity i
  total_le_max : M ≤ Finset.univ.sup transverseMultiplicity
  global_estimate : S + M ≤ 3 * Finset.univ.sup transverseMultiplicity
  product_dvd_ordered_minors : ∀ j k : Fin 3, j < k →
    (∏ i, component i ^ (transverseMultiplicity i - 1)) ∣
      jacobian (g.1.component j) (g.1.component k)
  intersection_finite : ∀ q ∈ U, ∀ i,
    HasFiniteIntersection (component i) (germLinearCombination g.1.component q)
  polar_sum : ∀ q (hq : q ∈ U),
    (∑ i, intersectionMultiplicity (component i) (germLinearCombination g.1.component q)
        (intersection_finite q hq i) * (transverseMultiplicity i - 1)) + M + b ≤ 2 * S

namespace CriticalComponentReductionData

variable {g : PointedMapGerm 2 3} {M S b : ℕ} {U : Set (Fin 3 → ℂ)}
    {ι : Type*} [Fintype ι] (D : CriticalComponentReductionData g M S b U ι)

/-- The three ordered minors determine divisibility for every ordered
pair of coordinate components, by alternation of the Jacobian. -/
theorem product_dvd_minors (j k : Fin 3) :
    (∏ i, D.component i ^ (D.transverseMultiplicity i - 1)) ∣
      jacobian (g.1.component j) (g.1.component k) := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact D.product_dvd_ordered_minors j k hlt
  · subst k
    rw [jacobian_self]
    exact dvd_zero _
  · rw [jacobian_swap (g.1.component k) (g.1.component j)]
    exact dvd_neg.mpr (D.product_dvd_ordered_minors k j hgt)

/-- Every individual factor of the supplied product divides every
coordinate minor. Irreducibility and coprimality are not needed here. -/
theorem component_dvd_minors (i : ι) (j k : Fin 3) :
    D.component i ^ (D.transverseMultiplicity i - 1) ∣
      jacobian (g.1.component j) (g.1.component k) := by
  exact (Finset.dvd_prod_of_mem
    (fun a => D.component a ^ (D.transverseMultiplicity a - 1))
      (Finset.mem_univ i)).trans (D.product_dvd_minors j k)

/-- A single component's polar term is bounded by the full sum. -/
theorem component_polar (i : ι) (q : Fin 3 → ℂ) (hq : q ∈ U) :
    intersectionMultiplicity (D.component i) (germLinearCombination g.1.component q)
      (D.intersection_finite q hq i) * (D.transverseMultiplicity i - 1) + M + b ≤
        2 * S := by
  have hterm : intersectionMultiplicity (D.component i)
      (germLinearCombination g.1.component q) (D.intersection_finite q hq i) *
        (D.transverseMultiplicity i - 1) ≤
      ∑ a, intersectionMultiplicity (D.component a) (germLinearCombination g.1.component q)
        (D.intersection_finite q hq a) * (D.transverseMultiplicity a - 1) :=
    Finset.single_le_sum (f := fun a => intersectionMultiplicity (D.component a)
      (germLinearCombination g.1.component q) (D.intersection_finite q hq a) *
        (D.transverseMultiplicity a - 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (Nat.add_le_add_right (Nat.add_le_add_right hterm M) b).trans (D.polar_sum q hq)

/-- The selected index is outside the quantifier over general members.
The family must be nonempty so that its maximum is attained. -/
theorem exists_maximal_component [Nonempty ι] :
    ∃ i : ι,
      D.transverseMultiplicity i = Finset.univ.sup D.transverseMultiplicity ∧
      (∀ a, D.transverseMultiplicity a ≤ D.transverseMultiplicity i) ∧
      2 ≤ D.transverseMultiplicity i ∧
      D.component i ∈ maximalIdeal 2 ∧
      M ≤ D.transverseMultiplicity i ∧
      S + M ≤ 3 * D.transverseMultiplicity i ∧
      (∀ j k : Fin 3, D.component i ^ (D.transverseMultiplicity i - 1) ∣
        jacobian (g.1.component j) (g.1.component k)) ∧
      ∀ q (hq : q ∈ U),
        intersectionMultiplicity (D.component i) (germLinearCombination g.1.component q)
          (D.intersection_finite q hq i) * (D.transverseMultiplicity i - 1) + M + b ≤
            2 * S := by
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_mem_eq_sup
    Finset.univ Finset.univ_nonempty D.transverseMultiplicity
  refine ⟨i, hmax.symm, ?_, D.two_le_multiplicity i, D.component_mem i,
    ?_, ?_, D.component_dvd_minors i, D.component_polar i⟩
  · intro a
    rw [← hmax]
    exact Finset.le_sup (Finset.mem_univ a)
  · simpa only [hmax] using D.total_le_max
  · simpa only [hmax] using D.global_estimate

end CriticalComponentReductionData

end OnLeConjecture.Analytic
