/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedMonomialDivision
public import OnLeConjecture.Analytic.Coordinates

/-!
# Ordinary order as a finite monomial ideal

For weights `(1, 1)`, the finite weighted monomial ideal of degree `D` is
the `D`th power of the maximal ideal. This identifies ordinary jet order
with the finite ideal used in radial rescaling arguments.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Multiplication by the maximal ideal raises the finite ordinary order by
one. -/
theorem maximalIdeal_mul_weightedOrderIdeal_one (D : ℕ) :
    Germ.maximalIdeal 2 * Germ.weightedOrderIdeal 1 D =
      Germ.weightedOrderIdeal 1 (D + 1) := by
  apply le_antisymm
  · rw [← Germ.span_range_coordinate_eq_maximalIdeal,
      Germ.weightedOrderIdeal, Germ.weightedOrderIdeal,
      Ideal.span_mul_span, Ideal.span_le]
    intro z hz
    rw [Set.mem_mul] at hz
    rcases hz with ⟨u, ⟨i, rfl⟩, v, ⟨k, rfl⟩, rfl⟩
    fin_cases i
    · let j : Fin (D + 2) := ⟨(k : ℕ) + 1, by omega⟩
      have hj : Germ.weightedOrderGenerator 1 (D + 1) j ∈
          Germ.weightedOrderIdeal 1 (D + 1) :=
        Ideal.subset_span (Set.mem_range_self j)
      have hk : (k : ℕ) ≤ D := by omega
      have hexponent :
          D + 1 - 1 * ((k : ℕ) + 1) = D - 1 * (k : ℕ) := by
        omega
      have heq :
          Germ.coordinate (0 : Fin 2) *
              Germ.weightedOrderGenerator 1 D k =
            Germ.weightedOrderGenerator 1 (D + 1) j := by
        simp only [Germ.weightedOrderGenerator, j]
        rw [hexponent]
        ring
      have htarget :
          Germ.coordinate (0 : Fin 2) *
              Germ.weightedOrderGenerator 1 D k ∈
            Germ.weightedOrderIdeal 1 (D + 1) := by
        rw [heq]
        exact hj
      change
        Germ.coordinate (0 : Fin 2) *
            Germ.weightedOrderGenerator 1 D k ∈
          Germ.weightedOrderIdeal 1 (D + 1)
      exact htarget
    · let j : Fin (D + 2) := ⟨k, by omega⟩
      have hj : Germ.weightedOrderGenerator 1 (D + 1) j ∈
          Germ.weightedOrderIdeal 1 (D + 1) :=
        Ideal.subset_span (Set.mem_range_self j)
      have hk : (k : ℕ) ≤ D := by omega
      have hexponent :
          D + 1 - 1 * (k : ℕ) = (D - 1 * (k : ℕ)) + 1 := by
        omega
      have heq :
          Germ.coordinate (1 : Fin 2) *
              Germ.weightedOrderGenerator 1 D k =
            Germ.weightedOrderGenerator 1 (D + 1) j := by
        simp only [Germ.weightedOrderGenerator, j]
        rw [hexponent, pow_succ]
        ring
      have htarget :
          Germ.coordinate (1 : Fin 2) *
              Germ.weightedOrderGenerator 1 D k ∈
            Germ.weightedOrderIdeal 1 (D + 1) := by
        rw [heq]
        exact hj
      change
        Germ.coordinate (1 : Fin 2) *
            Germ.weightedOrderGenerator 1 D k ∈
          Germ.weightedOrderIdeal 1 (D + 1)
      exact htarget
  · rw [Germ.weightedOrderIdeal, Ideal.span_le]
    intro z hz
    rcases hz with ⟨k, rfl⟩
    by_cases hk : (k : ℕ) ≤ D
    · let j : Fin (D + 1) := ⟨k, by omega⟩
      have hx : Germ.coordinate (1 : Fin 2) ∈ Germ.maximalIdeal 2 :=
        Germ.coordinate_mem_maximalIdeal _
      have hj : Germ.weightedOrderGenerator 1 D j ∈
          Germ.weightedOrderIdeal 1 D :=
        Ideal.subset_span (Set.mem_range_self j)
      have hmul := Ideal.mul_mem_mul hx hj
      have hexponent :
          D + 1 - 1 * (k : ℕ) = (D - 1 * (k : ℕ)) + 1 := by
        omega
      have heq :
          Germ.weightedOrderGenerator 1 (D + 1) k =
            Germ.coordinate (1 : Fin 2) *
              Germ.weightedOrderGenerator 1 D j := by
        simp only [Germ.weightedOrderGenerator, j]
        rw [hexponent, pow_succ]
        ring
      rw [heq]
      exact hmul
    · have hk_last : (k : ℕ) = D + 1 := by omega
      let j : Fin (D + 1) := Fin.last D
      have hx : Germ.coordinate (0 : Fin 2) ∈ Germ.maximalIdeal 2 :=
        Germ.coordinate_mem_maximalIdeal _
      have hj : Germ.weightedOrderGenerator 1 D j ∈
          Germ.weightedOrderIdeal 1 D :=
        Ideal.subset_span (Set.mem_range_self j)
      have hmul := Ideal.mul_mem_mul hx hj
      have hk_fin : k = Fin.last (D + 1) := Fin.ext hk_last
      subst k
      have heq :
          Germ.weightedOrderGenerator 1 (D + 1) (Fin.last (D + 1)) =
            Germ.coordinate (0 : Fin 2) *
              Germ.weightedOrderGenerator 1 D j := by
        simp [Germ.weightedOrderGenerator, j, pow_succ']
      rw [heq]
      exact hmul

/-- For ordinary weights, the finite weighted monomial ideal is the
corresponding power of the maximal ideal. -/
theorem weightedOrderIdeal_one_eq_maximalIdeal_pow (D : ℕ) :
    Germ.weightedOrderIdeal 1 D = Germ.maximalIdeal 2 ^ D := by
  induction D with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      apply (Ideal.eq_top_iff_one _).2
      have hgenerator :
          Germ.weightedOrderGenerator 1 0 (Fin.last 0) = 1 := by
        simp [Germ.weightedOrderGenerator]
      rw [← hgenerator]
      exact Ideal.subset_span (Set.mem_range_self (Fin.last 0))
  | succ D ih =>
      rw [← maximalIdeal_mul_weightedOrderIdeal_one, ih]
      exact (pow_succ' (Germ.maximalIdeal 2) D).symm

/-- Membership in the finite ideal with ordinary weights is ordinary order
at least `D`. -/
theorem mem_weightedOrderIdeal_one_iff (D : ℕ) (f : Germ 2) :
    f ∈ Germ.weightedOrderIdeal 1 D ↔
      f ∈ Germ.maximalIdeal 2 ^ D := by
  rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal_pow]

end Germ

end OnLeConjecture.Analytic
