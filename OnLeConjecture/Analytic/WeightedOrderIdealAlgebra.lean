/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Derivation
public import OnLeConjecture.Analytic.TwoWeightMonomialIdeal

/-!
# Algebra of weighted order ideals

The finite ideal for weights `(a,1)` contains exactly the monomials whose
weighted degree reaches its threshold. These ideals are multiplicative.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Every displayed generator belongs to its weighted order ideal. -/
theorem weightedOrderGenerator_mem
    (a D : ℕ) (k : Fin (D + 1)) :
    Germ.weightedOrderGenerator a D k ∈
      Germ.weightedOrderIdeal a D :=
  Ideal.subset_span (Set.mem_range_self k)

/-- Every monomial of weighted degree at least `D` belongs to the finite
weighted order ideal. -/
theorem monomial_mem_weightedOrderIdeal_of_threshold
    (a D u v : ℕ) (ha : 0 < a)
    (hweight : D ≤ a * u + v) :
    Germ.coordinate (0 : Fin 2) ^ u *
        Germ.coordinate (1 : Fin 2) ^ v ∈
      Germ.weightedOrderIdeal a D := by
  by_cases hu : D ≤ u
  · let k : Fin (D + 1) := ⟨D, by omega⟩
    have hk := Germ.weightedOrderGenerator_mem a D k
    have hsub : D - a * D = 0 := by
      have hle : D ≤ a * D := by
        calc
          D = 1 * D := by simp
          _ ≤ a * D := Nat.mul_le_mul_right D ha
      omega
    have hpow : Germ.coordinate (0 : Fin 2) ^ (u - D) *
        Germ.coordinate (0 : Fin 2) ^ D =
          Germ.coordinate (0 : Fin 2) ^ u := by
      rw [← pow_add, Nat.sub_add_cancel hu]
    have hequality :
        Germ.coordinate (0 : Fin 2) ^ u *
            Germ.coordinate (1 : Fin 2) ^ v =
          (Germ.coordinate (0 : Fin 2) ^ (u - D) *
              Germ.coordinate (1 : Fin 2) ^ v) *
            Germ.weightedOrderGenerator a D k := by
      simp only [Germ.weightedOrderGenerator, k, hsub, pow_zero, mul_one]
      rw [← hpow]
      ring
    rw [hequality]
    exact Ideal.mul_mem_left _ _ hk
  · have huD : u < D := by omega
    let k : Fin (D + 1) := ⟨u, by omega⟩
    have hk := Germ.weightedOrderGenerator_mem a D k
    have hv : D - a * u ≤ v := by omega
    have hpow : Germ.coordinate (1 : Fin 2) ^ (v - (D - a * u)) *
        Germ.coordinate (1 : Fin 2) ^ (D - a * u) =
          Germ.coordinate (1 : Fin 2) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    have hequality :
        Germ.coordinate (0 : Fin 2) ^ u *
            Germ.coordinate (1 : Fin 2) ^ v =
          Germ.coordinate (1 : Fin 2) ^ (v - (D - a * u)) *
            Germ.weightedOrderGenerator a D k := by
      simp only [Germ.weightedOrderGenerator, k]
      rw [← hpow]
      ring
    rw [hequality]
    exact Ideal.mul_mem_left _ _ hk

/-- The original weighted order ideal agrees with the finite two weight
ideal for weights `(a,1)`. -/
theorem weightedOrderIdeal_eq_twoWeightOrderIdeal
    (a D : ℕ) (ha : 0 < a) :
    Germ.weightedOrderIdeal a D =
      Germ.twoWeightOrderIdeal a 1 D := by
  apply le_antisymm
  · rw [Germ.weightedOrderIdeal, Ideal.span_le]
    intro f hf
    obtain ⟨k, rfl⟩ := hf
    apply Germ.monomial_mem_twoWeightOrderIdeal_of_threshold
      a 1 D (k : ℕ) (D - a * (k : ℕ)) ha one_pos
    omega
  · rw [Germ.twoWeightOrderIdeal, Ideal.span_le]
    intro f hf
    obtain ⟨k, rfl⟩ := hf
    exact Germ.monomial_mem_weightedOrderIdeal_of_threshold
      a D (k.1.1 : ℕ) (k.1.2 : ℕ) ha (by simpa using k.2)

/-- Raising the threshold decreases the weighted order ideal. -/
theorem weightedOrderIdeal_antitone
    (a D E : ℕ) (ha : 0 < a) (hDE : D ≤ E) :
    Germ.weightedOrderIdeal a E ≤ Germ.weightedOrderIdeal a D := by
  rw [Germ.weightedOrderIdeal, Ideal.span_le]
  intro f hf
  obtain ⟨k, rfl⟩ := hf
  apply Germ.monomial_mem_weightedOrderIdeal_of_threshold
    a D (k : ℕ) (E - a * (k : ℕ)) ha
  have hE : E ≤ a * (k : ℕ) + (E - a * (k : ℕ)) := by omega
  exact hDE.trans hE

/-- Differentiating with respect to the first coordinate lowers weighted
order by at most `a`. -/
theorem partialDerivative_zero_mem_weightedOrderIdeal
    (a D : ℕ) (ha : 0 < a) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a (D + a)) :
    Germ.partialDerivative (0 : Fin 2) f ∈
      Germ.weightedOrderIdeal a D := by
  rw [Germ.mem_weightedOrderIdeal_iff] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc]
  change Germ.partialDerivation (0 : Fin 2)
      (∑ k, c k * Germ.weightedOrderGenerator a (D + a) k) ∈ _
  rw [map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [Germ.partialDerivation_apply, Germ.partialDerivative_mul]
  apply (Germ.weightedOrderIdeal a D).add_mem
  · exact Ideal.mul_mem_left _ _
      (Germ.weightedOrderIdeal_antitone a D (D + a) ha (by omega)
        (Germ.weightedOrderGenerator_mem a (D + a) k))
  · apply Ideal.mul_mem_left
    by_cases hk : (k : ℕ) = 0
    · have hkFin : k = 0 := Fin.eq_of_val_eq hk
      subst k
      simp [Germ.weightedOrderGenerator, Germ.partialDerivative_pow]
    · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
      have hweight :
          D ≤ a * ((k : ℕ) - 1) + (D + a - a * (k : ℕ)) := by
        have hkdecomp : (k : ℕ) = ((k : ℕ) - 1) + 1 := by omega
        have hthreshold :
            D + a ≤ a * (k : ℕ) + (D + a - a * (k : ℕ)) := by
          omega
        have hmul : a * (k : ℕ) = a * ((k : ℕ) - 1) + a := by
          calc
            a * (k : ℕ) = a * (((k : ℕ) - 1) + 1) := by
              exact congrArg (fun n : ℕ ↦ a * n) hkdecomp
            _ = a * ((k : ℕ) - 1) + a := by
              rw [Nat.mul_add, Nat.mul_one]
        rw [hmul] at hthreshold
        omega
      have hmonomial :=
        Germ.monomial_mem_weightedOrderIdeal_of_threshold
          a D ((k : ℕ) - 1) (D + a - a * (k : ℕ)) ha hweight
      have hderivative :
          Germ.partialDerivative (0 : Fin 2)
              (Germ.weightedOrderGenerator a (D + a) k) =
            (k : ℕ) •
              (Germ.coordinate (0 : Fin 2) ^ ((k : ℕ) - 1) *
                Germ.coordinate (1 : Fin 2) ^
                  (D + a - a * (k : ℕ))) := by
        simp only [Germ.weightedOrderGenerator,
          Germ.partialDerivative_mul, Germ.partialDerivative_pow,
          Germ.partialDerivative_coordinate_same,
          Germ.partialDerivative_coordinate_ne
            (show (0 : Fin 2) ≠ 1 by decide),
          mul_zero, add_zero, smul_eq_mul, mul_one,
          nsmul_eq_mul]
        ring
      rw [hderivative]
      exact (Germ.weightedOrderIdeal a D).toAddSubmonoid.nsmul_mem
        hmonomial (k : ℕ)

/-- Differentiating with respect to the second coordinate lowers weighted
order by at most one. -/
theorem partialDerivative_one_mem_weightedOrderIdeal
    (a D : ℕ) (ha : 0 < a) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a (D + 1)) :
    Germ.partialDerivative (1 : Fin 2) f ∈
      Germ.weightedOrderIdeal a D := by
  rw [Germ.mem_weightedOrderIdeal_iff] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc]
  change Germ.partialDerivation (1 : Fin 2)
      (∑ k, c k * Germ.weightedOrderGenerator a (D + 1) k) ∈ _
  rw [map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [Germ.partialDerivation_apply, Germ.partialDerivative_mul]
  apply (Germ.weightedOrderIdeal a D).add_mem
  · exact Ideal.mul_mem_left _ _
      (Germ.weightedOrderIdeal_antitone a D (D + 1) ha (by omega)
        (Germ.weightedOrderGenerator_mem a (D + 1) k))
  · apply Ideal.mul_mem_left
    let v := D + 1 - a * (k : ℕ)
    by_cases hv : v = 0
    · dsimp only [v] at hv
      simp [Germ.weightedOrderGenerator, hv,
        Germ.partialDerivative_pow]
    · have hvpos : 0 < v := Nat.pos_of_ne_zero hv
      have hweight : D ≤ a * (k : ℕ) + (v - 1) := by
        have hvdecomp : v = (v - 1) + 1 := by omega
        have hthreshold : D + 1 ≤ a * (k : ℕ) + v := by
          dsimp only [v]
          omega
        rw [hvdecomp] at hthreshold
        omega
      have hmonomial :=
        Germ.monomial_mem_weightedOrderIdeal_of_threshold
          a D (k : ℕ) (v - 1) ha hweight
      have hderivative :
          Germ.partialDerivative (1 : Fin 2)
              (Germ.weightedOrderGenerator a (D + 1) k) =
            v •
              (Germ.coordinate (0 : Fin 2) ^ (k : ℕ) *
                Germ.coordinate (1 : Fin 2) ^ (v - 1)) := by
        simp only [Germ.weightedOrderGenerator, v,
          Germ.partialDerivative_mul, Germ.partialDerivative_pow,
          Germ.partialDerivative_coordinate_same,
          Germ.partialDerivative_coordinate_ne
            (show (1 : Fin 2) ≠ 0 by decide),
          smul_eq_mul, mul_one,
          nsmul_eq_mul]
        ring
      rw [hderivative]
      exact (Germ.weightedOrderIdeal a D).toAddSubmonoid.nsmul_mem
        hmonomial v

/-- Multiplying weighted order ideals adds their thresholds. -/
theorem weightedOrderIdeal_mul_le
    (a D E : ℕ) (ha : 0 < a) :
    Germ.weightedOrderIdeal a D * Germ.weightedOrderIdeal a E ≤
      Germ.weightedOrderIdeal a (D + E) := by
  rw [Germ.weightedOrderIdeal, Germ.weightedOrderIdeal,
    Ideal.span_mul_span, Ideal.span_le]
  intro f hf
  rw [Set.mem_mul] at hf
  obtain ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩ := hf
  have hweightI :
      D ≤ a * (i : ℕ) + (D - a * (i : ℕ)) := by omega
  have hweightJ :
      E ≤ a * (j : ℕ) + (E - a * (j : ℕ)) := by omega
  have hweight :
      D + E ≤ a * ((i : ℕ) + (j : ℕ)) +
        ((D - a * (i : ℕ)) + (E - a * (j : ℕ))) := by
    calc
      D + E ≤
          (a * (i : ℕ) + (D - a * (i : ℕ))) +
            (a * (j : ℕ) + (E - a * (j : ℕ))) :=
        Nat.add_le_add hweightI hweightJ
      _ = a * ((i : ℕ) + (j : ℕ)) +
          ((D - a * (i : ℕ)) + (E - a * (j : ℕ))) := by ring
  have hmonomial := Germ.monomial_mem_weightedOrderIdeal_of_threshold
    a (D + E) ((i : ℕ) + (j : ℕ))
      ((D - a * (i : ℕ)) + (E - a * (j : ℕ))) ha hweight
  have hequality :
      Germ.weightedOrderGenerator a D i *
          Germ.weightedOrderGenerator a E j =
        Germ.coordinate (0 : Fin 2) ^ ((i : ℕ) + (j : ℕ)) *
          Germ.coordinate (1 : Fin 2) ^
            ((D - a * (i : ℕ)) + (E - a * (j : ℕ))) := by
    simp only [Germ.weightedOrderGenerator, pow_add]
    ring
  rw [hequality]
  exact hmonomial

/-- A product of elements of weighted orders `D` and `E` has weighted order
at least `D+E`. -/
theorem weightedOrderIdeal_mul_mem
    (a D E : ℕ) (ha : 0 < a) {f g : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a D)
    (hg : g ∈ Germ.weightedOrderIdeal a E) :
    f * g ∈ Germ.weightedOrderIdeal a (D + E) := by
  exact Germ.weightedOrderIdeal_mul_le a D E ha
    (Ideal.mul_mem_mul hf hg)

/-- The weighted order one ideal is the analytic maximal ideal. -/
theorem weightedOrderIdeal_one_eq_maximalIdeal
    (a : ℕ) (ha : 0 < a) :
    Germ.weightedOrderIdeal a 1 = Germ.maximalIdeal 2 := by
  rw [Germ.weightedOrderIdeal_eq_twoWeightOrderIdeal a 1 ha]
  apply le_antisymm
  · rw [Germ.twoWeightOrderIdeal, Ideal.span_le]
    intro f hf
    obtain ⟨k, rfl⟩ := hf
    by_cases hfirst : 0 < (k.1.1 : ℕ)
    · have hx : Germ.coordinate (0 : Fin 2) ^ (k.1.1 : ℕ) ∈
          Germ.maximalIdeal 2 :=
        Ideal.pow_mem_of_mem (Germ.maximalIdeal 2)
          (Germ.coordinate_mem_maximalIdeal 0) _ hfirst
      exact Ideal.mul_mem_right
        (Germ.coordinate (1 : Fin 2) ^ (k.1.2 : ℕ)) _ hx
    · have hsecond : 0 < (k.1.2 : ℕ) := by
        have hthreshold := k.2
        have hfirstZero : (k.1.1 : ℕ) = 0 :=
          Nat.eq_zero_of_not_pos hfirst
        rw [hfirstZero] at hthreshold
        omega
      have hy : Germ.coordinate (1 : Fin 2) ^ (k.1.2 : ℕ) ∈
          Germ.maximalIdeal 2 :=
        Ideal.pow_mem_of_mem (Germ.maximalIdeal 2)
          (Germ.coordinate_mem_maximalIdeal 1) _ hsecond
      exact Ideal.mul_mem_left _
        (Germ.coordinate (0 : Fin 2) ^ (k.1.1 : ℕ)) hy
  · rw [← Germ.span_range_coordinate_eq_maximalIdeal, Ideal.span_le]
    intro f hf
    obtain ⟨i, rfl⟩ := hf
    fin_cases i
    · have hmonomial :=
        Germ.monomial_mem_twoWeightOrderIdeal_of_threshold
          a 1 1 1 0 ha one_pos (by omega)
      simpa using hmonomial
    · have hmonomial :=
        Germ.monomial_mem_twoWeightOrderIdeal_of_threshold
          a 1 1 0 1 ha one_pos (by simp)
      simpa using hmonomial

end Germ

end OnLeConjecture.Analytic
