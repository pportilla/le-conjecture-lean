/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm

/-!
# Existence of weighted polynomial initial forms

Every analytic germ in a weighted order ideal has a weighted homogeneous
polynomial representative modulo the next weighted order ideal.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

open scoped BigOperators

/-- An analytic germ of weighted order at least `D` has a weighted homogeneous
polynomial representative of degree `D` modulo weighted order `D + 1`. -/
theorem exists_weightedHomogeneous_coordinatePolynomial_mod_succ
    (a D : ℕ) (ha : 0 < a) (f : Germ 2)
    (hf : f ∈ Germ.weightedOrderIdeal a D) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P.IsWeightedHomogeneous ![a, 1] D ∧
      f - Germ.coordinatePolynomialAlgHom 2 P ∈
        Germ.weightedOrderIdeal a (D + 1) := by
  classical
  obtain ⟨c, hc⟩ := (Germ.mem_weightedOrderIdeal_iff a D f).mp hf
  let P : MvPolynomial (Fin 2) ℂ :=
    ∑ k : Fin (D + 1),
      if a * (k : ℕ) ≤ D then
        MvPolynomial.C (Germ.valueRingHom 2 (c k)) *
          MvPolynomial.X (0 : Fin 2) ^ (k : ℕ) *
            MvPolynomial.X (1 : Fin 2) ^ (D - a * (k : ℕ))
      else 0
  have hP : P.IsWeightedHomogeneous ![a, 1] D := by
    dsimp only [P]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro k _
    split_ifs with hk
    · have hx :
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
            |>.IsWeightedHomogeneous ![a, 1] a :=
        MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
      have hy :
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
            |>.IsWeightedHomogeneous ![a, 1] 1 :=
        MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
      have hterm :=
        ((hx.pow (k : ℕ)).mul
          (hy.pow (D - a * (k : ℕ)))).C_mul
            (Germ.valueRingHom 2 (c k))
      have hdegree :
          (k : ℕ) • a + (D - a * (k : ℕ)) • 1 = D := by
        simp only [nsmul_eq_mul, mul_one]
        change (k : ℕ) * a + (D - a * (k : ℕ)) = D
        rw [Nat.mul_comm (k : ℕ) a]
        exact Nat.add_sub_of_le hk
      simpa only [hdegree, mul_assoc] using hterm
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ ![a, 1] D
  refine ⟨P, hP, ?_⟩
  have hequality :
      f - Germ.coordinatePolynomialAlgHom 2 P =
        ∑ k : Fin (D + 1),
          (c k * Germ.weightedOrderGenerator a D k -
            Germ.coordinatePolynomialAlgHom 2
              (if a * (k : ℕ) ≤ D then
                MvPolynomial.C (Germ.valueRingHom 2 (c k)) *
                  MvPolynomial.X (0 : Fin 2) ^ (k : ℕ) *
                    MvPolynomial.X (1 : Fin 2) ^
                      (D - a * (k : ℕ))
              else 0)) := by
    rw [← hc]
    simp only [P, map_sum, Finset.sum_sub_distrib]
  rw [hequality]
  apply Ideal.sum_mem
  intro k _
  by_cases hk : a * (k : ℕ) ≤ D
  · have hcoefficient :
        c k - Germ.constRingHom 2 (Germ.valueRingHom 2 (c k)) ∈
          Germ.weightedOrderIdeal a 1 := by
      rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal a ha,
        Germ.mem_maximalIdeal_iff, map_sub, Germ.valueRingHom_const]
      simp
    have hgenerator : Germ.weightedOrderGenerator a D k ∈
        Germ.weightedOrderIdeal a D :=
      Germ.weightedOrderGenerator_mem a D k
    have hproduct := Germ.weightedOrderIdeal_mul_mem
      a 1 D ha hcoefficient hgenerator
    have htermEquality :
        c k * Germ.weightedOrderGenerator a D k -
            Germ.coordinatePolynomialAlgHom 2
              (if a * (k : ℕ) ≤ D then
                MvPolynomial.C (Germ.valueRingHom 2 (c k)) *
                  MvPolynomial.X (0 : Fin 2) ^ (k : ℕ) *
                    MvPolynomial.X (1 : Fin 2) ^
                      (D - a * (k : ℕ))
              else 0) =
          (c k - Germ.constRingHom 2 (Germ.valueRingHom 2 (c k))) *
            Germ.weightedOrderGenerator a D k := by
      simp only [if_pos hk, map_mul, map_pow,
        Germ.coordinatePolynomialAlgHom_C,
        Germ.coordinatePolynomialAlgHom_X,
        Germ.weightedOrderGenerator]
      ring
    rw [htermEquality]
    simpa only [Nat.add_comm] using hproduct
  · have hweight :
        D + 1 ≤ a * (k : ℕ) + (D - a * (k : ℕ)) := by
      omega
    have hgenerator : Germ.weightedOrderGenerator a D k ∈
        Germ.weightedOrderIdeal a (D + 1) := by
      exact Germ.monomial_mem_weightedOrderIdeal_of_threshold
        a (D + 1) (k : ℕ) (D - a * (k : ℕ)) ha hweight
    simp only [if_neg hk, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ hgenerator

/-- An analytic germ of exact weighted order `D` has a nonzero weighted
homogeneous initial form. -/
theorem exists_nonzero_weightedHomogeneous_coordinatePolynomial_mod_succ
    (a D : ℕ) (ha : 0 < a) (f : Germ 2)
    (hf : f ∈ Germ.weightedOrderIdeal a D)
    (hnext : f ∉ Germ.weightedOrderIdeal a (D + 1)) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      P ≠ 0 ∧ P.IsWeightedHomogeneous ![a, 1] D ∧
      f - Germ.coordinatePolynomialAlgHom 2 P ∈
        Germ.weightedOrderIdeal a (D + 1) := by
  obtain ⟨P, hP, htail⟩ :=
    Germ.exists_weightedHomogeneous_coordinatePolynomial_mod_succ
      a D ha f hf
  refine ⟨P, ?_, hP, htail⟩
  intro hzero
  subst P
  apply hnext
  simpa only [map_zero, sub_zero] using htail

end Germ

end OnLeConjecture.Analytic
