/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra
public import OnLeConjecture.DThree.DepressedCubicInitialForm

/-!
# Weighted initial form of a depressed cubic

The leading terms of the two coefficient germs determine the cubic form for
weights `(a,1)`. Multiplication by an analytic unit preserves the strict next
weighted order after its value is included in the polynomial coefficient.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The cubic polynomial obtained from `cubicForm A B` after replacing its
second variable by the `a`th power of the second source coordinate. -/
@[expose]
noncomputable def weightedCubicPolynomial
    (a : ℕ) (A B : ℂ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 ^ 3 +
    MvPolynomial.C A * MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a) +
    MvPolynomial.C B * MvPolynomial.X 1 ^ (3 * a)

/-- Coordinate evaluation of the weighted cubic is its displayed analytic
germ. -/
theorem coordinatePolynomial_weightedCubicPolynomial
    (a : ℕ) (A B : ℂ) :
    Germ.coordinatePolynomialAlgHom 2 (weightedCubicPolynomial a A B) =
      Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.constRingHom 2 A * Germ.coordinate (0 : Fin 2) *
          Germ.coordinate (1 : Fin 2) ^ (2 * a) +
        Germ.constRingHom 2 B * Germ.coordinate (1 : Fin 2) ^ (3 * a) := by
  have hconst (c : ℂ) :
      algebraMap ℂ (Germ 2) c = Germ.constRingHom 2 c := by rfl
  simp [weightedCubicPolynomial, hconst]

/-- The weighted cubic is homogeneous of weighted degree `3a`. -/
theorem weightedCubicPolynomial_isWeightedHomogeneous
    (a : ℕ) (A B : ℂ) :
    (weightedCubicPolynomial a A B).IsWeightedHomogeneous
      ![a, 1] (3 * a) := by
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] a :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 0
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ)
      |>.IsWeightedHomogeneous ![a, 1] 1 :=
    MvPolynomial.isWeightedHomogeneous_X ℂ ![a, 1] 1
  have hfirst :
      (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ)
        |>.IsWeightedHomogeneous ![a, 1] (3 * a) := by
    simpa [nsmul_eq_mul] using hx.pow 3
  have hsecond :
      (MvPolynomial.C A * MvPolynomial.X (0 : Fin 2) *
          MvPolynomial.X (1 : Fin 2) ^ (2 * a) :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
        ![a, 1] (3 * a) := by
    have hraw := (hx.mul (hy.pow (2 * a))).C_mul A
    have hdegree : a + (2 * a) • 1 = 3 * a := by
      simp
      omega
    simpa only [hdegree, mul_assoc] using hraw
  have hthird :
      (MvPolynomial.C B * MvPolynomial.X (1 : Fin 2) ^ (3 * a) :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous
        ![a, 1] (3 * a) := by
    simpa [nsmul_eq_mul] using (hy.pow (3 * a)).C_mul B
  simpa only [weightedCubicPolynomial] using
    (hfirst.add hsecond).add hthird

private theorem oneVariable_factor_of_mem_maximalIdeal_pow
    (q : Germ 1) (d : ℕ) (hq : q ∈ Germ.maximalIdeal 1 ^ d) :
    ∃ v : Germ 1,
      q = Germ.coordinate (0 : Fin 1) ^ d * v := by
  rw [Germ.maximalIdeal_one_pow_eq_span_coordinate_pow,
    Ideal.mem_span_singleton] at hq
  exact hq

private theorem planeExtension_factor
    (q v : Germ 1) (d : ℕ)
    (hq : q = Germ.coordinate (0 : Fin 1) ^ d * v) :
    Germ.planeCoefficientExtension q =
      Germ.coordinate (1 : Fin 2) ^ d *
        Germ.planeCoefficientExtension v := by
  rw [hq, map_mul, map_pow, Germ.planeCoefficientExtension_apply,
    Germ.hyperplaneExtension_coordinate_plane]

/-- The depressed cubic before multiplication by its unit has weighted order
at least `3a`. -/
theorem depressedCubic_mem_weightedOrderIdeal
    (a : ℕ) (ha : 0 < a) (a₁ a₀ : Germ 1)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a)) :
    Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀ ∈
      Germ.weightedOrderIdeal a (3 * a) := by
  obtain ⟨v₁, hv₁⟩ :=
    oneVariable_factor_of_mem_maximalIdeal_pow a₁ (2 * a) ha₁
  obtain ⟨v₀, hv₀⟩ :=
    oneVariable_factor_of_mem_maximalIdeal_pow a₀ (3 * a) ha₀
  have hfirst := Germ.monomial_mem_weightedOrderIdeal_of_threshold
    a (3 * a) 3 0 ha (by omega)
  have hsecondMonomial :=
    Germ.monomial_mem_weightedOrderIdeal_of_threshold
      a (3 * a) 1 (2 * a) ha (by omega)
  have hsecond := Ideal.mul_mem_right
    (Germ.planeCoefficientExtension v₁)
      (Germ.weightedOrderIdeal a (3 * a)) hsecondMonomial
  have hsecondEquality :
      Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) =
        (Germ.coordinate (0 : Fin 2) *
          Germ.coordinate (1 : Fin 2) ^ (2 * a)) *
            Germ.planeCoefficientExtension v₁ := by
    rw [planeExtension_factor a₁ v₁ (2 * a) hv₁]
    ring
  have hsecond' :
      Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) ∈
        Germ.weightedOrderIdeal a (3 * a) := by
    rw [hsecondEquality]
    simpa only [pow_one] using hsecond
  have hthirdMonomial :=
    Germ.monomial_mem_weightedOrderIdeal_of_threshold
      a (3 * a) 0 (3 * a) ha (by omega)
  have hthird := Ideal.mul_mem_right
    (Germ.planeCoefficientExtension v₀)
      (Germ.weightedOrderIdeal a (3 * a)) hthirdMonomial
  have hthirdEquality :
      Germ.planeCoefficientExtension a₀ =
        (Germ.coordinate (0 : Fin 2) ^ 0 *
          Germ.coordinate (1 : Fin 2) ^ (3 * a)) *
            Germ.planeCoefficientExtension v₀ := by
    rw [planeExtension_factor a₀ v₀ (3 * a) hv₀]
    ring
  have hthird' : Germ.planeCoefficientExtension a₀ ∈
      Germ.weightedOrderIdeal a (3 * a) := by
    rw [hthirdEquality]
    exact hthird
  have hfirst' : Germ.coordinate (0 : Fin 2) ^ 3 ∈
      Germ.weightedOrderIdeal a (3 * a) := by
    simpa only [pow_zero, mul_one] using hfirst
  exact (Germ.weightedOrderIdeal a (3 * a)).add_mem
    ((Germ.weightedOrderIdeal a (3 * a)).add_mem hfirst' hsecond') hthird'

/-- The differences of the two coefficient germs from their leading terms
give a strict weighted tail for the depressed cubic. -/
theorem depressedCubic_sub_weightedInitial_mem_weightedOrderIdeal
    (a : ℕ) (ha : 0 < a) (a₁ a₀ : Germ 1) (A B : ℂ)
    (ha₁Tail :
      a₁ - Germ.constRingHom 1 A *
          Germ.coordinate (0 : Fin 1) ^ (2 * a) ∈
        Germ.maximalIdeal 1 ^ (2 * a + 1))
    (ha₀Tail :
      a₀ - Germ.constRingHom 1 B *
          Germ.coordinate (0 : Fin 1) ^ (3 * a) ∈
        Germ.maximalIdeal 1 ^ (3 * a + 1)) :
    (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) -
        Germ.coordinatePolynomialAlgHom 2
          (weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1) := by
  obtain ⟨v₁, hv₁⟩ := oneVariable_factor_of_mem_maximalIdeal_pow
    (a₁ - Germ.constRingHom 1 A *
      Germ.coordinate (0 : Fin 1) ^ (2 * a)) (2 * a + 1) ha₁Tail
  obtain ⟨v₀, hv₀⟩ := oneVariable_factor_of_mem_maximalIdeal_pow
    (a₀ - Germ.constRingHom 1 B *
      Germ.coordinate (0 : Fin 1) ^ (3 * a)) (3 * a + 1) ha₀Tail
  have hlinearMonomial :=
    Germ.monomial_mem_weightedOrderIdeal_of_threshold
      a (3 * a + 1) 1 (2 * a + 1) ha (by omega)
  have hlinear := Ideal.mul_mem_right
    (Germ.planeCoefficientExtension v₁)
      (Germ.weightedOrderIdeal a (3 * a + 1)) hlinearMonomial
  have hconstantMonomial :=
    Germ.monomial_mem_weightedOrderIdeal_of_threshold
      a (3 * a + 1) 0 (3 * a + 1) ha (by omega)
  have hconstant := Ideal.mul_mem_right
    (Germ.planeCoefficientExtension v₀)
      (Germ.weightedOrderIdeal a (3 * a + 1)) hconstantMonomial
  have hlinearEquality :
      Germ.planeCoefficientExtension
          (a₁ - Germ.constRingHom 1 A *
            Germ.coordinate (0 : Fin 1) ^ (2 * a)) *
          Germ.coordinate (0 : Fin 2) =
        (Germ.coordinate (0 : Fin 2) *
          Germ.coordinate (1 : Fin 2) ^ (2 * a + 1)) *
            Germ.planeCoefficientExtension v₁ := by
    rw [planeExtension_factor _ v₁ (2 * a + 1) hv₁]
    ring
  have hlinear' :
      Germ.planeCoefficientExtension
          (a₁ - Germ.constRingHom 1 A *
            Germ.coordinate (0 : Fin 1) ^ (2 * a)) *
          Germ.coordinate (0 : Fin 2) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
    rw [hlinearEquality]
    simpa only [pow_one] using hlinear
  have hconstantEquality :
      Germ.planeCoefficientExtension
          (a₀ - Germ.constRingHom 1 B *
            Germ.coordinate (0 : Fin 1) ^ (3 * a)) =
        (Germ.coordinate (0 : Fin 2) ^ 0 *
          Germ.coordinate (1 : Fin 2) ^ (3 * a + 1)) *
            Germ.planeCoefficientExtension v₀ := by
    rw [planeExtension_factor _ v₀ (3 * a + 1) hv₀]
    ring
  have hconstant' :
      Germ.planeCoefficientExtension
          (a₀ - Germ.constRingHom 1 B *
            Germ.coordinate (0 : Fin 1) ^ (3 * a)) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
    rw [hconstantEquality]
    exact hconstant
  have hequality :
      (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.planeCoefficientExtension a₁ *
              Germ.coordinate (0 : Fin 2) +
            Germ.planeCoefficientExtension a₀) -
          Germ.coordinatePolynomialAlgHom 2
            (weightedCubicPolynomial a A B) =
        Germ.planeCoefficientExtension
            (a₁ - Germ.constRingHom 1 A *
              Germ.coordinate (0 : Fin 1) ^ (2 * a)) *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension
            (a₀ - Germ.constRingHom 1 B *
              Germ.coordinate (0 : Fin 1) ^ (3 * a)) := by
    rw [coordinatePolynomial_weightedCubicPolynomial,
      map_sub, map_sub,
      planeCoefficientExtension_const_mul_coordinate_pow,
      planeCoefficientExtension_const_mul_coordinate_pow]
    ring
  rw [hequality]
  exact (Germ.weightedOrderIdeal a (3 * a + 1)).add_mem
    hlinear' hconstant'

/-- Multiplication by an analytic unit changes the weighted initial form by
its value and leaves a strict weighted tail. -/
theorem depressedCubic_mul_sub_weightedInitial_mem_weightedOrderIdeal
    (a : ℕ) (ha : 0 < a) (a₁ a₀ : Germ 1) (u : Germ 2) (A B : ℂ)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (ha₁Tail :
      a₁ - Germ.constRingHom 1 A *
          Germ.coordinate (0 : Fin 1) ^ (2 * a) ∈
        Germ.maximalIdeal 1 ^ (2 * a + 1))
    (ha₀Tail :
      a₀ - Germ.constRingHom 1 B *
          Germ.coordinate (0 : Fin 1) ^ (3 * a) ∈
        Germ.maximalIdeal 1 ^ (3 * a + 1)) :
    let U := Germ.valueRingHom 2 u
    (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u -
        Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C U * weightedCubicPolynomial a A B) ∈
      Germ.weightedOrderIdeal a (3 * a + 1) := by
  let P : Germ 2 :=
    Germ.coordinate (0 : Fin 2) ^ 3 +
      Germ.planeCoefficientExtension a₁ * Germ.coordinate 0 +
      Germ.planeCoefficientExtension a₀
  let F : Germ 2 := Germ.coordinatePolynomialAlgHom 2
    (weightedCubicPolynomial a A B)
  let U : ℂ := Germ.valueRingHom 2 u
  have hP : P ∈ Germ.weightedOrderIdeal a (3 * a) := by
    exact depressedCubic_mem_weightedOrderIdeal a ha a₁ a₀ ha₁ ha₀
  have hPTail : P - F ∈ Germ.weightedOrderIdeal a (3 * a + 1) := by
    exact depressedCubic_sub_weightedInitial_mem_weightedOrderIdeal
      a ha a₁ a₀ A B ha₁Tail ha₀Tail
  have huTail : u - Germ.constRingHom 2 U ∈
      Germ.weightedOrderIdeal a 1 := by
    rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal a ha,
      Germ.mem_maximalIdeal_iff, map_sub, Germ.valueRingHom_const]
    simp [U]
  have hfirst : P * (u - Germ.constRingHom 2 U) ∈
      Germ.weightedOrderIdeal a (3 * a + 1) := by
    simpa only [Nat.add_comm] using
      Germ.weightedOrderIdeal_mul_mem a (3 * a) 1 ha hP huTail
  have hsecond : (P - F) * Germ.constRingHom 2 U ∈
      Germ.weightedOrderIdeal a (3 * a + 1) :=
    Ideal.mul_mem_right (Germ.constRingHom 2 U) _ hPTail
  have hcoordinate :
      Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C U * weightedCubicPolynomial a A B) =
        Germ.constRingHom 2 U * F := by
    rw [map_mul, Germ.coordinatePolynomialAlgHom_C]
  change P * u - Germ.coordinatePolynomialAlgHom 2
      (MvPolynomial.C U * weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1)
  rw [hcoordinate]
  have hequality :
      P * u - Germ.constRingHom 2 U * F =
        P * (u - Germ.constRingHom 2 U) +
          (P - F) * Germ.constRingHom 2 U := by ring
  rw [hequality]
  exact (Germ.weightedOrderIdeal a (3 * a + 1)).add_mem hfirst hsecond

/-- If at least one coefficient has the exact threshold order, the weighted
cubic initial form has a nonzero lower coefficient. -/
theorem exists_weightedCubicInitialForm_of_coefficientOrders
    (a : ℕ) (ha : 0 < a) (a₁ a₀ : Germ 1) (u : Germ 2)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ (2 * a))
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ (3 * a))
    (hexact :
      a₁ ∉ Germ.maximalIdeal 1 ^ (2 * a + 1) ∨
        a₀ ∉ Germ.maximalIdeal 1 ^ (3 * a + 1)) :
    ∃ A B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧
      let U := Germ.valueRingHom 2 u
      (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.planeCoefficientExtension a₁ *
              Germ.coordinate (0 : Fin 2) +
            Germ.planeCoefficientExtension a₀) * u -
          Germ.coordinatePolynomialAlgHom 2
            (MvPolynomial.C U * weightedCubicPolynomial a A B) ∈
        Germ.weightedOrderIdeal a (3 * a + 1) := by
  rcases hexact with ha₁Exact | ha₀Exact
  · obtain ⟨A, hA, ha₁Tail⟩ :=
      Germ.exists_nonzero_scalar_leadingTerm_of_exact_maximalIdeal_pow
        a₁ (2 * a) ha₁ ha₁Exact
    obtain ⟨B, ha₀Tail⟩ :=
      Germ.exists_scalar_leadingTerm_of_mem_maximalIdeal_pow
        a₀ (3 * a) ha₀
    refine ⟨A, B, Or.inl hA, ?_⟩
    exact depressedCubic_mul_sub_weightedInitial_mem_weightedOrderIdeal
      a ha a₁ a₀ u A B ha₁ ha₀ ha₁Tail ha₀Tail
  · obtain ⟨A, ha₁Tail⟩ :=
      Germ.exists_scalar_leadingTerm_of_mem_maximalIdeal_pow
        a₁ (2 * a) ha₁
    obtain ⟨B, hB, ha₀Tail⟩ :=
      Germ.exists_nonzero_scalar_leadingTerm_of_exact_maximalIdeal_pow
        a₀ (3 * a) ha₀ ha₀Exact
    refine ⟨A, B, Or.inr hB, ?_⟩
    exact depressedCubic_mul_sub_weightedInitial_mem_weightedOrderIdeal
      a ha a₁ a₀ u A B ha₁ ha₀ ha₁Tail ha₀Tail

end OnLeConjecture.DThree
