/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableLeadingTerm
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder
public import OnLeConjecture.Analytic.PlaneElimination
public import OnLeConjecture.DThree.AnalyticRescaling

/-!
# The cubic initial form of a prepared first component

The coefficient orders of a depressed analytic cubic determine its ordinary
degree three initial form. The value of its analytic unit is removed by a
constant target rescaling.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Extending a scalar monomial in the parameter gives the corresponding
monomial in the second plane coordinate. -/
theorem planeCoefficientExtension_const_mul_coordinate_pow
    (A : ℂ) (d : ℕ) :
    Germ.planeCoefficientExtension
        (Germ.constRingHom 1 A * Germ.coordinate (0 : Fin 1) ^ d) =
      Germ.constRingHom 2 A * Germ.coordinate (1 : Fin 2) ^ d := by
  rw [map_mul, map_pow]
  have hconstOne : Germ.constRingHom 1 A =
      algebraMap ℂ (Germ 1) A := by rfl
  have hconstTwo : Germ.constRingHom 2 A =
      algebraMap ℂ (Germ 2) A := by rfl
  rw [hconstOne, AlgHom.commutes, hconstTwo,
    Germ.planeCoefficientExtension_apply,
    Germ.hyperplaneExtension_coordinate_plane]

/-- Coordinate evaluation of `cubicForm A B` is its displayed plane cubic. -/
theorem coordinatePolynomial_cubicForm (A B : ℂ) :
    Germ.coordinatePolynomialAlgHom 2 (cubicForm A B) =
      Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.constRingHom 2 A * Germ.coordinate (0 : Fin 2) *
          Germ.coordinate (1 : Fin 2) ^ 2 +
        Germ.constRingHom 2 B * Germ.coordinate (1 : Fin 2) ^ 3 := by
  have hconst (c : ℂ) :
      algebraMap ℂ (Germ 2) c = Germ.constRingHom 2 c := by
    rfl
  simp [cubicForm, formX, formT, hconst]

/-- A depressed cubic multiplied by an analytic germ has the degree three
initial form obtained from the leading coefficient germs and the value of the
multiplier. -/
theorem depressedCubic_mul_sub_initialForm_mem_maximalIdeal_four
    (a₁ a₀ : Germ 1) (u : Germ 2) (A B : ℂ)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1 ^ 2)
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1 ^ 3)
    (ha₁Tail :
      a₁ - Germ.constRingHom 1 A * Germ.coordinate (0 : Fin 1) ^ 2 ∈
        Germ.maximalIdeal 1 ^ 3)
    (ha₀Tail :
      a₀ - Germ.constRingHom 1 B * Germ.coordinate (0 : Fin 1) ^ 3 ∈
        Germ.maximalIdeal 1 ^ 4) :
    let U := Germ.valueRingHom 2 u
    (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ * Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u -
        Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C U * cubicForm A B) ∈
      Germ.maximalIdeal 2 ^ 4 := by
  let x : Germ 2 := Germ.coordinate 0
  let y : Germ 2 := Germ.coordinate 1
  let P : Germ 2 :=
    x ^ 3 + Germ.planeCoefficientExtension a₁ * x +
      Germ.planeCoefficientExtension a₀
  let F : Germ 2 := Germ.coordinatePolynomialAlgHom 2 (cubicForm A B)
  let U : ℂ := Germ.valueRingHom 2 u
  have hx : x ∈ Germ.maximalIdeal 2 :=
    Germ.coordinate_mem_maximalIdeal 0
  have hPTail : P - F ∈ Germ.maximalIdeal 2 ^ 4 := by
    have ha₁Extension :
        Germ.planeCoefficientExtension
            (a₁ - Germ.constRingHom 1 A *
              Germ.coordinate (0 : Fin 1) ^ 2) ∈
          Germ.maximalIdeal 2 ^ 3 := by
      change Germ.hyperplaneExtension 1
          (a₁ - Germ.constRingHom 1 A *
            Germ.coordinate (0 : Fin 1) ^ 2) ∈
        Germ.maximalIdeal 2 ^ 3
      exact PointedMapGerm.pullback_mem_maximalIdeal_pow
        (Germ.hyperplaneTailGerm 1) ha₁Tail
    have ha₀Extension :
        Germ.planeCoefficientExtension
            (a₀ - Germ.constRingHom 1 B *
              Germ.coordinate (0 : Fin 1) ^ 3) ∈
          Germ.maximalIdeal 2 ^ 4 := by
      change Germ.hyperplaneExtension 1
          (a₀ - Germ.constRingHom 1 B *
            Germ.coordinate (0 : Fin 1) ^ 3) ∈
        Germ.maximalIdeal 2 ^ 4
      exact PointedMapGerm.pullback_mem_maximalIdeal_pow
        (Germ.hyperplaneTailGerm 1) ha₀Tail
    have hlinearProduct := Ideal.mul_mem_mul ha₁Extension hx
    have hlinear :
        Germ.planeCoefficientExtension
            (a₁ - Germ.constRingHom 1 A *
              Germ.coordinate (0 : Fin 1) ^ 2) * x ∈
          Germ.maximalIdeal 2 ^ 4 := by
      simpa only [show (4 : ℕ) = 3 + 1 by omega,
        Submodule.pow_succ] using hlinearProduct
    have hsum :=
      (Germ.maximalIdeal 2 ^ 4).add_mem hlinear ha₀Extension
    have hleadingOne :
        Germ.planeCoefficientExtension
            (Germ.constRingHom 1 A *
              Germ.coordinate (0 : Fin 1) ^ 2) =
          Germ.constRingHom 2 A * y ^ 2 := by
      simpa only [y] using
        planeCoefficientExtension_const_mul_coordinate_pow A 2
    have hleadingZero :
        Germ.planeCoefficientExtension
            (Germ.constRingHom 1 B *
              Germ.coordinate (0 : Fin 1) ^ 3) =
          Germ.constRingHom 2 B * y ^ 3 := by
      simpa only [y] using
        planeCoefficientExtension_const_mul_coordinate_pow B 3
    have hF :
        F = x ^ 3 + Germ.constRingHom 2 A * x * y ^ 2 +
          Germ.constRingHom 2 B * y ^ 3 := by
      simpa only [F, x, y] using coordinatePolynomial_cubicForm A B
    have hequality :
        P - F =
          Germ.planeCoefficientExtension
              (a₁ - Germ.constRingHom 1 A *
                Germ.coordinate (0 : Fin 1) ^ 2) * x +
            Germ.planeCoefficientExtension
              (a₀ - Germ.constRingHom 1 B *
                Germ.coordinate (0 : Fin 1) ^ 3) := by
      rw [hF, map_sub, map_sub, hleadingOne, hleadingZero]
      dsimp only [P]
      ring
    rw [hequality]
    exact hsum
  have hP : P ∈ Germ.maximalIdeal 2 ^ 3 := by
    exact Germ.depressedCubic_mem_maximalIdeal_cube_of_coefficients
      a₁ a₀ ha₁ ha₀
  have huTail : u - Germ.constRingHom 2 U ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff, map_sub,
      Germ.valueRingHom_const]
    simp [U]
  have hfirstProduct := Ideal.mul_mem_mul hP huTail
  have hfirst : P * (u - Germ.constRingHom 2 U) ∈
      Germ.maximalIdeal 2 ^ 4 := by
    simpa only [show (4 : ℕ) = 3 + 1 by omega,
      Submodule.pow_succ] using hfirstProduct
  have hsecond : (P - F) * Germ.constRingHom 2 U ∈
      Germ.maximalIdeal 2 ^ 4 :=
    Ideal.mul_mem_right (Germ.constRingHom 2 U)
      (Germ.maximalIdeal 2 ^ 4) hPTail
  have hsum := (Germ.maximalIdeal 2 ^ 4).add_mem hfirst hsecond
  have hcoordinate :
      Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C U * cubicForm A B) =
        Germ.constRingHom 2 U * F := by
    rw [map_mul, Germ.coordinatePolynomialAlgHom_C]
  change P * u - Germ.coordinatePolynomialAlgHom 2
      (MvPolynomial.C U * cubicForm A B) ∈ Germ.maximalIdeal 2 ^ 4
  rw [hcoordinate]
  have hequality :
      P * u - Germ.constRingHom 2 U * F =
        P * (u - Germ.constRingHom 2 U) +
          (P - F) * Germ.constRingHom 2 U := by
    ring
  rw [hequality]
  exact hsum

/-- Rescaling the leading cubic by the inverse value of the analytic unit
restores its monic normalization. -/
theorem rescaleForm_inv_mul_cubicForm
    (U A B : ℂ) (hU : U ≠ 0) :
    rescaleForm 1 U⁻¹ (MvPolynomial.C U * cubicForm A B) =
      cubicForm A B := by
  simp only [rescaleForm, Fin.isValue, MvPolynomial.C_1, formX, one_mul,
    formT, MvPolynomial.eval₂Hom_C_eq_bind₁, cubicForm, RingHom.coe_coe,
    map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, map_add,
    map_pow, MvPolynomial.bind₁_X_right, ↓reduceIte, one_ne_zero]
  rw [← mul_assoc, ← map_mul]
  rw [inv_mul_cancel₀ hU, map_one, one_mul]

/-- An injective germ of coordinate order three admits an equivalent germ
whose first component has the displayed cubic initial form. -/
theorem exists_injective_firstComponent_cubicInitialForm
    (g : PointedMapGerm 2 3)
    (hfinite : g.IsFiniteAtOrigin)
    (hinjective : g.HasInjectiveRepresentative)
    (hdifferential : g.differential = 0)
    (horder : g.coordinateOrder (by omega) hfinite = 3) :
    ∃ h : PointedMapGerm 2 3, ∃ A B : ℂ,
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        h.HasInjectiveRepresentative ∧ h.differential = 0 ∧
        h.1.component 0 - Germ.coordinatePolynomialAlgHom 2
            (cubicForm A B) ∈ Germ.maximalIdeal 2 ^ 4 := by
  obtain ⟨h₀, a₁, a₀, u, hequivalent₀, hfinite₀,
      hinjective₀, hdifferential₀, ha₁, ha₀, hu, hcomponent⟩ :=
    g.exists_injective_firstComponent_depressedCubic_with_coefficientOrders
      hfinite hinjective hdifferential horder
  obtain ⟨A, ha₁Tail⟩ :=
    Germ.exists_scalar_leadingTerm_of_mem_maximalIdeal_pow a₁ 2 ha₁
  obtain ⟨B, ha₀Tail⟩ :=
    Germ.exists_scalar_leadingTerm_of_mem_maximalIdeal_pow a₀ 3 ha₀
  let U : ℂ := Germ.valueRingHom 2 u
  have hU : U ≠ 0 := by
    exact Germ.valueRingHom_ne_zero_of_isUnit hu
  have htailBefore :
      h₀.1.component 0 - Germ.coordinatePolynomialAlgHom 2
          (MvPolynomial.C U * cubicForm A B) ∈
        Germ.maximalIdeal 2 ^ 4 := by
    rw [hcomponent]
    exact depressedCubic_mul_sub_initialForm_mem_maximalIdeal_four
      a₁ a₀ u A B ha₁ ha₀ ha₁Tail ha₀Tail
  let h := rescaledPointedMap h₀ 1 U⁻¹ 1 1 one_ne_zero
    (inv_ne_zero hU) one_ne_zero one_ne_zero
  have hequivalent₁ : h₀.RightLeftEquivalent h :=
    rightLeftEquivalent_rescaledPointedMap h₀ 1 U⁻¹ 1 1
      one_ne_zero (inv_ne_zero hU) one_ne_zero one_ne_zero
  have hequivalent : g.RightLeftEquivalent h :=
    hequivalent₀.trans hequivalent₁
  have hfiniteH : h.IsFiniteAtOrigin :=
    hequivalent.isFiniteAtOrigin_iff.mpr hfinite
  have hinjectiveH : h.HasInjectiveRepresentative :=
    hequivalent.hasInjectiveRepresentative hinjective
  have hdifferentialH : h.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff
      hequivalent).mpr hdifferential
  refine ⟨h, A, B, hequivalent, hfiniteH, hinjectiveH,
    hdifferentialH, ?_⟩
  have htail := rescaledPointedMap_component_tail
    h₀ 1 U⁻¹ 1 1 one_ne_zero (inv_ne_zero hU) one_ne_zero
      one_ne_zero 0 (MvPolynomial.C U * cubicForm A B) 4 htailBefore
  have htarget :
      targetRescaleVector U⁻¹ 1 1 (0 : Fin 3) = U⁻¹ := rfl
  rw [htarget, rescaleForm_inv_mul_cubicForm U A B hU] at htail
  exact htail

end OnLeConjecture.DThree
