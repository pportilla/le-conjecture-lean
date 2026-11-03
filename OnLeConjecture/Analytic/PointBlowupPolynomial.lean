/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolar
public import OnLeConjecture.Analytic.RootClusterUnitComplement
public import OnLeConjecture.Analytic.WeightedPolynomialScaling
public import OnLeConjecture.Analytic.ScaledResultantOrder

/-!
# Polynomial identities in a point blowup chart

Root scaling in the coefficient ring gives the polynomial defining the
chart transform. The identities below compare it with the actual
analytic pullback and commute polynomial differentiation with analytic
differentiation.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem pointBlowupChart_pullback_hyperplaneExtension (c : ℂ) (a : Germ 1) :
    (pointBlowupChartGerm c).pullbackRingHom (hyperplaneExtension 1 a) =
      hyperplaneExtension 1 a := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFunction a
  rw [hyperplaneExtension_ofFunction, PointedMapGerm.pullbackRingHom_apply]
  change compPointed _ (PointedMapGerm.ofFunction _ _ _) = _
  rw [compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  change f (hyperplaneTail 1 (pointBlowupChart c z)) = f (hyperplaneTail 1 z)
  congr 1
  funext i
  fin_cases i
  rfl

theorem pointBlowupChart_pullback_polynomialEvaluation
    (c : ℂ) (P : Polynomial (Germ 1)) :
    (pointBlowupChartGerm c).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      P.eval₂ (hyperplaneExtension 1)
        (coordinate (1 : Fin 2) * (coordinate (0 : Fin 2) + constRingHom 2 c)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [firstCoordinatePolynomialEvaluation, eval₂_add, map_add] using
        congrArg₂ (· + ·) hP hQ
  | monomial n a =>
      simp only [firstCoordinatePolynomialEvaluation, eval₂_monomial, map_mul, map_pow,
        pointBlowupChart_pullback_hyperplaneExtension, pointBlowupChartGerm_pullback_zero]

/-- The scaled polynomial yields the actual strict-transform factor
identity in every finite point blowup chart. -/
theorem pointBlowupChart_pullback_scaled_polynomial
    (c : ℂ) (A : Polynomial (Germ 1)) :
    (pointBlowupChartGerm c).pullbackRingHom
        (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1)))) =
      coordinate (1 : Fin 2) ^ A.natDegree *
        firstCoordinatePolynomialEvaluation (rootTranslation A c) := by
  rw [pointBlowupChart_pullback_polynomialEvaluation]
  have hext : hyperplaneExtension 1 (coordinate (0 : Fin 1)) = coordinate (1 : Fin 2) :=
    hyperplaneExtension_coordinate_plane
  rw [← hext, scaleRoots_eval₂_mul]
  rw [hext]
  congr 1
  simp only [firstCoordinatePolynomialEvaluation, rootTranslation, taylor_apply, eval₂_comp,
    eval₂_add, eval₂_X, eval₂_C]
  congr 2

theorem partialDerivative_firstCoordinatePolynomialEvaluation
    (P : Polynomial (Germ 1)) :
    partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation P.derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [firstCoordinatePolynomialEvaluation, eval₂_add, derivative_add,
        partialDerivative_add] using congrArg₂ (· + ·) hP hQ
  | monomial n a =>
      cases n with
      | zero => simp [firstCoordinatePolynomialEvaluation,
          partialDerivative_zero_hyperplaneExtension]
      | succ n =>
          simp only [firstCoordinatePolynomialEvaluation, eval₂_monomial,
            partialDerivative_mul, partialDerivative_zero_hyperplaneExtension,
            zero_mul, zero_add, partialDerivative_pow, partialDerivative_coordinate_same,
            Nat.add_sub_cancel, derivative_monomial, map_mul, map_natCast,
            smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one, map_add, map_one]
          ring

/-- Analytic coefficient germs have characteristic zero, so polynomial
differentiation decreases the degree by one. -/
theorem natDegree_derivative_germ (A : Polynomial (Germ 1)) :
    A.derivative.natDegree = A.natDegree - 1 := by
  let _ : CharZero (Germ 1) := ⟨fun a b h ↦ by
    have hvalue := congrArg (valueRingHom 1) h
    simp only [map_natCast] at hvalue
    exact_mod_cast hvalue⟩
  exact natDegree_derivative A

/-- Differentiation commutes with root scaling over analytic coefficient
germs, whose characteristic is zero. -/
theorem derivative_scaleRoots_germ (A : Polynomial (Germ 1)) (y : Germ 1) :
    (A.scaleRoots y).derivative = A.derivative.scaleRoots y := by
  apply Polynomial.ext
  intro j
  simp only [coeff_derivative, coeff_scaleRoots, natDegree_derivative_germ, Nat.sub_sub]
  rw [Nat.add_comm 1 j]
  ring

end OnLeConjecture.Analytic.Germ
