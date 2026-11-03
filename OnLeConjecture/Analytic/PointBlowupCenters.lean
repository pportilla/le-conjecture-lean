/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Analytic.CoordinatePermutation
import Mathlib.Tactic

/-!
# Blowup centers are zeros of the actual ordinary initial form

The exceptional restriction of the analytic strict transform determines
which chart centers can lie on the transformed curve. For initial form
`κ*x^m`, the finite chart admits only center zero. The complementary
chart, where the initial form becomes `κ*y^m`, has no such center.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

private theorem value_translated_initial_chart
    (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    valueRingHom 1 (oneVariablePolynomialEvaluation
      (MvPolynomial.aeval (![X + C c, 1] : Fin 2 → ℂ[X]) P)) =
      MvPolynomial.eval ![c, 1] P := by
  have hconst (a : ℂ) : valueRingHom 1 ((algebraMap ℂ (Germ 1)) a) = a :=
    valueRingHom_const 1 a
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
        oneVariablePolynomialEvaluation, Polynomial.aeval_C, MvPolynomial.eval_C,
        hconst, Algebra.algebraMap_self, RingHom.id_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP, MvPolynomial.eval_mul]
      congr 1
      fin_cases i <;>
        simp [oneVariablePolynomialEvaluation, MvPolynomial.aeval_X,
          Polynomial.aeval_X, Polynomial.aeval_C, valueRingHom_coordinate, hconst]

/-- Every chart center at which the strict transform vanishes is a root
of the ordinary initial polynomial on the exceptional line. -/
theorem initial_eval_eq_zero_of_vanishing_pointBlowupTransform
    (c : ℂ) (m : ℕ) (f g : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hP : P.IsWeightedHomogeneous ![1, 1] m)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) (hg : g ∈ maximalIdeal 2) :
    MvPolynomial.eval ![c, 1] P = 0 := by
  have hrestriction := pointBlowupTransform_exceptionalRestriction c m f g P
    hf hnext hP htail htransform
  have hvalue := congrArg (valueRingHom 1) hrestriction
  rw [PointedMapGerm.valueRingHom_pullback, value_translated_initial_chart,
    mem_maximalIdeal_iff.mp hg] at hvalue
  exact hvalue.symm

/-- A nonzero pure first-coordinate tangent polynomial allows only the
finite exceptional coordinate zero. -/
theorem center_eq_zero_of_initial_first_power
    (c κ : ℂ) (hκ : κ ≠ 0) (m : ℕ) (hm : 0 < m) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (htail : f - constRingHom 2 κ * coordinate (0 : Fin 2) ^ m ∈
      maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) (hg : g ∈ maximalIdeal 2) : c = 0 := by
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.C κ * MvPolynomial.X 0 ^ m
  have hP : P.IsWeightedHomogeneous ![1, 1] m := by
    simpa only [P, Matrix.cons_val_zero, nsmul_eq_mul, mul_one, Nat.cast_id] using
      ((MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 0).pow m).C_mul κ
  have hPtail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1) := by
    simpa only [P, map_mul, map_pow, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X] using htail
  have heval := initial_eval_eq_zero_of_vanishing_pointBlowupTransform c m f g P
    hf hnext hP hPtail htransform hg
  have hzero : κ * c ^ m = 0 := by simpa [P] using heval
  exact (pow_eq_zero_iff hm.ne').mp ((mul_eq_zero.mp hzero).resolve_left hκ)

/-- A nonzero pure second-coordinate initial form does not vanish
anywhere on this exceptional chart. Applied after swapping coordinates,
this rules out the point at infinity for a pure first-coordinate tangent. -/
theorem no_vanishing_transform_of_initial_second_power
    (c κ : ℂ) (hκ : κ ≠ 0) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (htail : f - constRingHom 2 κ * coordinate (1 : Fin 2) ^ m ∈
      maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) (hg : g ∈ maximalIdeal 2) : False := by
  let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.C κ * MvPolynomial.X 1 ^ m
  have hP : P.IsWeightedHomogeneous ![1, 1] m := by
    simpa only [P, Matrix.cons_val_one, Matrix.cons_val_zero, nsmul_eq_mul,
      mul_one, Nat.cast_id] using
      ((MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) 1).pow m).C_mul κ
  have hPtail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1) := by
    simpa only [P, map_mul, map_pow, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X] using htail
  have heval := initial_eval_eq_zero_of_vanishing_pointBlowupTransform c m f g P
    hf hnext hP hPtail htransform hg
  exact hκ (by simpa [P] using heval)

/-- The complementary chart condition follows from an actual coordinate
swap, including the analytic remainder estimate. -/
theorem coordinateSwap_initial_first_power
    (κ : ℂ) (m : ℕ) (f : Germ 2)
    (htail : f - constRingHom 2 κ * coordinate (0 : Fin 2) ^ m ∈
      maximalIdeal 2 ^ (m + 1)) :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f -
      constRingHom 2 κ * coordinate (1 : Fin 2) ^ m ∈ maximalIdeal 2 ^ (m + 1) := by
  have h := PointedMapGerm.pullback_mem_maximalIdeal_pow
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward htail
  rw [map_sub, map_mul, map_pow, PointedMapGerm.pullback_constRingHom,
    PointedMapGerm.pullback_coordinate, coordinateSwapPointedEquiv_component_zero] at h
  exact h

end OnLeConjecture.Analytic.Germ
