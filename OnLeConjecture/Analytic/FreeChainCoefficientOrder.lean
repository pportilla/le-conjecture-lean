/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.PullbackEquivalence
public import OnLeConjecture.Analytic.WeightedInitialFormDivisibility
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Coefficient orders from repeated free blowup charts

An actual identity `P(y^h x,y)=y^(h*m) f_h`, with `f_h` of ordinary
order at least `m`, forces the coefficient of `x^i` in `P` to have order
at least `(h+1)*(m-i)`. Monicity and a degree assumption are unnecessary
for this implication. We also derive the displayed identity from a
finite sequence of actual zero-center chart identities of constant order.
-/

public section

namespace OnLeConjecture.Analytic

open Filter _root_.Polynomial
open scoped Topology

namespace Germ

/-- The composite of `h` zero-center point blowup charts. -/
@[expose] noncomputable def freeChainChart (h : ℕ) (z : Source 2) : Source 2 :=
  ![z 1 ^ h * z 0, z 1]

theorem freeChainChart_analyticAt (h : ℕ) : AnalyticAt ℂ (freeChainChart h) 0 := by
  apply AnalyticAt.pi
  intro i
  have hzero := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have hone := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  fin_cases i
  · exact (hone.pow h).mul hzero
  · exact hone

@[simp] theorem freeChainChart_origin (h : ℕ) : freeChainChart h 0 = 0 := by
  ext i
  fin_cases i <;> simp [freeChainChart]

@[expose] noncomputable def freeChainChartGerm (h : ℕ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (freeChainChart h) (freeChainChart_analyticAt h)
    (freeChainChart_origin h)

@[simp] theorem freeChainChartGerm_zero :
    freeChainChartGerm 0 = PointedMapGerm.identity 2 := by
  have h : freeChainChart 0 = id := by
    funext z
    ext i
    fin_cases i <;> simp [freeChainChart]
  simp only [freeChainChartGerm, h, PointedMapGerm.identity]

@[simp] theorem freeChainChartGerm_one :
    freeChainChartGerm 1 = pointBlowupChartGerm 0 := by
  have h : freeChainChart 1 = pointBlowupChart 0 := by
    funext z
    ext i
    fin_cases i <;> simp [freeChainChart, pointBlowupChart]
  simp only [freeChainChartGerm, h, pointBlowupChartGerm]

/-- The analytic chart germs compose by addition of the number of blowups. -/
theorem freeChainChartGerm_add (h k : ℕ) :
    freeChainChartGerm (h + k) = (freeChainChartGerm h).comp (freeChainChartGerm k) := by
  have heq : freeChainChart (h + k) = freeChainChart h ∘ freeChainChart k := by
    funext z
    ext i
    fin_cases i
    · simp [freeChainChart, pow_add, mul_assoc]
    · rfl
  simp only [freeChainChartGerm, PointedMapGerm.comp_ofFunction, heq]

@[simp] theorem freeChainChartGerm_pullback_zero (h : ℕ) :
    (freeChainChartGerm h).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) ^ h * coordinate (0 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  exact MapGerm.component_ofFunction (freeChainChart h) (freeChainChart_analyticAt h) 0

@[simp] theorem freeChainChartGerm_pullback_one (h : ℕ) :
    (freeChainChartGerm h).pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate (1 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  exact MapGerm.component_ofFunction (freeChainChart h) (freeChainChart_analyticAt h) 1

/-- Repeated free charts leave every germ in the parameter alone. -/
@[simp] theorem freeChainChartGerm_pullback_hyperplaneExtension (h : ℕ) (f : Germ 1) :
    (freeChainChartGerm h).pullbackRingHom (hyperplaneExtension 1 f) =
      hyperplaneExtension 1 f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF) (hyperplaneTailGerm 1))
    (freeChainChartGerm h) = compPointed (ofFunction F hF) (hyperplaneTailGerm 1)
  simp only [freeChainChartGerm, hyperplaneTailGerm, compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Eventually.of_forall fun z ↦ ?_
  change F (hyperplaneTail 1 (freeChainChart h z)) = F (hyperplaneTail 1 z)
  congr 1
  ext i
  fin_cases i
  rfl

/-- First-coordinate expansion of a polynomial evaluation recovers the
polynomial over the analytic parameter ring. -/
theorem firstCoordinateFormalRingHom_polynomialEvaluation (P : Polynomial (Germ 1)) :
    firstCoordinateFormalRingHom 1 (firstCoordinatePolynomialEvaluation P) =
      (P : PowerSeries (Germ 1)) := by
  rw [firstCoordinatePolynomialEvaluation, Polynomial.hom_eval₂]
  have hcomp : (firstCoordinateFormalRingHom 1).comp (hyperplaneExtension 1) =
      PowerSeries.C := by
    apply RingHom.ext
    intro r
    exact firstCoordinateFormalRingHom_hyperplaneExtension r
  rw [hcomp, firstCoordinateFormalRingHom_coordinate]
  exact Polynomial.eval₂_C_X_eq_coe

@[simp] theorem firstCoordinateTaylorCoefficient_polynomialEvaluation
    (P : Polynomial (Germ 1)) (i : ℕ) :
    firstCoordinateTaylorCoefficient i (firstCoordinatePolynomialEvaluation P) = P.coeff i := by
  have h := congrArg (PowerSeries.coeff i) (firstCoordinateFormalRingHom_polynomialEvaluation P)
  simpa only [firstCoordinateFormalRingHom_apply, firstCoordinateFormalSeries_coeff,
    Polynomial.coeff_coe] using h

/-- Pullback is the genuine polynomial substitution `X ↦ y^h X`. -/
theorem freeChainChartGerm_pullback_polynomialEvaluation
    (h : ℕ) (P : Polynomial (Germ 1)) :
    (freeChainChartGerm h).pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation (P.comp (C (coordinate (0 : Fin 1) ^ h) * X)) := by
  rw [firstCoordinatePolynomialEvaluation, Polynomial.hom_eval₂]
  have hcomp : (freeChainChartGerm h).pullbackRingHom.comp (hyperplaneExtension 1) =
      hyperplaneExtension 1 := by
    apply RingHom.ext
    intro r
    exact freeChainChartGerm_pullback_hyperplaneExtension h r
  rw [hcomp, freeChainChartGerm_pullback_zero, firstCoordinatePolynomialEvaluation,
    Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, map_pow, hyperplaneExtension_coordinate_plane]

/-- The coefficient identity is derived from the analytic pullback. -/
theorem firstCoordinateTaylorCoefficient_freeChainChart
    (h : ℕ) (P : Polynomial (Germ 1)) (i : ℕ) :
    firstCoordinateTaylorCoefficient i
        ((freeChainChartGerm h).pullbackRingHom (firstCoordinatePolynomialEvaluation P)) =
      coordinate (0 : Fin 1) ^ (h * i) * P.coeff i := by
  rw [freeChainChartGerm_pullback_polynomialEvaluation,
    firstCoordinateTaylorCoefficient_polynomialEvaluation, Polynomial.comp_C_mul_X_coeff,
    ← pow_mul, mul_comm]

/-- Ordinary order at least `m` bounds each parameter coefficient by
`m-i`, with truncated subtraction. -/
theorem coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_maximalIdeal_pow
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) (i : ℕ) :
    coordinate (0 : Fin 1) ^ (m - i) ∣ firstCoordinateTaylorCoefficient i f := by
  have h := coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_weightedOrderIdeal
    1 m f ((mem_weightedOrderIdeal_one_iff m f).mpr hf) i
  simpa only [one_mul] using h

/-- The coefficient order forced by an actual length-`h` transform
identity. This statement includes `h=0` and does not need monicity. -/
theorem coefficient_mem_pow_of_freeChain_transform
    (h m : ℕ) (P : Polynomial (Germ 1)) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m)
    (htransform : (freeChainChartGerm h).pullbackRingHom
        (firstCoordinatePolynomialEvaluation P) = coordinate (1 : Fin 2) ^ (h * m) * f)
    (i : ℕ) (hi : i ≤ m) :
    P.coeff i ∈ maximalIdeal 1 ^ ((h + 1) * (m - i)) := by
  have hcoeff := congrArg (firstCoordinateTaylorCoefficient i) htransform
  rw [firstCoordinateTaylorCoefficient_freeChainChart] at hcoeff
  have hy : coordinate (1 : Fin 2) ^ (h * m) =
      hyperplaneExtension 1 (coordinate (0 : Fin 1) ^ (h * m)) := by
    rw [map_pow, hyperplaneExtension_coordinate_plane]
  rw [hy, firstCoordinateTaylorCoefficient_hyperplaneExtension_mul] at hcoeff
  obtain ⟨q, hq⟩ :=
    coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_maximalIdeal_pow m f hf i
  rw [hq, ← mul_assoc, ← pow_add] at hcoeff
  have hexponent : h * m + (m - i) = h * i + (h + 1) * (m - i) := by
    rw [Nat.add_mul, one_mul, ← add_assoc, ← Nat.mul_add, Nat.add_sub_of_le hi]
  rw [hexponent, pow_add, mul_assoc] at hcoeff
  have hcancel := mul_left_cancel₀ (pow_ne_zero (h * i) coordinate_zero_ne_zero) hcoeff
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton]
  exact ⟨q, hcancel⟩

/-- Multiplying the exceptional factors in a finite chain of actual
zero-center strict-transform identities gives the cumulative factor.
The statement only uses those identities, not a valuation hypothesis. -/
theorem freeChain_cumulative_transform
    (h m : ℕ) (f : ℕ → Germ 2)
    (hsteps : ∀ j < h, (pointBlowupChartGerm 0).pullbackRingHom (f j) =
      coordinate (1 : Fin 2) ^ m * f (j + 1)) :
    (freeChainChartGerm h).pullbackRingHom (f 0) =
      coordinate (1 : Fin 2) ^ (h * m) * f h := by
  induction h with
  | zero =>
      rw [freeChainChartGerm_zero, PointedMapGerm.pullbackRingHom_identity]
      simp
  | succ h ih =>
      have hprev := ih (fun j hj ↦ hsteps j (by omega))
      rw [freeChainChartGerm_add, PointedMapGerm.pullbackRingHom_comp,
        RingHom.comp_apply, hprev, map_mul, map_pow, freeChainChartGerm_one,
        pointBlowupChartGerm_pullback_one, hsteps h (by omega), ← mul_assoc, ← pow_add]
      congr 1
      congr 1
      ring

/-- Coefficient orders follow from a length-`h` chain of actual chart
identities and ordinary order at least `m` at its final center. -/
theorem coefficient_mem_pow_of_freeChain
    (h m : ℕ) (P : Polynomial (Germ 1)) (f : ℕ → Germ 2)
    (hzero : f 0 = firstCoordinatePolynomialEvaluation P)
    (hsteps : ∀ j < h, (pointBlowupChartGerm 0).pullbackRingHom (f j) =
      coordinate (1 : Fin 2) ^ m * f (j + 1))
    (hfinal : f h ∈ maximalIdeal 2 ^ m) (i : ℕ) (hi : i ≤ m) :
    P.coeff i ∈ maximalIdeal 1 ^ ((h + 1) * (m - i)) := by
  apply coefficient_mem_pow_of_freeChain_transform h m P (f h) hfinal
  · rw [← hzero]
    exact freeChain_cumulative_transform h m f hsteps
  · exact hi

/-- The same conclusion applies to a Weierstrass polynomial of the initial
germ. Its analytic unit factor is pulled back and inverted, so the chain
identities need only be given for the original germ. -/
theorem coefficient_mem_pow_of_prepared_freeChain
    (h m : ℕ) (P : Polynomial (Germ 1)) (f : ℕ → Germ 2)
    (u : Germ 2) (hu : IsUnit u)
    (hzero : f 0 = firstCoordinatePolynomialEvaluation P * u)
    (hsteps : ∀ j < h, (pointBlowupChartGerm 0).pullbackRingHom (f j) =
      coordinate (1 : Fin 2) ^ m * f (j + 1))
    (hfinal : f h ∈ maximalIdeal 2 ^ m) (i : ℕ) (hi : i ≤ m) :
    P.coeff i ∈ maximalIdeal 1 ^ ((h + 1) * (m - i)) := by
  obtain ⟨v, hv⟩ := (hu.map (freeChainChartGerm h).pullbackRingHom).exists_right_inv
  have hcum := freeChain_cumulative_transform h m f hsteps
  rw [hzero, map_mul] at hcum
  have hnorm := congrArg (fun a : Germ 2 ↦ a * v) hcum
  simp only [mul_assoc, hv, mul_one] at hnorm
  exact coefficient_mem_pow_of_freeChain_transform h m P (f h * v)
    (Ideal.mul_mem_right _ _ hfinal) hnorm i hi

end Germ

end OnLeConjecture.Analytic
