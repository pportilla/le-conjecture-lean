/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridLetterSchedule
public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordCircle

/-! # The fixed rounded-word schedule in an arbitrary base period

These are identities of the literal complex paths. The base-period origin is
retained explicitly, so no source or ambient rotation is hidden.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
open OnLeConjecture.Analytic

namespace OnLeConjecture.KnotTheory

/-- The fixed schedule with unit letters and unit connector intervals. -/
theorem positiveGridScheduledWord_fixed_eq_lift {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) :
    positiveGridScheduledWord w (fun j => 2 * (j.val : ℝ) + 1)
      (fun j => 2 * (j.val : ℝ) + 2) k t = (positiveRoundedWordLift w k 0 t).2 := by
  have hden (j : Fin w.length) :
      (2 * (j.val : ℝ) + 2) - (2 * (j.val : ℝ) + 1) = 1 := by ring
  apply Complex.ext
  · simp [positiveGridScheduledWord, finiteSmoothPathConcat, positiveRoundedWordLift,
      positiveRoundedWordCanonicalReal, positiveGridGenerator, hden]
  · simp [positiveGridScheduledWord, finiteSmoothPathConcat, positiveRoundedWordLift,
      positiveRoundedWordCanonicalImag, positiveGridGenerator, hden]

/-- Affine changes of the base parameter preserve the exact local generator time. -/
theorem positiveGridScheduledWord_affine {m : ℕ} (w : PositiveAdjacentWord m)
    (left right : Fin w.length → ℝ) (hlt : ∀ j, left j < right j)
    (b : ℝ) {c : ℝ} (hc : c ≠ 0) (k : Fin m) (θ : ℝ) :
    positiveGridScheduledWord w (fun j => b + c * left j) (fun j => b + c * right j) k θ =
      positiveGridScheduledWord w left right k ((θ - b) / c) := by
  unfold positiveGridScheduledWord finiteSmoothPathConcat
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have hd : right j - left j ≠ 0 := sub_ne_zero.mpr (hlt j).ne'
  rw [show b + c * right j - (b + c * left j) = c * (right j - left j) by ring]
  field_simp [hc, hd]
  ring

/-- Start of a fixed generator interval inside the retained angular period. -/
def positiveFixedAngularLeft {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (j : Fin w.length) : ℝ :=
  b + (2 * Real.pi / (2 * (w.length : ℝ) + 1)) * (2 * (j.val : ℝ) + 1)

/-- End of the same interval. -/
def positiveFixedAngularRight {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (j : Fin w.length) : ℝ :=
  b + (2 * Real.pi / (2 * (w.length : ℝ) + 1)) * (2 * (j.val : ℝ) + 2)

theorem positiveFixedAngular_left_lt_right {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (j : Fin w.length) :
    positiveFixedAngularLeft w b j < positiveFixedAngularRight w b j := by
  apply add_lt_add_right
  apply mul_lt_mul_of_pos_left (by linarith)
  exact div_pos Real.two_pi_pos (by positivity)

theorem positiveFixedAngular_order {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (j q : Fin w.length) (hjq : j < q) :
    positiveFixedAngularRight w b j ≤ positiveFixedAngularLeft w b q := by
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (div_nonneg Real.two_pi_pos.le (by positivity))
  have h : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hjq
  linarith

theorem positiveFixedAngular_inside {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (j : Fin w.length) :
    b < positiveFixedAngularLeft w b j ∧ positiveFixedAngularRight w b j < b + 2 * Real.pi := by
  have hT : (0 : ℝ) < 2 * (w.length : ℝ) + 1 := by positivity
  constructor
  · exact lt_add_of_pos_right _ (mul_pos (div_pos Real.two_pi_pos hT) (by positivity))
  · have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
    have hh : (2 * (j.val : ℝ) + 2) / (2 * (w.length : ℝ) + 1) < 1 :=
      (div_lt_one hT).mpr (by linarith)
    have hp := mul_lt_mul_of_pos_left hh Real.two_pi_pos
    unfold positiveFixedAngularRight
    nlinarith [show 2 * Real.pi / (2 * (w.length : ℝ) + 1) * (2 * (j.val : ℝ) + 2) =
      2 * Real.pi * ((2 * (j.val : ℝ) + 2) / (2 * (w.length : ℝ) + 1)) by ring]

/-- The fixed angular schedule is exactly the initial rounded-word path,
with its base-period origin subtracted in the time coordinate. -/
theorem positiveGridScheduledWord_fixedAngular_eq_lift {m : ℕ} (w : PositiveAdjacentWord m)
    (b : ℝ) (k : Fin m) (θ : ℝ) :
    positiveGridScheduledWord w (positiveFixedAngularLeft w b) (positiveFixedAngularRight w b) k θ =
      (positiveRoundedWordLift w k 0 (positiveRoundedWordPeriodTime w (θ - b))).2 := by
  unfold positiveFixedAngularLeft positiveFixedAngularRight
  rw [positiveGridScheduledWord_affine w _ _ (fun _ => by linarith) b
    (div_ne_zero Real.two_pi_pos.ne' (by positivity)) k θ,
    positiveGridScheduledWord_fixed_eq_lift]
  congr 2
  unfold positiveRoundedWordPeriodTime
  field_simp

end OnLeConjecture.KnotTheory
