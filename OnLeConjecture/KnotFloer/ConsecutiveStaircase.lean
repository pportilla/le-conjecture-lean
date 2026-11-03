/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.StaircaseHomology
public import OnLeConjecture.Numerical.Breakpoint
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Spectral values of the staircase with consecutive step lengths

The vertex coordinates are `j(j+1)/2` and `(n-j)(n+1-j)/2`, for
`0 ≤ j ≤ n`. The preceding homology computation identifies the spectral
threshold with the smallest weighted vertex value. Shifting minus twice
that value by `n(n+1)t/2` gives the maximum of the affine functions
`(n+1)jt-j(j+1)`. In particular the first two nonconstant affine terms
supply the lower bounds needed in the numerical conjecture reduction.

These statements compute the specified finite staircase. An identification
with the complex of the torus knot `T(n+1,n+2)` is not asserted.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.Staircase

/-- The first filtration coordinate of a consecutive-step staircase vertex. -/
noncomputable def consecutiveFirst (n : ℕ) (j : Fin (n + 1)) : ℝ := (j : ℝ) * ((j : ℝ) + 1) / 2

/-- The second filtration coordinate of a consecutive-step staircase vertex. -/
noncomputable def consecutiveSecond (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  ((n : ℝ) - (j : ℝ)) * ((n : ℝ) + 1 - (j : ℝ)) / 2

/-- The weighted coordinate used for the spectral threshold. -/
noncomputable def consecutiveWeight (n : ℕ) (t : ℝ) (j : Fin (n + 1)) : ℝ :=
  (1 - t / 2) * consecutiveFirst n j + (t / 2) * consecutiveSecond n j

/-- Minus twice the minimum vertex value, with the conventional genus shift for this model. -/
noncomputable def consecutiveShiftedValue (n : ℕ) (t : ℝ) : ℝ :=
  -2 * minimumWeight n (consecutiveWeight n t) + (n : ℝ) * ((n : ℝ) + 1) / 2 * t

theorem consecutive_shifted_vertex (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    -2 * consecutiveWeight n t j + (n : ℝ) * ((n : ℝ) + 1) / 2 * t =
      ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) := by
  unfold consecutiveWeight consecutiveFirst consecutiveSecond
  ring

/-- Every affine vertex term is a lower bound for the shifted spectral value. -/
theorem affine_le_consecutiveShiftedValue (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) ≤
      consecutiveShiftedValue n t := by
  rw [← consecutive_shifted_vertex]
  have h := minimumWeight_le n (consecutiveWeight n t) j
  unfold consecutiveShiftedValue
  linarith

/-- One of the finitely many affine terms attains the shifted value. -/
theorem exists_consecutiveShiftedValue_eq_affine (n : ℕ) (t : ℝ) :
    ∃ j : Fin (n + 1), consecutiveShiftedValue n t =
      ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) := by
  obtain ⟨j, hj⟩ := exists_minimumWeight_eq n (consecutiveWeight n t)
  refine ⟨j, ?_⟩
  rw [consecutiveShiftedValue, hj, consecutive_shifted_vertex]

/-- The affine term selected by its interval dominates every other vertex term. -/
theorem affine_le_selected_interval (n : ℕ) (t : ℝ) (i j : Fin (n + 1))
    (hlo : 2 * (j : ℝ) ≤ ((n : ℝ) + 1) * t)
    (hhi : ((n : ℝ) + 1) * t ≤ 2 * ((j : ℝ) + 1)) :
    ((n : ℝ) + 1) * (i : ℝ) * t - (i : ℝ) * ((i : ℝ) + 1) ≤
      ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hn : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
    have hr : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hn
    have hp : 0 ≤ ((j : ℝ) - (i : ℝ)) *
        (((n : ℝ) + 1) * t - ((i : ℝ) + (j : ℝ) + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  · exact le_rfl
  · have hn : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
    have hr : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hn
    have hp : 0 ≤ ((i : ℝ) - (j : ℝ)) *
        (((i : ℝ) + (j : ℝ) + 1) - ((n : ℝ) + 1) * t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]

/-- The exact piecewise affine formula, including both endpoints of every interval. -/
theorem consecutiveShiftedValue_eq_on_interval (n : ℕ) (t : ℝ) (j : Fin (n + 1))
    (hlo : 2 * (j : ℝ) ≤ ((n : ℝ) + 1) * t)
    (hhi : ((n : ℝ) + 1) * t ≤ 2 * ((j : ℝ) + 1)) :
    consecutiveShiftedValue n t =
      ((n : ℝ) + 1) * (j : ℝ) * t - (j : ℝ) * ((j : ℝ) + 1) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_consecutiveShiftedValue_eq_affine n t
    rw [hi]
    exact affine_le_selected_interval n t i j hlo hhi
  · exact affine_le_consecutiveShiftedValue n t j

/-- The first affine lower bound, including the smallest staircase where it is present. -/
theorem consecutiveShiftedValue_lower_one {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ((n : ℝ) + 1) * t - 2 ≤ consecutiveShiftedValue n t := by
  have h := affine_le_consecutiveShiftedValue n t ⟨1, by omega⟩
  norm_num at h
  linarith

/-- The second affine lower bound, including its endpoint size. -/
theorem consecutiveShiftedValue_lower_two {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    2 * ((n : ℝ) + 1) * t - 6 ≤ consecutiveShiftedValue n t := by
  have h := affine_le_consecutiveShiftedValue n t ⟨2, by omega⟩
  norm_num at h
  nlinarith [h]

/-- A single upper comparison with this explicit staircase implies the two numerical bounds.
The geometric cobordism comparison required to use this statement remains a separate input. -/
theorem estimates_of_consecutive_staircase_comparison (n M m : ℕ)
    (hn : 2 ≤ n) (hm : 0 < m)
    (hupper : consecutiveShiftedValue n (2 / (m : ℝ)) ≤
      2 * (((n : ℝ) + 1) - (M : ℝ)) / (m : ℝ)) :
    M ≤ m ∧ (n + 1) + M ≤ 3 * m := by
  apply Numerical.estimates_of_breakpoint_bounds (n + 1) M m
    (consecutiveShiftedValue n (2 / (m : ℝ))) hm
  · have h := consecutiveShiftedValue_lower_one (show 1 ≤ n by omega) (2 / (m : ℝ))
    convert h using 1
    push_cast
    ring
  · have h := consecutiveShiftedValue_lower_two hn (2 / (m : ℝ))
    convert h using 1
    push_cast
    ring
  · simpa only [Nat.cast_add, Nat.cast_one] using hupper

end OnLeConjecture.KnotFloer.Staircase
