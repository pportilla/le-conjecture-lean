/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusThreeCycleGrading

/-!
# The absolute Alexander grading of the reflected torus anchor

The southwest column sums evaluate the anchor grading to `n*(n+1)/2`.
Together with the three-cycle grading bound this gives the first staircase
vertex's absolute Alexander coordinate.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The diagonal column potentials have a closed finite sum. -/
theorem sum_reflectedTorusColumnPotential_diagonal (n : ℕ) :
    (∑ c : Fin (consecutiveTorusGridSize n),
      reflectedTorusColumnPotential n c.val c.val) = ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  have hleft : ∀ i : Fin (n + 1),
      reflectedTorusColumnPotential n (Fin.castAdd (n + 1 + 1) i).val
        (Fin.castAdd (n + 1 + 1) i).val = (i.val : ℤ) := by
    intro i
    have hi := i.isLt
    simp only [Fin.val_castAdd, reflectedTorusColumnPotential]
    omega
  have hright0 : reflectedTorusColumnPotential n
      (Fin.natAdd (n + 1) (0 : Fin (n + 1 + 1))).val
      (Fin.natAdd (n + 1) (0 : Fin (n + 1 + 1))).val = (n : ℤ) + 1 := by
    simp only [Fin.val_natAdd, Fin.val_zero, reflectedTorusColumnPotential]
    omega
  have hright : ∀ j : Fin (n + 1),
      reflectedTorusColumnPotential n (Fin.natAdd (n + 1) j.succ).val
        (Fin.natAdd (n + 1) j.succ).val = (n : ℤ) + 1 - j.val := by
    intro j
    have hj := j.isLt
    simp only [Fin.val_natAdd, Fin.val_succ, reflectedTorusColumnPotential]
    omega
  rw [Fin.sum_univ_add]
  simp only [hleft]
  rw [Fin.sum_univ_succ (fun j : Fin (n + 1 + 1) =>
    reflectedTorusColumnPotential n (Fin.natAdd (n + 1) j).val
      (Fin.natAdd (n + 1) j).val)]
  simp only [hright0, hright, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- At an O marking there are no southwest O markings. -/
theorem southwestCount_reflectedTorus_O_self (n : ℕ)
    (c : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusGrid n).O.southwestCount c ((reflectedTorusGrid n).O c) = 0 := by
  rw [southwestCount_reflectedTorus_O, reflectedTorusGrid_O_apply, Fin.val_rev]
  have hc := c.isLt
  omega

/-- The X marking permutation consists of two decreasing intervals, with
every point of the first interval southwest of every point of the second. -/
theorem southwestCount_reflectedTorus_X_self (n : ℕ)
    (c : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusGrid n).X.southwestCount c ((reflectedTorusGrid n).X c) =
      if c.val ≤ n then 0 else n + 1 := by
  rw [southwestCount_reflectedTorus_X, reflectedTorusGrid_X_val]
  have hc := c.isLt
  unfold consecutiveTorusGridSize at hc
  split_ifs <;> omega

/-- The total southwest count of X markings is the product of the interval lengths. -/
theorem sum_southwestCount_reflectedTorus_X_self (n : ℕ) :
    (∑ c : Fin (consecutiveTorusGridSize n),
      ((reflectedTorusGrid n).X.southwestCount c ((reflectedTorusGrid n).X c) : ℤ)) =
      ((n : ℤ) + 1) * ((n : ℤ) + 2) := by
  rw [Fin.sum_univ_add]
  have hleft : ∀ i : Fin (n + 1),
      (reflectedTorusGrid n).X.southwestCount (Fin.castAdd (n + 1 + 1) i)
        ((reflectedTorusGrid n).X (Fin.castAdd (n + 1 + 1) i)) = 0 := by
    intro i
    rw [southwestCount_reflectedTorus_X_self, if_pos (by simpa using Nat.le_of_lt_succ i.isLt)]
  have hright : ∀ j : Fin (n + 1 + 1),
      (reflectedTorusGrid n).X.southwestCount (Fin.natAdd (n + 1) j)
        ((reflectedTorusGrid n).X (Fin.natAdd (n + 1) j)) = n + 1 := by
    intro j
    rw [southwestCount_reflectedTorus_X_self, if_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [hleft, hright, Nat.cast_zero, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  ring

/-- Twice the anchor's Alexander grading is `n*(n+1)`. -/
theorem alexanderTwo_reflectedTorusAnchor (n : ℕ) :
    (reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) =
      (n : ℤ) * ((n : ℤ) + 1) := by
  rw [GridDiagram.alexanderTwoℤ_eq_sum_southwestCount]
  simp only [southwestCount_reflectedTorus_anchor_difference,
    southwestCount_reflectedTorus_O_self, Nat.cast_zero, Finset.sum_const_zero,
    sum_reflectedTorusColumnPotential_diagonal, sum_southwestCount_reflectedTorus_X_self]
  unfold consecutiveTorusGridSize
  push_cast
  ring

/-- The anchor has the absolute Alexander coordinate of the top torus staircase vertex. -/
theorem alexander_reflectedTorusAnchor (n : ℕ) :
    (reflectedTorusGrid n).alexander (reflectedTorusAnchor n) =
      (n : ℚ) * ((n : ℚ) + 1) / 2 := by
  have h := (reflectedTorusGrid n).two_mul_alexander_eq_intCast (reflectedTorusAnchor n)
  rw [alexanderTwo_reflectedTorusAnchor] at h
  push_cast at h
  linarith

end OnLeConjecture.KnotFloer.GridFull
