/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamGradingCounts
import Mathlib.Tactic.Ring

/-!
# Exact grading comparison on seam pair states

The O-Maslov defect is twice the explicit extra southwest pair. The
X-Maslov grading is additive. If the second O marking in the shared row
is in its last column, both Maslov and Alexander gradings are additive.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n m : ℕ}
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)

theorem connectedSumSeamGrid_maslovO (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState x z) =
      G.maslovOℤ x + H.maslovOℤ z - 2 * seamPairCountDefect G.O x H.O z := by
  simp only [GridDiagram.maslovOℤ_def, GridDiagram.OSet_def, connectedSumSeamGrid,
    JNumCenter_int_eq, seam_I_self, seam_I]
  push_cast
  ring

theorem connectedSumSeamGrid_maslovX (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (connectedSumSeamGrid G H hG hH).maslovXℤ (seamState x z) =
      G.maslovXℤ x + H.maslovXℤ z := by
  have hdef : seamPairCountDefect G.X x H.X z = 0 := by
    simp only [seamPairCountDefect, hG, not_lt_of_ge (Fin.le_last _), false_and, ite_false]
  simp only [GridDiagram.maslovXℤ_def, GridDiagram.XSet_def, connectedSumSeamGrid,
    JNumCenter_int_eq, seam_I_self, seam_I, hdef]
  push_cast
  ring

theorem connectedSumSeamGrid_alexander (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (connectedSumSeamGrid G H hG hH).alexander (seamState x z) =
      G.alexander x + H.alexander z - seamPairCountDefect G.O x H.O z := by
  simp only [GridDiagram.alexander_def, GridDiagram.maslovO_eq_intCast,
    GridDiagram.maslovX_eq_intCast, connectedSumSeamGrid_maslovO,
    connectedSumSeamGrid_maslovX]
  push_cast
  ring

theorem seamPairCountDefect_eq_zero_of_last_O (hO : H.O (Fin.last m) = 0)
    (x : GridState (n + 1)) (z : GridState (m + 1)) :
    seamPairCountDefect G.O x H.O z = 0 := by
  have hinv : H.O.toPerm.symm 0 = Fin.last m :=
    H.O.toPerm.injective ((H.O.toPerm.apply_symm_apply 0).trans hO.symm)
  simp only [seamPairCountDefect, hinv, not_lt_of_ge (Fin.le_last _), and_false, ite_false]

theorem connectedSumSeamGrid_maslovO_of_last_O (hO : H.O (Fin.last m) = 0)
    (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState x z) =
      G.maslovOℤ x + H.maslovOℤ z := by
  rw [connectedSumSeamGrid_maslovO, seamPairCountDefect_eq_zero_of_last_O G H hO,
    Nat.cast_zero, mul_zero, sub_zero]

theorem connectedSumSeamGrid_alexander_of_last_O (hO : H.O (Fin.last m) = 0)
    (x : GridState (n + 1)) (z : GridState (m + 1)) :
    (connectedSumSeamGrid G H hG hH).alexander (seamState x z) =
      G.alexander x + H.alexander z := by
  rw [connectedSumSeamGrid_alexander, seamPairCountDefect_eq_zero_of_last_O G H hO,
    Nat.cast_zero, sub_zero]

end OnLeConjecture.KnotFloer.GridFull
