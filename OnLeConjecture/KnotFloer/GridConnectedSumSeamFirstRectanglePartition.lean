/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateFirstBijection

/-!
# Removing the direct and immediate first-factor contributions

For a fixed second state, the direct rectangles are exactly the empty
factor rectangles whose candidate lift is empty. The zero-transition
corrections are exactly the obstructed factor rectangles incident to the
last column. Their integer cardinalities partition the factor rectangles
together with the remaining obstructed rectangles.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

abbrev SeamFirstDirectRectangle (x y : GridState (n + 1)) (z : GridState (m + 1)) :=
  {r : GridRectangleBetween x y // r.IsEmpty ∧ (seamFirstFactorRectangle r z).IsEmpty}

/-- The first-factor rectangles left after direct and immediate terms are removed. -/
abbrev SeamFirstRemainingRectangle (x y : GridState (n + 1)) (z : GridState (m + 1)) :=
  {r : GridRectangleBetween x y // r.IsEmpty ∧ ¬ (seamFirstFactorRectangle r z).IsEmpty ∧
    r.left ≠ Fin.last n ∧ r.right ≠ Fin.last n}

instance seamFirstDirectRectangleFintype (x y : GridState (n + 1))
    (z : GridState (m + 1)) : Fintype (SeamFirstDirectRectangle x y z) := inferInstance

instance seamFirstRemainingRectangleFintype (x y : GridState (n + 1))
    (z : GridState (m + 1)) : Fintype (SeamFirstRemainingRectangle x y z) := inferInstance

theorem seamFirstDirectRectangle_has_side (x y : GridState (n + 1)) (z : GridState (m + 1))
    (r : GridRectangleBetween (seamState x z) (seamState y z)) :
    r.left.val < n ∨ r.right.val < n := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact r.source_ne_target rfl
  exact seamRetainedRectangle_side_lt_of_first_ne (x, z) (y, z) r hne

/-- Both inverse maps retain the actual rectangle, not just its coefficient. -/
def seamFirstDirectRectangleEquiv (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    {r : GridRectangleBetween (seamState x z) (seamState y z) // r.IsEmpty} ≃
      SeamFirstDirectRectangle x y z where
  toFun r := ⟨seamRetainedFirstRectangle (x, z) (y, z) r.val
      (seamFirstDirectRectangle_has_side x y z r.val),
    seamRetainedFirstRectangle_isEmpty (x, z) (y, z) r.val
      (seamFirstDirectRectangle_has_side x y z r.val) r.property,
    by rw [seamFirstFactorRectangle_lift_project]; exact r.property⟩
  invFun r := ⟨seamFirstFactorRectangle r.val z, r.property.2⟩
  left_inv r := Subtype.ext (seamFirstFactorRectangle_lift_project z r.val
    (seamFirstDirectRectangle_has_side x y z r.val))
  right_inv r := Subtype.ext (seamFirstFactorRectangle_project r.val z)

/-- The exact integer partition used to cancel the already identified terms. -/
theorem seamFirstRectangle_partition (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    Fintype.card {r : GridRectangleBetween (seamState x z) (seamState y z) // r.IsEmpty} +
      Fintype.card (SeamCorrectionPath 0 (x, z) (y, z)) +
      Fintype.card (SeamFirstRemainingRectangle x y z) = (emptyRectangles x y).card := by
  classical
  let E := emptyRectangles x y
  let B := E.filter (fun r => ¬ (seamFirstFactorRectangle r z).IsEmpty)
  have hd : Fintype.card (SeamFirstDirectRectangle x y z) =
      (E.filter (fun r => (seamFirstFactorRectangle r z).IsEmpty)).card :=
    Fintype.card_of_subtype _ fun r => by simp only [E, Finset.mem_filter, mem_emptyRectangles]
  have hz : Fintype.card (SeamObstructedFirstLastRectangle (x, z) (y, z)) =
      (B.filter (fun r => r.left = Fin.last n ∨ r.right = Fin.last n)).card :=
    Fintype.card_of_subtype _ fun r => by
      simp only [B, E, Finset.mem_filter, mem_emptyRectangles, and_assoc]
  have hr : Fintype.card (SeamFirstRemainingRectangle x y z) =
      (B.filter (fun r => ¬ (r.left = Fin.last n ∨ r.right = Fin.last n))).card :=
    Fintype.card_of_subtype _ fun r => by
      simp only [B, E, Finset.mem_filter, mem_emptyRectangles, not_or, and_assoc]
  have h₁ := Finset.card_filter_add_card_filter_not (s := E)
    (fun r => (seamFirstFactorRectangle r z).IsEmpty)
  have h₂ := Finset.card_filter_add_card_filter_not (s := B)
    (fun r => r.left = Fin.last n ∨ r.right = Fin.last n)
  rw [Fintype.card_congr (seamFirstDirectRectangleEquiv x y z),
    seamCorrectionZeroFirst_card x y z, hd, hz, hr]
  change _ = E.card
  change (E.filter (fun r => (seamFirstFactorRectangle r z).IsEmpty)).card + B.card = E.card at h₁
  omega

/-- The positive internal lengths still present in the actual finite inverse. -/
def seamPositiveCorrectionCount (p q : SeamRetainedIndex n m) : ℕ :=
  ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m) - 1),
    Fintype.card (SeamCorrectionPath (k + 1) p q)

theorem seamTransferPath_card_zero_positive (p q : SeamRetainedIndex n m) :
    Fintype.card (SeamTransferPath p q) =
      Fintype.card {r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) //
        r.IsEmpty} + Fintype.card (SeamCorrectionPath 0 p q) + seamPositiveCorrectionCount p q := by
  classical
  rw [Fintype.card_sum, Fintype.card_sigma]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => Fintype.card (SeamCorrectionPath k p q))]
  by_cases h : Fintype.card (SeamMatchingSource n m) = 0
  · have : IsEmpty (SeamMatchingSource n m) := Fintype.card_eq_zero_iff.mp h
    have : IsEmpty (SeamCorrectionPath 0 p q) := ⟨fun c => isEmptyElim c.1⟩
    simp [seamPositiveCorrectionCount]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp only [seamPositiveCorrectionCount, hk, Nat.succ_sub_one, Finset.sum_range_succ']
    omega

/-- For a fixed second state, only the positive-length correction comparison remains. -/
theorem seamRetainedDifferential_first_evalOne_iff_positive_paths
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2)
      (Pi.single (x, z) 1) (y, z)) = ((emptyRectangles x y).card : ZMod 2) ↔
      (seamPositiveCorrectionCount (x, z) (y, z) : ZMod 2) =
        (Fintype.card (SeamFirstRemainingRectangle x y z) : ZMod 2) := by
  have hp := congrArg (fun a : ℕ => (a : ZMod 2)) (seamFirstRectangle_partition x y z)
  simp only [Nat.cast_add] at hp
  rw [seamRetainedDifferential_evalOne_eq_pathCard, seamTransferPath_card_zero_positive]
  simp only [Nat.cast_add]
  rw [← hp]
  exact add_left_cancel_iff

end OnLeConjecture.KnotFloer.GridFull
