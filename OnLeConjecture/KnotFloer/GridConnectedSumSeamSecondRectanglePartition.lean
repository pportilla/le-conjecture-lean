/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamImmediateSecondBijection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstRectanglePartition

/-!
# Removing the direct and immediate second-factor contributions

For a fixed first state, a retained empty rectangle is precisely an
empty second-factor rectangle with empty candidate lift. Obstructed
empty second-factor rectangles always wrap in columns. The immediate
corrections account for exactly those with a zero row endpoint, leaving
only the obstructed rectangles whose two row endpoints are nonzero.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

abbrev SeamSecondDirectRectangle (x : GridState (n + 1)) (z w : GridState (m + 1)) :=
  {r : GridRectangleBetween z w // r.IsEmpty ∧ (seamSecondFactorRectangle x r).IsEmpty}

/-- The second-factor rectangles left after direct and immediate terms are removed. -/
abbrev SeamSecondRemainingRectangle (x : GridState (n + 1)) (z w : GridState (m + 1)) :=
  {r : GridRectangleBetween z w // r.IsEmpty ∧ ¬ (seamSecondFactorRectangle x r).IsEmpty ∧
    r.bottom ≠ 0 ∧ r.top ≠ 0}

instance seamSecondDirectRectangleFintype (x : GridState (n + 1))
    (z w : GridState (m + 1)) : Fintype (SeamSecondDirectRectangle x z w) := inferInstance

instance seamSecondRemainingRectangleFintype (x : GridState (n + 1))
    (z w : GridState (m + 1)) : Fintype (SeamSecondRemainingRectangle x z w) := inferInstance

/-- A retained rectangle with fixed first factor has both side columns in the second block. -/
theorem seamSecondDirectRectangle_sides_ge (x : GridState (n + 1)) (z w : GridState (m + 1))
    (r : GridRectangleBetween (seamState x z) (seamState x w)) :
    n ≤ r.left.val ∧ n ≤ r.right.val := by
  have hnot : ¬ (r.left.val < n ∨ r.right.val < n) := by
    intro hh
    have hz : z = w := seamRetainedRectangle_second_eq_of_side_lt (x, z) (x, w) r hh
    exact r.source_ne_target (congrArg (seamState x) hz)
  constructor <;> by_contra hh
  · exact hnot (Or.inl (by omega))
  · exact hnot (Or.inr (by omega))

/-- The direct equivalence retains the full rectangles and both inverse constructions. -/
def seamSecondDirectRectangleEquiv (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    {r : GridRectangleBetween (seamState x z) (seamState x w) // r.IsEmpty} ≃
      SeamSecondDirectRectangle x z w where
  toFun r := ⟨seamRetainedSecondRectangle (x, z) (x, w) r.val
      (seamSecondDirectRectangle_sides_ge x z w r.val).1
      (seamSecondDirectRectangle_sides_ge x z w r.val).2,
    seamRetainedSecondRectangle_isEmpty (x, z) (x, w) r.val
      (seamSecondDirectRectangle_sides_ge x z w r.val).1
      (seamSecondDirectRectangle_sides_ge x z w r.val).2 r.property,
    by rw [seamSecondFactorRectangle_lift_project]; exact r.property⟩
  invFun r := ⟨seamSecondFactorRectangle x r.val, r.property.2⟩
  left_inv r := Subtype.ext (seamSecondFactorRectangle_lift_project x r.val
    (seamSecondDirectRectangle_sides_ge x z w r.val).1
    (seamSecondDirectRectangle_sides_ge x z w r.val).2)
  right_inv r := Subtype.ext (seamSecondFactorRectangle_project x r.val)

/-- A first-block point can obstruct a second-factor lift only when its columns wrap. -/
theorem seamSecondFactorRectangle_wraps_of_obstructed (x : GridState (n + 1))
    {z w : GridState (m + 1)} (r : GridRectangleBetween z w) (he : r.IsEmpty)
    (hb : ¬ (seamSecondFactorRectangle x r).IsEmpty) : r.right < r.left := by
  obtain ⟨a, hc, _⟩ := (seamSecondFactorRectangle_not_isEmpty_iff x r he).mp hb
  by_contra hrl
  have hne : r.left.val ≠ r.right.val := fun hh => r.left_ne_right (Fin.ext hh)
  have hlr : r.left.val < r.right.val := by omega
  rw [Grid.mem_cIoo, if_pos (by simp only [seamRight_val]; omega)] at hc
  have hh := hc.2.1
  simp only [seamLeft_val, seamRight_val, Fin.val_castSucc] at hh
  have ha := a.isLt
  omega

/-- In particular, every remaining rectangle still wraps in columns. -/
theorem seamSecondRemainingRectangle_wraps (x : GridState (n + 1))
    (z w : GridState (m + 1)) (r : SeamSecondRemainingRectangle x z w) :
    r.val.right < r.val.left :=
  seamSecondFactorRectangle_wraps_of_obstructed x r.val r.property.1 r.property.2.1

/-- The exact integer partition after removing direct and zero-transition terms. -/
theorem seamSecondRectangle_partition (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    Fintype.card {r : GridRectangleBetween (seamState x z) (seamState x w) // r.IsEmpty} +
      Fintype.card (SeamCorrectionPath 0 (x, z) (x, w)) +
      Fintype.card (SeamSecondRemainingRectangle x z w) = (emptyRectangles z w).card := by
  classical
  let E := emptyRectangles z w
  let B := E.filter (fun r => ¬ (seamSecondFactorRectangle x r).IsEmpty)
  have hd : Fintype.card (SeamSecondDirectRectangle x z w) =
      (E.filter (fun r => (seamSecondFactorRectangle x r).IsEmpty)).card :=
    Fintype.card_of_subtype _ fun r => by simp only [E, Finset.mem_filter, mem_emptyRectangles]
  have hz : Fintype.card (SeamObstructedSecondZeroRectangle (x, z) (x, w)) =
      (B.filter (fun r => r.bottom = 0 ∨ r.top = 0)).card :=
    Fintype.card_of_subtype _ fun r => by
      simp only [B, E, Finset.mem_filter, mem_emptyRectangles, and_assoc]
      constructor
      · rintro ⟨he, hb, hz⟩
        exact ⟨he, hb, seamSecondFactorRectangle_wraps_of_obstructed x r he hb, hz⟩
      · rintro ⟨he, hb, _, hz⟩
        exact ⟨he, hb, hz⟩
  have hr : Fintype.card (SeamSecondRemainingRectangle x z w) =
      (B.filter (fun r => ¬ (r.bottom = 0 ∨ r.top = 0))).card :=
    Fintype.card_of_subtype _ fun r => by
      simp only [B, E, Finset.mem_filter, mem_emptyRectangles, not_or, and_assoc]
  have h₁ := Finset.card_filter_add_card_filter_not (s := E)
    (fun r => (seamSecondFactorRectangle x r).IsEmpty)
  have h₂ := Finset.card_filter_add_card_filter_not (s := B)
    (fun r => r.bottom = 0 ∨ r.top = 0)
  rw [Fintype.card_congr (seamSecondDirectRectangleEquiv x z w),
    seamCorrectionZeroSecond_card x z w, hd, hz, hr]
  change _ = E.card
  change (E.filter (fun r => (seamSecondFactorRectangle x r).IsEmpty)).card + B.card = E.card at h₁
  omega

/-- For a fixed first state, the remaining comparison is exactly the positive-length path count. -/
theorem seamRetainedDifferential_second_evalOne_iff_positive_paths
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2)
      (Pi.single (x, z) 1) (x, w)) = ((emptyRectangles z w).card : ZMod 2) ↔
      (seamPositiveCorrectionCount (x, z) (x, w) : ZMod 2) =
        (Fintype.card (SeamSecondRemainingRectangle x z w) : ZMod 2) := by
  have hp := congrArg (fun a : ℕ => (a : ZMod 2)) (seamSecondRectangle_partition x z w)
  simp only [Nat.cast_add] at hp
  rw [seamRetainedDifferential_evalOne_eq_pathCard, seamTransferPath_card_zero_positive]
  simp only [Nat.cast_add]
  rw [← hp]
  exact add_left_cancel_iff

end OnLeConjecture.KnotFloer.GridFull
