/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorOneStepInverse
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstFactorTwoStepInverse
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamFirstRectanglePartition

/-!
# Partitioning the remaining first-factor rectangles by the zero preimage

The boundary and interior positions of the second-state zero preimage
partition the blocked empty rectangles with nonlast endpoints. The
correspondences with one-transition and birth-death two-transition paths
therefore give an integer count, without classifying longer paths.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

/-- The zero preimage is interior precisely when neither endpoint column contains zero. -/
theorem seamZeroPreimage_interior_iff (z : GridState (m + 1)) :
    (0 < (z.toPerm.symm 0).val ∧ (z.toPerm.symm 0).val < m) ↔
      ¬ (z 0 = 0 ∨ z (Fin.last m) = 0) := by
  constructor
  · rintro ⟨hfirst, hlast⟩ (h | h)
    · have hh : z.toPerm.symm 0 = 0 := z.toPerm.symm_apply_eq.mpr h.symm
      rw [hh] at hfirst
      exact Nat.lt_irrefl 0 hfirst
    · have hh : z.toPerm.symm 0 = Fin.last m := z.toPerm.symm_apply_eq.mpr h.symm
      rw [hh] at hlast
      exact Nat.lt_irrefl m hlast
  · intro h
    have hfirst : (z.toPerm.symm 0).val ≠ 0 := by
      intro hh
      have heq : z.toPerm.symm 0 = 0 := Fin.ext hh
      have hv := z.toPerm.apply_symm_apply 0
      rw [heq] at hv
      exact h (Or.inl hv)
    have hlast : (z.toPerm.symm 0).val ≠ m := by
      intro hh
      have heq : z.toPerm.symm 0 = Fin.last m := Fin.ext hh
      have hv := z.toPerm.apply_symm_apply 0
      rw [heq] at hv
      exact h (Or.inr hv)
    have hbound := (z.toPerm.symm 0).isLt
    exact ⟨by omega, by omega⟩

/-- The boundary and interior subtypes partition every remaining rectangle, including `m = 0`. -/
def seamFirstRemainingZeroPartitionEquiv
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamObstructedFirstNonlastBoundaryRectangle x y z ⊕
      SeamObstructedFirstInteriorRectangle x y z ≃ SeamFirstRemainingRectangle x y z where
  toFun
    | Sum.inl R => ⟨R.val, R.property.1, R.property.2.1,
        R.property.2.2.1, R.property.2.2.2.1⟩
    | Sum.inr R => ⟨R.val, R.property.1, R.property.2.1,
        R.property.2.2.1, R.property.2.2.2.1⟩
  invFun R := if h : z 0 = 0 ∨ z (Fin.last m) = 0 then
      Sum.inl ⟨R.val, R.property.1, R.property.2.1,
        R.property.2.2.1, R.property.2.2.2, h⟩
    else
      Sum.inr ⟨R.val, R.property.1, R.property.2.1,
        R.property.2.2.1, R.property.2.2.2, (seamZeroPreimage_interior_iff z).mpr h⟩
  left_inv := by
    rintro (R | R)
    · simp only [dif_pos R.property.2.2.2.2]
    · simp only [dif_neg ((seamZeroPreimage_interior_iff z).mp R.property.2.2.2.2)]
  right_inv := by
    intro R
    split_ifs <;> rfl

/-- One transition and the specified two-transition birth-death paths
cover the remaining rectangles. -/
def seamFirstShortCorrectionEquiv
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    SeamCorrectionPath 1 (x, z) (y, z) ⊕ SeamFirstBirthDeathCorrection (x, z) (y, z) ≃
      SeamFirstRemainingRectangle x y z :=
  (Equiv.sumCongr (seamFirstFactorOneStepEquiv x y z)
    (seamFirstFactorTwoStepEquiv x y z)).trans (seamFirstRemainingZeroPartitionEquiv x y z)

/-- The remaining factor count is the sum of the two established
short-path counts over the integers. -/
theorem seamFirstShortCorrection_card
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    Fintype.card (SeamCorrectionPath 1 (x, z) (y, z)) +
      Fintype.card (SeamFirstBirthDeathCorrection (x, z) (y, z)) =
      Fintype.card (SeamFirstRemainingRectangle x y z) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (seamFirstShortCorrectionEquiv x y z)

end OnLeConjecture.KnotFloer.GridFull
