/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepComplete

/-!
# The exact remaining first-factor count at lengths at least three

All one- and two-transition contributions are now identified over the
integers. The remaining first-factor parity comparison is precisely the
vanishing modulo two of the sum of longer-path counts. The rank bound
handles every small matching-source cardinality, including the empty case.
No longer-path vanishing assumption is introduced into a final theorem.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
open scoped BigOperators
variable {n m : ℕ}

/-- A correction with too many transitions cannot exist. -/
theorem seamCorrectionPath_isEmpty_of_card_le (p q : SeamRetainedIndex n m)
    (k : ℕ) (hk : Fintype.card (SeamMatchingSource n m) ≤ k) :
    IsEmpty (SeamCorrectionPath k p q) := by
  refine ⟨fun path => ?_⟩
  have hlt := seamInternalPath_length_lt path.2.2.2.1
  omega

/-- Integer count of all corrections with at least three internal transitions. -/
def seamLongCorrectionCount (p q : SeamRetainedIndex n m) : ℕ :=
  ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m) - 3),
    Fintype.card (SeamCorrectionPath (k + 3) p q)

/-- Split the bounded positive count at lengths one and two, including all small sizes. -/
theorem seamPositiveCorrectionCount_one_two_long (p q : SeamRetainedIndex n m) :
    seamPositiveCorrectionCount p q =
      Fintype.card (SeamCorrectionPath 1 p q) +
        Fintype.card (SeamCorrectionPath 2 p q) + seamLongCorrectionCount p q := by
  classical
  by_cases h : 3 ≤ Fintype.card (SeamMatchingSource n m)
  · have hsub : Fintype.card (SeamMatchingSource n m) - 1 =
        2 + (Fintype.card (SeamMatchingSource n m) - 3) := by omega
    unfold seamPositiveCorrectionCount seamLongCorrectionCount
    rw [hsub, Finset.sum_range_add]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.zero_add, Nat.reduceAdd]
    apply congrArg (fun v : ℕ => Fintype.card (SeamCorrectionPath 1 p q) +
      Fintype.card (SeamCorrectionPath 2 p q) + v)
    apply Finset.sum_congr rfl
    intro k hk
    have hidx : 2 + k + 1 = k + 3 := by omega
    rw [hidx]
  · have hcard2 : Fintype.card (SeamCorrectionPath 2 p q) = 0 := by
      exact Fintype.card_eq_zero_iff.mpr
        (seamCorrectionPath_isEmpty_of_card_le p q 2 (by omega))
    have hlong : seamLongCorrectionCount p q = 0 := by
      simp only [seamLongCorrectionCount, Nat.sub_eq_zero_of_le (by omega :
        Fintype.card (SeamMatchingSource n m) ≤ 3), Finset.range_zero, Finset.sum_empty]
    simp only [hcard2, hlong, Nat.add_zero]
    by_cases htwo : 2 ≤ Fintype.card (SeamMatchingSource n m)
    · have hsize : Fintype.card (SeamMatchingSource n m) = 2 := by omega
      simp [seamPositiveCorrectionCount, hsize]
    · have hcard1 : Fintype.card (SeamCorrectionPath 1 p q) = 0 := by
        exact Fintype.card_eq_zero_iff.mpr
          (seamCorrectionPath_isEmpty_of_card_le p q 1 (by omega))
      have hsize : Fintype.card (SeamMatchingSource n m) ≤ 1 := by omega
      simp [seamPositiveCorrectionCount, Nat.sub_eq_zero_of_le hsize, hcard1]

/-- Every remaining first rectangle is counted once by the short paths;
all additional positive contributions are exactly the longer paths. -/
theorem seamPositiveCorrectionCount_first_eq_remaining_add_long
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    seamPositiveCorrectionCount (x, z) (y, z) =
      Fintype.card (SeamFirstRemainingRectangle x y z) +
        seamLongCorrectionCount (x, z) (y, z) := by
  rw [seamPositiveCorrectionCount_one_two_long, seamFirstAllShortCorrection_card]

/-- The first positive-path comparison is now exactly the parity of lengths at least three. -/
theorem seamFirstPositiveComparison_iff_long_paths
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    ((seamPositiveCorrectionCount (x, z) (y, z) : ZMod 2) =
      (Fintype.card (SeamFirstRemainingRectangle x y z) : ZMod 2)) ↔
        (seamLongCorrectionCount (x, z) (y, z) : ZMod 2) = 0 := by
  rw [seamPositiveCorrectionCount_first_eq_remaining_add_long, Nat.cast_add]
  constructor
  · intro h
    have hh : (Fintype.card (SeamFirstRemainingRectangle x y z) : ZMod 2) +
        (seamLongCorrectionCount (x, z) (y, z) : ZMod 2) =
          (Fintype.card (SeamFirstRemainingRectangle x y z) : ZMod 2) + 0 := by
      simpa only [add_zero] using h
    exact add_left_cancel hh
  · intro h
    rw [h, add_zero]

/-- This is the first matrix-entry equality for the actual retained differential. -/
theorem seamRetainedDifferential_first_evalOne_iff_long_paths
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : GridState (n + 1)) (z : GridState (m + 1)) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2)
        (Pi.single (x, z) 1) (y, z)) = ((emptyRectangles x y).card : ZMod 2) ↔
      (seamLongCorrectionCount (x, z) (y, z) : ZMod 2) = 0 := by
  rw [seamRetainedDifferential_first_evalOne_iff_positive_paths,
    seamFirstPositiveComparison_iff_long_paths]

end OnLeConjecture.KnotFloer.GridFull
