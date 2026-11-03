/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondRectanglePartition
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTensorDifferential
public import Mathlib.Algebra.Field.ZMod

/-!
# The remaining positive-length path identities

All direct and zero-transition contributions are identified. The exact
tensor differential equality reduces to three cardinality comparisons for
positive internal lengths, according to which factor changes. These three
comparisons remain explicit proof obligations.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamCorrectionZero_factor_eq {p q : SeamRetainedIndex n m}
    (c : SeamCorrectionPath 0 p q) : p.1 = q.1 ∨ p.2 = q.2 := by
  rcases c with ⟨s, t, e, path, f⟩
  have hst : s = t := path.property
  subst t
  have heR := seamEnteringRectangle_ranges (seamState_mem_pairSector p.1 p.2)
    (seamComplementPartner s.val).property e.val
  have hfR := seamLeavingRectangle_ranges (seamState_mem_pairSector q.1 q.2) s.val.property f.val
  rcases heR with heR | heR <;> rcases hfR with hfR | hfR
  · exact Or.inr (seamImmediateFirstRight_second_factor_eq p q s e.val f.val
      e.property f.property heR.1 hfR.1)
  · exact Or.inl (seamImmediateMixed_first_factor_eq p q s e.val f.val e.property f.property
      (Or.inl ⟨heR.1, hfR.1⟩))
  · exact Or.inl (seamImmediateMixed_first_factor_eq p q s e.val f.val e.property f.property
      (Or.inr ⟨heR.1, hfR.1⟩))
  · exact Or.inr (seamImmediateFirstLeft_second_factor_eq p q s e.val f.val
      e.property f.property heR.1 hfR.1)

theorem seamCorrectionZero_isEmpty_of_both_ne (p q : SeamRetainedIndex n m)
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) : IsEmpty (SeamCorrectionPath 0 p q) :=
  ⟨fun c => (seamCorrectionZero_factor_eq c).elim h₁ h₂⟩

theorem seamTransferPath_card_of_both_ne (p q : SeamRetainedIndex n m)
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    Fintype.card (SeamTransferPath p q) = seamPositiveCorrectionCount p q := by
  have := seamRetainedRectangle_isEmpty_of_factor_ne p q h₁ h₂
  have := seamCorrectionZero_isEmpty_of_both_ne p q h₁ h₂
  rw [seamTransferPath_card_zero_positive]
  simp

theorem seamRetainedDifferential_both_ne_evalOne
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (p q : SeamRetainedIndex n m) (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2) (Pi.single p 1) q) =
      (seamPositiveCorrectionCount p q : ZMod 2) := by
  rw [seamRetainedDifferential_evalOne_eq_pathCard, seamTransferPath_card_of_both_ne p q h₁ h₂]

/-- The remaining comparisons after the proved direct and immediate bijections. -/
def SeamPositivePathComparisons (n m : ℕ) : Prop :=
  (∀ (x y : GridState (n + 1)) (z : GridState (m + 1)),
    (seamPositiveCorrectionCount (x, z) (y, z) : ZMod 2) =
      (Fintype.card (SeamFirstRemainingRectangle x y z) : ZMod 2)) ∧
  (∀ (x : GridState (n + 1)) (z w : GridState (m + 1)),
    (seamPositiveCorrectionCount (x, z) (x, w) : ZMod 2) =
      (Fintype.card (SeamSecondRemainingRectangle x z w) : ZMod 2)) ∧
  (∀ p q : SeamRetainedIndex n m, p.1 ≠ q.1 → p.2 ≠ q.2 →
    (seamPositiveCorrectionCount p q : ZMod 2) = 0)

/-- This is an equivalence to the actual tensor operator, not an assumed path identity. -/
theorem seamRetainedDifferential_eq_tensorCoordinate_iff_positive_paths
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (hO : H.O (Fin.last m) = 0) :
    seamRetainedDifferential G H hG hH (ZMod 2) =
        seamTensorCoordinateDifferential (K := ZMod 2) G H ↔
      SeamPositivePathComparisons n m := by
  rw [seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne G H hG hH hO]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x y z
      apply (seamRetainedDifferential_first_evalOne_iff_positive_paths G H hG hH x y z).mp
      simpa only [Prod.fst, Prod.snd, ite_true, emptyRectangles_self,
        Finset.card_empty, Nat.cast_zero, ite_self, add_zero] using h (x, z) (y, z)
    · intro x z w
      apply (seamRetainedDifferential_second_evalOne_iff_positive_paths G H hG hH x z w).mp
      simpa only [Prod.fst, Prod.snd, ite_true, emptyRectangles_self,
        Finset.card_empty, Nat.cast_zero, ite_self, zero_add] using h (x, z) (x, w)
    · intro p q h₁ h₂
      have hh := h p q
      rw [if_neg h₂, if_neg h₁, zero_add,
        seamRetainedDifferential_both_ne_evalOne G H hG hH p q h₁ h₂] at hh
      exact hh
  · rintro ⟨hfirst, hsecond, hboth⟩ ⟨x, z⟩ ⟨y, w⟩
    by_cases h₁ : x = y
    · subst y
      have hh := (seamRetainedDifferential_second_evalOne_iff_positive_paths
        G H hG hH x z w).mpr (hsecond x z w)
      simpa only [Prod.fst, Prod.snd, ite_true, emptyRectangles_self,
        Finset.card_empty, Nat.cast_zero, ite_self, zero_add] using hh
    · by_cases h₂ : z = w
      · subst w
        have hh := (seamRetainedDifferential_first_evalOne_iff_positive_paths
          G H hG hH x y z).mpr (hfirst x y z)
        simpa only [Prod.fst, Prod.snd, ite_true, emptyRectangles_self,
          Finset.card_empty, Nat.cast_zero, ite_self, add_zero] using hh
      · rw [seamRetainedDifferential_both_ne_evalOne G H hG hH (x, z) (y, w) h₁ h₂,
          hboth (x, z) (y, w) h₁ h₂]
        simp only [if_neg h₁, if_neg h₂, add_zero]

end OnLeConjecture.KnotFloer.GridFull
