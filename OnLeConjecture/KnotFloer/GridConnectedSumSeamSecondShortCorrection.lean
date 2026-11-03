/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortOneStep
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortTwoStep
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondShortNormal

/-!
# All one- and two-transition corrections in the second sector

For a fixed first state `x`, the one- and two-transition corrections from
`(x, z)` to `(x, w)` correspond bijectively to the remaining second-factor
rectangles from `z` to `w`. When the last first-factor row is `0` or `n`,
every such correction has one transition and there is none with two. When
the last row lies strictly between `0` and `n`, every such correction has two
transitions and there is none with one. The case `n = 0` is included: then
the last row is `0`, and both the corrections and the rectangles are absent.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section Assembly
variable {x : GridState (n + 1)} {z w : GridState (m + 1)}

/-- Every two-transition correction with equal first factors is the explicit path of a
remaining rectangle, and its last first-factor row is interior. -/
theorem seamSecondShortTwo_projection (d : SeamCorrectionPath 2 (x, z) (x, w)) :
    x (Fin.last n) ≠ 0 ∧ x (Fin.last n) ≠ Fin.last n ∧
    ∃ ρ : SeamSecondRemainingRectangle x z w,
      d.2.2.1.val.left = seamRight n m ρ.val.left ∧
      d.2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.1.2.1.val.left = seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      d.2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.1.2.2.2.1.val.left = seamLeft n m (x.toPerm.symm 0) ∧
      d.2.2.2.1.2.2.2.1.val.right = seamRight n m ρ.val.right ∧
      d.2.2.2.2.val.left = seamRight n m ρ.val.left ∧
      d.2.2.2.2.val.right = seamLeft n m (x.toPerm.symm (Fin.last n)) := by
  have hmid := seamCorrectionTwo_middle_eq_two (x, z) (x, w) d
  rcases d with ⟨a₀, a₂, e, ⟨a₁, r, ⟨a₂', t, ⟨⟨⟩, ha⟩⟩⟩, f⟩
  have ha' : a₂' = a₂ := ha
  subst a₂'
  exact seamSecondShortTwo_normal a₀ a₁ a₂ e.val r.val t.val f.val e.property r.property.2
    t.property.2 f.property hmid

/-- At a boundary last row there is no two-transition correction with equal first factors. -/
theorem seamSecondShortTwo_isEmpty_of_boundary
    (h : x (Fin.last n) = 0 ∨ x (Fin.last n) = Fin.last n) :
    IsEmpty (SeamCorrectionPath 2 (x, z) (x, w)) :=
  ⟨fun d => by
    obtain ⟨h0, hl, -⟩ := seamSecondShortTwo_projection d
    rcases h with h | h
    · exact h0 h
    · exact hl h⟩

/-- The chosen explicit two-transition correction of a remaining rectangle. -/
def seamSecondShortInteriorLift (h0 : x (Fin.last n) ≠ 0) (hl : x (Fin.last n) ≠ Fin.last n)
    (ρ : SeamSecondRemainingRectangle x z w) : SeamCorrectionPath 2 (x, z) (x, w) :=
  Classical.choose (seamSecondShortInterior_exists ρ h0 hl)

/-- The sides of the chosen two-transition correction. -/
theorem seamSecondShortInteriorLift_spec (h0 : x (Fin.last n) ≠ 0)
    (hl : x (Fin.last n) ≠ Fin.last n) (ρ : SeamSecondRemainingRectangle x z w) :
    (seamSecondShortInteriorLift h0 hl ρ).2.2.1.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.1.val.right = seamLeft n m (x.toPerm.symm 0) ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.1.2.1.val.left =
        seamLeft n m (x.toPerm.symm (Fin.last n)) ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.1.2.1.val.right = seamRight n m ρ.val.right ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.1.2.2.2.1.val.left =
        seamLeft n m (x.toPerm.symm 0) ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.1.2.2.2.1.val.right =
        seamRight n m ρ.val.right ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.2.val.left = seamRight n m ρ.val.left ∧
      (seamSecondShortInteriorLift h0 hl ρ).2.2.2.2.val.right =
        seamLeft n m (x.toPerm.symm (Fin.last n)) :=
  Classical.choose_spec (seamSecondShortInterior_exists ρ h0 hl)

/-- At an interior last row, the explicit two-transition corrections form a bijection. -/
theorem seamSecondShortInteriorLift_bijective (h0 : x (Fin.last n) ≠ 0)
    (hl : x (Fin.last n) ≠ Fin.last n) :
    Function.Bijective (seamSecondShortInteriorLift (z := z) (w := w) h0 hl) := by
  constructor
  · intro ρ₁ ρ₂ h
    have hh : (seamSecondShortInteriorLift h0 hl ρ₁).2.2.1.val.left =
        (seamSecondShortInteriorLift h0 hl ρ₂).2.2.1.val.left := by rw [h]
    rw [(seamSecondShortInteriorLift_spec h0 hl ρ₁).1,
      (seamSecondShortInteriorLift_spec h0 hl ρ₂).1] at hh
    exact Subtype.ext (GridRectangleBetween.left_injective (seamRight_injective hh))
  · intro d
    obtain ⟨-, -, ρ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := seamSecondShortTwo_projection d
    obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ := seamSecondShortInteriorLift_spec h0 hl ρ
    exact ⟨ρ, seamSecondShortPathTwo_ext _ _ (g₁.trans h₁.symm) (g₂.trans h₂.symm)
      (g₃.trans h₃.symm) (g₄.trans h₄.symm) (g₅.trans h₅.symm) (g₆.trans h₆.symm)
      (g₇.trans h₇.symm) (g₈.trans h₈.symm)⟩

/-- At an interior last row, two-transition corrections correspond to remaining rectangles. -/
def seamSecondShortInteriorEquiv (h0 : x (Fin.last n) ≠ 0)
    (hl : x (Fin.last n) ≠ Fin.last n) :
    SeamCorrectionPath 2 (x, z) (x, w) ≃ SeamSecondRemainingRectangle x z w :=
  (Equiv.ofBijective _ (seamSecondShortInteriorLift_bijective h0 hl)).symm

end Assembly

/-- All corrections with one or two internal transitions and equal first factors correspond
exactly to the remaining second-factor rectangles. -/
def seamSecondAllShortCorrectionEquiv (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    SeamCorrectionPath 1 (x, z) (x, w) ⊕ SeamCorrectionPath 2 (x, z) (x, w) ≃
      SeamSecondRemainingRectangle x z w := by
  classical
  by_cases h0 : x (Fin.last n) = 0
  · haveI := seamSecondShortTwo_isEmpty_of_boundary (z := z) (w := w) (Or.inl h0)
    exact (Equiv.sumEmpty _ _).trans (seamSecondShortZeroEquiv h0)
  by_cases hl : x (Fin.last n) = Fin.last n
  · haveI := seamSecondShortTwo_isEmpty_of_boundary (z := z) (w := w) (Or.inr hl)
    exact (Equiv.sumEmpty _ _).trans (seamSecondShortLastEquiv hl)
  · haveI := seamSecondShortOne_isEmpty_interior (z := z) (w := w) h0 hl
    exact (Equiv.emptySum _ _).trans (seamSecondShortInteriorEquiv h0 hl)

/-- Exact integer count for all one- and two-transition second-factor corrections. -/
theorem seamSecondAllShortCorrection_card (x : GridState (n + 1)) (z w : GridState (m + 1)) :
    Fintype.card (SeamCorrectionPath 1 (x, z) (x, w)) +
      Fintype.card (SeamCorrectionPath 2 (x, z) (x, w)) =
      Fintype.card (SeamSecondRemainingRectangle x z w) := by
  simpa only [Fintype.card_sum] using
    Fintype.card_congr (seamSecondAllShortCorrectionEquiv x z w)

end OnLeConjecture.KnotFloer.GridFull
