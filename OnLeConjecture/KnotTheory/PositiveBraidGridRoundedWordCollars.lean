/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordDeformation
import all OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordLift

/-! # Two-sided collars of the rounded word deformation

The global finite-sum formulas are straight beyond both ends. Together with the
proved interior collars, this supplies uniform open collars for smooth periodic
gluing, including the empty word.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
open OnLeConjecture.Analytic

namespace OnLeConjecture.KnotTheory

theorem positiveRoundedWordDepth_exterior {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0 ∨ 2 * (w.length : ℝ) + 1 ≤ t) :
    positiveRoundedWordDepth w k t = 0 := by
  rcases ht with ht | ht
  · have h := finiteSmoothPathConcat_initial (positiveRoundedWordDepthNode w k)
      (positiveRoundedWordDepthPath w k) (fun j => 2 * (j.val : ℝ))
      (fun j => 2 * (j.val : ℝ) + 1) (fun _ => by linarith)
      (fun j _ hv => positiveRoundedWordDepthPath_start w k j hv)
      (t := t) (fun j => by
        have : (0 : ℝ) ≤ j.val := by positivity
        linarith)
    exact h
  · have h := finiteSmoothPathConcat_final (positiveRoundedWordDepthNode w k)
      (positiveRoundedWordDepthPath w k) (fun j => 2 * (j.val : ℝ))
      (fun j => 2 * (j.val : ℝ) + 1) (fun _ => by linarith)
      (fun j _ hv => positiveRoundedWordDepthPath_end w k j hv)
      (t := t) (fun j => by
        have : (j.val : ℝ) ≤ w.length := by exact_mod_cast Nat.le_of_lt_succ j.isLt
        linarith)
    change positiveRoundedWordDepth w k t = _ at h
    rw [h]
    change positiveRectilinearWordGapFinal w (Fin.last w.length) k = 0
    simp

theorem positiveRoundedWordCanonicalImag_exterior {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0 ∨ 2 * (w.length : ℝ) + 1 ≤ t) :
    positiveRoundedWordCanonicalImag w k t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply generatorImaginary_outside
  rcases ht with ht | ht
  · left
    have : (0 : ℝ) ≤ j.val := by positivity
    linarith
  · right
    have : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
    linarith

theorem positiveRoundedWordLift_before {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ≤ 0) :
    positiveRoundedWordLift w k s t = (t, (k.val : ℂ)) := by
  have hr := finiteSmoothPathConcat_initial
    (fun j : Fin (w.length + 1) => (((positiveWordPrefix w j.val).symm k).val : ℝ))
    (fun j t => positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith) (fun j _ hv => adjacentReal_start w k j hv)
    (t := t) (fun j => by
        have : (0 : ℝ) ≤ j.val := by positivity
        linarith)
  change positiveRoundedWordCanonicalReal w k t = _ at hr
  simp only [positiveRoundedWordLift, hr, positiveRoundedWordCanonicalImag_exterior w k (Or.inl ht),
    positiveRoundedWordDepth_exterior w k (Or.inl ht)]
  simp
  rfl

theorem positiveRoundedWordLift_after {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : 2 * (w.length : ℝ) + 1 ≤ t) :
    positiveRoundedWordLift w k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  have hr := finiteSmoothPathConcat_final
    (fun j : Fin (w.length + 1) => (((positiveWordPrefix w j.val).symm k).val : ℝ))
    (fun j t => positiveAdjacentReal w[j.val] ((positiveWordPrefix w j.val).symm k) t)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith) (fun j _ hv => adjacentReal_end w k j hv)
    (t := t) (fun j => by
      have : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
      linarith)
  change positiveRoundedWordCanonicalReal w k t = _ at hr
  simp only [positiveRoundedWordLift, hr, positiveRoundedWordCanonicalImag_exterior w k (Or.inr ht),
    positiveRoundedWordDepth_exterior w k (Or.inr ht)]
  simp

theorem positiveRoundedWord_before {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ≤ 0) :
    positiveRoundedWord w l u k s t = (t, (k.val : ℂ)) := by
  have hr := finiteSmoothPathConcat_initial (positiveRoundedWordRankNode w k)
    (positiveRoundedWordLetterCorrection w l u k s)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith)
    (fun j _ hv => positiveRoundedWordLetterCorrection_start w hl hu hU k s j hv)
    (t := t) (fun j => by
        have : (0 : ℝ) ≤ j.val := by positivity
        linarith)
  simp [positiveRoundedWord, hr, positiveRoundedWordDepth_exterior w k (Or.inl ht),
    positiveRoundedWordRankNode]
  rfl

theorem positiveRoundedWord_after {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : 2 * (w.length : ℝ) + 1 ≤ t) :
    positiveRoundedWord w l u k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  have hr := finiteSmoothPathConcat_final (positiveRoundedWordRankNode w k)
    (positiveRoundedWordLetterCorrection w l u k s)
    (fun j => 2 * (j.val : ℝ) + 1) (fun j => 2 * (j.val : ℝ) + 2)
    (fun _ => by linarith)
    (fun j _ hv => positiveRoundedWordLetterCorrection_end w hl hu hU k s j hv)
    (t := t) (fun j => by
      have : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
      linarith)
  simp [positiveRoundedWord, hr, positiveRoundedWordDepth_exterior w k (Or.inr ht),
    positiveRoundedWordRankNode]

theorem positiveRoundedWordDeformation_initial_open_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : t ≤ 1 / 3) :
    positiveRoundedWordDeformation w l u k s t = (t, (k.val : ℂ)) := by
  by_cases ht0 : 0 ≤ t
  · exact positiveRoundedWordDeformation_initial_collar w hl hu hU k s ⟨ht0, ht⟩
  · have ht' := le_of_not_ge ht0
    rw [positiveRoundedWordDeformation, positiveRoundedWordLift_before w k _ ht',
      positiveRoundedWord_before w hl hu hU k _ ht', positiveRoundedWordLift_before w k _ ht']
    abel

theorem positiveRoundedWordDeformation_final_open_collar {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (s : ℝ) {t : ℝ} (ht : 2 * (w.length : ℝ) + 2 / 3 ≤ t) :
    positiveRoundedWordDeformation w l u k s t = (t, ((w.permutation.symm k).val : ℂ)) := by
  by_cases ht0 : t ≤ 2 * (w.length : ℝ) + 1
  · exact positiveRoundedWordDeformation_final_collar w hl hu hU k s ⟨ht, ht0⟩
  · have ht' := le_of_not_ge ht0
    rw [positiveRoundedWordDeformation, positiveRoundedWordLift_after w k _ ht',
      positiveRoundedWord_after w hl hu hU k _ ht', positiveRoundedWordLift_after w k _ ht']
    abel

end OnLeConjecture.KnotTheory
