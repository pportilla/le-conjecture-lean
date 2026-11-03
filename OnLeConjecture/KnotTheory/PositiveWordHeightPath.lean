/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveAdjacentHeightPath
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Calculus.Deriv.Shift
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Smooth complex height paths for positive adjacent words

The position-to-label permutation after each prefix determines each strand's
real position. A sum of shifted smooth transitions interpolates these positions
globally, with fixed label-dependent imaginary heights.
-/

@[expose] public noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace OnLeConjecture.KnotTheory

/-- The permutation from positions to initial labels after the first `j` letters. -/
def positiveWordPrefix {m : ℕ} (w : PositiveAdjacentWord m) (j : ℕ) :
    Equiv.Perm (Fin m) := PositiveAdjacentWord.permutation (w.take j)

@[simp] theorem positiveWordPrefix_zero {m : ℕ} (w : PositiveAdjacentWord m) :
    positiveWordPrefix w 0 = 1 := by simp [positiveWordPrefix]

@[simp] theorem positiveWordPrefix_length {m : ℕ} (w : PositiveAdjacentWord m) :
    positiveWordPrefix w w.length = w.permutation := by simp [positiveWordPrefix]

theorem positiveWordPrefix_succ {m : ℕ} (w : PositiveAdjacentWord m)
    (j : ℕ) (hj : j < w.length) :
    positiveWordPrefix w (j + 1) = positiveWordPrefix w j * adjacentSwap w[j] := by
  have happ (u v : PositiveAdjacentWord m) :
      PositiveAdjacentWord.permutation (u ++ v) = u.permutation * v.permutation := by
    induction u with
    | nil => simp
    | cons i u ih =>
      simp only [List.cons_append, PositiveAdjacentWord.permutation_cons, ih, mul_assoc]
  change PositiveAdjacentWord.permutation (w.take (j + 1)) = _
  rw [List.take_succ_eq_append_getElem hj, happ]
  simp [positiveWordPrefix]

theorem positiveWordPrefix_succ_symm {m : ℕ} (w : PositiveAdjacentWord m)
    (j : ℕ) (hj : j < w.length) (k : Fin m) :
    (positiveWordPrefix w (j + 1)).symm k =
      adjacentSwap w[j] ((positiveWordPrefix w j).symm k) := by
  apply (positiveWordPrefix w (j + 1)).injective
  rw [Equiv.apply_symm_apply, positiveWordPrefix_succ w j hj]
  simp [Equiv.Perm.mul_apply, adjacentSwap.eq_def]

/-- A finite sum of shifted transitions, without piecewise gluing. -/
def positiveWordReal {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) (t : ℝ) : ℝ :=
  (k.val : ℝ) + ∑ j ∈ Finset.range w.length, Real.smoothTransition (t - j) *
    (((positiveWordPrefix w (j + 1)).symm k).val -
      (((positiveWordPrefix w j).symm k).val : ℝ))

/-- Complex heights with constant imaginary coordinate on each label. -/
def positiveWordHeight {m : ℕ} (w : PositiveAdjacentWord m) (y : Fin m → ℝ)
    (k : Fin m) (t : ℝ) : ℂ :=
  (positiveWordReal w k t : ℂ) + (y k : ℂ) * Complex.I

@[simp] theorem positiveWordHeight_re {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) (t : ℝ) :
    (positiveWordHeight w y k t).re = positiveWordReal w k t := by
  simp [positiveWordHeight]

@[simp] theorem positiveWordHeight_im {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) (t : ℝ) :
    (positiveWordHeight w y k t).im = y k := by simp [positiveWordHeight]

private theorem shifted_transition_sum_end (x : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ≤ t) :
    x 0 + ∑ j ∈ Finset.range n, Real.smoothTransition (t - j) * (x (j + 1) - x j) =
      x n := by
  have hs : ∀ j ∈ Finset.range n, Real.smoothTransition (t - j) = 1 := by
    intro j hj
    apply Real.smoothTransition.one_of_one_le
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hj
    linarith
  rw [Finset.sum_congr rfl (fun j hj => by rw [hs j hj, one_mul])]
  rw [Finset.sum_range_sub]
  ring

private theorem shifted_transition_sum_stage (x : ℕ → ℝ) (n j : ℕ)
    (hj : j < n) {t : ℝ} (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    x 0 + ∑ h ∈ Finset.range n, Real.smoothTransition (t - h) * (x (h + 1) - x h) =
      x j + Real.smoothTransition (t - j) * (x (j + 1) - x j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    by_cases he : j = n
    · subst j
      rw [shifted_transition_sum_end x n ht.1]
    · have hjn : j < n := by omega
      rw [ih hjn]
      have hz : Real.smoothTransition (t - n) = 0 := by
        apply Real.smoothTransition.zero_of_nonpos
        have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
        linarith [ht.2]
      rw [hz, zero_mul, add_zero]

theorem positiveWordReal_contDiff {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) :
    ContDiff ℝ ∞ (positiveWordReal w k) :=
  contDiff_const.add (ContDiff.sum fun _j _ =>
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul contDiff_const)

theorem positiveWordHeight_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) : ContDiff ℝ ∞ (positiveWordHeight w y k) :=
  (Complex.ofRealCLM.contDiff.comp (positiveWordReal_contDiff w k)).add contDiff_const

/-- On each letter interval, the real path is exactly the one-generator path
after relabeling by the prefix permutation. -/
theorem positiveWordReal_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (j : ℕ) (hj : j < w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    positiveWordReal w k t =
      positiveAdjacentReal w[j] ((positiveWordPrefix w j).symm k) (t - j) := by
  have hh := shifted_transition_sum_stage
    (fun h => (((positiveWordPrefix w h).symm k).val : ℝ)) w.length j hj ht
  simp only [positiveWordPrefix_zero, Equiv.Perm.one_def, Equiv.refl_symm,
    Equiv.refl_apply] at hh
  rw [positiveWordReal, hh, positiveWordPrefix_succ_symm w j hj, positiveAdjacentReal]
  ring

theorem positiveWordHeight_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (j : ℕ) (hj : j < w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    positiveWordHeight w y k t =
      positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
        ((positiveWordPrefix w j).symm k) (t - j) := by
  simp only [positiveWordHeight, positiveAdjacentHeight, positiveWordReal_stage w j hj k ht,
    Function.comp_apply, Equiv.apply_symm_apply]

theorem positiveWordReal_of_nonpos {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0) : positiveWordReal w k t = (k.val : ℝ) := by
  have hs : ∀ j : ℕ, Real.smoothTransition (t - j) = 0 := fun j =>
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr (ht.trans (Nat.cast_nonneg j)))
  simp [positiveWordReal, hs]

theorem positiveWordReal_of_length_le {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : (w.length : ℝ) ≤ t) :
    positiveWordReal w k t = ((w.permutation.symm k).val : ℝ) := by
  simpa only [positiveWordReal, positiveWordPrefix_zero, positiveWordPrefix_length,
    Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply] using
      shifted_transition_sum_end
        (fun h => (((positiveWordPrefix w h).symm k).val : ℝ)) w.length ht

@[simp] theorem positiveWordHeight_zero {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) :
    positiveWordHeight w y k 0 = (k.val : ℂ) + (y k : ℂ) * Complex.I := by
  simp [positiveWordHeight, positiveWordReal_of_nonpos w k le_rfl]

theorem positiveWordHeight_of_nonpos {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) {t : ℝ} (ht : t ≤ 0) :
    positiveWordHeight w y k t = positiveWordHeight w y k 0 := by
  simp [positiveWordHeight, positiveWordReal_of_nonpos w k ht,
    positiveWordReal_of_nonpos w k le_rfl]

theorem positiveWordHeight_of_length_le {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (k : Fin m) {t : ℝ} (ht : (w.length : ℝ) ≤ t) :
    positiveWordHeight w y k t =
      ((w.permutation.symm k).val : ℂ) + (y k : ℂ) * Complex.I := by
  simp [positiveWordHeight, positiveWordReal_of_length_le w k ht]

/-- The precise initial labels and crossing time of the `j`th letter. -/
theorem positiveWordHeight_stage_re_eq_iff {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (j : ℕ) (hj : j < w.length) {k l : Fin m} (hkl : k ≠ l)
    {t : ℝ} (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    (positiveWordHeight w y k t).re = (positiveWordHeight w y l t).re ↔
      ((k = positiveWordPrefix w j (adjacentLower w[j]) ∧
        l = positiveWordPrefix w j (adjacentUpper w[j])) ∨
       (k = positiveWordPrefix w j (adjacentUpper w[j]) ∧
        l = positiveWordPrefix w j (adjacentLower w[j]))) ∧ t = (j : ℝ) + 1 / 2 := by
  rw [positiveWordHeight_stage w y j hj k ht, positiveWordHeight_stage w y j hj l ht,
    positiveAdjacentHeight_re_eq_iff w[j] (y ∘ positiveWordPrefix w j)
      (fun he => hkl ((positiveWordPrefix w j).symm.injective he))]
  simp only [Equiv.symm_apply_eq]
  constructor <;> rintro ⟨h, htime⟩ <;> exact ⟨h, by linarith⟩

/-- Every projected coincidence occurs at the midpoint of a letter interval
and between exactly the labels exchanged by that prefix and letter. -/
theorem positiveWordHeight_re_eq_iff {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) {k l : Fin m} (hkl : k ≠ l) (t : ℝ) :
    (positiveWordHeight w y k t).re = (positiveWordHeight w y l t).re ↔
      ∃ j : ℕ, ∃ hj : j < w.length,
        ((k = positiveWordPrefix w j (adjacentLower w[j]) ∧
          l = positiveWordPrefix w j (adjacentUpper w[j])) ∨
         (k = positiveWordPrefix w j (adjacentUpper w[j]) ∧
          l = positiveWordPrefix w j (adjacentLower w[j]))) ∧ t = (j : ℝ) + 1 / 2 := by
  constructor
  · intro he
    have hr := he
    simp only [positiveWordHeight_re] at hr
    have ht₀ : 0 < t := by
      by_contra hn
      rw [positiveWordReal_of_nonpos w k (not_lt.mp hn),
        positiveWordReal_of_nonpos w l (not_lt.mp hn)] at hr
      exact hkl (Fin.ext (Nat.cast_injective hr))
    have ht₁ : t < (w.length : ℝ) := by
      by_contra hn
      rw [positiveWordReal_of_length_le w k (not_lt.mp hn),
        positiveWordReal_of_length_le w l (not_lt.mp hn)] at hr
      exact hkl (w.permutation.symm.injective (Fin.ext (Nat.cast_injective hr)))
    let j := Nat.floor t
    have hj : j < w.length := (Nat.floor_lt ht₀.le).mpr ht₁
    have hmem : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) :=
      ⟨Nat.floor_le ht₀.le, (Nat.lt_floor_add_one t).le⟩
    exact ⟨j, hj, (positiveWordHeight_stage_re_eq_iff w y j hj hkl hmem).mp he⟩
  · rintro ⟨j, hj, hp, rfl⟩
    apply (positiveWordHeight_stage_re_eq_iff w y j hj hkl ⟨by linarith, by linarith⟩).mpr
    exact ⟨hp, rfl⟩

/-- Distinct imaginary heights are required only for pairs exchanged by letters. -/
theorem positiveWordHeight_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ)
    (hy : ∀ j : ℕ, ∀ hj : j < w.length,
      y (positiveWordPrefix w j (adjacentLower w[j])) ≠
        y (positiveWordPrefix w j (adjacentUpper w[j]))) (t : ℝ) :
    Function.Injective (fun k => positiveWordHeight w y k t) := by
  intro k l he
  by_contra hkl
  obtain ⟨j, hj, h | h, _⟩ :=
    (positiveWordHeight_re_eq_iff w y hkl t).mp (congrArg Complex.re he)
  all_goals
    have hi := congrArg Complex.im he
    simp only [positiveWordHeight_im] at hi
    rcases h with ⟨rfl, rfl⟩
  · exact hy j hj hi
  · exact hy j hj hi.symm

/-- At an interior time of a letter interval, the projected derivative agrees
with that of the translated and relabeled one-generator path. -/
theorem positiveWordHeight_stage_deriv {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ) (j : ℕ) (hj : j < w.length) (k l : Fin m)
    {t : ℝ} (ht : t ∈ Ioo (j : ℝ) ((j : ℝ) + 1)) :
    deriv (fun s => (positiveWordHeight w y k s - positiveWordHeight w y l s).re) t =
      deriv (fun s => (positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
        ((positiveWordPrefix w j).symm k) s -
        positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
          ((positiveWordPrefix w j).symm l) s).re) (t - j) := by
  have he : (fun s => (positiveWordHeight w y k s - positiveWordHeight w y l s).re) =ᶠ[𝓝 t]
      fun s => (positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
        ((positiveWordPrefix w j).symm k) (s - j) -
        positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
          ((positiveWordPrefix w j).symm l) (s - j)).re := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [positiveWordHeight_stage w y j hj k ⟨hs.1.le, hs.2.le⟩,
      positiveWordHeight_stage w y j hj l ⟨hs.1.le, hs.2.le⟩]
  rw [he.deriv_eq]
  exact deriv_comp_sub_const (fun s : ℝ =>
    (positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
      ((positiveWordPrefix w j).symm k) s -
      positiveAdjacentHeight w[j] (y ∘ positiveWordPrefix w j)
        ((positiveWordPrefix w j).symm l) s).re) (j : ℝ) t

/-- Positive imaginary-height order for each exchanged pair makes every
projected coincidence transverse and positive. -/
theorem positiveWordHeight_positive_at_coincidence {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ)
    (hy : ∀ j : ℕ, ∀ hj : j < w.length,
      y (positiveWordPrefix w j (adjacentLower w[j])) <
        y (positiveWordPrefix w j (adjacentUpper w[j])))
    {k l : Fin m} (hkl : k ≠ l) {t : ℝ}
    (ht : (positiveWordHeight w y k t).re = (positiveWordHeight w y l t).re) :
    0 < -deriv (fun s => (positiveWordHeight w y k s - positiveWordHeight w y l s).re) t *
      (positiveWordHeight w y k t - positiveWordHeight w y l t).im ∧
      deriv (fun s => (positiveWordHeight w y k s - positiveWordHeight w y l s).re) t ≠ 0 := by
  obtain ⟨j, hj, _, htime⟩ := (positiveWordHeight_re_eq_iff w y hkl t).mp ht
  have hmem : t ∈ Ioo (j : ℝ) ((j : ℝ) + 1) := by
    rw [htime]
    constructor <;> linarith
  have hclosed : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) := ⟨hmem.1.le, hmem.2.le⟩
  rw [positiveWordHeight_stage w y j hj k hclosed,
    positiveWordHeight_stage w y j hj l hclosed] at ht
  have hpos := positiveAdjacentHeight_positive_at_coincidence w[j]
    (y ∘ positiveWordPrefix w j) (hy j hj)
    (fun he => hkl ((positiveWordPrefix w j).symm.injective he)) ht
  rw [positiveWordHeight_stage_deriv w y j hj k l hmem,
    positiveWordHeight_stage w y j hj k hclosed,
    positiveWordHeight_stage w y j hj l hclosed]
  exact hpos

end OnLeConjecture.KnotTheory
