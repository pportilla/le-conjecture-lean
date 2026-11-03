/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositivePermutationWords
import all OnLeConjecture.KnotTheory.BraidPermutationCycles
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Complex.RealDeriv

/-! # Smooth height paths for one positive adjacent crossing

The real coordinates interpolate between the identity order and one adjacent
transposition. Imaginary coordinates remain fixed. Only the two exchanged
labels require distinct imaginary heights. Their ordering fixes the sign of
the crossing determinant.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace OnLeConjecture.KnotTheory

/-- The transition reaches its midpoint at exactly time one half. -/
theorem smoothTransition_eq_half_iff (t : ℝ) :
    Real.smoothTransition t = 1 / 2 ↔ t = 1 / 2 := by
  constructor
  · intro h
    have ht₀ : 0 < t := by
      by_contra hn
      rw [Real.smoothTransition.zero_of_nonpos (not_lt.mp hn)] at h
      norm_num at h
    have ht₁ : t < 1 := by
      by_contra hn
      rw [Real.smoothTransition.one_of_one_le (not_lt.mp hn)] at h
      norm_num at h
    have hg : expNegInvGlue t = expNegInvGlue (1 - t) := by
      have hh := (div_eq_iff (Real.smoothTransition.pos_denom t).ne').mp h
      linarith
    simp only [expNegInvGlue, not_le_of_gt ht₀,
      not_le_of_gt (sub_pos.mpr ht₁), if_false] at hg
    have he := inv_injective (neg_injective (Real.exp_injective hg))
    linarith
  · rintro rfl
    have hg : expNegInvGlue (1 / 2) ≠ 0 :=
      (expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
    unfold Real.smoothTransition
    norm_num
    field_simp
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- The exact derivative at the sole crossing time is positive. -/
theorem smoothTransition_hasDerivAt_half :
    HasDerivAt Real.smoothTransition 2 (1 / 2) := by
  have hg : HasDerivAt expNegInvGlue (4 * expNegInvGlue (1 / 2)) (1 / 2) := by
    convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
      (1 : Polynomial ℝ) (1 / 2) using 1 <;> norm_num
  have hr : HasDerivAt (fun t : ℝ => expNegInvGlue (1 - t))
      (-4 * expNegInvGlue (1 / 2)) (1 / 2) := by
    have hg' : HasDerivAt expNegInvGlue (4 * expNegInvGlue (1 / 2))
        (1 - id (1 / 2 : ℝ)) := by convert hg using 1; norm_num
    convert hg'.comp (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1) using 1
    all_goals first | rfl | norm_num
  have hd := hg.div (hg.add hr) (Real.smoothTransition.pos_denom (1 / 2)).ne'
  change HasDerivAt (fun t => expNegInvGlue t /
    (expNegInvGlue t + expNegInvGlue (1 - t))) 2 (1 / 2)
  convert hd using 1 <;> try rfl
  have hne : expNegInvGlue (1 / 2) ≠ 0 :=
    (expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  norm_num
  field_simp
  ring

/-- Real positions for the adjacent transposition, constant before zero and after one. -/
def positiveAdjacentReal {m : ℕ} (i : Fin (m - 1)) (j : Fin m) (t : ℝ) : ℝ :=
  (1 - Real.smoothTransition t) * (j.val : ℝ) +
    Real.smoothTransition t * ((adjacentSwap i j).val : ℝ)

/-- Complex height paths with fixed imaginary coordinates. -/
def positiveAdjacentHeight {m : ℕ} (i : Fin (m - 1)) (y : Fin m → ℝ)
    (j : Fin m) (t : ℝ) : ℂ :=
  (positiveAdjacentReal i j t : ℂ) + (y j : ℂ) * Complex.I

@[simp] theorem positiveAdjacentHeight_re {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    (positiveAdjacentHeight i y j t).re = positiveAdjacentReal i j t := by
  simp [positiveAdjacentHeight]

@[simp] theorem positiveAdjacentHeight_im {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (j : Fin m) (t : ℝ) :
    (positiveAdjacentHeight i y j t).im = y j := by
  simp [positiveAdjacentHeight]

theorem positiveAdjacentReal_lower {m : ℕ} (i : Fin (m - 1)) (t : ℝ) :
    positiveAdjacentReal i (adjacentLower i) t = (i.val : ℝ) + Real.smoothTransition t := by
  simp [positiveAdjacentReal, adjacentSwap.eq_def, adjacentLower]
  ring

theorem positiveAdjacentReal_upper {m : ℕ} (i : Fin (m - 1)) (t : ℝ) :
    positiveAdjacentReal i (adjacentUpper i) t = (i.val : ℝ) + 1 - Real.smoothTransition t := by
  simp [positiveAdjacentReal, adjacentSwap.eq_def, adjacentUpper]
  ring

theorem positiveAdjacentReal_fixed {m : ℕ} (i : Fin (m - 1)) (j : Fin m)
    (hj₀ : j ≠ adjacentLower i) (hj₁ : j ≠ adjacentUpper i) (t : ℝ) :
    positiveAdjacentReal i j t = (j.val : ℝ) := by
  have hj : adjacentSwap i j = j := Equiv.swap_apply_of_ne_of_ne hj₀ hj₁
  rw [positiveAdjacentReal, hj]
  ring

@[simp] theorem positiveAdjacentReal_zero {m : ℕ} (i : Fin (m - 1)) (j : Fin m) :
    positiveAdjacentReal i j 0 = (j.val : ℝ) := by simp [positiveAdjacentReal]

@[simp] theorem positiveAdjacentReal_one {m : ℕ} (i : Fin (m - 1)) (j : Fin m) :
    positiveAdjacentReal i j 1 = ((adjacentSwap i j).val : ℝ) := by
  simp [positiveAdjacentReal]

@[simp] theorem positiveAdjacentHeight_zero {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (j : Fin m) :
    positiveAdjacentHeight i y j 0 = (j.val : ℂ) + (y j : ℂ) * Complex.I := by
  simp [positiveAdjacentHeight]

@[simp] theorem positiveAdjacentHeight_one {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (j : Fin m) :
    positiveAdjacentHeight i y j 1 =
      ((adjacentSwap i j).val : ℂ) + (y j : ℂ) * Complex.I := by
  simp [positiveAdjacentHeight]

theorem positiveAdjacentHeight_of_nonpos {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (j : Fin m) {t : ℝ} (ht : t ≤ 0) :
    positiveAdjacentHeight i y j t = positiveAdjacentHeight i y j 0 := by
  simp [positiveAdjacentHeight, positiveAdjacentReal,
    Real.smoothTransition.zero_of_nonpos ht]

theorem positiveAdjacentHeight_of_one_le {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (j : Fin m) {t : ℝ} (ht : 1 ≤ t) :
    positiveAdjacentHeight i y j t = positiveAdjacentHeight i y j 1 := by
  simp [positiveAdjacentHeight, positiveAdjacentReal,
    Real.smoothTransition.one_of_one_le ht]

theorem positiveAdjacentHeight_fixed {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (j : Fin m)
    (hj₀ : j ≠ adjacentLower i) (hj₁ : j ≠ adjacentUpper i) (t : ℝ) :
    positiveAdjacentHeight i y j t = (j.val : ℂ) + (y j : ℂ) * Complex.I := by
  simp only [positiveAdjacentHeight, positiveAdjacentReal_fixed i j hj₀ hj₁,
    Complex.ofReal_natCast]

theorem positiveAdjacentReal_contDiff {m : ℕ} (i : Fin (m - 1)) (j : Fin m) :
    ContDiff ℝ ∞ (positiveAdjacentReal i j) :=
  ((contDiff_const.sub Real.smoothTransition.contDiff).mul contDiff_const).add
    (Real.smoothTransition.contDiff.mul contDiff_const)

theorem positiveAdjacentHeight_contDiff {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (j : Fin m) :
    ContDiff ℝ ∞ (positiveAdjacentHeight i y j) :=
  (Complex.ofRealCLM.contDiff.comp (positiveAdjacentReal_contDiff i j)).add contDiff_const

private theorem adjacent_labels_of_real_mem_Icc {m : ℕ} (i : Fin (m - 1))
    (j : Fin m) (hj : (j.val : ℝ) ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1)) :
    j = adjacentLower i ∨ j = adjacentUpper i := by
  have h₀ : i.val ≤ j.val := by exact_mod_cast hj.1
  have h₁ : j.val ≤ i.val + 1 := by exact_mod_cast hj.2
  by_cases he : j.val = i.val
  · exact Or.inl (Fin.ext he)
  · right
    apply Fin.ext
    change j.val = i.val + 1
    omega

/-- The moving real coordinates cannot meet a fixed coordinate. -/
theorem positiveAdjacentReal_eq_fixed_iff {m : ℕ} (i : Fin (m - 1))
    (j : Fin m) (hj₀ : j ≠ adjacentLower i) (hj₁ : j ≠ adjacentUpper i)
    (k : Fin m) (t : ℝ) :
    positiveAdjacentReal i k t = (j.val : ℝ) ↔ k = j := by
  constructor
  · intro he
    have h₀ := Real.smoothTransition.nonneg t
    have h₁ := Real.smoothTransition.le_one t
    by_cases hk₀ : k = adjacentLower i
    · rw [hk₀, positiveAdjacentReal_lower] at he
      obtain h | h := adjacent_labels_of_real_mem_Icc i j ⟨by linarith, by linarith⟩
      · exact (hj₀ h).elim
      · exact (hj₁ h).elim
    by_cases hk₁ : k = adjacentUpper i
    · rw [hk₁, positiveAdjacentReal_upper] at he
      obtain h | h := adjacent_labels_of_real_mem_Icc i j ⟨by linarith, by linarith⟩
      · exact (hj₀ h).elim
      · exact (hj₁ h).elim
    rw [positiveAdjacentReal_fixed i k hk₀ hk₁] at he
    exact Fin.ext (Nat.cast_injective he)
  · rintro rfl
    exact positiveAdjacentReal_fixed i _ hj₀ hj₁ t

/-- Distinct projected strands coincide precisely for the exchanged pair at
transition value one half. The two possible label orders are both included. -/
theorem positiveAdjacentReal_eq_iff {m : ℕ} (i : Fin (m - 1))
    {j k : Fin m} (hjk : j ≠ k) (t : ℝ) :
    positiveAdjacentReal i j t = positiveAdjacentReal i k t ↔
      ((j = adjacentLower i ∧ k = adjacentUpper i) ∨
        (j = adjacentUpper i ∧ k = adjacentLower i)) ∧
          Real.smoothTransition t = 1 / 2 := by
  constructor
  · intro he
    have hj : j = adjacentLower i ∨ j = adjacentUpper i := by
      by_contra hn
      push Not at hn
      have hk := (positiveAdjacentReal_eq_fixed_iff i j hn.1 hn.2 k t).mp
        (he.symm.trans (positiveAdjacentReal_fixed i j hn.1 hn.2 t))
      exact hjk hk.symm
    have hk : k = adjacentLower i ∨ k = adjacentUpper i := by
      by_contra hn
      push Not at hn
      have hj' := (positiveAdjacentReal_eq_fixed_iff i k hn.1 hn.2 j t).mp
        (he.trans (positiveAdjacentReal_fixed i k hn.1 hn.2 t))
      exact hjk hj'
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
    · exact (hjk rfl).elim
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      rw [positiveAdjacentReal_lower, positiveAdjacentReal_upper] at he
      linarith
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      rw [positiveAdjacentReal_upper, positiveAdjacentReal_lower] at he
      linarith
    · exact (hjk rfl).elim
  · rintro ⟨h | h, ht⟩ <;> rcases h with ⟨rfl, rfl⟩ <;>
      rw [positiveAdjacentReal_lower, positiveAdjacentReal_upper, ht] <;> ring

/-- The unique projected crossing time is exactly one half. -/
theorem positiveAdjacentHeight_re_eq_iff {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) {j k : Fin m} (hjk : j ≠ k) (t : ℝ) :
    (positiveAdjacentHeight i y j t).re = (positiveAdjacentHeight i y k t).re ↔
      ((j = adjacentLower i ∧ k = adjacentUpper i) ∨
        (j = adjacentUpper i ∧ k = adjacentLower i)) ∧ t = 1 / 2 := by
  rw [positiveAdjacentHeight_re, positiveAdjacentHeight_re,
    positiveAdjacentReal_eq_iff i hjk, smoothTransition_eq_half_iff]

/-- Only the exchanged pair needs distinct imaginary heights to obtain a path
of configurations with no complex collisions. -/
theorem positiveAdjacentHeight_injective {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (hy : y (adjacentLower i) ≠ y (adjacentUpper i)) (t : ℝ) :
    Function.Injective (fun j => positiveAdjacentHeight i y j t) := by
  intro j k he
  by_contra hjk
  have hr := ((positiveAdjacentHeight_re_eq_iff i y hjk t).mp
    (congrArg Complex.re he)).1
  have hi := congrArg Complex.im he
  simp only [positiveAdjacentHeight_im] at hi
  rcases hr with h | h <;> rcases h with ⟨rfl, rfl⟩
  · exact hy hi
  · exact hy hi.symm

/-- The projected difference of the moving lower label and moving upper label. -/
theorem positiveAdjacentHeight_lower_sub_upper_re {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (t : ℝ) :
    (positiveAdjacentHeight i y (adjacentLower i) t -
      positiveAdjacentHeight i y (adjacentUpper i) t).re =
        2 * Real.smoothTransition t - 1 := by
  simp only [Complex.sub_re, positiveAdjacentHeight_re,
    positiveAdjacentReal_lower, positiveAdjacentReal_upper]
  ring

/-- The moving pair crosses transversely, with positive projected-difference derivative. -/
theorem positiveAdjacentHeight_crossing_hasDerivAt {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) :
    HasDerivAt (fun t => (positiveAdjacentHeight i y (adjacentLower i) t -
      positiveAdjacentHeight i y (adjacentUpper i) t).re) 4 (1 / 2) := by
  simp_rw [positiveAdjacentHeight_lower_sub_upper_re]
  convert (smoothTransition_hasDerivAt_half.const_mul 2).sub_const 1 using 1
  all_goals first | rfl | norm_num

/-- A lower initial imaginary height gives the positive determinant convention
`-x' * y > 0` at the sole projected crossing. -/
theorem positiveAdjacentHeight_crossing_positive {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (hy : y (adjacentLower i) < y (adjacentUpper i)) :
    0 < -deriv (fun t => (positiveAdjacentHeight i y (adjacentLower i) t -
        positiveAdjacentHeight i y (adjacentUpper i) t).re) (1 / 2) *
      (positiveAdjacentHeight i y (adjacentLower i) (1 / 2) -
        positiveAdjacentHeight i y (adjacentUpper i) (1 / 2)).im ∧
      deriv (fun t => (positiveAdjacentHeight i y (adjacentLower i) t -
        positiveAdjacentHeight i y (adjacentUpper i) t).re) (1 / 2) ≠ 0 := by
  rw [(positiveAdjacentHeight_crossing_hasDerivAt i y).deriv]
  simp only [Complex.sub_im, positiveAdjacentHeight_im]
  constructor
  · linarith
  · norm_num

/-- Every projected coincidence of distinct labels has positive crossing determinant,
independently of the order in which those two labels are named. -/
theorem positiveAdjacentHeight_positive_at_coincidence {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (hy : y (adjacentLower i) < y (adjacentUpper i))
    {j k : Fin m} (hjk : j ≠ k) {t : ℝ}
    (ht : (positiveAdjacentHeight i y j t).re = (positiveAdjacentHeight i y k t).re) :
    0 < -deriv (fun s => (positiveAdjacentHeight i y j s -
        positiveAdjacentHeight i y k s).re) t *
      (positiveAdjacentHeight i y j t - positiveAdjacentHeight i y k t).im ∧
      deriv (fun s => (positiveAdjacentHeight i y j s -
        positiveAdjacentHeight i y k s).re) t ≠ 0 := by
  obtain ⟨h | h, rfl⟩ := (positiveAdjacentHeight_re_eq_iff i y hjk t).mp ht
  · rcases h with ⟨rfl, rfl⟩
    exact positiveAdjacentHeight_crossing_positive i y hy
  · rcases h with ⟨rfl, rfl⟩
    have hf : (fun s => (positiveAdjacentHeight i y (adjacentUpper i) s -
        positiveAdjacentHeight i y (adjacentLower i) s).re) =
        fun s => -(positiveAdjacentHeight i y (adjacentLower i) s -
          positiveAdjacentHeight i y (adjacentUpper i) s).re := by
      funext s
      simp only [Complex.sub_re]
      ring
    have hd : deriv (fun s => -(positiveAdjacentHeight i y (adjacentLower i) s -
        positiveAdjacentHeight i y (adjacentUpper i) s).re) (1 / 2) = -4 := by
      exact (positiveAdjacentHeight_crossing_hasDerivAt i y).neg.deriv
    rw [hf, hd]
    simp only [Complex.sub_im, positiveAdjacentHeight_im]
    constructor
    · linarith
    · norm_num

end OnLeConjecture.KnotTheory
