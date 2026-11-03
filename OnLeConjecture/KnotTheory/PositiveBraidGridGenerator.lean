/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventModel
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Normalizing the geometric positive crossing before grid conversion

The generator below has real coordinates given by the existing adjacent
transition. Its two moving imaginary coordinates are opposite smooth bumps,
negative on the initially lower strand. Every event-model letter deforms to
this fixed generator through distinct complex configurations. Both time-end
configurations are recorded, since the deformation moves their imaginary
coordinates. This is a local geometric step. No grid realization or ambient
isotopy of a closed braid is asserted here.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace OnLeConjecture.KnotTheory

/-- A bump with value one at the crossing and zero outside the letter interval. -/
def positiveGridGeneratorBump (t : ℝ) : ℝ :=
  4 * Real.smoothTransition t * (1 - Real.smoothTransition t)

/-- The two exchanged labels have opposite imaginary displacements. -/
def positiveGridGeneratorImaginary {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (t : ℝ) : ℝ :=
  if k = adjacentLower i then -positiveGridGeneratorBump t
  else if k = adjacentUpper i then positiveGridGeneratorBump t else 0

/-- A fixed smooth representative of one positive adjacent crossing. -/
def positiveGridGenerator {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (t : ℝ) : ℂ :=
  (positiveAdjacentReal i k t : ℂ) +
    (positiveGridGeneratorImaginary i k t : ℂ) * Complex.I

/-- The real coordinates remain fixed while the imaginary coordinates deform. -/
def positiveGridGeneratorDeformation {m : ℕ} (i : Fin (m - 1))
    (y : Fin m → ℝ) (k : Fin m) (s t : ℝ) : ℂ :=
  (positiveAdjacentReal i k t : ℂ) +
    (((1 - s) * y k + s * positiveGridGeneratorImaginary i k t : ℝ) : ℂ) * Complex.I

@[simp] theorem positiveGridGeneratorBump_half : positiveGridGeneratorBump (1 / 2) = 1 := by
  rw [positiveGridGeneratorBump, (smoothTransition_eq_half_iff _).mpr rfl]
  norm_num

theorem positiveGridGeneratorBump_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    positiveGridGeneratorBump t = 0 := by
  simp [positiveGridGeneratorBump, Real.smoothTransition.zero_of_nonpos ht]

theorem positiveGridGeneratorBump_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    positiveGridGeneratorBump t = 0 := by
  simp [positiveGridGeneratorBump, Real.smoothTransition.one_of_one_le ht]

theorem positiveGridGeneratorBump_contDiff : ContDiff ℝ ∞ positiveGridGeneratorBump :=
  (contDiff_const.mul Real.smoothTransition.contDiff).mul
    (contDiff_const.sub Real.smoothTransition.contDiff)

@[simp] theorem positiveGridGeneratorImaginary_lower {m : ℕ}
    (i : Fin (m - 1)) (t : ℝ) :
    positiveGridGeneratorImaginary i (adjacentLower i) t = -positiveGridGeneratorBump t := by
  simp [positiveGridGeneratorImaginary]

@[simp] theorem positiveGridGeneratorImaginary_upper {m : ℕ}
    (i : Fin (m - 1)) (t : ℝ) :
    positiveGridGeneratorImaginary i (adjacentUpper i) t = positiveGridGeneratorBump t := by
  have hn : adjacentUpper i ≠ adjacentLower i := by
    intro he
    have := congrArg Fin.val he
    change i.val + 1 = i.val at this
    omega
  simp [positiveGridGeneratorImaginary, hn]

theorem positiveGridGeneratorImaginary_contDiff {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) :
    ContDiff ℝ ∞ (positiveGridGeneratorImaginary i k) := by
  unfold positiveGridGeneratorImaginary
  split_ifs
  · exact positiveGridGeneratorBump_contDiff.neg
  · exact positiveGridGeneratorBump_contDiff
  · exact contDiff_const

@[simp] theorem positiveGridGeneratorDeformation_re {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (s t : ℝ) :
    (positiveGridGeneratorDeformation i y k s t).re = positiveAdjacentReal i k t := by
  simp [positiveGridGeneratorDeformation]

@[simp] theorem positiveGridGeneratorDeformation_im {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (s t : ℝ) :
    (positiveGridGeneratorDeformation i y k s t).im =
      (1 - s) * y k + s * positiveGridGeneratorImaginary i k t := by
  simp [positiveGridGeneratorDeformation]

/-- Joint smoothness includes both the deformation and braid parameters. -/
theorem positiveGridGeneratorDeformation_contDiff {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveGridGeneratorDeformation i y k p.1 p.2) := by
  exact (Complex.ofRealCLM.contDiff.comp
    ((positiveAdjacentReal_contDiff i k).comp contDiff_snd)).add
      ((Complex.ofRealCLM.contDiff.comp
        (((contDiff_const.sub contDiff_fst).mul contDiff_const).add
          (contDiff_fst.mul ((positiveGridGeneratorImaginary_contDiff i k).comp
            contDiff_snd)))).mul contDiff_const)

@[simp] theorem positiveGridGeneratorDeformation_zero {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (t : ℝ) :
    positiveGridGeneratorDeformation i y k 0 t = positiveAdjacentHeight i y k t := by
  simp [positiveGridGeneratorDeformation, positiveAdjacentHeight]

@[simp] theorem positiveGridGeneratorDeformation_one {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (t : ℝ) :
    positiveGridGeneratorDeformation i y k 1 t = positiveGridGenerator i k t := by
  simp [positiveGridGeneratorDeformation, positiveGridGenerator]

/-- The initial real ranks stay fixed, while the imaginary heights shrink to zero. -/
theorem positiveGridGeneratorDeformation_of_nonpos {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (s : ℝ)
    {t : ℝ} (ht : t ≤ 0) :
    positiveGridGeneratorDeformation i y k s t =
      (k.val : ℂ) + (((1 - s) * y k : ℝ) : ℂ) * Complex.I := by
  simp [positiveGridGeneratorDeformation, positiveAdjacentReal,
    positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_nonpos ht,
    Real.smoothTransition.zero_of_nonpos ht]

/-- The terminal real ranks are the adjacent swap, with the same height shrinkage. -/
theorem positiveGridGeneratorDeformation_of_one_le {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (k : Fin m) (s : ℝ)
    {t : ℝ} (ht : 1 ≤ t) :
    positiveGridGeneratorDeformation i y k s t =
      ((adjacentSwap i k).val : ℂ) + (((1 - s) * y k : ℝ) : ℂ) * Complex.I := by
  simp [positiveGridGeneratorDeformation, positiveAdjacentReal,
    positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_one_le ht,
    Real.smoothTransition.one_of_one_le ht]

/-- The only projected crossing remains the exchanged pair at time one half. -/
theorem positiveGridGeneratorDeformation_re_eq_iff {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) {k l : Fin m}
    (hkl : k ≠ l) (s t : ℝ) :
    (positiveGridGeneratorDeformation i y k s t).re =
      (positiveGridGeneratorDeformation i y l s t).re ↔
      ((k = adjacentLower i ∧ l = adjacentUpper i) ∨
        (k = adjacentUpper i ∧ l = adjacentLower i)) ∧ t = 1 / 2 := by
  simp only [positiveGridGeneratorDeformation_re,
    positiveAdjacentReal_eq_iff i hkl, smoothTransition_eq_half_iff]

/-- The two moving heights remain strictly ordered at their projected crossing. -/
theorem positiveGridGeneratorDeformation_crossing_height {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ)
    (hy : y (adjacentLower i) < y (adjacentUpper i))
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    (positiveGridGeneratorDeformation i y (adjacentLower i) s (1 / 2)).im <
      (positiveGridGeneratorDeformation i y (adjacentUpper i) s (1 / 2)).im := by
  simp only [positiveGridGeneratorDeformation_im,
    positiveGridGeneratorImaginary_lower, positiveGridGeneratorImaginary_upper,
    positiveGridGeneratorBump_half]
  rcases lt_or_eq_of_le hs.2 with h | rfl
  · have hp := mul_pos (sub_pos.mpr h) (sub_pos.mpr hy)
    nlinarith [hs.1]
  · norm_num

/-- Every slice is a configuration of distinct points, including both deformation endpoints. -/
theorem positiveGridGeneratorDeformation_injective {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ)
    (hy : y (adjacentLower i) < y (adjacentUpper i))
    {s : ℝ} (hs : s ∈ Icc 0 1) (t : ℝ) :
    Function.Injective (fun k => positiveGridGeneratorDeformation i y k s t) := by
  intro k l he
  by_contra hkl
  obtain ⟨h | h, rfl⟩ := (positiveGridGeneratorDeformation_re_eq_iff i y hkl s t).mp
    (congrArg Complex.re he)
  all_goals
    rcases h with ⟨rfl, rfl⟩
    have hh := positiveGridGeneratorDeformation_crossing_height i y hy hs
    have hi := congrArg Complex.im he
    linarith

/-- The real crossing velocity is unchanged by the deformation. -/
theorem positiveGridGeneratorDeformation_crossing_hasDerivAt {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ) (s : ℝ) :
    HasDerivAt (fun t => (positiveGridGeneratorDeformation i y (adjacentLower i) s t -
      positiveGridGeneratorDeformation i y (adjacentUpper i) s t).re) 4 (1 / 2) := by
  simpa only [Complex.sub_re, positiveGridGeneratorDeformation_re,
    positiveAdjacentHeight_re] using positiveAdjacentHeight_crossing_hasDerivAt i y

/-- The positive crossing determinant is preserved for the full deformation. -/
theorem positiveGridGeneratorDeformation_crossing_positive {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ)
    (hy : y (adjacentLower i) < y (adjacentUpper i))
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    0 < -deriv (fun t => (positiveGridGeneratorDeformation i y (adjacentLower i) s t -
        positiveGridGeneratorDeformation i y (adjacentUpper i) s t).re) (1 / 2) *
      (positiveGridGeneratorDeformation i y (adjacentLower i) s (1 / 2) -
        positiveGridGeneratorDeformation i y (adjacentUpper i) s (1 / 2)).im := by
  rw [(positiveGridGeneratorDeformation_crossing_hasDerivAt i y s).deriv, Complex.sub_im]
  have hh := positiveGridGeneratorDeformation_crossing_height i y hy hs
  linarith

/-- The local deformation satisfies the coordinate-product separation used by
our ambient convex-isotopy construction. -/
theorem positiveGridGeneratorDeformation_separation {m : ℕ}
    (i : Fin (m - 1)) (y : Fin m → ℝ)
    (hy : y (adjacentLower i) < y (adjacentUpper i))
    {s : ℝ} (hs : s ∈ Icc 0 1) {k l : Fin m} (hkl : k ≠ l) (t : ℝ) :
    0 < (positiveAdjacentHeight i y k t - positiveAdjacentHeight i y l t).re *
      (positiveGridGeneratorDeformation i y k s t -
        positiveGridGeneratorDeformation i y l s t).re ∨
    0 < (positiveAdjacentHeight i y k t - positiveAdjacentHeight i y l t).im *
      (positiveGridGeneratorDeformation i y k s t -
        positiveGridGeneratorDeformation i y l s t).im := by
  by_cases he : positiveAdjacentReal i k t = positiveAdjacentReal i l t
  · right
    obtain ⟨hp, ht⟩ := (positiveAdjacentReal_eq_iff i hkl t).mp he
    have ht' := (smoothTransition_eq_half_iff t).mp ht
    subst t
    have hh := positiveGridGeneratorDeformation_crossing_height i y hy hs
    rcases hp with h | h
    · rcases h with ⟨rfl, rfl⟩
      simpa only [Complex.sub_im, positiveAdjacentHeight_im] using
        mul_pos_of_neg_of_neg (sub_neg.mpr hy) (sub_neg.mpr hh)
    · rcases h with ⟨rfl, rfl⟩
      simpa only [Complex.sub_im, positiveAdjacentHeight_im] using
        mul_pos (sub_pos.mpr hy) (sub_pos.mpr hh)
  · left
    simpa only [Complex.sub_re, positiveAdjacentHeight_re,
      positiveGridGeneratorDeformation_re] using mul_self_pos.mpr (sub_ne_zero.mpr he)

/-- The fixed generator begins and ends on the real axis. -/
theorem positiveGridGenerator_endpoints {m : ℕ} (i : Fin (m - 1)) (k : Fin m) :
    (∀ t ≤ 0, positiveGridGenerator i k t = (k.val : ℂ)) ∧
    (∀ t, 1 ≤ t → positiveGridGenerator i k t = ((adjacentSwap i k).val : ℂ)) := by
  constructor
  · intro t ht
    simpa using positiveGridGeneratorDeformation_of_nonpos i (fun _ => 0) k 1 ht
  · intro t ht
    simpa using positiveGridGeneratorDeformation_of_one_le i (fun _ => 0) k 1 ht

theorem positiveGridGenerator_contDiff {m : ℕ} (i : Fin (m - 1)) (k : Fin m) :
    ContDiff ℝ ∞ (positiveGridGenerator i k) := by
  exact (Complex.ofRealCLM.contDiff.comp (positiveAdjacentReal_contDiff i k)).add
    ((Complex.ofRealCLM.contDiff.comp (positiveGridGeneratorImaginary_contDiff i k)).mul
      contDiff_const)

/-- The normalized crossing itself has no complex collisions. -/
theorem positiveGridGenerator_injective {m : ℕ} (i : Fin (m - 1)) (t : ℝ) :
    Function.Injective (fun k => positiveGridGenerator i k t) := by
  have hy : positiveGridGeneratorImaginary i (adjacentLower i) (1 / 2) <
      positiveGridGeneratorImaginary i (adjacentUpper i) (1 / 2) := by
    rw [positiveGridGeneratorImaginary_lower, positiveGridGeneratorImaginary_upper,
      positiveGridGeneratorBump_half]
    norm_num
  simpa using positiveGridGeneratorDeformation_injective i
    (fun k => positiveGridGeneratorImaginary i k (1 / 2)) hy
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) t

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The normalization of an event-model letter, in the original sheet labels. -/
def positiveBraidEventGeneratorDeformation {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (j : ℕ) (hj : j < w.length)
    (k : Fin a) (s t : ℝ) : ℂ :=
  positiveGridGeneratorDeformation w[j]
    (fun v => (K (before (positiveWordPrefix w j v)) θ).im)
    ((positiveWordPrefix w j).symm (before.symm k)) s t

/-- The starting path is exactly the corresponding interval of the existing
positive event model, including both ends of the letter interval. -/
theorem positiveBraidEventGeneratorDeformation_zero {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (j : ℕ) (hj : j < w.length)
    (k : Fin a) {t : ℝ} (ht : t ∈ Icc 0 1) :
    positiveBraidEventGeneratorDeformation K θ before w j hj k 0 t =
      planeBranchBraidEventModel K θ before w k ((j : ℝ) + t) := by
  rw [planeBranchBraidEventModel, positiveWordHeight_stage w _ j hj _
    (show (j : ℝ) + t ∈ Icc (j : ℝ) ((j : ℝ) + 1) by constructor <;> linarith [ht.1, ht.2])]
  simp only [positiveBraidEventGeneratorDeformation, positiveGridGeneratorDeformation_zero,
    add_sub_cancel_left, Function.comp_def]

/-- The final path is the fixed positive generator with the exact prefix relabeling. -/
@[simp] theorem positiveBraidEventGeneratorDeformation_one {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (j : ℕ) (hj : j < w.length)
    (k : Fin a) (t : ℝ) :
    positiveBraidEventGeneratorDeformation K θ before w j hj k 1 t =
      positiveGridGenerator w[j] ((positiveWordPrefix w j).symm (before.symm k)) t := by
  simp [positiveBraidEventGeneratorDeformation]

theorem positiveBraidEventGeneratorDeformation_contDiff {a : ℕ}
    (K : Fin a → ℝ → ℂ) (θ : ℝ) (before : Equiv.Perm (Fin a))
    (w : PositiveAdjacentWord a) (j : ℕ) (hj : j < w.length) (k : Fin a) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      positiveBraidEventGeneratorDeformation K θ before w j hj k p.1 p.2) :=
  positiveGridGeneratorDeformation_contDiff _ _ _

/-- The needed height order is derived from the positive event word, with no
additional geometric separation hypothesis. -/
theorem IsPositiveBraidEventWord.generatorDeformation_injective
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (j : ℕ) (hj : j < w.length) {s : ℝ} (hs : s ∈ Icc 0 1) (t : ℝ) :
    Function.Injective (fun k =>
      positiveBraidEventGeneratorDeformation K θ before w j hj k s t) :=
  (positiveGridGeneratorDeformation_injective _ _ (h.letter_height_order j hj) hs t).comp
    ((positiveWordPrefix w j).symm.injective.comp before.symm.injective)

/-- The derived event-model letter and its canonical generator deformation
satisfy the separation inequality in the original sheet labels. -/
theorem IsPositiveBraidEventWord.generatorDeformation_separation
    {a : ℕ} {K : Fin a → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin a)} {w : PositiveAdjacentWord a}
    (h : IsPositiveBraidEventWord K θ before after w)
    (j : ℕ) (hj : j < w.length) {s : ℝ} (hs : s ∈ Icc 0 1)
    {k l : Fin a} (hkl : k ≠ l) {t : ℝ} (ht : t ∈ Icc 0 1) :
    0 < (planeBranchBraidEventModel K θ before w k ((j : ℝ) + t) -
        planeBranchBraidEventModel K θ before w l ((j : ℝ) + t)).re *
      (positiveBraidEventGeneratorDeformation K θ before w j hj k s t -
        positiveBraidEventGeneratorDeformation K θ before w j hj l s t).re ∨
    0 < (planeBranchBraidEventModel K θ before w k ((j : ℝ) + t) -
        planeBranchBraidEventModel K θ before w l ((j : ℝ) + t)).im *
      (positiveBraidEventGeneratorDeformation K θ before w j hj k s t -
        positiveBraidEventGeneratorDeformation K θ before w j hj l s t).im := by
  rw [← positiveBraidEventGeneratorDeformation_zero K θ before w j hj k ht,
    ← positiveBraidEventGeneratorDeformation_zero K θ before w j hj l ht]
  simp only [positiveBraidEventGeneratorDeformation, positiveGridGeneratorDeformation_zero]
  apply positiveGridGeneratorDeformation_separation _ _ (h.letter_height_order j hj) hs
  exact fun he => hkl (before.symm.injective ((positiveWordPrefix w j).symm.injective he))

end OnLeConjecture.Analytic
