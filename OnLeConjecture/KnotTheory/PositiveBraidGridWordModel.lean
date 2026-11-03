/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridGenerator
public import OnLeConjecture.Analytic.PlaneBranchBraidGlobalModel
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Canonical smooth positive word paths

The imaginary coordinate is a finite sum of the prefix-labelled generator
bumps. At most one summand can be nonzero. Thus every letter interval is the
fixed generator, the initial and terminal configurations lie on the real axis,
and the model retains the existing event intervals and intervening gaps.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff BigOperators

namespace OnLeConjecture.KnotTheory

def positiveGridWordImaginary {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) : ℝ :=
  ∑ j : Fin w.length, positiveGridGeneratorImaginary w[j.val]
    ((positiveWordPrefix w j.val).symm k) (t - j.val)

/-- The canonical word path uses the same real coordinates as the event word. -/
def positiveGridWord {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) (t : ℝ) : ℂ :=
  (positiveWordReal w k t : ℂ) + (positiveGridWordImaginary w k t : ℂ) * Complex.I

@[simp] theorem positiveGridWord_re {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) : (positiveGridWord w k t).re = positiveWordReal w k t := by
  simp [positiveGridWord]

@[simp] theorem positiveGridWord_im {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (t : ℝ) : (positiveGridWord w k t).im = positiveGridWordImaginary w k t := by
  simp [positiveGridWord]

theorem positiveGridGeneratorImaginary_of_nonpos {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) {t : ℝ} (ht : t ≤ 0) : positiveGridGeneratorImaginary i k t = 0 := by
  simp [positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_nonpos ht]

theorem positiveGridGeneratorImaginary_of_one_le {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) {t : ℝ} (ht : 1 ≤ t) : positiveGridGeneratorImaginary i k t = 0 := by
  simp [positiveGridGeneratorImaginary, positiveGridGeneratorBump_of_one_le ht]

theorem positiveGridWordImaginary_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : ContDiff ℝ ∞ (positiveGridWordImaginary w k) :=
  ContDiff.sum fun _j _ => (positiveGridGeneratorImaginary_contDiff _ _).comp
    (contDiff_id.sub contDiff_const)

theorem positiveGridWord_contDiff {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) : ContDiff ℝ ∞ (positiveGridWord w k) :=
  (Complex.ofRealCLM.contDiff.comp (positiveWordReal_contDiff w k)).add
    ((Complex.ofRealCLM.contDiff.comp (positiveGridWordImaginary_contDiff w k)).mul contDiff_const)

theorem positiveGridWordImaginary_of_nonpos {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0) : positiveGridWordImaginary w k t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact positiveGridGeneratorImaginary_of_nonpos _ _ (by linarith [Nat.cast_nonneg (α := ℝ) j.val])

theorem positiveGridWordImaginary_of_length_le {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : (w.length : ℝ) ≤ t) :
    positiveGridWordImaginary w k t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply positiveGridGeneratorImaginary_of_one_le
  have hj : (j.val : ℝ) + 1 ≤ w.length := by exact_mod_cast j.isLt
  linarith

/-- On a letter interval all the other bump summands vanish, including at the seams. -/
theorem positiveGridWordImaginary_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (j : ℕ) (hj : j < w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    positiveGridWordImaginary w k t =
      positiveGridGeneratorImaginary w[j] ((positiveWordPrefix w j).symm k) (t - j) := by
  unfold positiveGridWordImaginary
  apply Finset.sum_eq_single (⟨j, hj⟩ : Fin w.length)
  · intro q _ hq
    have hn : q.val ≠ j := fun he => hq (Fin.ext he)
    rcases lt_or_gt_of_ne hn with h | h
    · apply positiveGridGeneratorImaginary_of_one_le
      have hcast : (q.val : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [ht.1]
    · apply positiveGridGeneratorImaginary_of_nonpos
      have hcast : (j : ℝ) + 1 ≤ q.val := by exact_mod_cast h
      linarith [ht.2]
  · simp

/-- The word path is exactly the fixed generator in the prefix labels. -/
theorem positiveGridWord_stage {m : ℕ} (w : PositiveAdjacentWord m)
    (j : ℕ) (hj : j < w.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (j : ℝ) ((j : ℝ) + 1)) :
    positiveGridWord w k t =
      positiveGridGenerator w[j] ((positiveWordPrefix w j).symm k) (t - j) := by
  rw [positiveGridWord, positiveWordReal_stage w j hj k ht,
    positiveGridWordImaginary_stage w j hj k ht]
  rfl

theorem positiveGridWord_of_nonpos {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ 0) : positiveGridWord w k t = (k.val : ℂ) := by
  simp [positiveGridWord, positiveWordReal_of_nonpos w k ht,
    positiveGridWordImaginary_of_nonpos w k ht]

theorem positiveGridWord_of_length_le {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : (w.length : ℝ) ≤ t) :
    positiveGridWord w k t = ((w.permutation.symm k).val : ℂ) := by
  simp [positiveGridWord, positiveWordReal_of_length_le w k ht,
    positiveGridWordImaginary_of_length_le w k ht]

/-- The canonical word is separated from every event word with the same
positive crossing-height orders. -/
theorem positiveGridWord_separation {m : ℕ} (w : PositiveAdjacentWord m)
    (y : Fin m → ℝ)
    (hy : ∀ j : ℕ, ∀ hj : j < w.length,
      y (positiveWordPrefix w j (adjacentLower w[j])) <
        y (positiveWordPrefix w j (adjacentUpper w[j])))
    {k l : Fin m} (hkl : k ≠ l) (t : ℝ) :
    0 < (positiveWordHeight w y k t - positiveWordHeight w y l t).re *
      (positiveGridWord w k t - positiveGridWord w l t).re ∨
    0 < (positiveWordHeight w y k t - positiveWordHeight w y l t).im *
      (positiveGridWord w k t - positiveGridWord w l t).im := by
  by_cases he : positiveWordReal w k t = positiveWordReal w l t
  · have he' : (positiveWordHeight w y k t).re = (positiveWordHeight w y l t).re := by
      simpa using he
    obtain ⟨j, hj, _, ht⟩ := (positiveWordHeight_re_eq_iff w y hkl t).mp he'
    have hmem : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) := by rw [ht]; constructor <;> linarith
    rw [positiveWordHeight_stage w y j hj k hmem,
      positiveWordHeight_stage w y j hj l hmem,
      positiveGridWord_stage w j hj k hmem, positiveGridWord_stage w j hj l hmem]
    simpa only [positiveGridGeneratorDeformation_one] using
      positiveGridGeneratorDeformation_separation w[j] (y ∘ positiveWordPrefix w j)
        (hy j hj) (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
        (fun hh => hkl ((positiveWordPrefix w j).symm.injective hh)) (t - j)
  · left
    simpa only [Complex.sub_re, positiveWordHeight_re, positiveGridWord_re] using
      mul_self_pos.mpr (sub_ne_zero.mpr he)

/-- Canonical word paths have no collisions, without any chosen event heights. -/
theorem positiveGridWord_injective {m : ℕ} (w : PositiveAdjacentWord m) (t : ℝ) :
    Function.Injective (fun k => positiveGridWord w k t) := by
  by_cases ht₀ : t ≤ 0
  · simp_rw [positiveGridWord_of_nonpos w _ ht₀]
    exact fun k l he => Fin.ext (Nat.cast_injective he)
  by_cases ht₁ : (w.length : ℝ) ≤ t
  · simp_rw [positiveGridWord_of_length_le w _ ht₁]
    exact fun k l he => w.permutation.symm.injective (Fin.ext (Nat.cast_injective he))
  let j := Nat.floor t
  have hj : j < w.length := (Nat.floor_lt (le_of_not_ge ht₀)).mpr (lt_of_not_ge ht₁)
  have hmem : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) :=
    ⟨Nat.floor_le (le_of_not_ge ht₀), (Nat.lt_floor_add_one t).le⟩
  simp_rw [positiveGridWord_stage w j hj _ hmem]
  exact (positiveGridGenerator_injective w[j] (t - j)).comp
    (positiveWordPrefix w j).symm.injective

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory

/-- The canonical word of an event on its original outer interval, with the
same prefix labels and the same constant time collars. -/
def positiveGridEventPath {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (j : Fin N) (k : Fin a) (t : ℝ) : ℂ :=
  positiveGridWord (w j) ((σ j.castSucc).symm k)
    ((w j).length * (3 * ((t - left j) / (right j - left j)) - 1))

/-- The global canonical word model. Gaps have constant real configurations,
so only event increments contribute to the sum. -/
def positiveGridGlobalWordModel {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (k : Fin a) (t : ℝ) : ℂ :=
  (((σ 0).symm k).val : ℂ) + ∑ j : Fin N,
    (positiveGridEventPath left right σ w j k t - (((σ j.castSucc).symm k).val : ℂ))

theorem positiveGridEventPath_contDiff {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (j : Fin N) (k : Fin a) : ContDiff ℝ ∞ (positiveGridEventPath left right σ w j k) :=
  (positiveGridWord_contDiff _ _).comp
    (contDiff_const.mul ((contDiff_const.mul
      ((contDiff_id.sub contDiff_const).div_const _)).sub contDiff_const))

theorem positiveGridGlobalWordModel_contDiff {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (k : Fin a) : ContDiff ℝ ∞ (positiveGridGlobalWordModel left right σ w k) :=
  contDiff_const.add (ContDiff.sum fun j _ =>
    (positiveGridEventPath_contDiff left right σ w j k).sub contDiff_const)

theorem positiveGridEventPath_of_le {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (j : Fin N) (k : Fin a) (hlt : left j < right j) {t : ℝ} (ht : t ≤ left j) :
    positiveGridEventPath left right σ w j k t = (((σ j.castSucc).symm k).val : ℂ) := by
  apply positiveGridWord_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
  have hh : (t - left j) / (right j - left j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlt.le)
  linarith

theorem positiveGridEventPath_of_ge {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (j : Fin N) (k : Fin a) (hlt : left j < right j)
    (hp : σ j.castSucc * (w j).permutation = σ j.succ)
    {t : ℝ} (ht : right j ≤ t) :
    positiveGridEventPath left right σ w j k t = (((σ j.succ).symm k).val : ℂ) := by
  have hh : 1 ≤ (t - left j) / (right j - left j) :=
    (le_div_iff₀ (sub_pos.mpr hlt)).mpr (by linarith)
  have htime : ((w j).length : ℝ) ≤
      (w j).length * (3 * ((t - left j) / (right j - left j)) - 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (w j).length]
  rw [positiveGridEventPath, positiveGridWord_of_length_le _ _ htime]
  congr 2
  apply (σ j.succ).injective
  rw [← hp]
  simp

/-- The finite sum equals its active event path, including interval endpoints. -/
theorem positiveGridGlobalWordModel_on_event {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (j : Fin N) (k : Fin a) {t : ℝ} (ht : t ∈ Icc (left j) (right j)) :
    positiveGridGlobalWordModel left right σ w k t =
      positiveGridEventPath left right σ w j k t := by
  apply finitePath_sum_eq_active
    (fun i => (((σ i).symm k).val : ℂ))
    (fun q => positiveGridEventPath left right σ w q k t) j
  · intro q hq
    exact positiveGridEventPath_of_ge left right σ w q k (hlt q) (hp q)
      ((hsep q j hq).le.trans ht.1)
  · intro q hq
    exact positiveGridEventPath_of_le left right σ w q k (hlt q)
      (ht.2.trans (hsep j q hq).le)

/-- Every original gap becomes the constant real-rank configuration. -/
theorem positiveGridGlobalWordModel_on_gap {a N : ℕ} (b d : ℝ) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (i : Fin (N + 1)) (k : Fin a) {t : ℝ}
    (ht : t ∈ Icc (braidModelGapLeft b right i) (braidModelGapRight d left i)) :
    positiveGridGlobalWordModel left right σ w k t = (((σ i).symm k).val : ℂ) := by
  apply finitePath_sum_eq_cut
    (fun i => (((σ i).symm k).val : ℂ))
    (fun q => positiveGridEventPath left right σ w q k t) i
  · intro j hj
    exact positiveGridEventPath_of_ge left right σ w j k (hlt j) (hp j)
      ((braidModel_right_le_gapLeft b left right hlt hsep j i hj).trans ht.1)
  · intro j hj
    exact positiveGridEventPath_of_le left right σ w j k (hlt j)
      (ht.2.trans (braidModel_gapRight_le_left d left right hlt hsep i j hj))

/-- Exact initial and final plateaus of the canonical global model. -/
theorem positiveGridGlobalWordModel_of_le {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (k : Fin a) {t : ℝ} (ht : ∀ j, t ≤ left j) :
    positiveGridGlobalWordModel left right σ w k t = (((σ 0).symm k).val : ℂ) := by
  simp [positiveGridGlobalWordModel, positiveGridEventPath_of_le left right σ w _ k
    (hlt _) (ht _)]

theorem positiveGridGlobalWordModel_of_ge {a N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (k : Fin a) {t : ℝ} (ht : ∀ j, right j ≤ t) :
    positiveGridGlobalWordModel left right σ w k t = (((σ (Fin.last N)).symm k).val : ℂ) := by
  unfold positiveGridGlobalWordModel
  simp_rw [positiveGridEventPath_of_ge left right σ w _ k (hlt _) (hp _) (ht _)]
  exact finitePath_sum_differences (fun i => (((σ i).symm k).val : ℂ))

/-- Full collars include both sides of the period endpoints. -/
theorem positiveGridGlobalWordModel_left_collar {a N : ℕ} (b : ℝ) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hb : ∀ j, b < left j) (k : Fin a) :
    ∀ᶠ t in 𝓝 b, positiveGridGlobalWordModel left right σ w k t =
      (((σ 0).symm k).val : ℂ) := by
  have ht : ∀ᶠ t in 𝓝 b, ∀ j, t < left j :=
    Filter.eventually_all.mpr fun j => eventually_lt_nhds (hb j)
  filter_upwards [ht] with t ht
  exact positiveGridGlobalWordModel_of_le left right σ w hlt k (fun j => (ht j).le)

theorem positiveGridGlobalWordModel_right_collar {a N : ℕ} (d : ℝ) (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hd : ∀ j, right j < d) (k : Fin a) :
    ∀ᶠ t in 𝓝 d, positiveGridGlobalWordModel left right σ w k t =
      (((σ (Fin.last N)).symm k).val : ℂ) := by
  have ht : ∀ᶠ t in 𝓝 d, ∀ j, right j < t :=
    Filter.eventually_all.mpr fun j => eventually_gt_nhds (hd j)
  filter_upwards [ht] with t ht
  exact positiveGridGlobalWordModel_of_ge left right σ w hlt hp k (fun j => (ht j).le)

/-- Separation from the original event/gap model is proved from its positive
crossings. There is no additional separation certificate. -/
theorem positiveGridGlobalWordModel_separation {a N : ℕ}
    (K : Fin a → ℝ → ℂ) (b d : ℝ) (event left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hgap : ∀ i, braidModelGapLeft b right i < braidModelGapRight d left i)
    (hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    {k l : Fin a} (hkl : k ≠ l) {t : ℝ} (ht : t ∈ Icc b d) :
    0 < (planeBranchBraidGlobalModel K b d event left right σ w k t -
        planeBranchBraidGlobalModel K b d event left right σ w l t).re *
      (positiveGridGlobalWordModel left right σ w k t -
        positiveGridGlobalWordModel left right σ w l t).re ∨
    0 < (planeBranchBraidGlobalModel K b d event left right σ w k t -
        planeBranchBraidGlobalModel K b d event left right σ w l t).im *
      (positiveGridGlobalWordModel left right σ w k t -
        positiveGridGlobalWordModel left right σ w l t).im := by
  have hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ := fun j => (hevent j).1
  rcases braidModel_intervals_cover b d left right ht with ⟨j, hj⟩ | ⟨i, hi⟩
  · rw [planeBranchBraidGlobalModel_on_event K b d event left right σ w hlt hsep hgap hevent j k hj,
      planeBranchBraidGlobalModel_on_event K b d event left right σ w hlt hsep hgap hevent j l hj,
      positiveGridGlobalWordModel_on_event left right σ w hlt hsep hp j k hj,
      positiveGridGlobalWordModel_on_event left right σ w hlt hsep hp j l hj]
    exact positiveGridWord_separation (w j) (fun v => (K (σ j.castSucc v) (event j)).im)
      (fun q hq => (hevent j).letter_height_order q hq)
      (fun he => hkl ((σ j.castSucc).symm.injective he)) _
  · rw [planeBranchBraidGlobalModel_on_gap K b d event left right σ w hlt hsep hgap hevent i k hi,
      planeBranchBraidGlobalModel_on_gap K b d event left right σ w hlt hsep hgap hevent i l hi,
      positiveGridGlobalWordModel_on_gap b d left right σ w hlt hsep hp i k hi,
      positiveGridGlobalWordModel_on_gap b d left right σ w hlt hsep hp i l hi]
    left
    have hn : (((σ i).symm k).val : ℝ) ≠ ((σ i).symm l).val := by
      intro he
      exact hkl ((σ i).symm.injective (Fin.ext (Nat.cast_injective he)))
    simpa only [braidGlobalGapPath, Complex.sub_re, planeBranchBraidGapModel_re,
      Complex.natCast_re] using mul_self_pos.mpr (sub_ne_zero.mpr hn)

/-- The complete canonical model has distinct strands at every time of the
base period, using only the transition permutations. -/
theorem positiveGridGlobalWordModel_injective {a N : ℕ} (b d : ℝ)
    (left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    {t : ℝ} (ht : t ∈ Icc b d) :
    Function.Injective (fun k => positiveGridGlobalWordModel left right σ w k t) := by
  rcases braidModel_intervals_cover b d left right ht with ⟨j, hj⟩ | ⟨i, hi⟩
  · simp_rw [positiveGridGlobalWordModel_on_event left right σ w hlt hsep hp j _ hj]
    exact (positiveGridWord_injective (w j) _).comp (σ j.castSucc).symm.injective
  · simp_rw [positiveGridGlobalWordModel_on_gap b d left right σ w hlt hsep hp i _ hi]
    exact fun k l he => (σ i).symm.injective (Fin.ext (Nat.cast_injective he))

/-- The endpoint rotation already proved for the actual sheets gives the
cyclic seam for the canonical model, without an additional matching premise. -/
theorem positiveGridGlobalWordModel_cyclic {a N : ℕ} (b d : ℝ)
    (left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hb : ∀ j, b < left j) (hd : ∀ j, right j < d)
    (hσ : (σ (Fin.last N)).trans (finRotate a) = σ 0) (k : Fin a) :
    positiveGridGlobalWordModel left right σ w k d =
      positiveGridGlobalWordModel left right σ w (finRotate a k) b := by
  rw [positiveGridGlobalWordModel_of_ge left right σ w hlt hp k (fun j => (hd j).le),
    positiveGridGlobalWordModel_of_le left right σ w hlt (finRotate a k) (fun j => (hb j).le)]
  congr 2
  apply (σ 0).injective
  rw [Equiv.apply_symm_apply, ← hσ]
  simp

end OnLeConjecture.Analytic
