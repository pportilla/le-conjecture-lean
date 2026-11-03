/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidEventGaps
public import OnLeConjecture.Analytic.PlaneBranchBraidEventIntervals
public import OnLeConjecture.Analytic.PlaneBranchBraidEventSeparation
public import OnLeConjecture.Analytic.PlaneBranchBraidGapModel
public import OnLeConjecture.Analytic.PlaneBranchBraidPathConcatenation

/-! # A smooth height model for all projected braid events

The model is the sum of the increments of the event paths and the intervening
rank-preserving connectors. The event words and their original sheet labels
are retained throughout the construction.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Left endpoint of each of the `N+1` gaps. -/
def braidModelGapLeft {N : ℕ} (b : ℝ) (right : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.cases b right

/-- Right endpoint of each of the `N+1` gaps. -/
def braidModelGapRight {N : ℕ} (d : ℝ) (left : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.lastCases d left

@[simp] theorem braidModelGapLeft_zero {N : ℕ} (b : ℝ) (right : Fin N → ℝ) :
    braidModelGapLeft b right 0 = b := rfl

@[simp] theorem braidModelGapLeft_succ {N : ℕ} (b : ℝ) (right : Fin N → ℝ) (j : Fin N) :
    braidModelGapLeft b right j.succ = right j := rfl

@[simp] theorem braidModelGapRight_last {N : ℕ} (d : ℝ) (left : Fin N → ℝ) :
    braidModelGapRight d left (Fin.last N) = d := by simp [braidModelGapRight]

@[simp] theorem braidModelGapRight_castSucc {N : ℕ} (d : ℝ) (left : Fin N → ℝ) (j : Fin N) :
    braidModelGapRight d left j.castSucc = left j := by simp [braidModelGapRight]

/-- At a gap, the previous event interval has already ended. -/
theorem braidModel_right_le_gapLeft {N : ℕ} (b : ℝ) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j k, j < k → right j < left k)
    (j : Fin N) (i : Fin (N + 1)) (hji : j.val < i.val) :
    right j ≤ braidModelGapLeft b right i := by
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (show i ≠ 0 by intro h; subst i; simp at hji)
  have hjk : j ≤ k := by change j.val ≤ k.val; simpa only [Fin.val_succ] using Nat.le_of_lt_succ hji
  rcases lt_or_eq_of_le hjk with h | rfl
  · exact (hsep j k h).le.trans (hlt k).le
  · exact le_rfl

/-- The next event interval starts after the current gap. -/
theorem braidModel_gapRight_le_left {N : ℕ} (d : ℝ) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j k, j < k → right j < left k)
    (i : Fin (N + 1)) (j : Fin N) (hij : i.val ≤ j.val) :
    braidModelGapRight d left i ≤ left j := by
  let k : Fin N := ⟨i.val, lt_of_le_of_lt hij j.isLt⟩
  have hi : i = k.castSucc := Fin.ext rfl
  rw [hi, braidModelGapRight_castSucc]
  have hkj : k ≤ j := hij
  rcases lt_or_eq_of_le hkj with h | heq
  · exact (hlt k).le.trans (hsep k j h).le
  · exact le_of_eq (congrArg left heq)

/-- The gap intervals are themselves strictly ordered. -/
theorem braidModel_gapRight_lt_gapLeft {N : ℕ} (b d : ℝ) (left right : Fin N → ℝ)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j k, j < k → right j < left k)
    (i j : Fin (N + 1)) (hij : i < j) :
    braidModelGapRight d left i < braidModelGapLeft b right j := by
  let k : Fin N := ⟨i.val, by have := j.isLt; change i.val < j.val at hij; omega⟩
  have hi : i = k.castSucc := Fin.ext rfl
  rw [hi, braidModelGapRight_castSucc]
  exact (hlt k).trans_le (braidModel_right_le_gapLeft b left right hlt hsep k j hij)

/-- Every gap has positive length, including the two outer gaps. -/
theorem braidModel_gap_pos {N : ℕ} (b d : ℝ) (hbd : b < d)
    (left right : Fin N → ℝ) (hbl : ∀ j, b < left j) (hrd : ∀ j, right j < d)
    (hsep : ∀ j k, j < k → right j < left k) (i : Fin (N + 1)) :
    braidModelGapLeft b right i < braidModelGapRight d left i := by
  by_cases hilast : i = Fin.last N
  · rw [hilast, braidModelGapRight_last]
    by_cases hi0 : i = 0
    · have hz : (Fin.last N : Fin (N + 1)) = 0 := hilast.symm.trans hi0
      rw [hz, braidModelGapLeft_zero]
      exact hbd
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi0
      rw [← hilast, ← hj, braidModelGapLeft_succ]
      exact hrd j
  · let k : Fin N := ⟨i.val, by
      have hi := i.isLt
      have hn : i.val ≠ N := fun he => hilast (Fin.ext he)
      omega⟩
    have hik : i = k.castSucc := Fin.ext rfl
    rw [hik, braidModelGapRight_castSucc]
    by_cases hi0 : i = 0
    · rw [← hik, hi0, braidModelGapLeft_zero]
      exact hbl k
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi0
      rw [← hik, ← hj, braidModelGapLeft_succ]
      exact hsep j k (by have he := congrArg Fin.val hj; dsimp at he; change j.val < i.val; omega)

/-- Initial imaginary heights of the gap connectors. -/
def braidModelGapHeightLeft {a N : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (event : Fin N → ℝ) : Fin (N + 1) → Fin a → ℝ :=
  Fin.cases (fun k => (K k b).im) (fun j k => (K k (event j)).im)

/-- Final imaginary heights of the gap connectors. -/
def braidModelGapHeightRight {a N : ℕ} (K : Fin a → ℝ → ℂ) (d : ℝ)
    (event : Fin N → ℝ) : Fin (N + 1) → Fin a → ℝ :=
  Fin.lastCases (fun k => (K k d).im) (fun j k => (K k (event j)).im)

def braidModelGapStart {a N : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (event : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a) : ℂ :=
  (((σ i).symm k).val : ℂ) + (braidModelGapHeightLeft K b event i k : ℂ) * Complex.I

def braidModelGapEnd {a N : ℕ} (K : Fin a → ℝ → ℂ) (d : ℝ)
    (event : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a) : ℂ :=
  (((σ i).symm k).val : ℂ) + (braidModelGapHeightRight K d event i k : ℂ) * Complex.I

/-- The connector on its prescribed real-time interval. -/
def braidGlobalGapPath {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a) (t : ℝ) : ℂ :=
  planeBranchBraidGapModel (σ i) (braidModelGapHeightLeft K b event i)
    (braidModelGapHeightRight K d event i) k
    ((t - braidModelGapLeft b right i) /
      (braidModelGapRight d left i - braidModelGapLeft b right i))

/-- The event word, rescaled with constant collars before one third and after two thirds. -/
def braidGlobalEventPath {a N : ℕ} (K : Fin a → ℝ → ℂ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (j : Fin N) (k : Fin a) (t : ℝ) : ℂ :=
  planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) k
    ((w j).length * (3 * ((t - left j) / (right j - left j)) - 1))

/-- The interleaved finite increment sum, in the original sheet labels. -/
def planeBranchBraidGlobalModel {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (k : Fin a) (t : ℝ) : ℂ :=
  braidModelGapStart K b event σ 0 k +
    (∑ i : Fin (N + 1),
      (braidGlobalGapPath K b d event left right σ i k t - braidModelGapStart K b event σ i k)) +
    ∑ j : Fin N,
      (braidGlobalEventPath K event left right σ w j k t -
        braidModelGapEnd K d event σ j.castSucc k)

theorem braidGlobalGapPath_contDiff {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a) :
    ContDiff ℝ ∞ (braidGlobalGapPath K b d event left right σ i k) := by
  exact (planeBranchBraidGapModel_contDiff _ _ _ _).comp
    ((contDiff_id.sub contDiff_const).div_const _)

theorem braidGlobalEventPath_contDiff {a N : ℕ} (K : Fin a → ℝ → ℂ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (j : Fin N) (k : Fin a) :
    ContDiff ℝ ∞ (braidGlobalEventPath K event left right σ w j k) := by
  exact (planeBranchBraidEventModel_contDiff _ _ _ _ _).comp
    (contDiff_const.mul ((contDiff_const.mul
      ((contDiff_id.sub contDiff_const).div_const _)).sub contDiff_const))

theorem planeBranchBraidGlobalModel_contDiff {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (k : Fin a) :
    ContDiff ℝ ∞ (planeBranchBraidGlobalModel K b d event left right σ w k) := by
  apply ContDiff.add
  · apply contDiff_const.add
    apply ContDiff.sum
    exact fun i _ => (braidGlobalGapPath_contDiff K b d event left right σ i k).sub contDiff_const
  · apply ContDiff.sum
    exact fun j _ => (braidGlobalEventPath_contDiff K event left right σ w j k).sub contDiff_const

theorem braidGlobalGapPath_of_le {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a)
    (hgap : braidModelGapLeft b right i < braidModelGapRight d left i)
    {t : ℝ} (ht : t ≤ braidModelGapLeft b right i) :
    braidGlobalGapPath K b d event left right σ i k t = braidModelGapStart K b event σ i k := by
  apply planeBranchBraidGapModel_of_le_third
  have hdiv : (t - braidModelGapLeft b right i) /
      (braidModelGapRight d left i - braidModelGapLeft b right i) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hgap.le)
  linarith

theorem braidGlobalGapPath_of_ge {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a)
    (hgap : braidModelGapLeft b right i < braidModelGapRight d left i)
    {t : ℝ} (ht : braidModelGapRight d left i ≤ t) :
    braidGlobalGapPath K b d event left right σ i k t = braidModelGapEnd K d event σ i k := by
  apply planeBranchBraidGapModel_of_two_thirds_le
  have hdiv : 1 ≤ (t - braidModelGapLeft b right i) /
      (braidModelGapRight d left i - braidModelGapLeft b right i) :=
    (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by linarith)
  linarith

theorem braidGlobalEventPath_of_le {a N : ℕ} (K : Fin a → ℝ → ℂ) (d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (j : Fin N) (k : Fin a)
    (hlt : left j < right j) {t : ℝ} (ht : t ≤ left j) :
    braidGlobalEventPath K event left right σ w j k t =
      braidModelGapEnd K d event σ j.castSucc k := by
  have hdiv : (t - left j) / (right j - left j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlt.le)
  have hn : (0 : ℝ) ≤ (w j).length := Nat.cast_nonneg _
  have he := planeBranchBraidEventModel_of_nonpos K (event j) (σ j.castSucc) (w j) k
    (show (w j).length * (3 * ((t - left j) / (right j - left j)) - 1) ≤ (0 : ℝ) by
      exact mul_nonpos_of_nonneg_of_nonpos hn (by linarith))
  simpa only [braidGlobalEventPath, braidModelGapEnd, braidModelGapHeightRight,
    Fin.lastCases_castSucc] using he

theorem braidGlobalEventPath_of_ge {a N : ℕ} (K : Fin a → ℝ → ℂ) (b : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (j : Fin N) (k : Fin a)
    (hevent : IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (hlt : left j < right j) {t : ℝ} (ht : right j ≤ t) :
    braidGlobalEventPath K event left right σ w j k t =
      braidModelGapStart K b event σ j.succ k := by
  have hdiv : 1 ≤ (t - left j) / (right j - left j) :=
    (le_div_iff₀ (sub_pos.mpr hlt)).mpr (by linarith)
  have hn : (0 : ℝ) ≤ (w j).length := Nat.cast_nonneg _
  have he := hevent.model_of_length_le k
    (show (w j).length ≤ (w j).length *
      (3 * ((t - left j) / (right j - left j)) - 1) by nlinarith)
  simpa only [braidGlobalEventPath, braidModelGapStart, braidModelGapHeightLeft,
    Fin.cases_succ] using he

/-- Pair each gap increment with the following event increment. -/
theorem planeBranchBraidGlobalModel_eq_paired {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a) (k : Fin a) (t : ℝ) :
    planeBranchBraidGlobalModel K b d event left right σ w k t =
      braidModelGapStart K b event σ 0 k +
      (∑ j : Fin N,
        (braidGlobalGapPath K b d event left right σ j.castSucc k t +
          braidGlobalEventPath K event left right σ w j k t -
          braidModelGapEnd K d event σ j.castSucc k -
          braidModelGapStart K b event σ j.castSucc k)) +
      (braidGlobalGapPath K b d event left right σ (Fin.last N) k t -
        braidModelGapStart K b event σ (Fin.last N) k) := by
  unfold planeBranchBraidGlobalModel
  rw [Fin.sum_univ_castSucc]
  have hsum : (∑ j : Fin N,
      (braidGlobalGapPath K b d event left right σ j.castSucc k t +
        braidGlobalEventPath K event left right σ w j k t -
        braidModelGapEnd K d event σ j.castSucc k - braidModelGapStart K b event σ j.castSucc k)) =
      (∑ j : Fin N, (braidGlobalGapPath K b d event left right σ j.castSucc k t -
        braidModelGapStart K b event σ j.castSucc k)) +
      ∑ j : Fin N, (braidGlobalEventPath K event left right σ w j k t -
        braidModelGapEnd K d event σ j.castSucc k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    abel
  rw [hsum]
  abel

/-- On an event interval the complete sum is exactly the assigned event path. -/
theorem planeBranchBraidGlobalModel_on_event {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hgap : ∀ i, braidModelGapLeft b right i < braidModelGapRight d left i)
    (hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (j : Fin N) (k : Fin a) {t : ℝ} (ht : t ∈ Icc (left j) (right j)) :
    planeBranchBraidGlobalModel K b d event left right σ w k t =
      braidGlobalEventPath K event left right σ w j k t := by
  let A := fun i => braidModelGapStart K b event σ i k
  let V := fun q : Fin N => braidGlobalGapPath K b d event left right σ q.castSucc k t +
    braidGlobalEventPath K event left right σ w q k t -
    braidModelGapEnd K d event σ q.castSucc k
  have hGlast := braidGlobalGapPath_of_le K b d event left right σ (Fin.last N) k
    (hgap _) (ht.2.trans (braidModel_right_le_gapLeft b left right hlt hsep j _ j.isLt))
  have hB (q : Fin N) (hq : q < j) : V q = A q.succ := by
    have hG := braidGlobalGapPath_of_ge K b d event left right σ q.castSucc k (hgap _)
      ((braidModel_gapRight_le_left d left right hlt hsep q.castSucc j hq.le).trans ht.1)
    have hE := braidGlobalEventPath_of_ge K b event left right σ w q k (hevent q) (hlt q)
      ((hsep q j hq).le.trans ht.1)
    dsimp [V, A]
    rw [hG, hE]
    abel
  have hA (q : Fin N) (hq : j < q) : V q = A q.castSucc := by
    have hG := braidGlobalGapPath_of_le K b d event left right σ q.castSucc k (hgap _)
      (ht.2.trans (braidModel_right_le_gapLeft b left right hlt hsep j q.castSucc hq))
    have hE := braidGlobalEventPath_of_le K d event left right σ w q k (hlt q)
      (ht.2.trans (hsep j q hq).le)
    dsimp [V, A]
    rw [hG, hE]
    abel
  rw [planeBranchBraidGlobalModel_eq_paired, hGlast, sub_self, add_zero]
  change A 0 + ∑ q : Fin N, (V q - A q.castSucc) = _
  rw [finitePath_sum_eq_active A V j hB hA]
  have hGj := braidGlobalGapPath_of_ge K b d event left right σ j.castSucc k (hgap _)
    (by simpa only [braidModelGapRight_castSucc] using ht.1)
  dsimp [V]
  rw [hGj]
  abel

/-- On a gap interval the complete sum is exactly its rank-preserving connector. -/
theorem planeBranchBraidGlobalModel_on_gap {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hgap : ∀ i, braidModelGapLeft b right i < braidModelGapRight d left i)
    (hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (i : Fin (N + 1)) (k : Fin a) {t : ℝ}
    (ht : t ∈ Icc (braidModelGapLeft b right i) (braidModelGapRight d left i)) :
    planeBranchBraidGlobalModel K b d event left right σ w k t =
      braidGlobalGapPath K b d event left right σ i k t := by
  let A := fun q => braidModelGapStart K b event σ q k
  let V := fun q : Fin N => braidGlobalGapPath K b d event left right σ q.castSucc k t +
    braidGlobalEventPath K event left right σ w q k t -
    braidModelGapEnd K d event σ q.castSucc k
  have hB (q : Fin N) (hq : q.val < i.val) : V q = A q.succ := by
    have hG := braidGlobalGapPath_of_ge K b d event left right σ q.castSucc k (hgap _)
      ((braidModel_gapRight_lt_gapLeft b d left right hlt hsep q.castSucc i hq).le.trans ht.1)
    have hE := braidGlobalEventPath_of_ge K b event left right σ w q k (hevent q) (hlt q)
      ((braidModel_right_le_gapLeft b left right hlt hsep q i hq).trans ht.1)
    dsimp [V, A]
    rw [hG, hE]
    abel
  by_cases hilast : i = Fin.last N
  · subst i
    rw [planeBranchBraidGlobalModel_eq_paired]
    change (A 0 + ∑ q : Fin N, (V q - A q.castSucc)) + _ = _
    rw [finitePath_sum_eq_cut A V (Fin.last N) hB
      (fun q hq => (Nat.not_le_of_gt q.isLt hq).elim)]
    dsimp [A]
    abel
  · let j : Fin N := ⟨i.val, by
      have hi := i.isLt
      have hn : i.val ≠ N := fun he => hilast (Fin.ext he)
      omega⟩
    have hij : i = j.castSucc := Fin.ext rfl
    have hA (q : Fin N) (hq : j < q) : V q = A q.castSucc := by
      have hG := braidGlobalGapPath_of_le K b d event left right σ q.castSucc k (hgap _)
        (ht.2.trans (braidModel_gapRight_lt_gapLeft b d left right hlt hsep i q.castSucc hq).le)
      have hE := braidGlobalEventPath_of_le K d event left right σ w q k (hlt q)
        (ht.2.trans (braidModel_gapRight_le_left d left right hlt hsep i q hq.le))
      dsimp [V, A]
      rw [hG, hE]
      abel
    have hlast : i < Fin.last N := by change i.val < N; exact j.isLt
    have hGlast := braidGlobalGapPath_of_le K b d event left right σ (Fin.last N) k
      (hgap _) (ht.2.trans (braidModel_gapRight_lt_gapLeft b d left right hlt hsep i _ hlast).le)
    rw [planeBranchBraidGlobalModel_eq_paired, hGlast, sub_self, add_zero]
    change A 0 + ∑ q : Fin N, (V q - A q.castSucc) = _
    rw [finitePath_sum_eq_active A V j (fun q hq => hB q hq) hA]
    have hEj := braidGlobalEventPath_of_le K d event left right σ w j k (hlt j)
      (by simpa only [hij, braidModelGapRight_castSucc] using ht.2)
    dsimp [V]
    rw [hEj, ← hij]
    abel

theorem braidModelGapLeft_ge {N : ℕ} (b : ℝ) (right : Fin N → ℝ)
    (hb : ∀ j, b ≤ right j) (i : Fin (N + 1)) : b ≤ braidModelGapLeft b right i := by
  induction i using Fin.cases with
  | zero => exact le_rfl
  | succ j => exact hb j

theorem braidModelGapRight_le {N : ℕ} (d : ℝ) (left : Fin N → ℝ)
    (hd : ∀ j, left j ≤ d) (i : Fin (N + 1)) : braidModelGapRight d left i ≤ d := by
  induction i using Fin.lastCases with
  | last => simp only [braidModelGapRight_last, le_refl]
  | cast j => simpa only [braidModelGapRight_castSucc] using hd j

/-- The event intervals and their intervening gaps cover the entire base interval. -/
theorem braidModel_intervals_cover {N : ℕ} (b d : ℝ) (left right : Fin N → ℝ)
    {t : ℝ} (ht : t ∈ Icc b d) :
    (∃ j, t ∈ Icc (left j) (right j)) ∨
      ∃ i, t ∈ Icc (braidModelGapLeft b right i) (braidModelGapRight d left i) := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter fun j => t ≤ right j
  by_cases hS : S.Nonempty
  · let j := S.min' hS
    have htR : t ≤ right j := (Finset.mem_filter.mp (S.min'_mem hS)).2
    by_cases htL : left j ≤ t
    · exact Or.inl ⟨j, htL, htR⟩
    · right
      refine ⟨j.castSucc, ?_, ?_⟩
      · by_cases hj0 : j.castSucc = 0
        · simpa only [hj0, braidModelGapLeft_zero] using ht.1
        · obtain ⟨p, hp⟩ := Fin.exists_succ_eq.mpr hj0
          rw [← hp, braidModelGapLeft_succ]
          by_contra hn
          have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hn).le⟩
          have hjp := S.min'_le p hpS
          have hval := congrArg Fin.val hp
          simp only [Fin.val_succ, Fin.val_castSucc] at hval
          change j.val ≤ p.val at hjp
          omega
      · simpa only [braidModelGapRight_castSucc] using (lt_of_not_ge htL).le
  · right
    refine ⟨Fin.last N, ?_, ?_⟩
    · by_cases hN : N = 0
      · subst N
        simpa only [Fin.last_zero, braidModelGapLeft_zero] using ht.1
      · obtain ⟨p, hp⟩ := Fin.exists_succ_eq.mpr (show (Fin.last N : Fin (N + 1)) ≠ 0 by
          intro he
          have hv := congrArg Fin.val he
          exact hN (by simpa only [Fin.val_last, Fin.val_zero] using hv))
        rw [← hp, braidModelGapLeft_succ]
        by_contra hn
        exact hS ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hn).le⟩⟩
    · simpa only [braidModelGapRight_last] using ht.2

/-- The closed gap intervals have no projected event, including both outer gaps. -/
theorem braidModel_gap_event_free {N : ℕ} (event left right : Fin N → ℝ)
    (b d : ℝ) (E : Finset ℝ) (henum : List.ofFn event = E.sort (· ≤ ·))
    (hmono : StrictMono event) (hle : ∀ j, left j < event j)
    (her : ∀ j, event j < right j) (i : Fin (N + 1)) :
    ∀ t ∈ Icc (braidModelGapLeft b right i) (braidModelGapRight d left i), t ∉ E := by
  apply braid_event_gap_of_adjacent_cut event E henum hmono i
  · intro j hj
    have hi : i = j.succ := Fin.ext hj.symm
    simpa only [hi, braidModelGapLeft_succ] using her j
  · intro j hj
    have hi : i = j.castSucc := Fin.ext hj.symm
    simpa only [hi, braidModelGapRight_castSucc] using hle j

/-- Separation of the complete model follows from the concrete event and gap paths. -/
theorem planeBranchBraidGlobalModel_separation {a N : ℕ}
    {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (b d : ℝ) (hbd : b < d) (E : Finset ℝ)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (event left right : Fin N → ℝ) (henum : List.ofFn event = E.sort (· ≤ ·))
    (hmono : StrictMono event) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hblocks : ∀ j, b < left j ∧ left j < event j ∧ event j < right j ∧ right j < d ∧
      StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
      IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (hsortd : StrictMono (fun k => (K (σ (Fin.last N) k) d).re))
    (hsep : ∀ j q, j < q → right j < left q)
    (hmodel : ∀ j, ∀ t ∈ Icc (left j) (right j), ∀ τ : ℝ, ∀ k l : Fin a, k ≠ l →
      0 < (K k t - K l t).re *
        (planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) k τ -
          planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) l τ).re ∨
      0 < (K k t - K l t).im *
        (planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) k τ -
          planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) l τ).im) :
    ∀ t ∈ Icc b d, ∀ k l : Fin a, k ≠ l →
      0 < (K k t - K l t).re *
        (planeBranchBraidGlobalModel K b d event left right σ w k t -
          planeBranchBraidGlobalModel K b d event left right σ w l t).re ∨
      0 < (K k t - K l t).im *
        (planeBranchBraidGlobalModel K b d event left right σ w k t -
          planeBranchBraidGlobalModel K b d event left right σ w l t).im := by
  have hlt (j : Fin N) : left j < right j := (hblocks j).2.1.trans (hblocks j).2.2.1
  have hgap := braidModel_gap_pos b d hbd left right (fun j => (hblocks j).1)
    (fun j => (hblocks j).2.2.2.1) hsep
  have hw (j : Fin N) := (hblocks j).2.2.2.2.2
  intro t ht k l hkl
  rcases braidModel_intervals_cover b d left right ht with ⟨j, hj⟩ | ⟨i, hi⟩
  · rw [planeBranchBraidGlobalModel_on_event K b d event left right σ w hlt hsep hgap hw j k hj,
      planeBranchBraidGlobalModel_on_event K b d event left right σ w hlt hsep hgap hw j l hj]
    exact hmodel j t hj _ k l hkl
  · rw [planeBranchBraidGlobalModel_on_gap K b d event left right σ w hlt hsep hgap hw i k hi,
      planeBranchBraidGlobalModel_on_gap K b d event left right σ w hlt hsep hgap hw i l hi]
    left
    have hfree := braidModel_gap_event_free event left right b d E henum hmono
      (fun j => (hblocks j).2.1) (fun j => (hblocks j).2.2.1) i
    have hbounds : Icc (braidModelGapLeft b right i) (braidModelGapRight d left i) ⊆ Icc b d := by
      intro s hs
      exact ⟨(braidModelGapLeft_ge b right (fun j =>
        ((hblocks j).1.trans (hlt j)).le) i).trans hs.1,
        hs.2.trans (braidModelGapRight_le d left (fun j =>
          ((hlt j).trans (hblocks j).2.2.2.1).le) i)⟩
    have hsort : StrictMono (fun q => (K (σ i q) (braidModelGapRight d left i)).re) := by
      induction i using Fin.lastCases with
      | last => simpa only [braidModelGapRight_last] using hsortd
      | cast j => simpa only [braidModelGapRight_castSucc] using (hblocks j).2.2.2.2.1
    apply planeBranchBraidGapModel_real_product_pos_of_event_free hcont
      (q := braidModelGapRight d left i) ⟨(hgap i).le, le_rfl⟩ ?_ (σ i) hsort _ _ hi _ hkl
    intro s hs he
    exact hfree s hs ((hE s).mpr ⟨hbounds hs, he⟩)

theorem braidGlobalGapPath_eventually_of_le {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a)
    (hgap : braidModelGapLeft b right i < braidModelGapRight d left i)
    {t : ℝ} (ht : t ≤ braidModelGapLeft b right i) :
    braidGlobalGapPath K b d event left right σ i k =ᶠ[𝓝 t]
      fun _ => braidModelGapStart K b event σ i k := by
  let f : ℝ → ℝ := fun s => (s - braidModelGapLeft b right i) /
    (braidModelGapRight d left i - braidModelGapLeft b right i)
  have hc : ContinuousAt f t := by dsimp [f]; fun_prop
  have ht0 : f t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hgap.le)
  have he := hc.eventually_lt continuousAt_const (show f t < 1 / 3 by linarith)
  filter_upwards [he] with s hs
  exact planeBranchBraidGapModel_of_le_third _ _ _ _ hs.le

theorem braidGlobalGapPath_eventually_of_ge {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (i : Fin (N + 1)) (k : Fin a)
    (hgap : braidModelGapLeft b right i < braidModelGapRight d left i)
    {t : ℝ} (ht : braidModelGapRight d left i ≤ t) :
    braidGlobalGapPath K b d event left right σ i k =ᶠ[𝓝 t]
      fun _ => braidModelGapEnd K d event σ i k := by
  let f : ℝ → ℝ := fun s => (s - braidModelGapLeft b right i) /
    (braidModelGapRight d left i - braidModelGapLeft b right i)
  have hc : ContinuousAt f t := by dsimp [f]; fun_prop
  have ht1 : 1 ≤ f t := (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by linarith)
  have he := continuousAt_const.eventually_lt hc (show 2 / 3 < f t by linarith)
  filter_upwards [he] with s hs
  exact planeBranchBraidGapModel_of_two_thirds_le _ _ _ _ hs.le

/-- The global model has a full constant collar at the initial base angle. -/
theorem planeBranchBraidGlobalModel_left_collar {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hbl : ∀ j, b < left j) (hlt : ∀ j, left j < right j)
    (hgap : ∀ i, braidModelGapLeft b right i < braidModelGapRight d left i) (k : Fin a) :
    planeBranchBraidGlobalModel K b d event left right σ w k =ᶠ[𝓝 b]
      fun _ => (((σ 0).symm k).val : ℂ) + ((K k b).im : ℂ) * Complex.I := by
  have hG (i : Fin (N + 1)) := braidGlobalGapPath_eventually_of_le K b d event left right σ i k
    (hgap i) (braidModelGapLeft_ge b right (fun j => ((hbl j).trans (hlt j)).le) i)
  have hEv (j : Fin N) : ∀ᶠ t in 𝓝 b,
      braidGlobalEventPath K event left right σ w j k t =
        braidModelGapEnd K d event σ j.castSucc k := by
    filter_upwards [Iio_mem_nhds (hbl j)] with t ht
    exact braidGlobalEventPath_of_le K d event left right σ w j k (hlt j) ht.le
  filter_upwards [Filter.eventually_all.mpr hG, Filter.eventually_all.mpr hEv] with t htG htE
  simp only [planeBranchBraidGlobalModel, htG, htE, sub_self, Finset.sum_const_zero, add_zero]
  rfl

/-- The global model has a full constant collar at the final base angle. -/
theorem planeBranchBraidGlobalModel_right_collar {a N : ℕ} (K : Fin a → ℝ → ℂ) (b d : ℝ)
    (event left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin a))
    (w : Fin N → PositiveAdjacentWord a)
    (hrd : ∀ j, right j < d) (hlt : ∀ j, left j < right j)
    (hgap : ∀ i, braidModelGapLeft b right i < braidModelGapRight d left i)
    (hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j))
    (k : Fin a) :
    planeBranchBraidGlobalModel K b d event left right σ w k =ᶠ[𝓝 d]
      fun _ => (((σ (Fin.last N)).symm k).val : ℂ) + ((K k d).im : ℂ) * Complex.I := by
  have hG (i : Fin (N + 1)) := braidGlobalGapPath_eventually_of_ge K b d event left right σ i k
    (hgap i) (braidModelGapRight_le d left (fun j => ((hlt j).trans (hrd j)).le) i)
  have hEv (j : Fin N) : ∀ᶠ t in 𝓝 d,
      braidGlobalEventPath K event left right σ w j k t =
        braidModelGapStart K b event σ j.succ k := by
    filter_upwards [Ioi_mem_nhds (hrd j)] with t ht
    exact braidGlobalEventPath_of_ge K b event left right σ w j k (hevent j) (hlt j) ht.le
  filter_upwards [Filter.eventually_all.mpr hG, Filter.eventually_all.mpr hEv] with t htG htE
  rw [planeBranchBraidGlobalModel_eq_paired]
  simp only [htG, htE]
  have hsum : (∑ j : Fin N,
      (braidModelGapEnd K d event σ j.castSucc k + braidModelGapStart K b event σ j.succ k -
        braidModelGapEnd K d event σ j.castSucc k - braidModelGapStart K b event σ j.castSucc k)) =
      ∑ j : Fin N, (braidModelGapStart K b event σ j.succ k -
        braidModelGapStart K b event σ j.castSucc k) := by
    apply Finset.sum_congr rfl
    intro j _
    abel
  rw [hsum, finitePath_sum_differences (fun i => braidModelGapStart K b event σ i k)]
  have he : braidModelGapEnd K d event σ (Fin.last N) k =
      (((σ (Fin.last N)).symm k).val : ℂ) + ((K k d).im : ℂ) * Complex.I := by
    simp only [braidModelGapEnd, braidModelGapHeightRight, Fin.lastCases_last]
  rw [← he]
  abel

/-- Construct the complete smooth model from the original finite positive
crossing data. The separation condition is derived, not assumed. -/
theorem exists_planeBranchBraidGlobalModel
    {a : ℕ} {K : Fin a → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    (E : Finset ℝ) (b d : ℝ) (hbd : b < d)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧
      ∃ k l : Fin a, k ≠ l ∧ (K k t).re = (K l t).re)
    (hb : b ∉ E) (hd : d ∉ E)
    (hpos : ∀ θ ∈ E, ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∃ (N : ℕ) (event left right : Fin N → ℝ)
      (σ : Fin (N + 1) → Equiv.Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a),
      N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
      StrictMono (fun j => (K (σ 0 j) b).re) ∧
      StrictMono (fun j => (K (σ (Fin.last N) j) d).re) ∧
      (∀ j : Fin N,
        b < left j ∧ left j < event j ∧ event j < right j ∧ right j < d ∧
        StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
        StrictMono (fun k => (K (σ j.succ k) (right j)).re) ∧
        (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
        IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
      (∀ j q, j < q → right j < left q) ∧
      σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
        σ (Fin.last N) ∧
      (List.ofFn w).flatten.length = ∑ j : Fin N,
        (Finset.univ.filter fun p : Fin a × Fin a =>
          p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re =
            (K (σ j.succ p.2) (event j)).re).card ∧
      let M := planeBranchBraidGlobalModel K b d event left right σ w
      (∀ k, ContDiff ℝ ∞ (M k)) ∧
      (∀ k, M k =ᶠ[𝓝 b] fun _ => (((σ 0).symm k).val : ℂ) +
        ((K k b).im : ℂ) * Complex.I) ∧
      (∀ k, M k =ᶠ[𝓝 d] fun _ => (((σ (Fin.last N)).symm k).val : ℂ) +
        ((K k d).im : ℂ) * Complex.I) ∧
      (∀ k, M k b = (((σ 0).symm k).val : ℂ) + ((K k b).im : ℂ) * Complex.I) ∧
      (∀ k, M k d = (((σ (Fin.last N)).symm k).val : ℂ) +
        ((K k d).im : ℂ) * Complex.I) ∧
      (∀ t ∈ Icc b d, Function.Injective (fun k => M k t)) ∧
      (∀ t ∈ Icc b d, ∀ k l : Fin a, k ≠ l →
        0 < (K k t - K l t).re * (M k t - M l t).re ∨
        0 < (K k t - K l t).im * (M k t - M l t).im) := by
  classical
  obtain ⟨N, event, oldLeft, oldRight, σ, w, hN, henum, hmono, hσb, hσd,
      hold, hperm, hlength⟩ :=
    exists_finite_positive_braid_event_words hcont E b d hbd hE hb hd hpos
  have hcaps (j : Fin N) : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t ∈ ball (event j) ρ, ∀ τ : ℝ, ∀ k l : Fin a, k ≠ l →
        0 < (K k t - K l t).re *
          (planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) k τ -
            planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) l τ).re ∨
        0 < (K k t - K l t).im *
          (planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) k τ -
            planeBranchBraidEventModel K (event j) (σ j.castSucc) (w j) l τ).im := by
    obtain ⟨hbl, hle, her, hrd, hsort, _hsortR, hiso, hw⟩ := hold j
    exact exists_radius_braid_event_block_model_separation hcont E hE
      hbl hle her hrd hsort hiso hw
  choose cap hcap hsepModel using hcaps
  obtain ⟨left, right, _hsub, hnew, hsep, hball⟩ := refine_positive_braid_event_intervals_capped
    hcont E b d hE event oldLeft oldRight hmono cap hcap σ w hold
  have hshort (j : Fin N) : b < left j ∧ left j < event j ∧ event j < right j ∧
      right j < d ∧ StrictMono (fun k => (K (σ j.castSucc k) (left j)).re) ∧
      IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j) :=
    ⟨(hnew j).1, (hnew j).2.1, (hnew j).2.2.1, (hnew j).2.2.2.1,
      (hnew j).2.2.2.2.1, (hnew j).2.2.2.2.2.2.2⟩
  have hlt (j : Fin N) : left j < right j := (hnew j).2.1.trans (hnew j).2.2.1
  have hgap := braidModel_gap_pos b d hbd left right (fun j => (hnew j).1)
    (fun j => (hnew j).2.2.2.1) hsep
  have hw (j : Fin N) := (hnew j).2.2.2.2.2.2.2
  have hleft := planeBranchBraidGlobalModel_left_collar K b d event left right σ w
    (fun j => (hnew j).1) hlt hgap
  have hright := planeBranchBraidGlobalModel_right_collar K b d event left right σ w
    (fun j => (hnew j).2.2.2.1) hlt hgap hw
  have hseparation := planeBranchBraidGlobalModel_separation hcont b d hbd E hE
    event left right henum hmono σ w hshort hσd hsep
    (fun j t ht τ k l hkl => hsepModel j t (hball j ht) τ k l hkl)
  refine ⟨N, event, left, right, σ, w, hN, henum, hmono, hσb, hσd, hnew, hsep,
    hperm, hlength, planeBranchBraidGlobalModel_contDiff K b d event left right σ w,
    hleft, hright, fun k => (hleft k).eq_of_nhds, fun k => (hright k).eq_of_nhds, ?_, hseparation⟩
  intro t ht k l heq
  by_contra hkl
  rcases hseparation t ht k l hkl with hp | hp <;>
    simp only [heq, sub_self, Complex.zero_re, Complex.zero_im, mul_zero, lt_self_iff_false] at hp

/-- The endpoint rank configurations obey the same cyclic label identification
as the original strands and the endpoint sorting permutations. -/
theorem braid_rank_endpoint_configs_cyclic {a : ℕ} (K : Fin a → ℝ → ℂ)
    (b d : ℝ) (before after ρ : Equiv.Perm (Fin a))
    (hK : ∀ k, K k d = K (ρ k) b) (hσ : after.trans ρ = before) (k : Fin a) :
    ((after.symm k).val : ℂ) + ((K k d).im : ℂ) * Complex.I =
      ((before.symm (ρ k)).val : ℂ) + ((K (ρ k) b).im : ℂ) * Complex.I := by
  have hr : after.symm k = before.symm (ρ k) := by
    apply before.injective
    rw [← hσ]
    simp
  rw [hr, hK]

end OnLeConjecture.Analytic
