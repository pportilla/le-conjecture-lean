/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidWordModel

/-!
# A closed braid with finitely many positive events is represented by its event word

Let `K : Fin S → ℝ → ℂ` be continuous strands, pairwise distinct on `[b, d]`, closing up
by a permutation `τ` (`K k d = K (τ k) b`), whose real projections coincide at finitely
many interior times, each coincidence being a positive transverse crossing. The existing
event extraction `exists_planeBranchBraidGlobalModel` assigns a positive word to each
event and builds the smooth event/gap model. This module proves that the closed braid `K`
is represented, in the sense of `IsRepresentedByPositiveWord`, by the concatenation of
the event words, and that the endpoint sorting permutations satisfy the closing relation
`(σ last).trans τ = σ 0`.

The isotopy is the composite of three straight-line interpolations and one monotone
reparametrization: from `K` to the event/gap model (separation proved by the existing
global model theorem), from that model to the canonical global word model
`positiveGridGlobalWordModel` (separation proved by `positiveGridGlobalWordModel_separation`),
and finally an identification of the canonical global word model, relabelled by the
initial sorting permutation, with the canonical closed braid of the concatenated word
along a monotone change of parameter. The last identification uses the concatenation
formula `positiveGridWord_append`.

The statement generalizes the single-branch case, where `τ` is the cyclic rotation
`finRotate a`, to an arbitrary monodromy permutation.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### The concatenated canonical path of a sequence of words -/

/-- The number of letters before the block `j`. -/
def positiveWordBlockOffset {S N : ℕ} (w : Fin N → PositiveAdjacentWord S) (j : ℕ) : ℕ :=
  ((List.ofFn w).take j).flatten.length

theorem positiveWordBlockOffset_zero {S N : ℕ} (w : Fin N → PositiveAdjacentWord S) :
    positiveWordBlockOffset w 0 = 0 := by
  simp [positiveWordBlockOffset]

theorem positiveWordBlockOffset_succ {S N : ℕ} (w : Fin (N + 1) → PositiveAdjacentWord S)
    (j : ℕ) :
    positiveWordBlockOffset w (j + 1) =
      (w 0).length + positiveWordBlockOffset (fun i : Fin N => w i.succ) j := by
  simp [positiveWordBlockOffset, List.ofFn_succ, List.take_succ_cons]

theorem positiveWordBlockOffset_eq_sum {S N : ℕ} (w : Fin N → PositiveAdjacentWord S)
    (j : Fin N) :
    (positiveWordBlockOffset w j : ℝ) =
      ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i < j), ((w i).length : ℝ) := by
  induction N with
  | zero => exact j.elim0
  | succ N ih =>
    rw [Finset.sum_filter, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [positiveWordBlockOffset_zero]
    · rw [Fin.val_succ, positiveWordBlockOffset_succ, Nat.cast_add,
        ih (fun i => w i.succ) j, Finset.sum_filter]
      simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]

/-- The canonical path of a concatenation of words, labelled after a chain of
permutations, is the sum of the increments of the individual words. -/
theorem positiveGridWord_flatten {S N : ℕ} (w : Fin N → PositiveAdjacentWord S)
    (σ : Fin (N + 1) → Equiv.Perm (Fin S))
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ) (k : Fin S) (t : ℝ) :
    positiveGridWord (List.ofFn w).flatten ((σ 0).symm k) t =
      (((σ 0).symm k).val : ℂ) + ∑ j : Fin N,
        (positiveGridWord (w j) ((σ j.castSucc).symm k) (t - positiveWordBlockOffset w j) -
          (((σ j.castSucc).symm k).val : ℂ)) := by
  induction N generalizing t with
  | zero =>
    simp only [List.ofFn_zero, List.flatten_nil, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero]
    rcases le_or_gt t 0 with h | h
    · exact positiveGridWord_of_nonpos _ _ h
    · rw [positiveGridWord_of_length_le _ _ (by simpa using h.le)]
      simp only [PositiveAdjacentWord.permutation_nil]
      rfl
  | succ N ih =>
    have hp0 : σ 0 * (w 0).permutation = σ 1 := by simpa using hp 0
    have hlabel : (w 0).permutation.symm ((σ 0).symm k) = (σ 1).symm k := by
      rw [← perm_mul_symm_apply, hp0]
    have ih' := ih (fun j => w j.succ) (fun j => σ j.succ)
      (fun j => by simpa only [Fin.succ_castSucc] using hp j.succ) (t - (w 0).length)
    simp only [Fin.succ_zero_eq_one] at ih'
    rw [List.ofFn_succ, List.flatten_cons, positiveGridWord_append, hlabel, ih',
      Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, ← Fin.succ_castSucc, Fin.val_succ,
      positiveWordBlockOffset_succ, Nat.cast_add, Fin.val_zero]
    simp only [positiveWordBlockOffset_zero, Nat.cast_zero, sub_zero]
    have hsum : ∀ j : Fin N,
        positiveGridWord (w j.succ) ((σ j.castSucc.succ).symm k)
            (t - (w 0).length - positiveWordBlockOffset (fun i : Fin N => w i.succ) j) =
          positiveGridWord (w j.succ) ((σ j.castSucc.succ).symm k)
            (t - ((w 0).length + positiveWordBlockOffset (fun i : Fin N => w i.succ) j)) := by
      intro j
      congr 1
      ring
    simp only [hsum]
    ring

/-! ### Identification of the canonical global word model -/

/-- The clamp of a real number to `[0, 1]`. -/
def unitClamp (y : ℝ) : ℝ := max 0 (min y 1)

theorem unitClamp_continuous : Continuous unitClamp := by
  unfold unitClamp
  fun_prop

theorem unitClamp_mem (y : ℝ) : unitClamp y ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem unitClamp_of_nonpos {y : ℝ} (hy : y ≤ 0) : unitClamp y = 0 := by
  unfold unitClamp
  exact max_eq_left (min_le_of_left_le hy)

theorem unitClamp_of_one_le {y : ℝ} (hy : 1 ≤ y) : unitClamp y = 1 := by
  unfold unitClamp
  rw [min_eq_right hy]
  exact max_eq_right zero_le_one

/-- The time spent by the canonical word path within the event block `j`. -/
def positiveWordBlockTime {N : ℕ} (left right : Fin N → ℝ) (j : Fin N) (t : ℝ) : ℝ :=
  unitClamp (3 * ((t - left j) / (right j - left j)) - 1)

/-- The monotone change of parameter carrying the canonical global word model onto the
canonical closed braid of the concatenated word. The last summand runs through the final
unit interval of the canonical closed braid after the last event block. -/
def positiveWordGlobalTime {S N : ℕ} (left right : Fin N → ℝ)
    (w : Fin N → PositiveAdjacentWord S) (t₀ d t : ℝ) : ℝ :=
  (∑ j : Fin N, ((w j).length : ℝ) * positiveWordBlockTime left right j t) +
    unitClamp ((t - t₀) / (d - t₀))

theorem positiveWordBlockTime_of_le {N : ℕ} {left right : Fin N → ℝ} {j : Fin N}
    (hlt : left j < right j) {t : ℝ} (ht : t ≤ left j) :
    positiveWordBlockTime left right j t = 0 := by
  apply unitClamp_of_nonpos
  have : (t - left j) / (right j - left j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

theorem positiveWordBlockTime_of_ge {N : ℕ} {left right : Fin N → ℝ} {j : Fin N}
    (hlt : left j < right j) {t : ℝ} (ht : right j ≤ t) :
    positiveWordBlockTime left right j t = 1 := by
  apply unitClamp_of_one_le
  have : 1 ≤ (t - left j) / (right j - left j) :=
    (le_div_iff₀ (sub_pos.mpr hlt)).mpr (by linarith)
  linarith

theorem positiveWordGlobalTime_continuous {S N : ℕ} (left right : Fin N → ℝ)
    (w : Fin N → PositiveAdjacentWord S) (t₀ d : ℝ) :
    Continuous (positiveWordGlobalTime left right w t₀ d) := by
  unfold positiveWordGlobalTime positiveWordBlockTime
  have hc := unitClamp_continuous
  fun_prop

/-- The sum of the block times splits at a block. -/
theorem sum_blockTime_split {S N : ℕ} (left right : Fin N → ℝ)
    (w : Fin N → PositiveAdjacentWord S) (j : Fin N) (t : ℝ) :
    (∑ i : Fin N, ((w i).length : ℝ) * positiveWordBlockTime left right i t) =
      (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i < j),
          ((w i).length : ℝ) * positiveWordBlockTime left right i t) +
        ((w j).length : ℝ) * positiveWordBlockTime left right j t +
        ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => j < i),
          ((w i).length : ℝ) * positiveWordBlockTime left right i t := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N))
    (fun i => i < j) (fun i => ((w i).length : ℝ) * positiveWordBlockTime left right i t)
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin N)).filter (fun i => ¬ i < j)) (fun i => i = j)
    (fun i => ((w i).length : ℝ) * positiveWordBlockTime left right i t)
  have he : ((Finset.univ : Finset (Fin N)).filter (fun i => ¬ i < j)).filter (fun i => i = j) =
      {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨lt_irrefl _, rfl⟩
  have hg : ((Finset.univ : Finset (Fin N)).filter (fun i => ¬ i < j)).filter
      (fun i => ¬ i = j) = (Finset.univ : Finset (Fin N)).filter (fun i => j < i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, h'⟩
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm h')
    · intro h
      exact ⟨not_lt.mpr h.le, (ne_of_lt h).symm⟩
  rw [he, hg, Finset.sum_singleton] at h2
  rw [← h1, ← h2]
  ring

/-- Within its own block, the global time minus the offset of the block is the block
time scaled by the block length; before the block it is at most the offset, and after
the block it is at least the offset plus the block length. -/
theorem positiveWordGlobalTime_clamp {S N : ℕ} {left right : Fin N → ℝ}
    {w : Fin N → PositiveAdjacentWord S} (hlt : ∀ j, left j < right j)
    (hsep : ∀ j q, j < q → right j < left q) {t₀ d : ℝ} (hrt : ∀ j, right j ≤ t₀)
    (htd : t₀ < d) (j : Fin N) (t : ℝ) :
    max 0 (min (positiveWordGlobalTime left right w t₀ d t - positiveWordBlockOffset w j)
      (w j).length) =
    max 0 (min (((w j).length : ℝ) * (3 * ((t - left j) / (right j - left j)) - 1))
      (w j).length) := by
  have hL : (0 : ℝ) ≤ (w j).length := Nat.cast_nonneg _
  have hoff := positiveWordBlockOffset_eq_sum w j
  have hsplit := sum_blockTime_split left right w j t
  have hbt (i : Fin N) := unitClamp_mem (3 * ((t - left i) / (right i - left i)) - 1)
  have hlen (i : Fin N) : (0 : ℝ) ≤ (w i).length := Nat.cast_nonneg _
  have hlow : (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i < j),
      ((w i).length : ℝ) * positiveWordBlockTime left right i t) ≤ positiveWordBlockOffset w j := by
    rw [hoff]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_of_le_one_right (hlen i) (hbt i).2
  have hextra := unitClamp_mem ((t - t₀) / (d - t₀))
  rcases lt_or_ge t (left j) with h1 | h1
  · -- Before the block.
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => j < i),
        ((w i).length : ℝ) * positiveWordBlockTime left right i t = 0 := by
      intro i hi
      have hji := (Finset.mem_filter.mp hi).2
      rw [positiveWordBlockTime_of_le (hlt i) (by linarith [hsep j i hji, hlt j]), mul_zero]
    have hj0 : positiveWordBlockTime left right j t = 0 :=
      positiveWordBlockTime_of_le (hlt j) h1.le
    have hx : unitClamp ((t - t₀) / (d - t₀)) = 0 := by
      apply unitClamp_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hrt j, hlt j]) (by linarith)
    have hg : positiveWordGlobalTime left right w t₀ d t - positiveWordBlockOffset w j ≤ 0 := by
      unfold positiveWordGlobalTime
      rw [hsplit, Finset.sum_eq_zero hzero, hj0, hx]
      linarith
    have hr : ((w j).length : ℝ) * (3 * ((t - left j) / (right j - left j)) - 1) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hL
      have : (t - left j) / (right j - left j) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hlt j])
      linarith
    rw [max_eq_left (min_le_of_left_le hg), max_eq_left (min_le_of_left_le hr)]
  rcases le_or_gt t (right j) with h2 | h2
  · -- Within the block.
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => j < i),
        ((w i).length : ℝ) * positiveWordBlockTime left right i t = 0 := by
      intro i hi
      have hji := (Finset.mem_filter.mp hi).2
      rw [positiveWordBlockTime_of_le (hlt i) (by linarith [hsep j i hji]), mul_zero]
    have hone : (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i < j),
        ((w i).length : ℝ) * positiveWordBlockTime left right i t) =
        positiveWordBlockOffset w j := by
      rw [hoff]
      apply Finset.sum_congr rfl
      intro i hi
      have hij := (Finset.mem_filter.mp hi).2
      rw [positiveWordBlockTime_of_ge (hlt i) (by linarith [hsep i j hij]), mul_one]
    have hx : unitClamp ((t - t₀) / (d - t₀)) = 0 := by
      apply unitClamp_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hrt j]) (by linarith)
    have hg : positiveWordGlobalTime left right w t₀ d t - positiveWordBlockOffset w j =
        ((w j).length : ℝ) * positiveWordBlockTime left right j t := by
      unfold positiveWordGlobalTime
      rw [hsplit, Finset.sum_eq_zero hzero, hone, hx]
      ring
    rw [hg]
    unfold positiveWordBlockTime unitClamp
    set y := 3 * ((t - left j) / (right j - left j)) - 1
    rcases le_total y 0 with hy | hy
    · rw [min_eq_left (hy.trans zero_le_one), max_eq_left hy, mul_zero,
        max_eq_left (min_le_of_left_le (mul_nonpos_of_nonneg_of_nonpos hL hy)),
        min_eq_left hL, max_self]
    rcases le_total y 1 with hy' | hy'
    · rw [min_eq_left hy', max_eq_right hy, max_eq_right (le_min (mul_nonneg hL hy) hL),
        min_eq_left (mul_le_of_le_one_right hL hy')]
    · rw [min_eq_right hy', max_eq_right zero_le_one, mul_one, min_self,
        min_eq_right (le_mul_of_one_le_right hL hy')]
  · -- After the block.
    have hone : (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i < j),
        ((w i).length : ℝ) * positiveWordBlockTime left right i t) =
        positiveWordBlockOffset w j := by
      rw [hoff]
      apply Finset.sum_congr rfl
      intro i hi
      have hij := (Finset.mem_filter.mp hi).2
      rw [positiveWordBlockTime_of_ge (hlt i) (by linarith [hsep i j hij, hlt j]), mul_one]
    have hj1 : positiveWordBlockTime left right j t = 1 :=
      positiveWordBlockTime_of_ge (hlt j) h2.le
    have hrest : 0 ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => j < i),
        ((w i).length : ℝ) * positiveWordBlockTime left right i t :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hlen i) (hbt i).1
    have hg : ((w j).length : ℝ) ≤
        positiveWordGlobalTime left right w t₀ d t - positiveWordBlockOffset w j := by
      unfold positiveWordGlobalTime
      rw [hsplit, hone, hj1]
      linarith [hextra.1]
    have hr : ((w j).length : ℝ) ≤
        ((w j).length : ℝ) * (3 * ((t - left j) / (right j - left j)) - 1) := by
      have : 1 ≤ (t - left j) / (right j - left j) :=
        (le_div_iff₀ (sub_pos.mpr (hlt j))).mpr (by linarith)
      exact le_mul_of_one_le_right hL (by linarith)
    rw [min_eq_right hg, min_eq_right hr]

/-- The canonical global word model, relabelled by the initial sorting permutation, is
the canonical path of the concatenated word along the global time. -/
theorem positiveGridGlobalWordModel_eq_flatten {S N : ℕ} (left right : Fin N → ℝ)
    (σ : Fin (N + 1) → Equiv.Perm (Fin S)) (w : Fin N → PositiveAdjacentWord S)
    (hlt : ∀ j, left j < right j) (hsep : ∀ j q, j < q → right j < left q)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    {t₀ d : ℝ} (hrt : ∀ j, right j ≤ t₀) (htd : t₀ < d) (k : Fin S) (t : ℝ) :
    positiveGridGlobalWordModel left right σ w (σ 0 k) t =
      positiveGridWord (List.ofFn w).flatten k (positiveWordGlobalTime left right w t₀ d t) := by
  have hk : k = (σ 0).symm (σ 0 k) := by simp
  conv_rhs => rw [hk]
  rw [positiveGridWord_flatten w σ hp]
  unfold positiveGridGlobalWordModel
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold positiveGridEventPath
  rw [positiveGridWord_eq_clamp (w j) _ (positiveWordGlobalTime left right w t₀ d t - _),
    positiveGridWord_eq_clamp (w j) _ (((w j).length : ℝ) * _),
    positiveWordGlobalTime_clamp hlt hsep hrt htd j t]

/-! ### Representation by the event word -/

/-- The canonical global word model closes up with the monodromy of the strands. -/
theorem positiveGridGlobalWordModel_closing {S N : ℕ} (b d : ℝ)
    (left right : Fin N → ℝ) (σ : Fin (N + 1) → Equiv.Perm (Fin S))
    (w : Fin N → PositiveAdjacentWord S) (hlt : ∀ j, left j < right j)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (hb : ∀ j, b < left j) (hd : ∀ j, right j < d) {τ : Equiv.Perm (Fin S)}
    (hσ : (σ (Fin.last N)).trans τ = σ 0) (k : Fin S) :
    positiveGridGlobalWordModel left right σ w k d =
      positiveGridGlobalWordModel left right σ w (τ k) b := by
  rw [positiveGridGlobalWordModel_of_ge left right σ w hlt hp k (fun j => (hd j).le),
    positiveGridGlobalWordModel_of_le left right σ w hlt (τ k) (fun j => (hb j).le)]
  congr 2
  apply (σ 0).injective
  rw [Equiv.apply_symm_apply, ← hσ]
  simp

/-- **Event representation.** A closed braid whose projected coincidences on `[b, d]`
form a finite set of interior positive transverse crossings is represented by the
concatenation of its positive event words. The event data are those of
`exists_planeBranchBraidGlobalModel`, and the endpoint sorting permutations satisfy the
closing relation with the monodromy. -/
theorem exists_positive_event_words_isRepresented
    {S : ℕ} {K : Fin S → ℝ → ℂ} (hcont : ∀ k, Continuous (K k))
    {b d : ℝ} (hbd : b < d) {τ : Equiv.Perm (Fin S)}
    (hinj : ∀ t ∈ Icc b d, Function.Injective fun k => K k t)
    (hclose : ∀ k, K k d = K (τ k) b)
    (E : Finset ℝ)
    (hE : ∀ t, t ∈ E ↔ t ∈ Icc b d ∧ ∃ k l : Fin S, k ≠ l ∧ (K k t).re = (K l t).re)
    (hb : b ∉ E) (hd : d ∉ E)
    (hpos : ∀ θ ∈ E, ∀ k l, k ≠ l → (K k θ).re = (K l θ).re →
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im) :
    ∃ (N : ℕ) (event left right : Fin N → ℝ)
      (σ : Fin (N + 1) → Equiv.Perm (Fin S)) (w : Fin N → PositiveAdjacentWord S),
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
      (σ (Fin.last N)).trans τ = σ 0 ∧
      σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
        σ (Fin.last N) ∧
      (List.ofFn w).flatten.length = ∑ j : Fin N,
        (Finset.univ.filter fun p : Fin S × Fin S =>
          p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re =
            (K (σ j.succ p.2) (event j)).re).card ∧
      ClosedStrandBraidIsotopic (fun k t => K (σ 0 k) t)
        (positiveWordModel (List.ofFn w).flatten b d) b d
        (PositiveAdjacentWord.permutation (List.ofFn w).flatten)⁻¹ ∧
      IsRepresentedByPositiveWord K b d (List.ofFn w).flatten := by
  classical
  obtain ⟨N, event, left, right, σ, w, hN, henum, hmono, hσb, hσd, hblocks, hsep, hperm,
      hlength, hM⟩ := exists_planeBranchBraidGlobalModel hcont E b d hbd hE hb hd hpos
  obtain ⟨hMc, -, -, hMb, hMd, hMinj, hMsep⟩ := hM
  set M := planeBranchBraidGlobalModel K b d event left right σ w with hMdef
  set W := (List.ofFn w).flatten with hWdef
  have hbI : b ∈ Icc b d := left_mem_Icc.mpr hbd.le
  have hdI : d ∈ Icc b d := right_mem_Icc.mpr hbd.le
  -- The closing relation of the sorting permutations.
  have hregb : Function.Injective fun k => (K k b).re := by
    intro k l heq
    by_contra hkl
    exact hb ((hE b).mpr ⟨hbI, k, l, hkl, heq⟩)
  have hσ : (σ (Fin.last N)).trans τ = σ 0 := by
    apply sortingPerm_unique hregb
    · intro i j hij
      simpa only [Equiv.trans_apply, ← hclose] using hσd hij
    · exact hσb
  have hlt : ∀ j, left j < right j := fun j => (hblocks j).2.1.trans (hblocks j).2.2.1
  have hbl : ∀ j, b < left j := fun j => (hblocks j).1
  have hrd : ∀ j, right j < d := fun j => (hblocks j).2.2.2.1
  have hevent : ∀ j, IsPositiveBraidEventWord K (event j) (σ j.castSucc) (σ j.succ) (w j) :=
    fun j => (hblocks j).2.2.2.2.2.2.2
  have hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ := fun j => (hevent j).1
  -- The three closed braids.
  have hK : IsClosedStrandBraid K b d τ :=
    ⟨hbd, fun k => (hcont k).continuousOn, hinj, hclose⟩
  have hMcl : IsClosedStrandBraid M b d τ := by
    refine ⟨hbd, fun k => (hMc k).continuous.continuousOn, hMinj, fun k => ?_⟩
    rw [hMd k, hMb (τ k)]
    exact braid_rank_endpoint_configs_cyclic K b d (σ 0) (σ (Fin.last N)) τ hclose hσ k
  set G := positiveGridGlobalWordModel left right σ w with hGdef
  have hgap := braidModel_gap_pos b d hbd left right hbl hrd hsep
  have hGcl : IsClosedStrandBraid G b d τ :=
    ⟨hbd, fun k => (positiveGridGlobalWordModel_contDiff left right σ w k).continuous.continuousOn,
      fun t ht => positiveGridGlobalWordModel_injective b d left right σ w hlt hsep hp ht,
      fun k => positiveGridGlobalWordModel_closing b d left right σ w hlt hp hbl hrd hσ k⟩
  have hKM : ClosedStrandBraidIsotopic K M b d τ :=
    ClosedStrandBraidIsotopic.of_separation hK hMcl hMsep
  have hMG : ClosedStrandBraidIsotopic M G b d τ :=
    ClosedStrandBraidIsotopic.of_separation hMcl hGcl fun t ht k l hkl =>
      positiveGridGlobalWordModel_separation K b d event left right σ w hlt hsep hgap hevent
        hkl ht
  -- The monodromy of the relabelled braid is the inverse word permutation.
  have hWperm : PositiveAdjacentWord.permutation W = (σ 0)⁻¹ * σ (Fin.last N) := by
    rw [← hperm]
    change PositiveAdjacentWord.permutation W =
      (σ 0)⁻¹ * (σ 0 * PositiveAdjacentWord.permutation W)
    group
  have hmono' : (σ 0)⁻¹ * τ * σ 0 = (PositiveAdjacentWord.permutation W)⁻¹ := by
    rw [hWperm, ← hσ]
    ext k
    simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  have hKG := (hKM.trans hMG).relabel (σ 0)
  rw [hmono'] at hKG
  -- The global time.
  let t₀ : ℝ := (insert b (Finset.univ.image right)).max' (Finset.insert_nonempty _ _)
  have hrt : ∀ j, right j ≤ t₀ := fun j =>
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hbt : b ≤ t₀ := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have htd : t₀ < d := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hbd
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact hrd j
  let ψ := positiveWordGlobalTime left right w t₀ d
  have hψc : Continuous ψ := positiveWordGlobalTime_continuous left right w t₀ d
  have hWlen : (W.length : ℝ) = ∑ j : Fin N, ((w j).length : ℝ) := by
    rw [hWdef, positiveWordSequence_length]
    push_cast
    rfl
  have hψb : ψ b = 0 := by
    simp only [ψ, positiveWordGlobalTime]
    rw [Finset.sum_eq_zero (fun j _ => by
      rw [positiveWordBlockTime_of_le (hlt j) (hbl j).le, mul_zero]), zero_add]
    exact unitClamp_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hψd : ψ d = (W.length : ℝ) + 1 := by
    simp only [ψ, positiveWordGlobalTime]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [positiveWordBlockTime_of_ge (hlt j) (hrd j).le, mul_one]), ← hWlen]
    rw [unitClamp_of_one_le (by rw [div_self (by linarith)])]
  have hψm : MapsTo ψ (Icc b d) (Icc 0 ((W.length : ℝ) + 1)) := by
    intro t _
    have hsum0 : 0 ≤ ∑ j : Fin N, ((w j).length : ℝ) * positiveWordBlockTime left right j t :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
        (unitClamp_mem _).1
    have hsum1 : ∑ j : Fin N, ((w j).length : ℝ) * positiveWordBlockTime left right j t ≤
        W.length := by
      rw [hWlen]
      exact Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (Nat.cast_nonneg _)
        (unitClamp_mem _).2
    have hx := unitClamp_mem ((t - t₀) / (d - t₀))
    simp only [ψ, positiveWordGlobalTime]
    constructor <;> linarith [hx.1, hx.2]
  have hGW : ∀ k, ∀ t ∈ Icc b d, G (σ 0 k) t = positiveGridWord W k (ψ t) := by
    intro k t ht
    exact positiveGridGlobalWordModel_eq_flatten left right σ w hlt hsep hp hrt htd k t
  have hreparam := ClosedStrandBraidIsotopic.of_reparam (positiveGridWord_isClosedStrandBraid W)
    hbd hψc.continuousOn (positiveWordModelTime_continuous W b d).continuousOn hψm
    (positiveWordModelTime_mapsTo W hbd) hψb hψd (positiveWordModelTime_left W b d)
    (positiveWordModelTime_right W hbd)
  have hfinal : ClosedStrandBraidIsotopic (fun k t => K (σ 0 k) t) (positiveWordModel W b d) b d
      (PositiveAdjacentWord.permutation W)⁻¹ :=
    hKG.trans (hreparam.congr (fun k t ht => hGW k t ht) (fun k t _ => rfl))
  exact ⟨N, event, left, right, σ, w, hN, henum, hmono, hσb, hσd, hblocks, hsep, hσ, hperm,
    hlength, hfinal, σ 0, hfinal⟩

end OnLeConjecture.Analytic
