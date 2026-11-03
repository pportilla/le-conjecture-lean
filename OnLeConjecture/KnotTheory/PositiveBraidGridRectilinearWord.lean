/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinear
public import OnLeConjecture.KnotTheory.PositiveBraidGridWordModel

/-! # Joining the rectilinear gadgets of a positive word

Letter `j` occupies the horizontal slab `[2j+1,2j+2]`, with its original labels
recovered from the word prefix. The gaps occupy `[2j,2j+1]`. Their real ranks
are fixed while their depths interpolate between consecutive gadgets. The
first and last gap depths are zero. Endpoint matching is proved from the
actual word permutations, not supplied as an additional premise.
-/

@[expose] public noncomputable section

open Set
open scoped Topology

namespace OnLeConjecture.KnotTheory

/-- The depth assigned to an original label in a particular letter gadget. -/
def positiveRectilinearWordDepth {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) : ℝ :=
  positiveGridRectilinearDepth w[j.val] ((positiveWordPrefix w j.val).symm k)

/-- Initial connector depths, including zero before the first letter. -/
def positiveRectilinearWordGapInitial {m : ℕ} (w : PositiveAdjacentWord m) :
    Fin (w.length + 1) → Fin m → ℝ :=
  Fin.cases (fun _ => 0) (positiveRectilinearWordDepth w)

/-- Final connector depths, including zero after the last letter. -/
def positiveRectilinearWordGapFinal {m : ℕ} (w : PositiveAdjacentWord m) :
    Fin (w.length + 1) → Fin m → ℝ :=
  Fin.lastCases (fun _ => 0) (positiveRectilinearWordDepth w)

/-- A literal translated crossing gadget, with its prefix relabeling. -/
def positiveRectilinearWordLetter {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  let p := positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k) t
  (2 * (j.val : ℝ) + 1 + p.1, p.2)

/-- The horizontal connector between the outgoing and incoming gadget depths. -/
def positiveRectilinearWordGap {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  (2 * (j.val : ℝ) + t,
    (((positiveWordPrefix w j.val).symm k).val : ℂ) +
      (((1 - t) * positiveRectilinearWordGapInitial w j k +
        t * positiveRectilinearWordGapFinal w j k : ℝ) : ℂ) * Complex.I)

@[simp] theorem positiveRectilinearWordGapInitial_zero {m : ℕ}
    (w : PositiveAdjacentWord m) (k : Fin m) : positiveRectilinearWordGapInitial w 0 k = 0 := rfl

@[simp] theorem positiveRectilinearWordGapInitial_succ {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordGapInitial w j.succ k = positiveRectilinearWordDepth w j k := rfl

@[simp] theorem positiveRectilinearWordGapFinal_last {m : ℕ}
    (w : PositiveAdjacentWord m) (k : Fin m) :
    positiveRectilinearWordGapFinal w (Fin.last w.length) k = 0 := by
  simp [positiveRectilinearWordGapFinal]

@[simp] theorem positiveRectilinearWordGapFinal_castSucc {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordGapFinal w j.castSucc k = positiveRectilinearWordDepth w j k := by
  simp [positiveRectilinearWordGapFinal]

theorem positiveRectilinearWordLetter_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) : Continuous (positiveRectilinearWordLetter w j k) := by
  have hp : Continuous (fun t => positiveGridRectilinear w[j.val]
      ((positiveWordPrefix w j.val).symm k) t) := by
    have hh := (positiveGridRectilinearDeformation_continuous w[j.val]
      ((positiveWordPrefix w j.val).symm k)).comp
      ((continuous_const (y := (1 : ℝ))).prodMk continuous_id)
    change Continuous (fun t => positiveGridRectilinearDeformation w[j.val]
      ((positiveWordPrefix w j.val).symm k) 1 t) at hh
    simpa only [positiveGridRectilinearDeformation_one] using hh
  exact (continuous_const.add hp.fst).prodMk hp.snd

theorem positiveRectilinearWordGap_continuous {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) (k : Fin m) : Continuous (positiveRectilinearWordGap w j k) := by
  exact (continuous_const.add continuous_id).prodMk
    (continuous_const.add ((Complex.continuous_ofReal.comp
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const))).mul continuous_const))

/-- Each translated gadget begins at the ranks before its letter. -/
theorem positiveRectilinearWordLetter_zero {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordLetter w j k 0 =
      (2 * (j.val : ℝ) + 1, (((positiveWordPrefix w j.val).symm k).val : ℂ) +
        (positiveRectilinearWordDepth w j k : ℂ) * Complex.I) := by
  have h := (positiveGridRectilinearDeformation_endpoints w[j.val]
    ((positiveWordPrefix w j.val).symm k) 1).1
  rw [positiveGridRectilinearDeformation_one] at h
  simp only [positiveRectilinearWordLetter, h, add_zero, positiveRectilinearWordDepth]

/-- The terminal ranks are exactly those of the next prefix. -/
theorem positiveRectilinearWordLetter_one {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordLetter w j k 1 =
      (2 * (j.val : ℝ) + 2, (((positiveWordPrefix w (j.val + 1)).symm k).val : ℂ) +
        (positiveRectilinearWordDepth w j k : ℂ) * Complex.I) := by
  have h := (positiveGridRectilinearDeformation_endpoints w[j.val]
    ((positiveWordPrefix w j.val).symm k) 1).2
  rw [positiveGridRectilinearDeformation_one] at h
  simp only [positiveRectilinearWordLetter, h, positiveRectilinearWordDepth,
    ← positiveWordPrefix_succ_symm w j.val j.isLt k]
  congr 1
  ring

/-- The connector and the following letter have identical endpoints in all three coordinates. -/
theorem positiveRectilinearWordGap_one_eq_letter_zero {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordGap w j.castSucc k 1 = positiveRectilinearWordLetter w j k 0 := by
  simp [positiveRectilinearWordGap, positiveRectilinearWordLetter_zero]

/-- The letter and the following connector have identical endpoints in all three coordinates. -/
theorem positiveRectilinearWordLetter_one_eq_gap_zero {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin w.length) (k : Fin m) :
    positiveRectilinearWordLetter w j k 1 = positiveRectilinearWordGap w j.succ k 0 := by
  simp only [positiveRectilinearWordLetter_one, positiveRectilinearWordGap,
    Fin.val_succ, zero_mul, add_zero, sub_zero, one_mul,
    positiveRectilinearWordGapInitial_succ]
  push_cast
  congr 1
  ring

/-- The whole tangle starts on the real axis in the identity order. -/
theorem positiveRectilinearWord_initial {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) :
    positiveRectilinearWordGap w 0 k 0 = (0, (k.val : ℂ)) := by
  simp [positiveRectilinearWordGap, Equiv.Perm.one_def]

/-- The whole tangle ends on the real axis in the exact terminal word order. -/
theorem positiveRectilinearWord_final {m : ℕ} (w : PositiveAdjacentWord m) (k : Fin m) :
    positiveRectilinearWordGap w (Fin.last w.length) k 1 =
      (2 * (w.length : ℝ) + 1, ((w.permutation.symm k).val : ℂ)) := by
  simp [positiveRectilinearWordGap]

/-- Distinct labels in a connector remain separated by their real ranks. -/
theorem positiveRectilinearWordGap_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin (w.length + 1)) :
    Function.Injective (fun p : Fin m × ℝ => positiveRectilinearWordGap w j p.1 p.2) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hx := congrArg Prod.fst he
  have hr := congrArg (fun p : ℝ × ℂ => p.2.re) he
  simp only [positiveRectilinearWordGap, Complex.add_re, Complex.natCast_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero] at hx hr
  have ht : t = u := by linarith
  have hk : k = l := (positiveWordPrefix w j.val).symm.injective (Fin.ext (Nat.cast_injective hr))
  simp [hk, ht]

/-- Each word letter is the proved embedded polygonal gadget in its exact original labels. -/
theorem positiveRectilinearWordLetter_injective {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) :
    Function.Injective (fun p : Fin m × ℝ => positiveRectilinearWordLetter w j p.1 p.2) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hx := congrArg Prod.fst he
  have hz := congrArg Prod.snd he
  simp only [positiveRectilinearWordLetter] at hx hz
  have he' : positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k) t =
      positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm l) u :=
    Prod.ext (by linarith) hz
  have hp := positiveGridRectilinearDeformation_injective w[j.val]
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (a₁ := ((positiveWordPrefix w j.val).symm k, t))
    (a₂ := ((positiveWordPrefix w j.val).symm l, u))
    (by simpa only [positiveGridRectilinearDeformation_one] using he')
  have hk : k = l := (positiveWordPrefix w j.val).symm.injective (congrArg Prod.fst hp)
  have ht : t = u := congrArg Prod.snd hp
  simp [hk, ht]

/-- The projected crossing in a letter has exactly the prefix labels prescribed by the word. -/
theorem positiveRectilinearWordLetter_crossing_iff {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) {k l : Fin m} (hkl : k ≠ l)
    {t u : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) :
    positiveGridRectilinearProjection (positiveRectilinearWordLetter w j k t) =
      positiveGridRectilinearProjection (positiveRectilinearWordLetter w j l u) ↔
      ((k = positiveWordPrefix w j.val (adjacentLower w[j.val]) ∧
        l = positiveWordPrefix w j.val (adjacentUpper w[j.val])) ∨
       (k = positiveWordPrefix w j.val (adjacentUpper w[j.val]) ∧
        l = positiveWordPrefix w j.val (adjacentLower w[j.val]))) ∧
          t = 1 / 2 ∧ u = 1 / 2 := by
  have hne : (positiveWordPrefix w j.val).symm k ≠ (positiveWordPrefix w j.val).symm l :=
    fun he => hkl ((positiveWordPrefix w j.val).symm.injective he)
  have hh := positiveGridRectilinear_projected_crossing_iff w[j.val] hne ht hu
  simpa only [positiveGridRectilinearProjection, positiveRectilinearWordLetter,
    Prod.mk.injEq, add_right_inj, Equiv.symm_apply_eq] using hh

/-- The three columns of every word gadget are literal translated corner columns. -/
def positiveRectilinearWordColumn {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) : ℝ :=
  2 * (j.val : ℝ) + 1 + positiveGridRectilinearColumns c

/-- Starting corners of all vertical moves in the finite word drawing. -/
def positiveRectilinearWordXCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) : ℝ × ℝ :=
  (positiveRectilinearWordColumn w j c,
    positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.X c))

/-- Terminal corners of all vertical moves in the finite word drawing. -/
def positiveRectilinearWordOCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) : ℝ × ℝ :=
  (positiveRectilinearWordColumn w j c,
    positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.O c))

/-- Vertical moves from different letters have strictly ordered horizontal coordinates. -/
theorem positiveRectilinearWordColumn_lt {m : ℕ} (w : PositiveAdjacentWord m)
    {j q : Fin w.length} (hjq : j < q) (c d : Fin 3) :
    positiveRectilinearWordColumn w j c < positiveRectilinearWordColumn w q d := by
  have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hjq
  fin_cases c <;> fin_cases d <;>
    norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns]
  all_goals first | exact hjq | linarith

/-- The finite set of vertical moves has no repeated column, even before row perturbation. -/
theorem positiveRectilinearWordColumn_injective {m : ℕ} (w : PositiveAdjacentWord m) :
    Function.Injective (fun p : Fin w.length × Fin 3 =>
      positiveRectilinearWordColumn w p.1 p.2) := by
  rintro ⟨j, c⟩ ⟨q, d⟩ he
  have hjq : j = q := by
    rcases lt_trichotomy j q with h | h | h
    · exact (ne_of_lt (positiveRectilinearWordColumn_lt w h c d) he).elim
    · exact h
    · exact (ne_of_lt (positiveRectilinearWordColumn_lt w h d c) he.symm).elim
  subst q
  have hcd : c = d := positiveGridRectilinearColumns_strictMono.injective
    (add_left_cancel he)
  simp [hcd]

/-- Every local polygon lies in its unit slab, and meets its two boundary planes only at
its corresponding endpoints. -/
theorem positiveRectilinearWord_local_slab {m : ℕ} (i : Fin (m - 1)) (k : Fin m)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (positiveGridRectilinear i k t).1 ∈ Icc 0 1 ∧
      ((positiveGridRectilinear i k t).1 = 0 ↔ t = 0) ∧
      ((positiveGridRectilinear i k t).1 = 1 ↔ t = 1) := by
  by_cases hk₀ : k = adjacentLower i
  · subst k
    rcases positiveGridRectilinear_lower_segments i with ⟨h₀, h₁, h₂, h₃, h₄⟩
    by_cases h : t ≤ 1 / 6
    · have he := congrArg Prod.fst (h₀ t ⟨ht.1, h⟩)
      change (positiveGridRectilinear i (adjacentLower i) t).1 = 2 * t at he
      rw [he]
      constructor
      · constructor <;> linarith [ht.1]
      · constructor <;> constructor <;> intro hh <;> linarith
    by_cases h' : t ≤ 5 / 12
    · have he := congrArg Prod.fst (h₁ t ⟨by linarith, h'⟩)
      change (positiveGridRectilinear i (adjacentLower i) t).1 = 1 / 3 at he
      rw [he]
      constructor
      · constructor <;> norm_num
      · constructor <;> constructor <;> intro hh <;> linarith
    by_cases h'' : t ≤ 7 / 12
    · have he := congrArg Prod.fst (h₂ t ⟨by linarith, h''⟩)
      change (positiveGridRectilinear i (adjacentLower i) t).1 = 2 * t - 1 / 2 at he
      rw [he]
      constructor
      · constructor <;> linarith
      · constructor <;> constructor <;> intro hh <;> linarith
    by_cases hLast : t ≤ 5 / 6
    · have he := congrArg Prod.fst (h₃ t ⟨by linarith, hLast⟩)
      change (positiveGridRectilinear i (adjacentLower i) t).1 = 2 / 3 at he
      rw [he]
      constructor
      · constructor <;> norm_num
      · constructor <;> constructor <;> intro hh <;> linarith
    · have he := congrArg Prod.fst (h₄ t ⟨by linarith, ht.2⟩)
      change (positiveGridRectilinear i (adjacentLower i) t).1 = 2 * t - 1 at he
      rw [he]
      constructor
      · constructor <;> linarith [ht.2]
      · constructor <;> constructor <;> intro hh <;> linarith
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    rcases positiveGridRectilinear_upper_segments i with ⟨h₀, h₁, h₂⟩
    by_cases h : t ≤ 1 / 4
    · have he := congrArg Prod.fst (h₀ t ⟨ht.1, h⟩)
      change (positiveGridRectilinear i (adjacentUpper i) t).1 = 2 * t at he
      rw [he]
      constructor
      · constructor <;> linarith [ht.1]
      · constructor <;> constructor <;> intro hh <;> linarith
    by_cases h' : t ≤ 3 / 4
    · have he := congrArg Prod.fst (h₁ t ⟨by linarith, h'⟩)
      change (positiveGridRectilinear i (adjacentUpper i) t).1 = 1 / 2 at he
      rw [he]
      constructor
      · constructor <;> norm_num
      · constructor <;> constructor <;> intro hh <;> linarith
    · have he := congrArg Prod.fst (h₂ t ⟨by linarith, ht.2⟩)
      change (positiveGridRectilinear i (adjacentUpper i) t).1 = 2 * t - 1 at he
      rw [he]
      constructor
      · constructor <;> linarith [ht.2]
      · constructor <;> constructor <;> intro hh <;> linarith
  · rw [positiveGridRectilinear_fixed i k hk₀ hk₁]
    exact ⟨ht, Iff.rfl, Iff.rfl⟩

/-- Distinct letters are separated by a positive horizontal gap. This rules out projected
crossings between different letter gadgets. -/
theorem positiveRectilinearWordLetter_separated {m : ℕ} (w : PositiveAdjacentWord m)
    {j q : Fin w.length} (hjq : j < q) (k l : Fin m)
    {t u : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) :
    (positiveRectilinearWordLetter w j k t).1 < (positiveRectilinearWordLetter w q l u).1 := by
  have hj := (positiveRectilinearWord_local_slab w[j.val]
    ((positiveWordPrefix w j.val).symm k) ht).1
  have hq := (positiveRectilinearWord_local_slab w[q.val]
    ((positiveWordPrefix w q.val).symm l) hu).1
  have hh : (j.val : ℝ) + 1 ≤ q.val := by exact_mod_cast hjq
  change 2 * (j.val : ℝ) + 1 + _ < 2 * (q.val : ℝ) + 1 + _
  linarith [hj.2, hq.1]

/-- A connector has no projected crossings between different labels. -/
theorem positiveRectilinearWordGap_projection_injective {m : ℕ}
    (w : PositiveAdjacentWord m) (j : Fin (w.length + 1)) :
    Function.Injective (fun p : Fin m × ℝ =>
      positiveGridRectilinearProjection (positiveRectilinearWordGap w j p.1 p.2)) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hx := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  simp only [positiveGridRectilinearProjection, positiveRectilinearWordGap,
    Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero] at hx hr
  have ht : t = u := by linarith
  have hk : k = l := (positiveWordPrefix w j.val).symm.injective
    (Fin.ext (Nat.cast_injective hr))
  simp [hk, ht]

/-- The starting corner coordinates are attained by the corresponding original word labels. -/
theorem positiveRectilinearWordXCorner_eq {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    positiveRectilinearWordXCorner w j c =
      ![positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentLower w[j.val])) (1 / 6)),
        positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentUpper w[j.val])) (1 / 4)),
        positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentLower w[j.val])) (7 / 12))] c := by
  have hl := positiveGridRectilinear_lower_segments w[j.val]
  have hu := positiveGridRectilinear_upper_segments w[j.val]
  have h₀ := hl.1 (1 / 6) (by constructor <;> norm_num)
  have h₁ := hu.1 (1 / 4) (by constructor <;> norm_num)
  have h₂ := hl.2.2.1 (7 / 12) (by constructor <;> norm_num)
  change (positiveRectilinearWordColumn w j c,
    positiveGridRectilinearRows w[j.val] (Equiv.swap 1 2 c)) = _
  fin_cases c <;> norm_num [positiveRectilinearWordLetter, positiveRectilinearWordColumn,
    positiveGridRectilinearProjection, positiveGridRectilinearColumns,
    positiveGridRectilinearRows, Equiv.swap_apply_def, Fin.ext_iff,
    Matrix.cons_val_two] at *
  all_goals constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

/-- The terminal corner coordinates are attained by the corresponding original word labels. -/
theorem positiveRectilinearWordOCorner_eq {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    positiveRectilinearWordOCorner w j c =
      ![positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentLower w[j.val])) (5 / 12)),
        positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentUpper w[j.val])) (3 / 4)),
        positiveGridRectilinearProjection (positiveRectilinearWordLetter w j
          (positiveWordPrefix w j.val (adjacentLower w[j.val])) (5 / 6))] c := by
  have hl := positiveGridRectilinear_lower_segments w[j.val]
  have hu := positiveGridRectilinear_upper_segments w[j.val]
  have h₀ := hl.2.1 (5 / 12) (by constructor <;> norm_num)
  have h₁ := hu.2.1 (3 / 4) (by constructor <;> norm_num)
  have h₂ := hl.2.2.2.1 (5 / 6) (by constructor <;> norm_num)
  change (positiveRectilinearWordColumn w j c,
    positiveGridRectilinearRows w[j.val] (Equiv.swap 0 1 c)) = _
  fin_cases c <;> norm_num [positiveRectilinearWordLetter, positiveRectilinearWordColumn,
    positiveGridRectilinearProjection, positiveGridRectilinearColumns,
    positiveGridRectilinearRows, Equiv.swap_apply_def, Fin.ext_iff,
    Matrix.cons_val_two] at *
  all_goals constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

end OnLeConjecture.KnotTheory
