/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelImage
public import OnLeConjecture.KnotTheory.MarkedCancelReal
public import OnLeConjecture.KnotTheory.MarkedCancelTie
public import OnLeConjecture.KnotTheory.SignedWordGridMovesCancel

/-!
# Cancellation of an inverse pair with a protected block outside the window

The marked window grid `winGrid` of `X ++ t`, with a block `X` of two inverse letters and with
the marked arc leaving an outside corner `p`, realizes the same window state as the initial grid
(`real_winGrid`): the block columns are outside columns, the output row of the block keeps the
label of the marked arc, and every other block row is an outside label. The window sequence of
the unmarked cancellation therefore applies, followed by the two contractions of
`SignedGrid.cancel_front_of_data`. The resulting grid is recognized as a marked word grid of `t`
with the marked arc leaving the corner of `t` under `p` (`marked_cancel_front`). This is the
marked inverse cancellation of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8) when the marked arc leaves a corner outside the
cancelled letters.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid

variable {m : ℕ}

/-! ### The marked window grid realizes the window state -/

/-- The labels of the block columns of a marked window grid. -/
def winQ (L k : ℕ) : List (ℕ × Fin 3) :=
  List.ofFn (fun j : Fin (k + 1) => (L + j.val, (0 : Fin 3)))

section RealWin

variable {K E i k : ℕ} {offs : List ℕ} {sg : List Bool} {flags : List Bool}
  {B t : SignedAdjacentWord m} (S : WState) (hB : BlockS K E i offs sg B t (flagOf flags))
  (hS : InitOKS K S offs sg flags) (p : Fin (B ++ t).length × Fin 3)
  (H : GridDiagram (k + 1)) (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0)

theorem winBlock_cols : (winBlock K S p H hX hO).cols = (winQ (B ++ t).length k).map Sum.inr := by
  change List.ofFn _ = (List.ofFn _).map Sum.inr
  rw [List.map_ofFn]; rfl

include hB in
theorem sInitGrid_O_corner (q : Fin (B ++ t).length × Fin 3) :
    (sInitGrid S hB hS).O (sfCol K (B ++ t) q) = sgRow K S (B ++ t) q := by
  rw [sInitGrid_O, sfColInv_sfCol]

theorem sfCol_out (q : Fin (B ++ t).length × Fin 3) (hq : K ≤ q.1.val) :
    sfCol K (B ++ t) q = Sum.inr (q.1.val, q.2) := by
  unfold sfCol; rw [if_neg (by omega)]

theorem sfCol_mem_sInitGrid_cols (q : Fin (B ++ t).length × Fin 3) :
    sfCol K (B ++ t) q ∈ (sInitGrid S hB hS).cols := by
  change _ ∈ (sCols (B ++ t)).map (sfCol K (B ++ t))
  exact List.mem_map_of_mem (mem_sCols _ q)

theorem lefts_winBlock_rows :
    lefts (winBlock K S p H hX hO).rows = lefts [sgRow K S (B ++ t) p] := by
  change lefts (List.ofFn _) = _
  rw [ofFn_succ_last, lefts_append]
  have h0 : lefts (List.ofFn (fun j : Fin (k + 1) => (winBlock K S p H hX hO).hr j.castSucc)) =
      [] := by
    simp only [lefts, List.filterMap_eq_nil_iff, List.mem_ofFn]
    rintro _ ⟨j, rfl⟩
    rw [winBlock_hr_of_ne S p H hX hO (Fin.castSucc_ne_last j)]
    rfl
  rw [h0, List.nil_append, winBlock_hr_last]

/-- **The marked window grid realizes the initial window state.** -/
theorem real_winGrid (hp : K ≤ p.1.val) :
    Real S (winGrid S hB hS p H hX hO) (List.range (3 * K))
      (outsideQK K (B ++ t).length ++ winQ (B ++ t).length k) := by
  have hR := sInitGrid_real S hB hS
  have h := real_insertBlock (S' := S) hR (winData S hB hS p H hX hO)
    (Q₁ := outsideQK K (B ++ t).length) (Q₂ := []) (qH := winQ (B ++ t).length k)
    hR.cols rfl (winBlock_cols S p H hX hO) rfl ?_ ?_
  · rw [List.append_nil] at h; exact h
  · intro w hw
    have hw1 : w.1 ∈ List.range (3 * K) := (List.of_mem_zip hw).1
    obtain ⟨h1, h2⟩ := hR.marks w hw
    rw [blockO_window hR (winData S hB hS p H hX hO) hw1,
      blockX_window hR (winData S hB hS p H hX hO) hw1, h1, h2]
    constructor
    · rw [if_neg]
      intro he
      have hpc := sfCol_mem_sInitGrid_cols S hB hS p
      have hwc := mem_cols_of_mem_W hR hw1
      have := (sInitGrid S hB hS).O_inj _ hwc _ hpc
        (by rw [h1, he, sInitGrid_O_corner S hB hS p])
      rw [sfCol_out p hp] at this
      simp at this
    · split_ifs with he
      · rw [winBlock_hr_last, ← he]
      · rfl
  · rw [lefts_newRows, ← hR.rows, lefts_rows_eq (winData S hB hS p H hX hO),
      lefts_winBlock_rows]

end RealWin

/-! ### Lists with a replaced element -/

section Lists

variable {β : Type*}

theorem eq_of_append_cons_eq {l₁ l₂ c d : List β} {a : β} (hnd : (l₁ ++ a :: l₂).Nodup)
    (h : l₁ ++ a :: l₂ = c ++ a :: d) : l₁ = c ∧ l₂ = d := by
  classical
  have ha1 : a ∉ l₁ := fun hm => not_mem_of_nodup_middle hnd (List.mem_append_left _ hm)
  have hnd' := hnd; rw [h] at hnd'
  have ha2 : a ∉ c := fun hm => not_mem_of_nodup_middle hnd' (List.mem_append_left _ hm)
  have h1 : (l₁ ++ a :: l₂).idxOf a = l₁.length := by
    rw [List.idxOf_append_of_notMem ha1]; simp
  have h2 : (c ++ a :: d).idxOf a = c.length := by
    rw [List.idxOf_append_of_notMem ha2]; simp
  rw [h] at h1
  have hl : l₁.length = c.length := h1.symm.trans h2
  obtain ⟨e1, e2⟩ := List.append_inj h hl
  exact ⟨e1, by simpa using e2⟩

/-- Replacing an element by a list ending in it keeps two consecutive elements consecutive. -/
theorem consec_replace {l₁ l₂ B n₁ n₂ : List β} {a x y : β} (hnd : (l₁ ++ a :: l₂).Nodup)
    (h : l₁ ++ a :: l₂ = n₁ ++ x :: y :: n₂) (hay : a ≠ y) {Bi : List β} (hB : B = Bi ++ [a]) :
    ∃ n₁' n₂', l₁ ++ B ++ l₂ = n₁' ++ x :: y :: n₂' := by
  by_cases hax : a = x
  · subst hax
    obtain ⟨e1, e2⟩ := eq_of_append_cons_eq (c := n₁) (d := y :: n₂) hnd h
    refine ⟨l₁ ++ Bi, n₂, ?_⟩
    rw [hB, e2]; simp
  · have hmem : a ∈ n₁ ++ x :: y :: n₂ := by rw [← h]; simp
    simp only [List.mem_append, List.mem_cons] at hmem
    rcases hmem with hm | hm | hm | hm
    · obtain ⟨c, d, rfl⟩ := List.append_of_mem hm
      have h' : l₁ ++ a :: l₂ = c ++ a :: (d ++ x :: y :: n₂) := by rw [h]; simp
      obtain ⟨e1, e2⟩ := eq_of_append_cons_eq hnd h'
      refine ⟨c ++ B ++ d, n₂, ?_⟩
      rw [e1, e2]; simp
    · exact absurd hm hax
    · exact absurd hm hay
    · obtain ⟨c, d, rfl⟩ := List.append_of_mem hm
      have h' : l₁ ++ a :: l₂ = (n₁ ++ x :: y :: c) ++ a :: d := by rw [h]; simp
      obtain ⟨e1, e2⟩ := eq_of_append_cons_eq hnd h'
      refine ⟨n₁, c ++ B ++ d, ?_⟩
      rw [e1, e2]; simp

theorem filter_ne_of_consec [DecidableEq β] {l n₁ n₂ : List β} {x y : β} (hnd : l.Nodup)
    (h : l = n₁ ++ x :: y :: n₂) : n₁ ++ x :: n₂ = l.filter (fun z => z ≠ y) := by
  subst h
  have hy1 : y ∉ n₁ := fun hm => by
    have := (List.nodup_append.mp hnd).2.2 y hm y (by simp); exact this rfl
  have hnd2 := (List.nodup_append.mp hnd).2.1
  have hxy : x ≠ y := fun e => by subst e; simp at hnd2
  have hy2 : y ∉ n₂ := fun hm => by
    have := (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1; exact this hm
  have e1 : n₁.filter (fun z => z ≠ y) = n₁ := List.filter_eq_self.mpr (fun z hz => by
    simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hy1 hz)
  have e2 : n₂.filter (fun z => z ≠ y) = n₂ := List.filter_eq_self.mpr (fun z hz => by
    simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hy2 hz)
  rw [List.filter_append, e1, List.filter_cons_of_pos (by simpa using hxy),
    List.filter_cons_of_neg (by simp), e2]

theorem filter_replace (φ : β → Bool) {m₁ m₂ B : List β} (hB : ∀ z ∈ B, φ z = true) :
    (m₁ ++ B ++ m₂).filter φ = m₁.filter φ ++ B ++ m₂.filter φ := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr hB]

end Lists

/-! ### The outside corners as shifted corners -/

theorem outsideQK_two_eq (t : SignedAdjacentWord m) :
    outsideQK 2 (2 + t.length) = (sCols t).map (fun q => (q.1.val + 2, q.2)) := by
  apply List.ext_getElem
  · rw [outsideQK_length, List.length_map, sCols_length]; omega
  · intro i h1 h2
    rw [outsideQK_getElem, List.getElem_map, sCols_getElem]
    simp only [kc, finProdFinEquiv_symm_apply, Prod.mk.injEq, Fin.divNat, Fin.modNat]
    refine ⟨by omega, Fin.ext ?_⟩
    simp only
    omega

end OnLeConjecture.KnotTheory.MarkedCancel
