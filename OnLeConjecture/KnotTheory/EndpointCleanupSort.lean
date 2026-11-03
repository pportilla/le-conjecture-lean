/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros

/-! # Sorting the rows and the columns of a labeled grid

Let `G` be a labeled grid (`LabeledGrid`) and let `l` be a permutation of its list of rows. Call a
pair of rows `(x, y)` *inverted* if `x` lies below `y` in `G` and above `y` in `l`. If every
inverted pair of rows has non-interleaving segments (`LabeledGrid.RowsNonint`), then the grid of
`G` and the grid with the rows in the order `l` are related by grid moves
(`LabeledGrid.movesTo_withRows_of_inverted`). The proof is an insertion sort: the first row of `l`
is moved down past the rows below it, each of which forms an inverted pair with it, and the
remaining rows are sorted recursively. The columns are treated in the same way
(`LabeledGrid.movesTo_withCols_of_inverted`).

These lemmas are used for the cleanup of the scissor endpoint in the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 10, "The raw scissor endpoint is already this cyclic
grid", and the positioning of the auxiliary blocks). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### Positions in lists after removing one entry -/

section ListIdx

variable {α : Type*} [DecidableEq α]

/-- Removing an entry from a list without duplicates does not change the relative order of the
other entries. -/
theorem idxOf_lt_iff_of_erase_middle {u v : List α} {a x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (u ++ a :: v).idxOf x < (u ++ a :: v).idxOf y ↔ (u ++ v).idxOf x < (u ++ v).idxOf y := by
  rw [LabeledGrid.idxOf_append_cons_of_ne u v a x hx,
    LabeledGrid.idxOf_append_cons_of_ne u v a y hy]
  split_ifs <;> omega

/-- The positions of the entries other than the head of a list. -/
theorem idxOf_lt_iff_cons {l : List α} {a x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (a :: l).idxOf x < (a :: l).idxOf y ↔ l.idxOf x < l.idxOf y := by
  rw [List.idxOf_cons_ne _ (Ne.symm hx), List.idxOf_cons_ne _ (Ne.symm hy)]
  omega

end ListIdx

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

omit [DecidableEq R] in
/-- `RowsNonint` depends only on the columns and the markings. -/
theorem rowsNonint_of_data {G G' : LabeledGrid n C R} (hc : G'.cols = G.cols) (hO : G'.O = G.O)
    (hX : G'.X = G.X) {x y : R} (h : G.RowsNonint x y) : G'.RowsNonint x y := by
  intro a a' b b' ha ha' hb hb' e1 e2 e3 e4
  have hcp : ∀ c, G'.cpos c = G.cpos c := fun c => by simp only [cpos, hc]
  rw [hcp, hcp, hcp, hcp]
  rw [hc] at ha ha' hb hb'
  rw [hO] at e1 e3
  rw [hX] at e2 e4
  exact h a a' b b' ha ha' hb hb' e1 e2 e3 e4

omit [DecidableEq C] in
/-- `ColsNonint` depends only on the rows and the markings. -/
theorem colsNonint_of_data {G G' : LabeledGrid n C R} (hr : G'.rows = G.rows) (hO : G'.O = G.O)
    (hX : G'.X = G.X) {c d : C} (h : G.ColsNonint c d) : G'.ColsNonint c d := by
  have hrp : ∀ r, G'.rpos r = G.rpos r := fun r => by simp only [rpos, hr]
  unfold ColsNonint
  rw [hrp, hrp, hrp, hrp, hO, hX]
  exact h

/-- **Insertion sort of rows, with a fixed prefix.** -/
theorem exists_sortRows_aux (m' : List R) :
    ∀ (G : LabeledGrid n C R) (P m : List R), G.rows = P ++ m → m.Perm m' →
      (∀ x ∈ m, ∀ y ∈ m, m.idxOf x < m.idxOf y → m'.idxOf y < m'.idxOf x → G.RowsNonint x y) →
      ∃ G' : LabeledGrid n C R, G'.cols = G.cols ∧ G'.rows = P ++ m' ∧ G'.O = G.O ∧
        G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  induction m' with
  | nil =>
    intro G P m hr hp _
    have hm : m = [] := List.Perm.eq_nil hp
    subst hm
    exact ⟨G, rfl, by simpa using hr, rfl, rfl, GridDiagram.MovesTo.refl _⟩
  | cons a m'' ih =>
    intro G P m hr hp hni
    have ham : a ∈ m := hp.symm.subset (by simp)
    obtain ⟨u, v, rfl⟩ := List.append_of_mem ham
    have hnd : (P ++ (u ++ a :: v)).Nodup := hr ▸ G.rows_nodup
    have hndm : (u ++ a :: v).Nodup := (List.nodup_append.mp hnd).2.1
    have hau : a ∉ u := fun h => (List.nodup_cons.mp (List.nodup_middle.mp hndm)).1
      (List.mem_append_left _ h)
    have hav : a ∉ v := fun h => (List.nodup_cons.mp (List.nodup_middle.mp hndm)).1
      (List.mem_append_right _ h)
    have hndm' : (a :: m'').Nodup := hp.nodup_iff.mp hndm
    have ham'' : a ∉ m'' := (List.nodup_cons.mp hndm').1
    -- move `a` down past `u`
    have hr' : G.rows = P ++ u ++ a :: v := by rw [hr]; simp
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowDown (m₁ := P) (mid := u) (m₂ := v)
      (x := a) hr' (fun z hz => by
        have hza : z ≠ a := fun h => hau (h ▸ hz)
        refine hni z (by simp [hz]) a (by simp) ?_ ?_
        · rw [List.idxOf_append_of_mem hz, List.idxOf_append_of_notMem hau,
            List.idxOf_cons_self]
          have := List.idxOf_lt_length_iff.mpr hz
          omega
        · rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hza)]
          omega)
    -- sort the rest
    have hp' : (u ++ v).Perm m'' := by
      have h1 : (a :: (u ++ v)).Perm (a :: m'') := (List.perm_middle.symm.trans hp)
      exact (List.perm_cons a).mp h1
    obtain ⟨G', hc', hr'', hO', hX', hm'⟩ := ih G₁ (P ++ [a]) (u ++ v)
      (by rw [hr₁]; simp) hp' (fun x hx y hy hxy hyx => by
        have hxa : x ≠ a := fun h => by
          rcases List.mem_append.mp hx with h' | h'
          · exact hau (h ▸ h')
          · exact hav (h ▸ h')
        have hya : y ≠ a := fun h => by
          rcases List.mem_append.mp hy with h' | h'
          · exact hau (h ▸ h')
          · exact hav (h ▸ h')
        have hxm : x ∈ u ++ a :: v := by
          rcases List.mem_append.mp hx with h' | h' <;> simp [h']
        have hym : y ∈ u ++ a :: v := by
          rcases List.mem_append.mp hy with h' | h' <;> simp [h']
        refine rowsNonint_of_data hc₁ hO₁ hX₁ (hni x hxm y hym ?_ ?_)
        · exact (idxOf_lt_iff_of_erase_middle hxa hya).mpr hxy
        · exact (idxOf_lt_iff_cons hya hxa).mpr hyx)
    exact ⟨G', hc'.trans hc₁, by rw [hr'']; simp, hO'.trans hO₁, hX'.trans hX₁, hm₁.trans hm'⟩

/-- **Sorting the rows.** If every pair of rows whose order differs between `G` and `l` has
non-interleaving segments, then `G` and `G` with the rows in the order `l` are related by grid
moves. -/
theorem movesTo_withRows_of_inverted (G : LabeledGrid n C R) (l : List R) (hl : l.Perm G.rows)
    (hni : ∀ x ∈ G.rows, ∀ y ∈ G.rows, G.rows.idxOf x < G.rows.idxOf y →
      l.idxOf y < l.idxOf x → G.RowsNonint x y) :
    G.toGrid.MovesTo (G.withRows l hl).toGrid := by
  obtain ⟨G', hc, hr, hO, hX, hm⟩ := exists_sortRows_aux l G [] G.rows rfl hl.symm hni
  have he : G'.toGrid = (G.withRows l hl).toGrid := toGrid_eq_of_data _ _ hc
    (by simp only [List.nil_append] at hr; exact hr)
    (fun c _ => congrFun hO c) (fun c _ => congrFun hX c)
  rwa [he] at hm

/-- **Insertion sort of columns, with a fixed prefix.** -/
theorem exists_sortCols_aux (l' : List C) :
    ∀ (G : LabeledGrid n C R) (P l : List C), G.cols = P ++ l → l.Perm l' →
      (∀ c ∈ l, ∀ d ∈ l, l.idxOf c < l.idxOf d → l'.idxOf d < l'.idxOf c → G.ColsNonint c d) →
      ∃ G' : LabeledGrid n C R, G'.cols = P ++ l' ∧ G'.rows = G.rows ∧ G'.O = G.O ∧
        G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  induction l' with
  | nil =>
    intro G P l hc hp _
    have hl : l = [] := List.Perm.eq_nil hp
    subst hl
    exact ⟨G, by simpa using hc, rfl, rfl, rfl, GridDiagram.MovesTo.refl _⟩
  | cons a l'' ih =>
    intro G P l hc hp hni
    have hal : a ∈ l := hp.symm.subset (by simp)
    obtain ⟨u, v, rfl⟩ := List.append_of_mem hal
    have hnd : (P ++ (u ++ a :: v)).Nodup := hc ▸ G.cols_nodup
    have hndl : (u ++ a :: v).Nodup := (List.nodup_append.mp hnd).2.1
    have hau : a ∉ u := fun h => (List.nodup_cons.mp (List.nodup_middle.mp hndl)).1
      (List.mem_append_left _ h)
    have hav : a ∉ v := fun h => (List.nodup_cons.mp (List.nodup_middle.mp hndl)).1
      (List.mem_append_right _ h)
    have hc' : G.cols = P ++ u ++ a :: v := by rw [hc]; simp
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveColLeft (l₁ := P) (mid := u) (l₂ := v)
      (c := a) hc' (fun z hz => by
        have hza : z ≠ a := fun h => hau (h ▸ hz)
        refine hni z (by simp [hz]) a (by simp) ?_ ?_
        · rw [List.idxOf_append_of_mem hz, List.idxOf_append_of_notMem hau,
            List.idxOf_cons_self]
          have := List.idxOf_lt_length_iff.mpr hz
          omega
        · rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hza)]
          omega)
    have hp' : (u ++ v).Perm l'' := by
      have h1 : (a :: (u ++ v)).Perm (a :: l'') := (List.perm_middle.symm.trans hp)
      exact (List.perm_cons a).mp h1
    obtain ⟨G', hc'', hr', hO', hX', hm'⟩ := ih G₁ (P ++ [a]) (u ++ v)
      (by rw [hc₁]; simp) hp' (fun x hx y hy hxy hyx => by
        have hxa : x ≠ a := fun h => by
          rcases List.mem_append.mp hx with h' | h'
          · exact hau (h ▸ h')
          · exact hav (h ▸ h')
        have hya : y ≠ a := fun h => by
          rcases List.mem_append.mp hy with h' | h'
          · exact hau (h ▸ h')
          · exact hav (h ▸ h')
        have hxm : x ∈ u ++ a :: v := by
          rcases List.mem_append.mp hx with h' | h' <;> simp [h']
        have hym : y ∈ u ++ a :: v := by
          rcases List.mem_append.mp hy with h' | h' <;> simp [h']
        refine colsNonint_of_data hr₁ hO₁ hX₁ (hni x hxm y hym ?_ ?_)
        · exact (idxOf_lt_iff_of_erase_middle hxa hya).mpr hxy
        · exact (idxOf_lt_iff_cons hya hxa).mpr hyx)
    exact ⟨G', by rw [hc'']; simp, hr'.trans hr₁, hO'.trans hO₁, hX'.trans hX₁, hm₁.trans hm'⟩

/-- **Sorting the columns.** If every pair of columns whose order differs between `G` and `l` has
non-interleaving segments, then `G` and `G` with the columns in the order `l` are related by grid
moves. -/
theorem movesTo_withCols_of_inverted (G : LabeledGrid n C R) (l : List C) (hl : l.Perm G.cols)
    (hni : ∀ c ∈ G.cols, ∀ d ∈ G.cols, G.cols.idxOf c < G.cols.idxOf d →
      l.idxOf d < l.idxOf c → G.ColsNonint c d) :
    G.toGrid.MovesTo (G.withCols l hl).toGrid := by
  obtain ⟨G', hc, hr, hO, hX, hm⟩ := exists_sortCols_aux l G [] G.cols rfl hl.symm hni
  have he : G'.toGrid = (G.withCols l hl).toGrid := toGrid_eq_of_data _ _
    (by simp only [List.nil_append] at hc; exact hc) hr
    (fun c _ => congrFun hO c) (fun c _ => congrFun hX c)
  rwa [he] at hm

end LabeledGrid

end OnLeConjecture.KnotTheory
