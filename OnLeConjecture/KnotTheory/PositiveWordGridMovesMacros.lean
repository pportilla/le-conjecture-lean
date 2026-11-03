/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesLabeled

/-! # Sequences of moves of labeled grids

This module assembles the elementary moves of `PositiveWordGridMovesLabeled.lean` into longer
sequences.

* `LabeledGrid.exists_moveRowUp`, `LabeledGrid.exists_moveRowDown`: a row passes a list of
  consecutive rows, each of which it does not interleave.
* `LabeledGrid.exists_moveColRight`, `LabeledGrid.exists_moveColLeft`: the same for columns.
* `LabeledGrid.rowsNonint_of_short`, `LabeledGrid.nonintN_cols_of_short`: a row (column) whose
  markings lie in consecutive columns (rows) does not interleave any row (column) without
  markings there.
* `LabeledGrid.exists_mergeX`, `LabeledGrid.exists_mergeO`: a row whose two markings lie in
  consecutive columns is moved next to the other row of one of these columns, and the corner is
  removed by a destabilization.

The results produce a labeled grid with prescribed lists and markings, related to the original
one by grid moves. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

omit [DecidableEq C] in
/-- Labeled grids with the same lists and the same markings on the columns have the same grid. -/
theorem toGrid_eq_of_data (G G' : LabeledGrid n C R) (hc : G.cols = G'.cols)
    (hr : G.rows = G'.rows) (hO : ∀ c ∈ G.cols, G.O c = G'.O c)
    (hX : ∀ c ∈ G.cols, G.X c = G'.X c) : G.toGrid = G'.toGrid := by
  have hcol : ∀ i, G.colAt i = G'.colAt i := fun i => by
    rw [G.colAt_eq_of_cols hc]; rfl
  have hrp : ∀ r, G.rpos r = G'.rpos r := fun r => by
    simp only [rpos, hr]
  apply toGrid_eq_of_incidence
  · intro i; rw [hO _ (G.colAt_mem i), hrp, hcol]
  · intro i; rw [hX _ (G.colAt_mem i), hrp, hcol]

omit [DecidableEq C] [DecidableEq R] in
/-- Every row label carries an `O`-marking. -/
theorem exists_O_eq (G : LabeledGrid n C R) {r : R} (hr : r ∈ G.rows) :
    ∃ c ∈ G.cols, G.O c = r := by
  have hnd : (G.cols.map G.O).Nodup :=
    List.Nodup.map_on (fun a ha b hb h => G.O_inj a ha b hb h) G.cols_nodup
  have hsub : (G.cols.map G.O).Subperm G.rows :=
    hnd.subperm fun x hx => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact G.O_mem c hc
  have hperm := hsub.perm_of_length_le (by rw [List.length_map, G.cols_length, G.rows_length])
  obtain ⟨c, hc, he⟩ := List.mem_map.mp (hperm.symm.subset hr)
  exact ⟨c, hc, he⟩

omit [DecidableEq C] [DecidableEq R] in
/-- Every row label carries an `X`-marking. -/
theorem exists_X_eq (G : LabeledGrid n C R) {r : R} (hr : r ∈ G.rows) :
    ∃ c ∈ G.cols, G.X c = r := by
  obtain ⟨c, hc, he⟩ := G.swapMarks.exists_O_eq (r := r) hr
  exact ⟨c, hc, he⟩

/-- Two rows have non-interleaving segments, expressed through the columns of their markings. -/
def RowsNonint (G : LabeledGrid n C R) (x z : R) : Prop :=
  ∀ cx cx' cz cz', cx ∈ G.cols → cx' ∈ G.cols → cz ∈ G.cols → cz' ∈ G.cols →
    G.O cx = x → G.X cx' = x → G.O cz = z → G.X cz' = z →
      NonintN (G.cpos cx) (G.cpos cx') (G.cpos cz) (G.cpos cz')

/-- Two columns have non-interleaving segments. -/
def ColsNonint (G : LabeledGrid n C R) (c d : C) : Prop :=
  NonintN (G.rpos (G.O c)) (G.rpos (G.X c)) (G.rpos (G.O d)) (G.rpos (G.X d))

omit [DecidableEq R] in
/-- A row whose markings lie in consecutive columns does not interleave any other row without
markings in these columns. -/
theorem rowsNonint_of_short (G : LabeledGrid n C R) {x z : R} {cx cx' : C}
    (hcx : cx ∈ G.cols) (hcx' : cx' ∈ G.cols) (hOx : G.O cx = x) (hXx : G.X cx' = x)
    (hadj : G.cpos cx' = G.cpos cx + 1 ∨ G.cpos cx = G.cpos cx' + 1)
    (hz1 : z ≠ x) (hz2 : z ≠ G.O cx') (hz3 : z ≠ G.X cx) : G.RowsNonint x z := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  have e1 : a = cx := G.O_inj a ha cx hcx (hOa.trans hOx.symm)
  have e2 : a' = cx' := G.X_inj a' ha' cx' hcx' (hXa.trans hXx.symm)
  subst e1 e2
  have hb1 : b ≠ a := fun he => hz1 (by rw [← hOb, he, hOa])
  have hb2 : b ≠ a' := fun he => hz2 (by rw [← hOb, he])
  have hb'1 : b' ≠ a := fun he => hz3 (by rw [← hXb, he])
  have hb'2 : b' ≠ a' := fun he => hz1 (by rw [← hXb, he, hXa])
  refine nonintN_of_adjacent hadj ⟨fun he => hb1 (G.cpos_inj hb he),
    fun he => hb2 (G.cpos_inj hb he)⟩ ⟨fun he => hb'1 (G.cpos_inj hb' he),
    fun he => hb'2 (G.cpos_inj hb' he)⟩

omit [DecidableEq C] in
/-- A column whose markings lie in consecutive rows does not interleave any column without
markings in these rows. -/
theorem colsNonint_of_short (G : LabeledGrid n C R) {c d : C} (hc : c ∈ G.cols)
    (hd : d ∈ G.cols)
    (hadj : G.rpos (G.X c) = G.rpos (G.O c) + 1 ∨ G.rpos (G.O c) = G.rpos (G.X c) + 1)
    (h1 : G.O d ≠ G.O c) (h2 : G.O d ≠ G.X c) (h3 : G.X d ≠ G.O c) (h4 : G.X d ≠ G.X c) :
    G.ColsNonint c d := by
  have hO := G.O_mem c hc
  have hX := G.X_mem c hc
  refine nonintN_of_adjacent hadj ⟨fun he => h1 ?_, fun he => h2 ?_⟩
    ⟨fun he => h3 ?_, fun he => h4 ?_⟩
  · exact (G.rpos_inj (G.O_mem d hd) he).trans rfl
  · exact G.rpos_inj (G.O_mem d hd) he
  · exact G.rpos_inj (G.X_mem d hd) he
  · exact G.rpos_inj (G.X_mem d hd) he

/-- **Moving a row up.** A row passes a list of rows above it, provided that it does not
interleave any of them. -/
theorem exists_moveRowUp (G : LabeledGrid n C R) {m₁ mid m₂ : List R} {x : R}
    (h : G.rows = m₁ ++ x :: (mid ++ m₂)) (hni : ∀ z ∈ mid, G.RowsNonint x z) :
    ∃ G' : LabeledGrid n C R, G'.cols = G.cols ∧ G'.rows = m₁ ++ mid ++ x :: m₂ ∧
      G'.O = G.O ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  induction mid generalizing G m₁ with
  | nil => exact ⟨G, rfl, by simpa using h, rfl, rfl, GridDiagram.MovesTo.refl _⟩
  | cons z mid ih =>
    have h' : G.rows = m₁ ++ x :: z :: (mid ++ m₂) := by simpa using h
    have hxm : x ∈ G.rows := by rw [h']; simp
    have hzm : z ∈ G.rows := by rw [h']; simp
    obtain ⟨cx, hcx, hOx⟩ := G.exists_O_eq hxm
    obtain ⟨cx', hcx', hXx⟩ := G.exists_X_eq hxm
    obtain ⟨cz, hcz, hOz⟩ := G.exists_O_eq hzm
    obtain ⟨cz', hcz', hXz⟩ := G.exists_X_eq hzm
    have hm1 := G.movesTo_swapRows h' hcx hcx' hcz hcz' hOx hXx hOz hXz
      (hni z (by simp) _ _ _ _ hcx hcx' hcz hcz' hOx hXx hOz hXz)
    set G₁ := G.swapRows h'
    have h₁ : G₁.rows = (m₁ ++ [z]) ++ x :: (mid ++ m₂) := by
      rw [swapRows_rows]; simp
    obtain ⟨G', hc', hr', hO', hX', hm'⟩ := ih G₁ h₁ (fun z' hz' => by
      intro a a' b b' ha ha' hb hb' e1 e2 e3 e4
      exact hni z' (by simp [hz']) a a' b b' ha ha' hb hb' e1 e2 e3 e4)
    exact ⟨G', hc', by rw [hr']; simp, hO', hX', hm1.trans hm'⟩

omit [DecidableEq R] in
theorem rowsNonint_comm (G : LabeledGrid n C R) {x z : R} :
    G.RowsNonint x z ↔ G.RowsNonint z x := by
  constructor <;> intro h a a' b b' ha ha' hb hb' e1 e2 e3 e4 <;>
    exact nonintN_comm.mp (h b b' a a' hb hb' ha ha' e3 e4 e1 e2)

/-- **Moving a row down.** A row passes a list of rows below it, provided that it does not
interleave any of them. -/
theorem exists_moveRowDown (G : LabeledGrid n C R) {m₁ mid m₂ : List R} {x : R}
    (h : G.rows = m₁ ++ mid ++ x :: m₂) (hni : ∀ z ∈ mid, G.RowsNonint z x) :
    ∃ G' : LabeledGrid n C R, G'.cols = G.cols ∧ G'.rows = m₁ ++ x :: (mid ++ m₂) ∧
      G'.O = G.O ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  have hp : (m₁ ++ x :: (mid ++ m₂)).Perm G.rows := by
    rw [h]
    simpa using (List.perm_middle (a := x) (l₁ := mid) (l₂ := m₂)).symm.append_left m₁
  set G' := G.withRows (m₁ ++ x :: (mid ++ m₂)) hp
  obtain ⟨G'', h1, h2, h3, h4, h5⟩ := G'.exists_moveRowUp (m₁ := m₁) (mid := mid) (m₂ := m₂)
    (x := x) rfl (fun z hz => (G'.rowsNonint_comm).mpr (hni z hz))
  have he : G''.toGrid = G.toGrid := toGrid_eq_of_data _ _ (h1.trans rfl)
    (by rw [h2, h]) (fun c _ => congrFun h3 c) (fun c _ => congrFun h4 c)
  rw [he] at h5
  exact ⟨G', rfl, rfl, rfl, rfl, h5.symm⟩

omit [DecidableEq C] in
/-- **Moving a column right.** A column passes a list of columns to its right, provided that it
does not interleave any of them. -/
theorem exists_moveColRight (G : LabeledGrid n C R) {l₁ mid l₂ : List C} {c : C}
    (h : G.cols = l₁ ++ c :: (mid ++ l₂)) (hni : ∀ d ∈ mid, G.ColsNonint c d) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ mid ++ c :: l₂ ∧ G'.rows = G.rows ∧
      G'.O = G.O ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  induction mid generalizing G l₁ with
  | nil => exact ⟨G, by simpa using h, rfl, rfl, rfl, GridDiagram.MovesTo.refl _⟩
  | cons d mid ih =>
    have h' : G.cols = l₁ ++ c :: d :: (mid ++ l₂) := by simpa using h
    have hm1 := G.movesTo_swapCols h' (hni d (by simp))
    set G₁ := G.swapCols h'
    have h₁ : G₁.cols = (l₁ ++ [d]) ++ c :: (mid ++ l₂) := by
      rw [swapCols_cols]; simp
    obtain ⟨G', hc', hr', hO', hX', hm'⟩ := ih G₁ h₁ (fun d' hd' => hni d' (by simp [hd']))
    exact ⟨G', by rw [hc']; simp, hr', hO', hX', hm1.trans hm'⟩

omit [DecidableEq C] in
theorem colsNonint_comm (G : LabeledGrid n C R) {c d : C} :
    G.ColsNonint c d ↔ G.ColsNonint d c := nonintN_comm

omit [DecidableEq C] in
/-- **Moving a column left.** A column passes a list of columns to its left, provided that it
does not interleave any of them. -/
theorem exists_moveColLeft (G : LabeledGrid n C R) {l₁ mid l₂ : List C} {c : C}
    (h : G.cols = l₁ ++ mid ++ c :: l₂) (hni : ∀ d ∈ mid, G.ColsNonint d c) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ c :: (mid ++ l₂) ∧ G'.rows = G.rows ∧
      G'.O = G.O ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  have hp : (l₁ ++ c :: (mid ++ l₂)).Perm G.cols := by
    rw [h]
    simpa using (List.perm_middle (a := c) (l₁ := mid) (l₂ := l₂)).symm.append_left l₁
  set G' := G.withCols (l₁ ++ c :: (mid ++ l₂)) hp
  obtain ⟨G'', h1, h2, h3, h4, h5⟩ := G'.exists_moveColRight (l₁ := l₁) (mid := mid) (l₂ := l₂)
    (c := c) rfl (fun d hd => (G'.colsNonint_comm).mpr (hni d hd))
  have he : G''.toGrid = G.toGrid := toGrid_eq_of_data _ _ (by rw [h1, h])
    (h2.trans rfl) (fun c _ => congrFun h3 c) (fun c _ => congrFun h4 c)
  rw [he] at h5
  exact ⟨G', rfl, rfl, rfl, rfl, h5.symm⟩


omit [DecidableEq R] in
/-- Positions of two consecutive columns. -/
theorem cpos_adj_of_cols (G : LabeledGrid n C R) {l₁ l₂ : List C} {c d : C}
    (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂) :
    G.cpos d = G.cpos c + 1 ∨ G.cpos c = G.cpos d + 1 := by
  rcases hcols with h | h
  · left
    rw [G.cpos_of_cols_eq h, G.cpos_of_cols_eq (l₁ := l₁ ++ [c]) (l₂ := l₂) (by rw [h]; simp)]
    simp
  · right
    rw [G.cpos_of_cols_eq h, G.cpos_of_cols_eq (l₁ := l₁ ++ [d]) (l₂ := l₂) (by rw [h]; simp)]
    simp

omit [DecidableEq C] in
theorem rpos_succ_of_rows (G : LabeledGrid n C R) {m₁ m₂ : List R} {x y : R}
    (h : G.rows = m₁ ++ x :: y :: m₂) : G.rpos y = G.rpos x + 1 := by
  rw [G.rpos_of_rows_eq h, G.rpos_of_rows_eq (m₁ := m₁ ++ [x]) (m₂ := m₂) (by rw [h]; simp)]
  simp

omit [DecidableEq C] [DecidableEq R] in
theorem cols_split_of_adj (G : LabeledGrid n C R) {l₁ l₂ : List C} {c d : C}
    (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂) :
    ∃ L₁ L₂, G.cols = L₁ ++ c :: L₂ ∧ L₁ ++ L₂ = l₁ ++ d :: l₂ := by
  rcases hcols with h | h
  · exact ⟨l₁, d :: l₂, h, rfl⟩
  · exact ⟨l₁ ++ [d], l₂, by rw [h]; simp, by simp⟩

/-- **Merging upward, `X` version.** The row `e = O c = X d` lies in the consecutive columns
`c, d`; it is moved up past the rows `mid`, none of which is `O d`, to the row `z = X c`, and the
corner is removed by an `X`-destabilization. -/
theorem exists_mergeX_up (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ mid m₂ : List R}
    {c d : C} {e z : R} (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂)
    (hrows : G.rows = m₁ ++ e :: (mid ++ z :: m₂)) (hOc : G.O c = e) (hXc : G.X c = z)
    (hXd : G.X d = e) (hOd : G.O d ≠ z) (hmid : ∀ r ∈ mid, r ≠ G.O d) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ d :: l₂ ∧ G'.rows = m₁ ++ mid ++ z :: m₂ ∧
      G'.O = G.O ∧ G'.X = Function.update G.X d z ∧ G.toGrid.MovesTo G'.toGrid := by
  have hcm : c ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hdm : d ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hnd := G.rows_nodup
  rw [hrows] at hnd
  have heM : e ∉ mid := by
    intro hm; have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp [hm] at this
  have hzM : z ∉ mid := by
    intro hm
    have h2 := (List.nodup_append.mp hnd).2.1
    have h3 := (List.nodup_cons.mp h2).2
    have h4 := (List.nodup_append.mp h3).2.2
    exact h4 z hm z (by simp) rfl
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowUp (x := e) (mid := mid)
    (m₂ := z :: m₂) hrows (fun r hr => G.rowsNonint_of_short hcm hdm hOc hXd
      (G.cpos_adj_of_cols hcols) (fun he => heM (he ▸ hr)) (hmid r hr)
      (fun he => hzM (by rw [hXc] at he; exact he ▸ hr)))
  obtain ⟨L₁, L₂, hL, hLe⟩ := G₁.cols_split_of_adj (hc₁ ▸ hcols)
  have hx₁ : G₁.rows = (m₁ ++ mid) ++ e :: (z :: m₂) := by rw [hr₁]
  have hD := G₁.isDestabilization_destabX hL hx₁ (by rw [hO₁, hOc]) (by rw [hX₁, hXc])
    (by rw [hX₁, hXd]) (by rw [hO₁]; exact hOd) (by rw [hc₁]; exact hdm)
    (by have := G₁.cpos_adj_of_cols (hc₁ ▸ hcols); omega)
    (Or.inl (G₁.rpos_succ_of_rows hx₁))
  refine ⟨_, by rw [destabX_cols, hLe], by rw [destabX_rows], by rw [destabX_O, hO₁],
    by rw [destabX_X, hX₁], hm₁.trans hD.movesTo⟩

/-- **Merging downward, `X` version.** As `exists_mergeX_up`, with the row `z = X c` below `e`. -/
theorem exists_mergeX_down (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ mid m₂ : List R}
    {c d : C} {e z : R} (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂)
    (hrows : G.rows = m₁ ++ z :: (mid ++ e :: m₂)) (hOc : G.O c = e) (hXc : G.X c = z)
    (hXd : G.X d = e) (hOd : G.O d ≠ z) (hmid : ∀ r ∈ mid, r ≠ G.O d) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ d :: l₂ ∧ G'.rows = m₁ ++ z :: (mid ++ m₂) ∧
      G'.O = G.O ∧ G'.X = Function.update G.X d z ∧ G.toGrid.MovesTo G'.toGrid := by
  have hcm : c ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hdm : d ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hnd := G.rows_nodup
  rw [hrows] at hnd
  have h2 := (List.nodup_append.mp hnd).2.1
  have hzM : z ∉ mid := by
    intro hm; have := (List.nodup_cons.mp h2).1; simp [hm] at this
  have heM : e ∉ mid := by
    intro hm
    have h3 := (List.nodup_cons.mp h2).2
    have h4 := (List.nodup_append.mp h3).2.2
    exact h4 e hm e (by simp) rfl
  have hrows' : G.rows = (m₁ ++ [z]) ++ mid ++ e :: m₂ := by rw [hrows]; simp
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowDown (x := e) hrows'
    (fun r hr => (G.rowsNonint_comm).mp (G.rowsNonint_of_short hcm hdm hOc hXd
      (G.cpos_adj_of_cols hcols) (fun he => heM (he ▸ hr)) (hmid r hr)
      (fun he => hzM (by rw [hXc] at he; exact he ▸ hr))))
  obtain ⟨L₁, L₂, hL, hLe⟩ := G₁.cols_split_of_adj (hc₁ ▸ hcols)
  have hx₁ : G₁.rows = (m₁ ++ [z]) ++ e :: (mid ++ m₂) := by rw [hr₁]
  have hD := G₁.isDestabilization_destabX hL hx₁ (by rw [hO₁, hOc]) (by rw [hX₁, hXc])
    (by rw [hX₁, hXd]) (by rw [hO₁]; exact hOd) (by rw [hc₁]; exact hdm)
    (by have := G₁.cpos_adj_of_cols (hc₁ ▸ hcols); omega)
    (Or.inr (G₁.rpos_succ_of_rows (m₁ := m₁) (m₂ := mid ++ m₂) (by rw [hx₁]; simp)))
  refine ⟨_, by rw [destabX_cols, hLe], by rw [destabX_rows]; simp, by rw [destabX_O, hO₁],
    by rw [destabX_X, hX₁], hm₁.trans hD.movesTo⟩

/-- **Merging upward, `O` version.** The row `e = X c = O d` lies in the consecutive columns
`c, d`; it is moved up past the rows `mid`, none of which is `X d`, to the row `z = O c`, and the
corner is removed by an `O`-destabilization. -/
theorem exists_mergeO_up (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ mid m₂ : List R}
    {c d : C} {e z : R} (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂)
    (hrows : G.rows = m₁ ++ e :: (mid ++ z :: m₂)) (hXc : G.X c = e) (hOc : G.O c = z)
    (hOd : G.O d = e) (hXd : G.X d ≠ z) (hmid : ∀ r ∈ mid, r ≠ G.X d) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ d :: l₂ ∧ G'.rows = m₁ ++ mid ++ z :: m₂ ∧
      G'.O = Function.update G.O d z ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  have hcm : c ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hdm : d ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hnd := G.rows_nodup
  rw [hrows] at hnd
  have heM : e ∉ mid := by
    intro hm; have := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1; simp [hm] at this
  have hzM : z ∉ mid := by
    intro hm
    have h2 := (List.nodup_append.mp hnd).2.1
    have h3 := (List.nodup_cons.mp h2).2
    have h4 := (List.nodup_append.mp h3).2.2
    exact h4 z hm z (by simp) rfl
  have hadj := G.cpos_adj_of_cols hcols
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowUp (x := e) (mid := mid)
    (m₂ := z :: m₂) hrows (fun r hr => G.rowsNonint_of_short hdm hcm hOd hXc
      (by omega) (fun he => heM (he ▸ hr))
      (fun he => hzM (by rw [hOc] at he; exact he ▸ hr)) (hmid r hr))
  obtain ⟨L₁, L₂, hL, hLe⟩ := G₁.cols_split_of_adj (hc₁ ▸ hcols)
  have hx₁ : G₁.rows = (m₁ ++ mid) ++ e :: (z :: m₂) := by rw [hr₁]
  have hD := G₁.isDestabilization_destabO hL hx₁ (by rw [hX₁, hXc]) (by rw [hO₁, hOc])
    (by rw [hO₁, hOd]) (by rw [hX₁]; exact hXd) (by rw [hc₁]; exact hdm)
    (by have := G₁.cpos_adj_of_cols (hc₁ ▸ hcols); omega)
    (Or.inl (G₁.rpos_succ_of_rows hx₁))
  refine ⟨_, by rw [destabO_cols, hLe], by rw [destabO_rows], by rw [destabO_O, hO₁],
    by rw [destabO_X, hX₁], hm₁.trans hD.movesTo⟩

/-- **Merging downward, `O` version.** As `exists_mergeO_up`, with the row `z = O c` below `e`. -/
theorem exists_mergeO_down (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C} {m₁ mid m₂ : List R}
    {c d : C} {e z : R} (hcols : G.cols = l₁ ++ c :: d :: l₂ ∨ G.cols = l₁ ++ d :: c :: l₂)
    (hrows : G.rows = m₁ ++ z :: (mid ++ e :: m₂)) (hXc : G.X c = e) (hOc : G.O c = z)
    (hOd : G.O d = e) (hXd : G.X d ≠ z) (hmid : ∀ r ∈ mid, r ≠ G.X d) :
    ∃ G' : LabeledGrid n C R, G'.cols = l₁ ++ d :: l₂ ∧ G'.rows = m₁ ++ z :: (mid ++ m₂) ∧
      G'.O = Function.update G.O d z ∧ G'.X = G.X ∧ G.toGrid.MovesTo G'.toGrid := by
  have hcm : c ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hdm : d ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  have hnd := G.rows_nodup
  rw [hrows] at hnd
  have h2 := (List.nodup_append.mp hnd).2.1
  have hzM : z ∉ mid := by
    intro hm; have := (List.nodup_cons.mp h2).1; simp [hm] at this
  have heM : e ∉ mid := by
    intro hm
    have h3 := (List.nodup_cons.mp h2).2
    have h4 := (List.nodup_append.mp h3).2.2
    exact h4 e hm e (by simp) rfl
  have hadj := G.cpos_adj_of_cols hcols
  have hrows' : G.rows = (m₁ ++ [z]) ++ mid ++ e :: m₂ := by rw [hrows]; simp
  obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hm₁⟩ := G.exists_moveRowDown (x := e) hrows'
    (fun r hr => (G.rowsNonint_comm).mp (G.rowsNonint_of_short hdm hcm hOd hXc
      (by omega) (fun he => heM (he ▸ hr))
      (fun he => hzM (by rw [hOc] at he; exact he ▸ hr)) (hmid r hr)))
  obtain ⟨L₁, L₂, hL, hLe⟩ := G₁.cols_split_of_adj (hc₁ ▸ hcols)
  have hx₁ : G₁.rows = (m₁ ++ [z]) ++ e :: (mid ++ m₂) := by rw [hr₁]
  have hD := G₁.isDestabilization_destabO hL hx₁ (by rw [hX₁, hXc]) (by rw [hO₁, hOc])
    (by rw [hO₁, hOd]) (by rw [hX₁]; exact hXd) (by rw [hc₁]; exact hdm)
    (by have := G₁.cpos_adj_of_cols (hc₁ ▸ hcols); omega)
    (Or.inr (G₁.rpos_succ_of_rows (m₁ := m₁) (m₂ := mid ++ m₂) (by rw [hx₁]; simp)))
  refine ⟨_, by rw [destabO_cols, hLe], by rw [destabO_rows]; simp, by rw [destabO_O, hO₁],
    by rw [destabO_X, hX₁], hm₁.trans hD.movesTo⟩

end LabeledGrid

end OnLeConjecture.KnotTheory
