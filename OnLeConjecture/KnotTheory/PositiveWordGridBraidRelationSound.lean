/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridBraidRelationReal

/-! # Soundness of the local moves

`docs/route-n/J09-word-grid-moves.tex`, Lemma *soundness*: if a labeled grid realizes a window
state `S` and `step S m = some S'`, then grid moves lead to a labeled grid realizing `S'`, with the
same outside columns and markings and the same order of connecting and external rows
(`BraidWindow.step_sound`, `BraidWindow.run_sound`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.BraidWindow

open TauCeti

/-! ### Lists -/

section Lists

variable {α : Type*}

theorem swapAt_decomp {l : List α} {t : ℕ} (h : t + 1 < l.length) :
    ∃ l₁ a b l₂, l = l₁ ++ a :: b :: l₂ ∧ l₁.length = t ∧ swapAt l t = l₁ ++ b :: a :: l₂ := by
  induction t generalizing l with
  | zero =>
    match l, h with
    | a :: b :: l₂, _ => exact ⟨[], a, b, l₂, rfl, rfl, rfl⟩
  | succ t ih =>
    match l, h with
    | c :: l, h =>
      obtain ⟨l₁, a, b, l₂, h1, h2, h3⟩ := ih (l := l) (by simp at h; omega)
      exact ⟨c :: l₁, a, b, l₂, by rw [h1]; rfl, by simp [h2], by simp [swapAt, h3]⟩

theorem decomp_at {l : List α} {t : ℕ} (h : t < l.length) :
    l = l.take t ++ l[t] :: l.drop (t + 1) := by
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem decomp_at₂ {l : List α} {t : ℕ} (h : t + 1 < l.length) :
    l = l.take t ++ l[t] :: l[t + 1] :: l.drop (t + 2) := by
  rw [List.cons_getElem_drop_succ, List.cons_getElem_drop_succ, List.take_append_drop]

theorem set_eraseIdx_of_succ {l₁ l₂ : List α} {a b v : α} :
    ((l₁ ++ a :: b :: l₂).set (l₁.length + 1) v).eraseIdx l₁.length = l₁ ++ v :: l₂ := by
  rw [List.set_append_right _ _ (by omega), show l₁.length + 1 - l₁.length = 1 by omega]
  simp [List.eraseIdx_append_of_length_le]

theorem set_eraseIdx_of_pred {l₁ l₂ : List α} {a b v : α} :
    ((l₁ ++ a :: b :: l₂).set l₁.length v).eraseIdx (l₁.length + 1) = l₁ ++ v :: l₂ := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self]
  simp [List.eraseIdx_append_of_length_le]

theorem insertIdx_append_len {l₁ l : List α} {i : ℕ} {w : α} :
    (l₁ ++ l).insertIdx (l₁.length + i) w = l₁ ++ l.insertIdx i w := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [List.length_cons, show l₁.length + 1 + i = (l₁.length + i) + 1 by omega, List.cons_append,
      List.insertIdx_succ_cons, ih, List.cons_append]

theorem set_insertIdx_right {l₁ l₂ : List α} {a v w : α} :
    ((l₁ ++ a :: l₂).set l₁.length v).insertIdx (l₁.length + 1) w = l₁ ++ v :: w :: l₂ := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, insertIdx_append_len]
  simp

theorem set_insertIdx_left {l₁ l₂ : List α} {a v w : α} :
    ((l₁ ++ a :: l₂).set l₁.length v).insertIdx l₁.length w = l₁ ++ w :: v :: l₂ := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self]
  have := insertIdx_append_len (l₁ := l₁) (l := v :: l₂) (i := 0) (w := w)
  simpa using this

theorem eraseIdx_mid {l₁ l₂ : List α} {a b : α} :
    (l₁ ++ a :: b :: l₂).eraseIdx l₁.length = l₁ ++ b :: l₂ := by
  simp [List.eraseIdx_append_of_length_le]

theorem eraseIdx_mid' {l₁ l₂ : List α} {a b : α} :
    (l₁ ++ a :: b :: l₂).eraseIdx (l₁.length + 1) = l₁ ++ a :: l₂ := by
  simp [List.eraseIdx_append_of_length_le]

theorem set_insertIdx_right' {l₁ l₂ : List α} {a v w : α} {i : ℕ} (h : l₁.length = i) :
    ((l₁ ++ a :: l₂).set i v).insertIdx (i + 1) w = l₁ ++ v :: w :: l₂ := by
  subst h; exact set_insertIdx_right

theorem set_insertIdx_left' {l₁ l₂ : List α} {a v w : α} {i : ℕ} (h : l₁.length = i) :
    ((l₁ ++ a :: l₂).set i v).insertIdx i w = l₁ ++ w :: v :: l₂ := by
  subst h; exact set_insertIdx_left

theorem filter_ins_after (p : α → Bool) {M₁ M₂ : List α} {a b : α} (hp : p b = false) :
    (M₁ ++ a :: b :: M₂).filter p = (M₁ ++ a :: M₂).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

theorem filter_ins_before (p : α → Bool) {M₁ M₂ : List α} {a b : α} (hp : p b = false) :
    (M₁ ++ b :: a :: M₂).filter p = (M₁ ++ a :: M₂).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

end Lists

theorem countEq_four {k a b c d : ℕ} (h : countEq k [a, b, c, d] ≤ 1) :
    ¬(a = k ∧ b = k) ∧ ¬(a = k ∧ c = k) ∧ ¬(a = k ∧ d = k) ∧ ¬(b = k ∧ c = k) ∧
      ¬(b = k ∧ d = k) ∧ ¬(c = k ∧ d = k) := by
  simp only [countEq, List.filter_cons, List.filter_nil, beq_iff_eq] at h
  split_ifs at h <;> simp at h <;> omega

theorem cmp_agree {k v₁ v₁' v₂ v₂' : ℕ} (h₁ : (v₁' < k ∧ v₁ = v₁') ∨ (v₁' = k ∧ k ≤ v₁))
    (h₂ : (v₂' < k ∧ v₂ = v₂') ∨ (v₂' = k ∧ k ≤ v₂)) (hk : ¬(v₁' = k ∧ v₂' = k)) :
    v₁ < v₂ ↔ v₁' < v₂' := by
  omega

namespace Real

variable {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ} {Q : List (ℕ × Fin 3)}

theorem rows_nodup (hG : Real S G W Q) : S.rows.Nodup := by
  rw [← hG.rows]
  exact G.rows_nodup.filterMap fun a a' b ha ha' => by
    rcases a with a | a <;> rcases a' with a' | a' <;> simp at ha ha' <;> subst ha <;> simp_all

theorem mem_of_O (hG : Real S G W Q) {c : BCol} (hc : c ∈ G.cols) {z : ℕ}
    (h : G.O c = Sum.inl z) : z ∈ S.rows := by
  rw [← hG.mem_rows, ← h]; exact G.O_mem c hc

theorem mem_of_X (hG : Real S G W Q) {c : BCol} (hc : c ∈ G.cols) {z : ℕ}
    (h : G.X c = Sum.inl z) : z ∈ S.rows := by
  rw [← hG.mem_rows, ← h]; exact G.X_mem c hc

/-- `NonintN` of four window rows in `G` and in the model. -/
theorem nonintN_rows (hG : Real S G W Q) {u₁ u₂ u₃ u₄ : ℕ} (h₁ : u₁ ∈ S.rows) (h₂ : u₂ ∈ S.rows)
    (h₃ : u₃ ∈ S.rows) (h₄ : u₄ ∈ S.rows) :
    NonintN (G.rpos (Sum.inl u₁)) (G.rpos (Sum.inl u₂)) (G.rpos (Sum.inl u₃))
      (G.rpos (Sum.inl u₄)) ↔ NonintN (S.ri u₁) (S.ri u₂) (S.ri u₃) (S.ri u₄) :=
  nonintN_congr (hG.rpos_lt_iff h₁ h₂) (hG.rpos_lt_iff h₂ h₁) (hG.rpos_lt_iff h₁ h₃)
    (hG.rpos_lt_iff h₃ h₁) (hG.rpos_lt_iff h₁ h₄) (hG.rpos_lt_iff h₄ h₁) (hG.rpos_lt_iff h₂ h₃)
    (hG.rpos_lt_iff h₃ h₂) (hG.rpos_lt_iff h₂ h₄) (hG.rpos_lt_iff h₄ h₂) (hG.rpos_lt_iff h₃ h₄)
    (hG.rpos_lt_iff h₄ h₃)

/-- Two rows consecutive among the window rows are separated in `G` by external rows only. -/
theorem split_adj (hG : Real S G W Q) {x y : ℕ} (hx : x ∈ S.rows) (hy : y ∈ S.rows)
    (hri : S.ri y = S.ri x + 1) :
    ∃ M₁ E M₂, G.rows = M₁ ++ Sum.inl x :: (E ++ Sum.inl y :: M₂) ∧ ∀ z, Sum.inl z ∉ E := by
  have hlt : G.rpos (Sum.inl x) < G.rpos (Sum.inl y) := (hG.rpos_lt_iff hx hy).mpr (by omega)
  obtain ⟨M₁, E, M₂, hsplit⟩ := exists_split_of_idxOf_lt ((hG.mem_rows).mpr hx)
    ((hG.mem_rows).mpr hy) hlt
  refine ⟨M₁, E, M₂, hsplit, fun z hz => ?_⟩
  have hb := idxOf_mid_bounds' G.rows_nodup hsplit hz
  have hzS : z ∈ S.rows := (hG.mem_rows).mp (by rw [hsplit]; simp [hz])
  have h1 := (hG.rpos_lt_iff hx hzS).mp hb.1
  have h2 := (hG.rpos_lt_iff hzS hy).mp hb.2
  omega

/-- An internal row does not interleave an external row. -/
theorem rowsNonint_int_ext (hG : Real S G W Q) {x : ℕ} (hxO : S.pO x < W.length)
    (hxX : S.pX x < W.length) (e : ℕ × Fin 3) : G.RowsNonint (Sum.inl x) (Sum.inr e) := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  have h1 := hG.O_col ha hOa
  have h2 := hG.X_col ha' hXa
  have h3 := hG.cpos_q (hG.col_of_inr hb (Or.inl hOb))
  have h4 := hG.cpos_q (hG.col_of_inr hb' (Or.inr hXb))
  apply nonintN_of_lt; left
  simp only [max_lt_iff, lt_min_iff]; omega

/-- Non-interleaving of two window rows from the model, when at most one marking is outside. -/
theorem rowsNonint_of_model (hG : Real S G W Q) {x y : ℕ}
    (hc : countEq S.cols.length [S.pO x, S.pX x, S.pO y, S.pX y] ≤ 1)
    (hni : NonintN (S.pO x) (S.pX x) (S.pO y) (S.pX y)) : G.RowsNonint (Sum.inl x) (Sum.inl y) := by
  intro a a' b b' ha ha' hb hb' hOa hXa hOb hXb
  have h1 := hG.O_col ha hOa
  have h2 := hG.X_col ha' hXa
  have h3 := hG.O_col hb hOb
  have h4 := hG.X_col hb' hXb
  rw [← hG.len] at hc
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := countEq_four hc
  have sw : ∀ {p q : Prop}, ¬(p ∧ q) → ¬(q ∧ p) := fun h hqp => h ⟨hqp.2, hqp.1⟩
  rw [nonintN_congr (a' := S.pO x) (b' := S.pX x) (c' := S.pO y) (d' := S.pX y)
    (cmp_agree h1 h2 k1) (cmp_agree h2 h1 (sw k1)) (cmp_agree h1 h3 k2) (cmp_agree h3 h1 (sw k2))
    (cmp_agree h1 h4 k3) (cmp_agree h4 h1 (sw k3)) (cmp_agree h2 h3 k4) (cmp_agree h3 h2 (sw k4))
    (cmp_agree h2 h4 k5) (cmp_agree h4 h2 (sw k5)) (cmp_agree h3 h4 k6) (cmp_agree h4 h3 (sw k6))]
  exact hni

end Real

/-! ### The column exchange -/

theorem col_of_decomp {S : WState} {C₁ C₂ : List (ℕ × ℕ)} {c : ℕ × ℕ}
    (h : S.cols = C₁ ++ c :: C₂) : S.col C₁.length = c := by
  simp [WState.col, h, List.getD_eq_getElem?_getD]

theorem sound_c {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {t : ℕ} (ht : t + 1 < S.cols.length)
    (hni : NonintN (S.ri (S.col t).1) (S.ri (S.col t).2) (S.ri (S.col (t + 1)).1)
      (S.ri (S.col (t + 1)).2)) :
    ∃ (W' : List ℕ) (G' : LabeledGrid n BCol BRow), Real ⟨swapAt S.cols t, S.rows⟩ G' W' Q ∧
      SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨C₁, ca, cb, C₂, hC, hC₁, hsw⟩ := swapAt_decomp ht
  have htW : t + 1 < W.length := hG.len ▸ ht
  obtain ⟨W₁, a, b, W₂, hW, hW₁, -⟩ := swapAt_decomp htW
  have hcols : G.cols = W₁.map Sum.inl ++ Sum.inl a :: Sum.inl b :: (W₂.map Sum.inl ++
      Q.map Sum.inr) := by rw [hG.cols, hW]; simp
  have hlen₂ : W₂.length = C₂.length := by
    have h1 := congrArg List.length hW
    have h2 := congrArg List.length hC
    have h3 := hG.len
    simp only [List.length_append, List.length_cons] at h1 h2
    omega
  have hzip : W.zip S.cols = W₁.zip C₁ ++ (a, ca) :: (b, cb) :: W₂.zip C₂ := by
    rw [hW, hC, List.zip_append (by omega)]; rfl
  have ma := hG.marks (a, ca) (by rw [hzip]; simp)
  have mb := hG.marks (b, cb) (by rw [hzip]; simp)
  have hca : S.col t = ca := by rw [← hC₁]; exact col_of_decomp hC
  have hcb : S.col (t + 1) = cb := by
    have := col_of_decomp (S := S) (C₁ := C₁ ++ [ca]) (c := cb) (C₂ := C₂) (by rw [hC]; simp)
    simpa [hC₁] using this
  have hma : Sum.inl a ∈ G.cols := by rw [hcols]; simp
  have hmb : Sum.inl b ∈ G.cols := by rw [hcols]; simp
  have hni' : NonintN (G.rpos (G.O (Sum.inl a))) (G.rpos (G.X (Sum.inl a)))
      (G.rpos (G.O (Sum.inl b))) (G.rpos (G.X (Sum.inl b))) := by
    rw [ma.1, ma.2, mb.1, mb.2, hG.nonintN_rows (hG.mem_of_O hma ma.1) (hG.mem_of_X hma ma.2)
      (hG.mem_of_O hmb mb.1) (hG.mem_of_X hmb mb.2), ← hca, ← hcb]
    exact hni
  refine ⟨W₁ ++ b :: a :: W₂, G.swapCols hcols, ⟨?_, ?_, ?_, ?_⟩, ⟨fun _ _ => ⟨rfl, rfl⟩, rfl⟩,
    G.movesTo_swapCols hcols hni'⟩
  · rw [LabeledGrid.swapCols_cols]; simp
  · simp only [hsw, List.length_append, List.length_cons]; omega
  · intro p hp
    rw [hsw, List.zip_append (by omega)] at hp
    have hp' : p ∈ W.zip S.cols := by
      rw [hzip]
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append_left _ h
      · simp only [List.zip_cons_cons, List.mem_cons] at h
        rcases h with rfl | rfl | h
        · simp
        · simp
        · simp [h]
    exact hG.marks p hp'
  · exact hG.rows

/-! ### The row exchange -/

theorem filter_move_up {α : Type*} (p : α → Bool) {M₁ E M₂ : List α} {a b : α}
    (hp : p a = false) :
    (M₁ ++ E ++ [b] ++ a :: M₂).filter p = (M₁ ++ a :: (E ++ b :: M₂)).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

theorem filter_move_down {α : Type*} (p : α → Bool) {M₁ E M₂ : List α} {a b : α}
    (hp : p b = false) :
    (M₁ ++ [b] ++ a :: (E ++ M₂)).filter p = (M₁ ++ a :: (E ++ b :: M₂)).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

theorem swapAt_append_length {α : Type*} {l₁ l₂ : List α} {a b : α} :
    swapAt (l₁ ++ a :: b :: l₂) l₁.length = l₁ ++ b :: a :: l₂ := by
  induction l₁ with
  | nil => rfl
  | cons c l₁ ih => simp [swapAt, ih]

theorem isInt_facts {S : WState} {z : ℕ} (h : S.isInt z = true) :
    isConn z = false ∧ S.pO z < S.cols.length ∧ S.pX z < S.cols.length := by
  simp only [WState.isInt, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨⟨h1, ⟨c, hc, hc'⟩⟩, ⟨d, hd, hd'⟩⟩ := h
  exact ⟨h1, List.findIdx_lt_length.mpr ⟨c, hc, hc'⟩, List.findIdx_lt_length.mpr ⟨d, hd, hd'⟩⟩

theorem lefts_of_split {M₁ E M₂ : List BRow} {x y : ℕ} (hE : ∀ z, Sum.inl z ∉ E) :
    lefts (M₁ ++ Sum.inl x :: (E ++ Sum.inl y :: M₂)) = lefts M₁ ++ x :: y :: lefts M₂ := by
  have : lefts E = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz; exact hE z (mem_lefts.mp hz)
  simp [lefts_append, lefts_cons_inl, this]

theorem lefts_nil_of {E : List BRow} (hE : ∀ z, Sum.inl z ∉ E) : lefts E = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun z hz => hE z (mem_lefts.mp hz)

theorem ri_succ_of_adj {S : WState} (hnd : S.rows.Nodup) {x y : ℕ} (h : adjRows S x y = true) :
    x ∈ S.rows ∧ y ∈ S.rows ∧ S.ri y = S.ri x + 1 := by
  simp only [adjRows, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  obtain ⟨hx, hy⟩ := h
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hy
  refine ⟨hx, hget ▸ List.getElem_mem hlt, ?_⟩
  rw [← hget]
  exact List.Nodup.idxOf_getElem hnd _ _

theorem sound_r {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {x y : ℕ} (hadj : adjRows S x y = true)
    (hint : (S.isInt x || S.isInt y) = true)
    (hc : countEq S.cols.length [S.pO x, S.pX x, S.pO y, S.pX y] ≤ 1)
    (hni : NonintN (S.pO x) (S.pX x) (S.pO y) (S.pX y)) :
    ∃ (W' : List ℕ) (G' : LabeledGrid n BCol BRow),
      Real ⟨S.cols, swapAt S.rows (S.ri x)⟩ G' W' Q ∧ SameOut G G' Q ∧
        G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨hx, hy, hri⟩ := ri_succ_of_adj hG.rows_nodup hadj
  obtain ⟨M₁, E, M₂, hsplit, hE⟩ := hG.split_adj hx hy hri
  have hS : S.rows = lefts M₁ ++ x :: y :: lefts M₂ := by
    rw [← hG.rows, hsplit, lefts_of_split hE]
  have hnd := hG.rows_nodup
  rw [hS] at hnd
  have hxM : x ∉ lefts M₁ := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hri' : S.ri x = (lefts M₁).length := by
    unfold WState.ri; rw [hS, List.idxOf_append_of_notMem hxM]; simp
  have hS' : swapAt S.rows (S.ri x) = lefts M₁ ++ y :: x :: lefts M₂ := by
    rw [hri', hS, swapAt_append_length]
  have hxy := hG.rowsNonint_of_model hc hni
  have hlE := lefts_nil_of hE
  rcases hxI : S.isInt x with _ | _
  · -- `y` is internal: move it down to `x`
    simp only [hxI, Bool.false_or] at hint
    obtain ⟨hyc, hyO, hyX⟩ := isInt_facts hint
    rw [← hG.len] at hyO hyX
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G.exists_moveRowDown (m₁ := M₁ ++ [Sum.inl x])
      (mid := E) (x := Sum.inl y) (m₂ := M₂) (by rw [hsplit]; simp) (fun z hz => by
        rcases z with z | e
        · exact absurd hz (hE z)
        · exact (G.rowsNonint_comm).mp (hG.rowsNonint_int_ext hyO hyX e))
    obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hmv₂⟩ := G₁.exists_moveRowUp (m₁ := M₁) (x := Sum.inl x)
      (mid := [Sum.inl y]) (m₂ := E ++ M₂) (by rw [hr₁]; simp)
      (by simpa using (LabeledGrid.rowsNonint_congr G G₁ hc₁ hO₁ hX₁).mpr hxy)
    refine ⟨W, G₂, ⟨by rw [hc₂, hc₁, hG.cols], hG.len, ?_, ?_⟩, ⟨fun c _ => ?_, ?_⟩,
      hmv₁.trans hmv₂⟩
    · intro p hp; rw [hO₂, hO₁, hX₂, hX₁]; exact hG.marks p hp
    · rw [hr₂, hS']; simp [lefts_append, lefts_cons_inl, hlE]
    · rw [hO₂, hO₁, hX₂, hX₁]; exact ⟨rfl, rfl⟩
    · rw [hr₂, hsplit]
      exact filter_move_down nonInt (by simpa [nonInt] using hyc)
  · -- `x` is internal: move it up to `y`
    obtain ⟨hxc, hxO, hxX⟩ := isInt_facts hxI
    rw [← hG.len] at hxO hxX
    obtain ⟨G₁, hc₁, hr₁, hO₁, hX₁, hmv₁⟩ := G.exists_moveRowUp (m₁ := M₁) (x := Sum.inl x)
      (mid := E) (m₂ := Sum.inl y :: M₂) hsplit (fun z hz => by
        rcases z with z | e
        · exact absurd hz (hE z)
        · exact hG.rowsNonint_int_ext hxO hxX e)
    obtain ⟨G₂, hc₂, hr₂, hO₂, hX₂, hmv₂⟩ := G₁.exists_moveRowUp (m₁ := M₁ ++ E)
      (x := Sum.inl x) (mid := [Sum.inl y]) (m₂ := M₂) (by rw [hr₁]; simp)
      (by simpa using (LabeledGrid.rowsNonint_congr G G₁ hc₁ hO₁ hX₁).mpr hxy)
    refine ⟨W, G₂, ⟨by rw [hc₂, hc₁, hG.cols], hG.len, ?_, ?_⟩, ⟨fun c _ => ?_, ?_⟩,
      hmv₁.trans hmv₂⟩
    · intro p hp; rw [hO₂, hO₁, hX₂, hX₁]; exact hG.marks p hp
    · rw [hr₂, hS']; simp [lefts_append, lefts_cons_inl, hlE]
    · rw [hO₂, hO₁, hX₂, hX₁]; exact ⟨rfl, rfl⟩
    · rw [hr₂, hsplit]
      exact filter_move_up nonInt (by simpa [nonInt] using hxc)

/-! ### Destabilizations -/

theorem filter_del_up {α : Type*} (p : α → Bool) {M₁ E M₂ : List α} {a b : α}
    (hp : p a = false) :
    (M₁ ++ E ++ b :: M₂).filter p = (M₁ ++ a :: (E ++ b :: M₂)).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

theorem filter_del_down {α : Type*} (p : α → Bool) {M₁ E M₂ : List α} {a b : α}
    (hp : p a = false) :
    (M₁ ++ b :: (E ++ M₂)).filter p = (M₁ ++ b :: (E ++ a :: M₂)).filter p := by
  simp [List.filter_append, List.filter_cons, hp]

/-- The rows around a deleted internal row `x` next to `y`. -/
theorem rows_split_del {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {x y : ℕ}
    (hadj : adjRows S x y = true ∨ adjRows S y x = true) :
    ∃ M₁ E M₂, (∀ z, Sum.inl z ∉ E) ∧
      ((G.rows = M₁ ++ Sum.inl x :: (E ++ Sum.inl y :: M₂) ∧
          S.rows.erase x = lefts M₁ ++ y :: lefts M₂) ∨
        (G.rows = M₁ ++ Sum.inl y :: (E ++ Sum.inl x :: M₂) ∧
          S.rows.erase x = lefts M₁ ++ y :: lefts M₂)) := by
  rcases hadj with hadj | hadj
  · obtain ⟨hx, hy, hri⟩ := ri_succ_of_adj hG.rows_nodup hadj
    obtain ⟨M₁, E, M₂, hsplit, hE⟩ := hG.split_adj hx hy hri
    have hS : S.rows = lefts M₁ ++ x :: y :: lefts M₂ := by
      rw [← hG.rows, hsplit, lefts_of_split hE]
    have hnd := hG.rows_nodup
    rw [hS] at hnd
    have hxM : x ∉ lefts M₁ := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
    refine ⟨M₁, E, M₂, hE, Or.inl ⟨hsplit, ?_⟩⟩
    rw [hS, List.erase_append_right _ hxM, List.erase_cons_head]
  · obtain ⟨hy, hx, hri⟩ := ri_succ_of_adj hG.rows_nodup hadj
    obtain ⟨M₁, E, M₂, hsplit, hE⟩ := hG.split_adj hy hx hri
    have hS : S.rows = lefts M₁ ++ y :: x :: lefts M₂ := by
      rw [← hG.rows, hsplit, lefts_of_split hE]
    have hnd := hG.rows_nodup
    rw [hS] at hnd
    have hxM : x ∉ lefts M₁ ++ [y] := by
      intro h
      rw [List.mem_append] at h
      rcases h with h | h
      · exact (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
      · have hxy : x = y := by simpa using h
        have h2 := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
        exact h2 (by rw [hxy]; simp)
    refine ⟨M₁, E, M₂, hE, Or.inr ⟨hsplit, ?_⟩⟩
    rw [hS, show lefts M₁ ++ y :: x :: lefts M₂ = (lefts M₁ ++ [y]) ++ x :: lefts M₂ by simp,
      List.erase_append_right _ hxM, List.erase_cons_head]
    simp

/-- The decomposition of the window at two consecutive columns `p, s`. -/
theorem window_pair {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {p s : ℕ} (hps : p + 1 = s ∨ s + 1 = p)
    (hp : p < S.cols.length) (hs : s < S.cols.length) (v : ℕ × ℕ) :
    ∃ (W₁ W₂ : List ℕ) (C₁ C₂ : List (ℕ × ℕ)) (wp ws : ℕ),
      (G.cols = W₁.map Sum.inl ++ Sum.inl wp :: Sum.inl ws :: (W₂.map Sum.inl ++ Q.map Sum.inr) ∨
        G.cols = W₁.map Sum.inl ++ Sum.inl ws :: Sum.inl wp :: (W₂.map Sum.inl ++ Q.map Sum.inr)) ∧
      W₁.length = C₁.length ∧ W₂.length = C₂.length ∧
      (∀ q, q ∈ W.zip S.cols ↔ q ∈ W₁.zip C₁ ∨ q = (wp, S.col p) ∨ q = (ws, S.col s) ∨
        q ∈ W₂.zip C₂) ∧
      (S.cols.set s v).eraseIdx p = C₁ ++ v :: C₂ := by
  have hlen := hG.len
  rcases hps with rfl | rfl
  · have hC := decomp_at₂ (l := S.cols) (t := p) hs
    have hW := decomp_at₂ (l := W) (t := p) (by omega)
    refine ⟨W.take p, W.drop (p + 2), S.cols.take p, S.cols.drop (p + 2), W[p], W[p + 1], ?_,
      by simp; omega, by simp; omega, fun q => ?_, ?_⟩
    · left; rw [hG.cols]; conv_lhs => rw [hW]
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    · have hzip : W.zip S.cols = (W.take p).zip (S.cols.take p) ++ (W[p], S.cols[p]) ::
          (W[p + 1], S.cols[p + 1]) :: (W.drop (p + 2)).zip (S.cols.drop (p + 2)) := by
        conv_lhs => rw [hW, hC]
        rw [List.zip_append (by simp; omega)]; rfl
      rw [hzip, Real.col_eq (by omega), Real.col_eq hs]
      simp only [List.mem_append, List.mem_cons]
    · conv_lhs => rw [hC]
      have := set_eraseIdx_of_succ (l₁ := S.cols.take p) (l₂ := S.cols.drop (p + 2))
        (a := S.cols[p]) (b := S.cols[p + 1]) (v := v)
      rwa [List.length_take, min_eq_left (by omega)] at this
  · have hC := decomp_at₂ (l := S.cols) (t := s) hp
    have hW := decomp_at₂ (l := W) (t := s) (by omega)
    refine ⟨W.take s, W.drop (s + 2), S.cols.take s, S.cols.drop (s + 2), W[s + 1], W[s], ?_,
      by simp; omega, by simp; omega, fun q => ?_, ?_⟩
    · right; rw [hG.cols]; conv_lhs => rw [hW]
      simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    · have hzip : W.zip S.cols = (W.take s).zip (S.cols.take s) ++ (W[s], S.cols[s]) ::
          (W[s + 1], S.cols[s + 1]) :: (W.drop (s + 2)).zip (S.cols.drop (s + 2)) := by
        conv_lhs => rw [hW, hC]
        rw [List.zip_append (by simp; omega)]; rfl
      rw [hzip, Real.col_eq (by omega), Real.col_eq hs]
      simp only [List.mem_append, List.mem_cons]
      tauto
    · conv_lhs => rw [hC]
      have := set_eraseIdx_of_pred (l₁ := S.cols.take s) (l₂ := S.cols.drop (s + 2))
        (a := S.cols[s]) (b := S.cols[s + 1]) (v := v)
      rwa [List.length_take, min_eq_left (by omega)] at this


theorem sound_dX {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {p s x y : ℕ} (hps : p + 1 = s ∨ s + 1 = p)
    (hp : p < S.cols.length) (hs : s < S.cols.length) (hcp : S.col p = (x, y))
    (hcs : (S.col s).2 = x) (hcs' : (S.col s).1 ≠ y) (hxc : isConn x = false)
    (hadj : adjRows S x y = true ∨ adjRows S y x = true) :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow),
      Real ⟨(S.cols.set s ((S.col s).1, y)).eraseIdx p, S.rows.erase x⟩ G' W' Q ∧
        SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨W₁, W₂, C₁, C₂, wp, ws, hcols, hl₁, hl₂, hzip, hset⟩ :=
    window_pair hG hps hp hs ((S.col s).1, y)
  have hmp := hG.marks (wp, S.col p) ((hzip _).mpr (Or.inr (Or.inl rfl)))
  have hms := hG.marks (ws, S.col s) ((hzip _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  rw [hcp] at hmp
  have hwpm : (Sum.inl wp : BCol) ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by have := G.cpos_lt hwpm; omega⟩
  have hnd := G.cols_nodup
  have hws : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, q.1 ≠ ws := by
    intro q hq he
    have h1 : q.1 ∈ W₁ ∨ q.1 ∈ W₂ := by
      rcases List.mem_append.mp hq with h | h
      · exact Or.inl (List.of_mem_zip h).1
      · exact Or.inr (List.of_mem_zip h).1
    rw [he] at h1
    have hnot : ws ∉ W₁ ∧ ws ∉ W₂ := by
      rcases hcols with h | h <;> rw [h, List.nodup_append] at hnd <;> obtain ⟨-, h2, h3⟩ := hnd
      · refine ⟨fun hw => h3 _ (List.mem_map_of_mem hw) _ (by simp) rfl, fun hw => ?_⟩
        rw [List.nodup_cons, List.nodup_cons] at h2
        exact h2.2.1 (by simp [hw])
      · refine ⟨fun hw => h3 _ (List.mem_map_of_mem hw) _ (by simp) rfl, fun hw => ?_⟩
        rw [List.nodup_cons] at h2
        exact h2.1 (by simp [hw])
    rcases h1 with h1 | h1
    · exact hnot.1 h1
    · exact hnot.2 h1
  obtain ⟨M₁, E, M₂, hE, hrows⟩ := rows_split_del hG hadj
  have hmid : ∀ r ∈ E, r ≠ G.O (Sum.inl ws) := by
    intro r hr he; rw [hms.1] at he; exact hE _ (he ▸ hr)
  have hfin : ∀ (G' : LabeledGrid n₀ BCol BRow),
      G'.cols = W₁.map Sum.inl ++ Sum.inl ws :: (W₂.map Sum.inl ++ Q.map Sum.inr) →
      G'.O = G.O → G'.X = Function.update G.X (Sum.inl ws) (Sum.inl y) →
      lefts G'.rows = S.rows.erase x → G'.rows.filter nonInt = G.rows.filter nonInt →
      Real ⟨(S.cols.set s ((S.col s).1, y)).eraseIdx p, S.rows.erase x⟩ G' (W₁ ++ ws :: W₂) Q ∧
        SameOut G G' Q := by
    intro G' hc' hsame hchg hl hf
    refine ⟨⟨by rw [hc']; simp, by rw [hset]; simp; omega, ?_, hl⟩, ⟨fun c _ => ?_, hf⟩⟩
    · intro q hq
      rw [hset, List.zip_append (by omega)] at hq
      rcases List.mem_append.mp hq with hq | hq
      · have hne := hws q (List.mem_append_left _ hq)
        rw [hsame, hchg, Function.update_of_ne (by simpa using hne)]
        exact hG.marks q ((hzip q).mpr (Or.inl hq))
      · rw [List.zip_cons_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [hsame, hchg, Function.update_self]
          exact ⟨hms.1, rfl⟩
        · have hne := hws q (List.mem_append_right _ hq)
          rw [hsame, hchg, Function.update_of_ne (by simpa using hne)]
          exact hG.marks q ((hzip q).mpr (Or.inr (Or.inr (Or.inr hq))))
    · rw [hsame, hchg, Function.update_of_ne (by simp)]; exact ⟨rfl, rfl⟩
  rcases hrows with ⟨hsplit, herase⟩ | ⟨hsplit, herase⟩
  · obtain ⟨G', hc', hr', hO', hX', hmv⟩ := G.exists_mergeX_up (l₁ := W₁.map Sum.inl)
      (l₂ := W₂.map Sum.inl ++ Q.map Sum.inr) (c := Sum.inl wp) (d := Sum.inl ws)
      (e := Sum.inl x) (z := Sum.inl y) hcols hsplit hmp.1 hmp.2 (by rw [hms.2, hcs]) (by rw [hms.1]; simpa using hcs') hmid
    obtain ⟨hR, hS⟩ := hfin G' hc' hO' hX'
      (by rw [hr', herase]; simp [lefts_append, lefts_cons_inl, lefts_nil_of hE])
      (by rw [hr', hsplit]; exact filter_del_up nonInt (by simpa [nonInt] using hxc))
    exact ⟨n₀, _, G', hR, hS, hmv⟩
  · obtain ⟨G', hc', hr', hO', hX', hmv⟩ := G.exists_mergeX_down (l₁ := W₁.map Sum.inl)
      (l₂ := W₂.map Sum.inl ++ Q.map Sum.inr) (c := Sum.inl wp) (d := Sum.inl ws)
      (e := Sum.inl x) (z := Sum.inl y) hcols hsplit hmp.1 hmp.2 (by rw [hms.2, hcs]) (by rw [hms.1]; simpa using hcs') hmid
    obtain ⟨hR, hS⟩ := hfin G' hc' hO' hX'
      (by rw [hr', herase]; simp [lefts_append, lefts_cons_inl, lefts_nil_of hE])
      (by rw [hr', hsplit]; exact filter_del_down nonInt (by simpa [nonInt] using hxc))
    exact ⟨n₀, _, G', hR, hS, hmv⟩

theorem sound_dO {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {p s x y : ℕ} (hps : p + 1 = s ∨ s + 1 = p)
    (hp : p < S.cols.length) (hs : s < S.cols.length) (hcp : S.col p = (y, x))
    (hcs : (S.col s).1 = x) (hcs' : (S.col s).2 ≠ y) (hxc : isConn x = false)
    (hadj : adjRows S x y = true ∨ adjRows S y x = true) :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow),
      Real ⟨(S.cols.set s (y, (S.col s).2)).eraseIdx p, S.rows.erase x⟩ G' W' Q ∧
        SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨W₁, W₂, C₁, C₂, wp, ws, hcols, hl₁, hl₂, hzip, hset⟩ :=
    window_pair hG hps hp hs (y, (S.col s).2)
  have hmp := hG.marks (wp, S.col p) ((hzip _).mpr (Or.inr (Or.inl rfl)))
  have hms := hG.marks (ws, S.col s) ((hzip _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  rw [hcp] at hmp
  have hwpm : (Sum.inl wp : BCol) ∈ G.cols := by rcases hcols with h | h <;> rw [h] <;> simp
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by have := G.cpos_lt hwpm; omega⟩
  have hnd := G.cols_nodup
  have hws : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, q.1 ≠ ws := by
    intro q hq he
    have h1 : q.1 ∈ W₁ ∨ q.1 ∈ W₂ := by
      rcases List.mem_append.mp hq with h | h
      · exact Or.inl (List.of_mem_zip h).1
      · exact Or.inr (List.of_mem_zip h).1
    rw [he] at h1
    have hnot : ws ∉ W₁ ∧ ws ∉ W₂ := by
      rcases hcols with h | h <;> rw [h, List.nodup_append] at hnd <;> obtain ⟨-, h2, h3⟩ := hnd
      · refine ⟨fun hw => h3 _ (List.mem_map_of_mem hw) _ (by simp) rfl, fun hw => ?_⟩
        rw [List.nodup_cons, List.nodup_cons] at h2
        exact h2.2.1 (by simp [hw])
      · refine ⟨fun hw => h3 _ (List.mem_map_of_mem hw) _ (by simp) rfl, fun hw => ?_⟩
        rw [List.nodup_cons] at h2
        exact h2.1 (by simp [hw])
    rcases h1 with h1 | h1
    · exact hnot.1 h1
    · exact hnot.2 h1
  obtain ⟨M₁, E, M₂, hE, hrows⟩ := rows_split_del hG hadj
  have hmid : ∀ r ∈ E, r ≠ G.X (Sum.inl ws) := by
    intro r hr he; rw [hms.2] at he; exact hE _ (he ▸ hr)
  have hfin : ∀ (G' : LabeledGrid n₀ BCol BRow),
      G'.cols = W₁.map Sum.inl ++ Sum.inl ws :: (W₂.map Sum.inl ++ Q.map Sum.inr) →
      G'.X = G.X → G'.O = Function.update G.O (Sum.inl ws) (Sum.inl y) →
      lefts G'.rows = S.rows.erase x → G'.rows.filter nonInt = G.rows.filter nonInt →
      Real ⟨(S.cols.set s (y, (S.col s).2)).eraseIdx p, S.rows.erase x⟩ G' (W₁ ++ ws :: W₂) Q ∧
        SameOut G G' Q := by
    intro G' hc' hsame hchg hl hf
    refine ⟨⟨by rw [hc']; simp, by rw [hset]; simp; omega, ?_, hl⟩, ⟨fun c _ => ?_, hf⟩⟩
    · intro q hq
      rw [hset, List.zip_append (by omega)] at hq
      rcases List.mem_append.mp hq with hq | hq
      · have hne := hws q (List.mem_append_left _ hq)
        rw [hsame, hchg, Function.update_of_ne (by simpa using hne)]
        exact hG.marks q ((hzip q).mpr (Or.inl hq))
      · rw [List.zip_cons_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [hsame, hchg, Function.update_self]
          exact ⟨rfl, hms.2⟩
        · have hne := hws q (List.mem_append_right _ hq)
          rw [hsame, hchg, Function.update_of_ne (by simpa using hne)]
          exact hG.marks q ((hzip q).mpr (Or.inr (Or.inr (Or.inr hq))))
    · rw [hsame, hchg, Function.update_of_ne (by simp)]; exact ⟨rfl, rfl⟩
  rcases hrows with ⟨hsplit, herase⟩ | ⟨hsplit, herase⟩
  · obtain ⟨G', hc', hr', hO', hX', hmv⟩ := G.exists_mergeO_up (l₁ := W₁.map Sum.inl)
      (l₂ := W₂.map Sum.inl ++ Q.map Sum.inr) (c := Sum.inl wp) (d := Sum.inl ws)
      (e := Sum.inl x) (z := Sum.inl y) hcols hsplit hmp.2 hmp.1 (by rw [hms.1, hcs]) (by rw [hms.2]; simpa using hcs') hmid
    obtain ⟨hR, hS⟩ := hfin G' hc' hX' hO'
      (by rw [hr', herase]; simp [lefts_append, lefts_cons_inl, lefts_nil_of hE])
      (by rw [hr', hsplit]; exact filter_del_up nonInt (by simpa [nonInt] using hxc))
    exact ⟨n₀, _, G', hR, hS, hmv⟩
  · obtain ⟨G', hc', hr', hO', hX', hmv⟩ := G.exists_mergeO_down (l₁ := W₁.map Sum.inl)
      (l₂ := W₂.map Sum.inl ++ Q.map Sum.inr) (c := Sum.inl wp) (d := Sum.inl ws)
      (e := Sum.inl x) (z := Sum.inl y) hcols hsplit hmp.2 hmp.1 (by rw [hms.1, hcs]) (by rw [hms.2]; simpa using hcs') hmid
    obtain ⟨hR, hS⟩ := hfin G' hc' hX' hO'
      (by rw [hr', herase]; simp [lefts_append, lefts_cons_inl, lefts_nil_of hE])
      (by rw [hr', hsplit]; exact filter_del_down nonInt (by simpa [nonInt] using hxc))
    exact ⟨n₀, _, G', hR, hS, hmv⟩

/-! ### Stabilizations -/

section Stab

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

open LabeledGrid in
theorem exists_stabO_gen (G : LabeledGrid n C R) {d κ : C} {ν : R} (cols' : List C)
    (rows' : List R) (L₁ L₂ : List C) (M₁ M₂ : List R) (hcs : cols' = L₁ ++ κ :: L₂)
    (hcG : G.cols = L₁ ++ L₂) (hrs : rows' = M₁ ++ ν :: M₂) (hrG : G.rows = M₁ ++ M₂)
    (hdm : d ∈ G.cols) (hcadj : (∃ l, L₁ = l ++ [d]) ∨ (∃ l, L₂ = d :: l))
    (hradj : (∃ m, M₁ = m ++ [G.O d]) ∨ (∃ m, M₂ = G.O d :: m)) (hκ : κ ∉ G.cols)
    (hν : ν ∉ G.rows) :
    ∃ G' : LabeledGrid (n + 1) C R, G'.cols = cols' ∧ G'.rows = rows' ∧
      G'.O = Function.update (Function.update G.O d ν) κ (G.O d) ∧
      G'.X = Function.update G.X κ ν ∧ G.toGrid.MovesTo G'.toGrid := by
  have hκd : κ ≠ d := fun h => hκ (h ▸ hdm)
  have hOdm : G.O d ∈ G.rows := G.O_mem d hdm
  have hνO : ν ≠ G.O d := fun h => hν (h ▸ hOdm)
  have hne : ∀ c ∈ G.cols, c ≠ κ := fun c hc h => hκ (h ▸ hc)
  have hcp : cols'.Perm (κ :: G.cols) := by
    rw [hcs, hcG]; exact List.perm_middle
  have hrp : rows'.Perm (ν :: G.rows) := by
    rw [hrs, hrG]; exact List.perm_middle
  have memc : ∀ c, c ∈ cols' ↔ c = κ ∨ c ∈ G.cols := fun c => by
    rw [hcp.mem_iff, List.mem_cons]
  have memr : ∀ x, x ∈ rows' ↔ x = ν ∨ x ∈ G.rows := fun x => by
    rw [hrp.mem_iff, List.mem_cons]
  let G' : LabeledGrid (n + 1) C R :=
    { cols := cols'
      rows := rows'
      O := Function.update (Function.update G.O d ν) κ (G.O d)
      X := Function.update G.X κ ν
      cols_length := by rw [hcp.length_eq, List.length_cons, G.cols_length]
      rows_length := by rw [hrp.length_eq, List.length_cons, G.rows_length]
      cols_nodup := hcp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hκ, G.cols_nodup⟩)
      rows_nodup := hrp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hν, G.rows_nodup⟩)
      O_mem := fun c hc' => by
        rw [memr]
        rcases (memc c).mp hc' with rfl | hc'
        · rw [Function.update_self]; exact Or.inr hOdm
        · by_cases hcd : c = d
          · subst hcd; rw [Function.update_of_ne (fun h => hκd h.symm), Function.update_self]
            exact Or.inl rfl
          · rw [Function.update_of_ne (hne _ hc'), Function.update_of_ne hcd]
            exact Or.inr (G.O_mem c hc')
      X_mem := fun c hc' => by
        rw [memr]
        rcases (memc c).mp hc' with rfl | hc'
        · rw [Function.update_self]; exact Or.inl rfl
        · rw [Function.update_of_ne (hne _ hc')]
          exact Or.inr (G.X_mem c hc')
      O_inj := fun a ha b hb h => by
        have key : ∀ c, c ∈ cols' →
            (c = κ ∧ Function.update (Function.update G.O d ν) κ (G.O d) c = G.O d) ∨
            (c = d ∧ Function.update (Function.update G.O d ν) κ (G.O d) c = ν) ∨
            (c ≠ κ ∧ c ≠ d ∧ c ∈ G.cols ∧
              Function.update (Function.update G.O d ν) κ (G.O d) c = G.O c) := by
          intro c hc'
          rcases (memc c).mp hc' with rfl | hc'
          · exact Or.inl ⟨rfl, Function.update_self _ _ _⟩
          · by_cases hcd : c = d
            · subst hcd
              exact Or.inr (Or.inl ⟨rfl, by
                rw [Function.update_of_ne (fun h => hκd h.symm), Function.update_self]⟩)
            · have hcκ : c ≠ κ := fun h => hκ (h ▸ hc')
              exact Or.inr (Or.inr ⟨hcκ, hcd, hc', by
                rw [Function.update_of_ne hcκ, Function.update_of_ne hcd]⟩)
        rcases key a ha with ⟨rfl, ea⟩ | ⟨rfl, ea⟩ | ⟨haκ, had, ham, ea⟩ <;>
          rcases key b hb with ⟨rfl, eb⟩ | ⟨rfl, eb⟩ | ⟨hbκ, hbd, hbm, eb⟩
        · rfl
        · rw [ea, eb] at h; exact absurd h.symm hνO
        · rw [ea, eb] at h; exact absurd (G.O_inj _ hdm _ hbm h) (Ne.symm hbd)
        · rw [ea, eb] at h; exact absurd h hνO
        · rfl
        · rw [ea, eb] at h; exact absurd (h ▸ G.O_mem b hbm) hν
        · rw [ea, eb] at h; exact absurd (G.O_inj _ ham _ hdm h) had
        · rw [ea, eb] at h; exact absurd (h.symm ▸ G.O_mem a ham) hν
        · rw [ea, eb] at h; exact G.O_inj _ ham _ hbm h
      X_inj := fun a ha b hb h => by
        rcases (memc a).mp ha with rfl | ham <;> rcases (memc b).mp hb with rfl | hbm
        · rfl
        · rw [Function.update_self, Function.update_of_ne (hne _ hbm)] at h
          exact absurd (h ▸ G.X_mem b hbm) hν
        · rw [Function.update_self, Function.update_of_ne (hne _ ham)] at h
          exact absurd (h.symm ▸ G.X_mem a ham) hν
        · rw [Function.update_of_ne (hne _ ham),
            Function.update_of_ne (hne _ hbm)] at h
          exact G.X_inj _ ham _ hbm h
      O_ne_X := fun c hc' => by
        rcases (memc c).mp hc' with rfl | hcm
        · rw [Function.update_self, Function.update_self]; exact Ne.symm hνO
        · rw [Function.update_of_ne (hne _ hcm), Function.update_of_ne (hne _ hcm)]
          by_cases hcd : c = d
          · subst hcd; rw [Function.update_self]
            exact fun h => hν (by rw [h]; exact G.X_mem _ hcm)
          · rw [Function.update_of_ne hcd]; exact G.O_ne_X c hcm }
  have hc' : G'.cols = L₁ ++ κ :: L₂ := hcs
  have hx' : G'.rows = M₁ ++ ν :: M₂ := hrs
  have hXκ : G'.X κ = ν := Function.update_self _ _ _
  have hOκ : G'.O κ = G.O d := Function.update_self _ _ _
  have hOd : G'.O d = ν := by
    simp only [G']; rw [Function.update_of_ne (Ne.symm hκd), Function.update_self]
  have hXd : G'.X d ≠ G.O d := by
    simp only [G']; rw [Function.update_of_ne (Ne.symm hκd)]; exact (G.O_ne_X d hdm).symm
  have hdm' : d ∈ G'.cols := by
    rw [hc']; rw [hcG] at hdm; simp only [List.mem_append, List.mem_cons] at hdm ⊢; tauto
  have hD := G'.isDestabilization_destabO hc' hx' hXκ hOκ hOd hXd hdm'
    (by
      rcases hcadj with ⟨l, hl⟩ | ⟨l, hl⟩
      · right
        rw [G'.cpos_of_cols_eq (c := d) (l₁ := l) (l₂ := κ :: L₂) (by rw [hc', hl]; simp),
          G'.cpos_of_cols_eq (c := κ) (l₁ := L₁) (l₂ := L₂) hc', hl]; simp
      · left
        rw [G'.cpos_of_cols_eq (c := d) (l₁ := L₁ ++ [κ]) (l₂ := l) (by rw [hc', hl]; simp),
          G'.cpos_of_cols_eq (c := κ) (l₁ := L₁) (l₂ := L₂) hc']; simp)
    (by
      rcases hradj with ⟨m, hm⟩ | ⟨m, hm⟩
      · right; exact G'.rpos_succ_of_rows (m₁ := m) (m₂ := M₂) (by rw [hx', hm]; simp)
      · left; exact G'.rpos_succ_of_rows (m₁ := M₁) (m₂ := m) (by rw [hx', hm]))
  have he : (G'.destabO hc' hx' hXκ hOκ hOd hXd hdm').toGrid = G.toGrid := by
    apply toGrid_eq_of_data
    · rw [destabO_cols, hcG]
    · rw [destabO_rows, hrG]
    · intro c hcm
      rw [destabO_cols] at hcm
      rw [destabO_O]
      by_cases hcd : c = d
      · subst hcd; rw [Function.update_self]
      · have hcm' : c ∈ G.cols := by rw [hcG]; exact hcm
        rw [Function.update_of_ne hcd]
        simp only [G']
        rw [Function.update_of_ne (hne _ hcm'), Function.update_of_ne hcd]
    · intro c hcm
      rw [destabO_cols] at hcm
      have hcm' : c ∈ G.cols := by rw [hcG]; exact hcm
      rw [destabO_X]
      simp only [G']
      rw [Function.update_of_ne (hne _ hcm')]
  refine ⟨G', rfl, rfl, rfl, rfl, ?_⟩
  rw [← he]
  exact hD.movesTo.symm

open LabeledGrid in
theorem exists_stabX_gen (G : LabeledGrid n C R) {d κ : C} {ν : R} (cols' : List C)
    (rows' : List R) (L₁ L₂ : List C) (M₁ M₂ : List R) (hcs : cols' = L₁ ++ κ :: L₂)
    (hcG : G.cols = L₁ ++ L₂) (hrs : rows' = M₁ ++ ν :: M₂) (hrG : G.rows = M₁ ++ M₂)
    (hdm : d ∈ G.cols) (hcadj : (∃ l, L₁ = l ++ [d]) ∨ (∃ l, L₂ = d :: l))
    (hradj : (∃ m, M₁ = m ++ [G.X d]) ∨ (∃ m, M₂ = G.X d :: m)) (hκ : κ ∉ G.cols)
    (hν : ν ∉ G.rows) :
    ∃ G' : LabeledGrid (n + 1) C R, G'.cols = cols' ∧ G'.rows = rows' ∧
      G'.O = Function.update G.O κ ν ∧
      G'.X = Function.update (Function.update G.X d ν) κ (G.X d) ∧
      G.toGrid.MovesTo G'.toGrid := by
  obtain ⟨G'', hc'', hr'', hO'', hX'', -⟩ := exists_stabO_gen G.swapMarks cols' rows' L₁ L₂ M₁ M₂
    hcs hcG hrs hrG hdm hcadj hradj hκ hν
  set G₃ := G''.swapMarks with hG₃
  have hO₃ : G₃.O = Function.update G.O κ ν := hX''
  have hX₃ : G₃.X = Function.update (Function.update G.X d ν) κ (G.X d) := hO''
  have hκd : κ ≠ d := fun h => hκ (h ▸ hdm)
  have hc' : G₃.cols = L₁ ++ κ :: L₂ := by rw [hG₃, swapMarks]; exact hc''.trans hcs
  have hx' : G₃.rows = M₁ ++ ν :: M₂ := by rw [hG₃, swapMarks]; exact hr''.trans hrs
  have hOc : G₃.O κ = ν := by rw [hO₃, Function.update_self]
  have hXc : G₃.X κ = G.X d := by rw [hX₃, Function.update_self]
  have hXd : G₃.X d = ν := by
    rw [hX₃, Function.update_of_ne (Ne.symm hκd), Function.update_self]
  have hOd : G₃.O d ≠ G.X d := by
    rw [hO₃, Function.update_of_ne (Ne.symm hκd)]; exact G.O_ne_X d hdm
  have hdm' : d ∈ G₃.cols := by
    rw [hc']; rw [hcG] at hdm; simp only [List.mem_append, List.mem_cons] at hdm ⊢; tauto
  have hne : ∀ c ∈ G.cols, c ≠ κ := fun c hc h => hκ (h ▸ hc)
  have hD := G₃.isDestabilization_destabX hc' hx' hOc hXc hXd hOd hdm'
    (by
      rcases hcadj with ⟨l, hl⟩ | ⟨l, hl⟩
      · right
        rw [G₃.cpos_of_cols_eq (c := d) (l₁ := l) (l₂ := κ :: L₂) (by rw [hc', hl]; simp),
          G₃.cpos_of_cols_eq (c := κ) (l₁ := L₁) (l₂ := L₂) hc', hl]; simp
      · left
        rw [G₃.cpos_of_cols_eq (c := d) (l₁ := L₁ ++ [κ]) (l₂ := l) (by rw [hc', hl]; simp),
          G₃.cpos_of_cols_eq (c := κ) (l₁ := L₁) (l₂ := L₂) hc']; simp)
    (by
      rcases hradj with ⟨m, hm⟩ | ⟨m, hm⟩
      · right; exact G₃.rpos_succ_of_rows (m₁ := m) (m₂ := M₂) (by rw [hx', hm]; simp)
      · left; exact G₃.rpos_succ_of_rows (m₁ := M₁) (m₂ := m) (by rw [hx', hm]))
  have he : (G₃.destabX hc' hx' hOc hXc hXd hOd hdm').toGrid = G.toGrid := by
    apply toGrid_eq_of_data
    · rw [destabX_cols, hcG]
    · rw [destabX_rows, hrG]
    · intro c hcm
      rw [destabX_cols] at hcm
      have hcm' : c ∈ G.cols := by rw [hcG]; exact hcm
      rw [destabX_O, hO₃, Function.update_of_ne (hne _ hcm')]
    · intro c hcm
      rw [destabX_cols] at hcm
      have hcm' : c ∈ G.cols := by rw [hcG]; exact hcm
      rw [destabX_X]
      by_cases hcd : c = d
      · subst hcd; rw [Function.update_self]
      · rw [Function.update_of_ne hcd, hX₃, Function.update_of_ne (hne _ hcm'),
          Function.update_of_ne hcd]
  refine ⟨G₃, hc'.trans hcs.symm, hx'.trans hrs.symm, hO₃, hX₃, ?_⟩
  rw [← he]
  exact hD.movesTo.symm

end Stab



theorem sound_sO {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {s : ℕ} (right above : Bool) {ν : ℕ}
    (hs : s < S.cols.length) (hν : S.rows.contains ν = false) (hνc : isConn ν = false) :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow),
      Real ⟨(S.cols.set s (ν, (S.col s).2)).insertIdx (if right then s + 1 else s) ((S.col s).1, ν),
        S.rows.insertIdx (if above then S.ri (S.col s).1 + 1 else S.ri (S.col s).1) ν⟩ G' W' Q ∧
        SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  have hlen := hG.len
  have hC := decomp_at (l := S.cols) (t := s) hs
  have hW := decomp_at (l := W) (t := s) (by omega)
  set C₁ := S.cols.take s with hC₁
  set C₂ := S.cols.drop (s + 1) with hC₂
  set W₁ := W.take s with hW₁
  set W₂ := W.drop (s + 1) with hW₂
  have hl₁ : W₁.length = C₁.length := by simp [hW₁, hC₁]; omega
  have hl₂ : W₂.length = C₂.length := by simp [hW₂, hC₂]; omega
  have hlC₁ : C₁.length = s := by simp [hC₁]; omega
  set ws := W[s]'(by omega) with hws
  have hcs : S.cols[s] = S.col s := (Real.col_eq hs).symm
  have hzip : W.zip S.cols = W₁.zip C₁ ++ (ws, S.col s) :: W₂.zip C₂ := by
    conv_lhs => rw [hW, hC]
    rw [List.zip_append hl₁, hcs]; rfl
  have hmw := hG.marks (ws, S.col s) (by rw [hzip]; simp)
  have hwsm : (Sum.inl ws : BCol) ∈ G.cols := by rw [hG.cols]; simp [hws, List.getElem_mem]
  -- the fresh column and row
  set κ := W.sum + 1 with hκ
  have hκW : κ ∉ W := fun h => by have := List.le_sum_of_mem h; omega
  have hκG : (Sum.inl κ : BCol) ∉ G.cols := by
    rw [hG.cols]; simp only [List.mem_append, List.mem_map, Sum.inl.injEq, reduceCtorEq,
      and_false, exists_false, or_false]
    rintro ⟨a, ha, rfl⟩; exact hκW ha
  have hνS : ν ∉ S.rows := by simpa using hν
  have hνG : (Sum.inl ν : BRow) ∉ G.rows := fun h => hνS ((hG.mem_rows).mp h)
  have hyS : (S.col s).1 ∈ S.rows := hG.mem_of_O hwsm hmw.1
  obtain ⟨M₁, M₂, hsplit⟩ := List.append_of_mem ((hG.mem_rows).mpr hyS)
  have hSr : S.rows = lefts M₁ ++ (S.col s).1 :: lefts M₂ := by
    rw [← hG.rows, hsplit, lefts_append, lefts_cons_inl]
  have hnd := hG.rows_nodup
  rw [hSr] at hnd
  have hyM : (S.col s).1 ∉ lefts M₁ := fun h =>
    (List.nodup_append.mp hnd).2.2 _ h _ (by simp) rfl
  have hri : S.ri (S.col s).1 = (lefts M₁).length := by
    unfold WState.ri; rw [hSr, List.idxOf_append_of_notMem hyM]; simp
  have hκws : (Sum.inl κ : BCol) ≠ Sum.inl ws := fun h => hκG (h ▸ hwsm)
  have hS'c : ((S.cols.set s (ν, (S.col s).2)).insertIdx (if right then s + 1 else s) ((S.col s).1, ν)) =
      if right then C₁ ++ (ν, (S.col s).2) :: ((S.col s).1, ν) :: C₂ else C₁ ++ ((S.col s).1, ν) :: (ν, (S.col s).2) :: C₂ := by
    have e : S.cols = C₁ ++ S.col s :: C₂ := by rw [← hcs]; exact hC
    cases right
    · simp only [Bool.false_eq_true, if_false]
      conv_lhs => rw [e]
      exact set_insertIdx_left' hlC₁
    · simp only [if_true]
      conv_lhs => rw [e]
      exact set_insertIdx_right' hlC₁
  have hWc : W.map (Sum.inl : ℕ → BCol) = W₁.map Sum.inl ++ Sum.inl ws :: W₂.map Sum.inl := by
    conv_lhs => rw [hW]
    simp only [List.map_append, List.map_cons]
  obtain ⟨G', hc', hr', hO', hX', hmv⟩ := exists_stabO_gen G (d := Sum.inl ws) (κ := Sum.inl κ)
    (ν := Sum.inl ν)
    (if right then (W₁ ++ ws :: κ :: W₂).map Sum.inl ++ Q.map Sum.inr
      else (W₁ ++ κ :: ws :: W₂).map Sum.inl ++ Q.map Sum.inr)
    (if above then M₁ ++ Sum.inl (S.col s).1 :: Sum.inl ν :: M₂
      else M₁ ++ Sum.inl ν :: Sum.inl (S.col s).1 :: M₂)
    (if right then W₁.map Sum.inl ++ [Sum.inl ws] else W₁.map Sum.inl)
    (if right then W₂.map Sum.inl ++ Q.map Sum.inr else Sum.inl ws :: (W₂.map Sum.inl ++ Q.map Sum.inr))
    (if above then M₁ ++ [Sum.inl (S.col s).1] else M₁)
    (if above then M₂ else Sum.inl (S.col s).1 :: M₂)
    (by cases right <;> simp) (by rw [hG.cols, hWc]; cases right <;> simp)
    (by cases above <;> simp) (by rw [hsplit]; cases above <;> simp) hwsm
    (by cases right
        · right; exact ⟨_, rfl⟩
        · left; exact ⟨_, rfl⟩)
    (by rw [hmw.1]; cases above
        · right; exact ⟨_, rfl⟩
        · left; exact ⟨_, rfl⟩) hκG hνG
  have hne : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, q.1 ≠ ws ∧ q.1 ≠ κ := by
    intro q hq
    have hq1 : q.1 ∈ W₁ ∨ q.1 ∈ W₂ := by
      rcases List.mem_append.mp hq with h | h
      · exact Or.inl (List.of_mem_zip h).1
      · exact Or.inr (List.of_mem_zip h).1
    have hWnd := hG.W_nodup
    rw [hW, List.nodup_append, List.nodup_cons] at hWnd
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rcases hq1 with h | h
      · exact hWnd.2.2 _ h _ List.mem_cons_self he
      · exact hWnd.2.1.1 (by rw [← he]; exact h)
    · rcases hq1 with h | h
      · exact hκW (by rw [← he]; exact List.mem_of_mem_take h)
      · exact hκW (by rw [← he]; exact List.mem_of_mem_drop h)
  have hold : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, G'.O (Sum.inl q.1) = Sum.inl q.2.1 ∧
      G'.X (Sum.inl q.1) = Sum.inl q.2.2 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hne q hq
    have hm := hG.marks q (by
      rw [hzip]; rcases List.mem_append.mp hq with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    rw [hO', hX', Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h1), Function.update_of_ne (by simpa using h2)]
    exact hm
  refine ⟨_, if right then W₁ ++ ws :: κ :: W₂ else W₁ ++ κ :: ws :: W₂, G',
    ⟨by rw [hc']; cases right <;> simp, ?_, ?_, ?_⟩, ⟨fun c _ => ?_, ?_⟩, hmv⟩
  · rw [hS'c]; cases right <;> simp <;> omega
  · intro q hq
    rw [hS'c] at hq
    cases right
    · simp only [Bool.false_eq_true, if_false] at hq
      rw [List.zip_append hl₁] at hq
      simp only [List.zip_cons_cons, List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | rfl | hq
      · exact hold q (List.mem_append_left _ hq)
      · exact ⟨by rw [hO', Function.update_self, hmw.1], by rw [hX', Function.update_self]⟩
      · exact ⟨by rw [hO', Function.update_of_ne (Ne.symm hκws), Function.update_self], by rw [hX', Function.update_of_ne (Ne.symm hκws), hmw.2]⟩
      · exact hold q (List.mem_append_right _ hq)
    · simp only [if_true] at hq
      rw [List.zip_append hl₁] at hq
      simp only [List.zip_cons_cons, List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | rfl | hq
      · exact hold q (List.mem_append_left _ hq)
      · exact ⟨by rw [hO', Function.update_of_ne (Ne.symm hκws), Function.update_self], by rw [hX', Function.update_of_ne (Ne.symm hκws), hmw.2]⟩
      · exact ⟨by rw [hO', Function.update_self, hmw.1], by rw [hX', Function.update_self]⟩
      · exact hold q (List.mem_append_right _ hq)
  · rw [hr', hSr, hri]
    cases above
    · simp only [Bool.false_eq_true, if_false]
      have := insertIdx_append_len (l₁ := lefts M₁) (l := (S.col s).1 :: lefts M₂) (i := 0)
        (w := ν)
      simp only [Nat.add_zero, List.insertIdx_zero] at this
      rw [this]; simp [lefts_append, lefts_cons_inl]
    · simp only [if_true]
      rw [insertIdx_append_len]; simp [lefts_append, lefts_cons_inl]
  · rw [hO', hX', Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact ⟨rfl, rfl⟩
  · rw [hr', hsplit]
    cases above
    · exact filter_ins_before nonInt (by simpa [nonInt] using hνc)
    · exact filter_ins_after nonInt (by simpa [nonInt] using hνc)

theorem sound_sX {n : ℕ} {S : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {s : ℕ} (right above : Bool) {ν : ℕ}
    (hs : s < S.cols.length) (hν : S.rows.contains ν = false) (hνc : isConn ν = false) :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow),
      Real ⟨(S.cols.set s ((S.col s).1, ν)).insertIdx (if right then s + 1 else s) (ν, (S.col s).2),
        S.rows.insertIdx (if above then S.ri (S.col s).2 + 1 else S.ri (S.col s).2) ν⟩ G' W' Q ∧
        SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  have hlen := hG.len
  have hC := decomp_at (l := S.cols) (t := s) hs
  have hW := decomp_at (l := W) (t := s) (by omega)
  set C₁ := S.cols.take s with hC₁
  set C₂ := S.cols.drop (s + 1) with hC₂
  set W₁ := W.take s with hW₁
  set W₂ := W.drop (s + 1) with hW₂
  have hl₁ : W₁.length = C₁.length := by simp [hW₁, hC₁]; omega
  have hl₂ : W₂.length = C₂.length := by simp [hW₂, hC₂]; omega
  have hlC₁ : C₁.length = s := by simp [hC₁]; omega
  set ws := W[s]'(by omega) with hws
  have hcs : S.cols[s] = S.col s := (Real.col_eq hs).symm
  have hzip : W.zip S.cols = W₁.zip C₁ ++ (ws, S.col s) :: W₂.zip C₂ := by
    conv_lhs => rw [hW, hC]
    rw [List.zip_append hl₁, hcs]; rfl
  have hmw := hG.marks (ws, S.col s) (by rw [hzip]; simp)
  have hwsm : (Sum.inl ws : BCol) ∈ G.cols := by rw [hG.cols]; simp [hws, List.getElem_mem]
  -- the fresh column and row
  set κ := W.sum + 1 with hκ
  have hκW : κ ∉ W := fun h => by have := List.le_sum_of_mem h; omega
  have hκG : (Sum.inl κ : BCol) ∉ G.cols := by
    rw [hG.cols]; simp only [List.mem_append, List.mem_map, Sum.inl.injEq, reduceCtorEq,
      and_false, exists_false, or_false]
    rintro ⟨a, ha, rfl⟩; exact hκW ha
  have hνS : ν ∉ S.rows := by simpa using hν
  have hνG : (Sum.inl ν : BRow) ∉ G.rows := fun h => hνS ((hG.mem_rows).mp h)
  have hyS : (S.col s).2 ∈ S.rows := hG.mem_of_X hwsm hmw.2
  obtain ⟨M₁, M₂, hsplit⟩ := List.append_of_mem ((hG.mem_rows).mpr hyS)
  have hSr : S.rows = lefts M₁ ++ (S.col s).2 :: lefts M₂ := by
    rw [← hG.rows, hsplit, lefts_append, lefts_cons_inl]
  have hnd := hG.rows_nodup
  rw [hSr] at hnd
  have hyM : (S.col s).2 ∉ lefts M₁ := fun h =>
    (List.nodup_append.mp hnd).2.2 _ h _ (by simp) rfl
  have hri : S.ri (S.col s).2 = (lefts M₁).length := by
    unfold WState.ri; rw [hSr, List.idxOf_append_of_notMem hyM]; simp
  have hκws : (Sum.inl κ : BCol) ≠ Sum.inl ws := fun h => hκG (h ▸ hwsm)
  have hS'c : ((S.cols.set s ((S.col s).1, ν)).insertIdx (if right then s + 1 else s) (ν, (S.col s).2)) =
      if right then C₁ ++ ((S.col s).1, ν) :: (ν, (S.col s).2) :: C₂ else C₁ ++ (ν, (S.col s).2) :: ((S.col s).1, ν) :: C₂ := by
    have e : S.cols = C₁ ++ S.col s :: C₂ := by rw [← hcs]; exact hC
    cases right
    · simp only [Bool.false_eq_true, if_false]
      conv_lhs => rw [e]
      exact set_insertIdx_left' hlC₁
    · simp only [if_true]
      conv_lhs => rw [e]
      exact set_insertIdx_right' hlC₁
  have hWc : W.map (Sum.inl : ℕ → BCol) = W₁.map Sum.inl ++ Sum.inl ws :: W₂.map Sum.inl := by
    conv_lhs => rw [hW]
    simp only [List.map_append, List.map_cons]
  obtain ⟨G', hc', hr', hO', hX', hmv⟩ := exists_stabX_gen G (d := Sum.inl ws) (κ := Sum.inl κ)
    (ν := Sum.inl ν)
    (if right then (W₁ ++ ws :: κ :: W₂).map Sum.inl ++ Q.map Sum.inr
      else (W₁ ++ κ :: ws :: W₂).map Sum.inl ++ Q.map Sum.inr)
    (if above then M₁ ++ Sum.inl (S.col s).2 :: Sum.inl ν :: M₂
      else M₁ ++ Sum.inl ν :: Sum.inl (S.col s).2 :: M₂)
    (if right then W₁.map Sum.inl ++ [Sum.inl ws] else W₁.map Sum.inl)
    (if right then W₂.map Sum.inl ++ Q.map Sum.inr else Sum.inl ws :: (W₂.map Sum.inl ++ Q.map Sum.inr))
    (if above then M₁ ++ [Sum.inl (S.col s).2] else M₁)
    (if above then M₂ else Sum.inl (S.col s).2 :: M₂)
    (by cases right <;> simp) (by rw [hG.cols, hWc]; cases right <;> simp)
    (by cases above <;> simp) (by rw [hsplit]; cases above <;> simp) hwsm
    (by cases right
        · right; exact ⟨_, rfl⟩
        · left; exact ⟨_, rfl⟩)
    (by rw [hmw.2]; cases above
        · right; exact ⟨_, rfl⟩
        · left; exact ⟨_, rfl⟩) hκG hνG
  have hne : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, q.1 ≠ ws ∧ q.1 ≠ κ := by
    intro q hq
    have hq1 : q.1 ∈ W₁ ∨ q.1 ∈ W₂ := by
      rcases List.mem_append.mp hq with h | h
      · exact Or.inl (List.of_mem_zip h).1
      · exact Or.inr (List.of_mem_zip h).1
    have hWnd := hG.W_nodup
    rw [hW, List.nodup_append, List.nodup_cons] at hWnd
    refine ⟨fun he => ?_, fun he => ?_⟩
    · rcases hq1 with h | h
      · exact hWnd.2.2 _ h _ List.mem_cons_self he
      · exact hWnd.2.1.1 (by rw [← he]; exact h)
    · rcases hq1 with h | h
      · exact hκW (by rw [← he]; exact List.mem_of_mem_take h)
      · exact hκW (by rw [← he]; exact List.mem_of_mem_drop h)
  have hold : ∀ q ∈ W₁.zip C₁ ++ W₂.zip C₂, G'.O (Sum.inl q.1) = Sum.inl q.2.1 ∧
      G'.X (Sum.inl q.1) = Sum.inl q.2.2 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hne q hq
    have hm := hG.marks q (by
      rw [hzip]; rcases List.mem_append.mp hq with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
    rw [hO', hX', Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h1)]
    exact hm
  refine ⟨_, if right then W₁ ++ ws :: κ :: W₂ else W₁ ++ κ :: ws :: W₂, G',
    ⟨by rw [hc']; cases right <;> simp, ?_, ?_, ?_⟩, ⟨fun c _ => ?_, ?_⟩, hmv⟩
  · rw [hS'c]; cases right <;> simp <;> omega
  · intro q hq
    rw [hS'c] at hq
    cases right
    · simp only [Bool.false_eq_true, if_false] at hq
      rw [List.zip_append hl₁] at hq
      simp only [List.zip_cons_cons, List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | rfl | hq
      · exact hold q (List.mem_append_left _ hq)
      · exact ⟨by rw [hO', Function.update_self], by rw [hX', Function.update_self, hmw.2]⟩
      · exact ⟨by rw [hO', Function.update_of_ne (Ne.symm hκws), hmw.1], by rw [hX', Function.update_of_ne (Ne.symm hκws), Function.update_self]⟩
      · exact hold q (List.mem_append_right _ hq)
    · simp only [if_true] at hq
      rw [List.zip_append hl₁] at hq
      simp only [List.zip_cons_cons, List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | rfl | hq
      · exact hold q (List.mem_append_left _ hq)
      · exact ⟨by rw [hO', Function.update_of_ne (Ne.symm hκws), hmw.1], by rw [hX', Function.update_of_ne (Ne.symm hκws), Function.update_self]⟩
      · exact ⟨by rw [hO', Function.update_self], by rw [hX', Function.update_self, hmw.2]⟩
      · exact hold q (List.mem_append_right _ hq)
  · rw [hr', hSr, hri]
    cases above
    · simp only [Bool.false_eq_true, if_false]
      have := insertIdx_append_len (l₁ := lefts M₁) (l := (S.col s).2 :: lefts M₂) (i := 0)
        (w := ν)
      simp only [Nat.add_zero, List.insertIdx_zero] at this
      rw [this]; simp [lefts_append, lefts_cons_inl]
    · simp only [if_true]
      rw [insertIdx_append_len]; simp [lefts_append, lefts_cons_inl]
  · rw [hO', hX', Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_of_ne (by simp)]; exact ⟨rfl, rfl⟩
  · rw [hr', hsplit]
    cases above
    · exact filter_ins_before nonInt (by simpa [nonInt] using hνc)
    · exact filter_ins_after nonInt (by simpa [nonInt] using hνc)

/-! ### Soundness of `step` and `run` -/

/-- **Lemma soundness.** -/
theorem step_sound {n : ℕ} {S S' : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {m : WMove} (h : step S m = some S') :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow), Real S' G' W' Q ∧
      SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  cases m with
  | c t =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, nonintB] at hc
    obtain ⟨W', G', h1, h2, h3⟩ := sound_c hG hc.1 hc.2
    exact ⟨n, W', G', h1, h2, h3⟩
  | r x y =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, nonintB] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    obtain ⟨W', G', r1, r2, r3⟩ := sound_r hG h1 h2 h3 h4
    exact ⟨n, W', G', r1, r2, r3⟩
  | dX p s x y =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
    exact sound_dX hG h1 h2 h3 h4 h5 h6 h7 h8
  | dO p s x y =>
    simp only [step] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
    exact sound_dO hG h1 h2 h3 h4 h5 h6 h7 h8
  | sO t right above ν =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact sound_sO hG right above hc.1.1 hc.1.2 hc.2
    · simp at h
  | sX t right above ν =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact sound_sX hG right above hc.1.1 hc.1.2 hc.2
    · simp at h

theorem run_sound {n : ℕ} {S S' : WState} {G : LabeledGrid n BCol BRow} {W : List ℕ}
    {Q : List (ℕ × Fin 3)} (hG : Real S G W Q) {ms : List WMove} (h : run S ms = some S') :
    ∃ (n' : ℕ) (W' : List ℕ) (G' : LabeledGrid n' BCol BRow), Real S' G' W' Q ∧
      SameOut G G' Q ∧ G.toGrid.MovesTo G'.toGrid := by
  induction ms generalizing n S G W with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨n, W, G, hG, SameOut.refl G Q, GridDiagram.MovesTo.refl _⟩
  | cons m ms ih =>
    simp only [run] at h
    rcases hs : step S m with _ | S₁
    · rw [hs] at h; simp at h
    · rw [hs] at h
      simp only [Option.bind_some] at h
      obtain ⟨n₁, W₁, G₁, h1, h2, h3⟩ := step_sound hG hs
      obtain ⟨n₂, W₂, G₂, k1, k2, k3⟩ := ih h1 h
      exact ⟨n₂, W₂, G₂, k1, h2.trans k2, h3.trans k3⟩

end OnLeConjecture.KnotTheory.BraidWindow
