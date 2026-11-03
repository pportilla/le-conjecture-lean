/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.TorusWordGridBaseWord

/-! # The first block

`docs/route-n/J11-torus-word-grid.tex`, Lemma *base case*: for `q = J + 1 ≥ 2`, the selected
grid of `β^q` is related by grid moves to the hybrid grid `H_{A+1,1}(β^J)`
(`exists_base`). The proof applies the block reduction to the first block of the selected
labeled grid of `β^q` (`baseGrid`), an `O`-stabilization (`LabeledGrid.exists_stabO`), three
commutations of rows and columns, the exchanges of the last outgoing arcs of the first and the
last block, and a renaming of the labels. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq C] [DecidableEq R]

/-- **`O`-stabilization.** A new column `κ` right of `d` and a new row `ν` right below `O d`, with
`O d := ν`, `O κ := O d` and `X κ := ν`. -/
theorem exists_stabO (G : LabeledGrid n C R) {l₁ l₂ : List C} {m₁ m₂ : List R} {d κ : C} {ν : R}
    (hc : G.cols = l₁ ++ d :: l₂) (hr : G.rows = m₁ ++ G.O d :: m₂) (hκ : κ ∉ G.cols)
    (hν : ν ∉ G.rows) :
    ∃ G' : LabeledGrid (n + 1) C R, G'.cols = l₁ ++ d :: κ :: l₂ ∧
      G'.rows = m₁ ++ ν :: G.O d :: m₂ ∧
      G'.O = Function.update (Function.update G.O d ν) κ (G.O d) ∧
      G'.X = Function.update G.X κ ν ∧ G.toGrid.MovesTo G'.toGrid := by
  have hdm : d ∈ G.cols := by rw [hc]; simp
  have hκd : κ ≠ d := fun h => hκ (h ▸ hdm)
  have hOdm : G.O d ∈ G.rows := G.O_mem d hdm
  have hνO : ν ≠ G.O d := fun h => hν (h ▸ hOdm)
  have hne : ∀ c ∈ G.cols, c ≠ κ := fun c hc h => hκ (h ▸ hc)
  have hcp : (l₁ ++ d :: κ :: l₂).Perm (κ :: G.cols) := by
    have e : l₁ ++ d :: κ :: l₂ = (l₁ ++ [d]) ++ κ :: l₂ := by simp
    rw [e, hc]
    exact List.perm_middle.trans (List.Perm.of_eq (by simp))
  have hrp : (m₁ ++ ν :: G.O d :: m₂).Perm (ν :: G.rows) := by
    rw [hr]; exact List.perm_middle
  have memc : ∀ c, c ∈ l₁ ++ d :: κ :: l₂ ↔ c = κ ∨ c ∈ G.cols := fun c => by
    rw [hcp.mem_iff, List.mem_cons]
  have memr : ∀ x, x ∈ m₁ ++ ν :: G.O d :: m₂ ↔ x = ν ∨ x ∈ G.rows := fun x => by
    rw [hrp.mem_iff, List.mem_cons]
  let G' : LabeledGrid (n + 1) C R :=
    { cols := l₁ ++ d :: κ :: l₂
      rows := m₁ ++ ν :: G.O d :: m₂
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
        have key : ∀ c, c ∈ l₁ ++ d :: κ :: l₂ →
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
  have hc' : G'.cols = (l₁ ++ [d]) ++ κ :: l₂ := by simp [G']
  have hx' : G'.rows = m₁ ++ ν :: (G.O d :: m₂) := rfl
  have hXκ : G'.X κ = ν := Function.update_self _ _ _
  have hOκ : G'.O κ = G.O d := Function.update_self _ _ _
  have hOd : G'.O d = ν := by
    simp only [G']; rw [Function.update_of_ne (Ne.symm hκd), Function.update_self]
  have hXd : G'.X d ≠ G.O d := by
    simp only [G']; rw [Function.update_of_ne (Ne.symm hκd)]; exact (G.O_ne_X d hdm).symm
  have hdm' : d ∈ G'.cols := by simp [G']
  have hD := G'.isDestabilization_destabO hc' hx' hXκ hOκ hOd hXd hdm'
    (Or.inr (by
      rw [G'.cpos_of_cols_eq (l₁ := l₁) (l₂ := κ :: l₂) rfl,
        G'.cpos_of_cols_eq (l₁ := l₁ ++ [d]) (l₂ := l₂) hc']; simp))
    (Or.inl (G'.rpos_succ_of_rows hx'))
  have he : (G'.destabO hc' hx' hXκ hOκ hOd hXd hdm').toGrid = G.toGrid := by
    apply toGrid_eq_of_data
    · rw [destabO_cols, hc]; simp
    · rw [destabO_rows, hr]
    · intro c hcm
      rw [destabO_cols] at hcm
      rw [destabO_O]
      by_cases hcd : c = d
      · subst hcd; rw [Function.update_self]
      · have hcm' : c ∈ G.cols := by
          rw [hc]; simp only [List.mem_append, List.mem_cons] at hcm ⊢; tauto
        rw [Function.update_of_ne hcd]
        simp only [G']
        rw [Function.update_of_ne (hne _ hcm'), Function.update_of_ne hcd]
    · intro c hcm
      rw [destabO_cols] at hcm
      have hcm' : c ∈ G.cols := by
        rw [hc]; simp only [List.mem_append, List.mem_cons] at hcm ⊢; tauto
      rw [destabO_X]
      simp only [G']
      rw [Function.update_of_ne (hne _ hcm')]
  refine ⟨G', rfl, rfl, rfl, rfl, ?_⟩
  rw [← he]
  exact hD.movesTo.symm

end LabeledGrid

namespace LabeledGrid

variable {n : ℕ} {C R : Type*} [DecidableEq R]

theorem rpos_lt_of_pairwise (G : LabeledGrid n C R) {Rl : R → R → Prop}
    (hasymm : ∀ a b, Rl a b → ¬ Rl b a) (hs : G.rows.Pairwise Rl) {a b : R} (ha : a ∈ G.rows)
    (hb : b ∈ G.rows) (h : Rl a b) : G.rpos a < G.rpos b := by
  rcases Nat.lt_trichotomy (G.rpos a) (G.rpos b) with h1 | h1 | h1
  · exact h1
  · exact absurd (G.rpos_inj ha h1 ▸ h) (hasymm _ _ h)
  · exact absurd (idxOf_rel_of_pairwise hs ha hb h1) (hasymm _ _ h)

end LabeledGrid

/-! ### The block reduction of the first block of `β^q` -/

/-- Levels for the block reduction of `β^{J+1}`: the arcs leaving the last occurrences in the last
block play the role of the rows `ι r` and are raised by one. -/
def lvB (A J : ℕ) : TorusRow → ℕ
  | Sum.inr (Sum.inr (b, t, c)) =>
    arcLv A t c.val + if b = J ∧ (c.val = 2 ∨ (c.val = 1 ∧ t = A - 1)) then 1 else 0
  | x => lvT A x

theorem lvB_arc (A J b t : ℕ) (c : Fin 3) : lvB A J (arc b t c) =
    arcLv A t c.val + if b = J ∧ (c.val = 2 ∨ (c.val = 1 ∧ t = A - 1)) then 1 else 0 := rfl

theorem arc_vals_base {A J b t : ℕ} (hb : b < J + 1) (c : Fin 3) :
    (subSw A (J + 1) 0 (arc b t c) = 4 * (J + 1) + 3 ∧
        lvB A J (arc b t c) = lvT A (arc b t c) + 1) ∨
      (subSw A (J + 1) 0 (arc b t c) ≤ 4 * (J + 1) + 2 ∧
        lvB A J (arc b t c) = lvT A (arc b t c)) := by
  have hc := c.isLt
  rw [subSw_arc, arcSub_zero, lvB_arc, lvT_arc]
  split_ifs <;> omega

theorem lvB_le {A J : ℕ} {x y : TorusRow} (hx : x ∈ wordArcs A (J + 1))
    (hy : y ∈ wordArcs A (J + 1)) (h : hybLtS A (J + 1) 0 x y) : lvB A J x ≤ lvB A J y := by
  obtain ⟨b, hb, t, ht, c, rfl⟩ := mem_wordArcs.mp hx
  obtain ⟨b', hb', t', ht', c', rfl⟩ := mem_wordArcs.mp hy
  have v1 := arc_vals_base (A := A) (t := t) hb c
  have v2 := arc_vals_base (A := A) (t := t') hb' c'
  unfold hybLtS at h
  omega

theorem baseGrid_blockData {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) :
    BlockData A (baseGrid A (J + 1) hA) (outArc A J) (lvB A J) [] (wordCols A 1 J) where
  cols := by rw [baseGrid_cols, wordCols_succ, blockCols_zero_eq]; simp
  O_cor t _ c := by rw [baseGrid_O, hybO_cor]
  X_cor0 t _ := by rw [baseGrid_X, baseX_cor]; simp [corX, inW]
  X_cor1 t _ := by rw [baseGrid_X, baseX_cor]; simp [corX, inW]
  X_cor2 t _ := by rw [baseGrid_X, baseX_cor]; simp [corX]
  inc_ne r t c := by
    unfold outArc; split_ifs <;> simp only [ne_eq, arc_inj_iff] <;> omega
  sorted := (baseRows_sorted A (J + 1)).imp_of_mem fun ha hb h =>
    lvB_le (mem_baseRows.mp ha) (mem_baseRows.mp hb) h
  lv_arc0 t _ := by rw [lvB_arc, if_neg (by omega)]; simp [arcLv]
  lv_arc1 t _ := by rw [lvB_arc, if_neg (by omega)]; simp [arcLv]
  lv_arc2 t _ := by rw [lvB_arc, if_neg (by omega)]; simp [arcLv]
  lv_inc r hr := by
    unfold outArc
    split_ifs with h0
    · subst h0; rw [lvB_arc, if_pos (by simp)]; simp [arcLv]
    · rw [lvB_arc, if_pos (by simp)]; simp [arcLv]; omega

/-! ### The prepared grid -/

/-- The rows after the block reduction of the first block of `β^{J+1}`. -/
def BaseRow (A J : ℕ) (x : TorusRow) : Prop :=
  (∃ r ≤ A, x = outArc A 0 r) ∨ ∃ b, 1 ≤ b ∧ b < J + 1 ∧ ∃ t < A, ∃ c : Fin 3, x = arc b t c

/-- The grid after the block reduction, the `O`-stabilization, and three commutations: columns
`V, B_{A-1}, …, B_0, κ` followed by the blocks `1, …, J`. -/
structure BaseState {n : ℕ} (A J : ℕ) (G : LabeledGrid n TorusCol TorusRow) : Prop where
  cols : G.cols = [cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0] ++ wordCols A 1 J
  O_V : G.O (cor 0 (A - 1) 1) = rRow 0
  O_κ : G.O (rCol 0) = outArc A 0 0
  O_B : ∀ s < A, G.O (cor 0 s 2) = arc 0 s 2
  O_w : ∀ c ∈ wordCols A 1 J, G.O c = hybO A 0 c
  X_V : G.X (cor 0 (A - 1) 1) = outArc A J A
  X_B : ∀ s < A, G.X (cor 0 s 2) = outArc A J (A - 1 - s)
  X_κ : G.X (rCol 0) = rRow 0
  X_w : ∀ c ∈ wordCols A 1 J, G.X c = baseX A (J + 1) c
  rows_iff : ∀ x, x ∈ G.rows ↔ x = rRow 0 ∨ BaseRow A J x
  sorted : G.rows.Pairwise (hybLtS A (J + 1) 0)

theorem outArc_ne_rRow0 (A : ℕ) {b r t : ℕ} : outArc A b r ≠ rRow t := by
  unfold outArc; split_ifs <;> exact arc_ne_rRow _ _ _ _

theorem hybLtS_rRow_zero {A K : ℕ} {b t : ℕ} (hb : b < K) (c : Fin 3) :
    hybLtS A K 0 (rRow 0) (arc b t c) := by
  unfold hybLtS
  rw [lvT_arc, subSw_arc, arcSub_zero]
  simp only [lvT_rRow, if_true, subSw_rRow]
  split_ifs <;> omega

theorem exists_baseState {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) :
    ∃ (n : ℕ) (G : LabeledGrid n TorusCol TorusRow), BaseState A J G ∧
      (baseGrid A (J + 1) hA).toGrid.MovesTo G.toGrid := by
  set G₀ := baseGrid A (J + 1) hA
  obtain ⟨m, G₂, -, hc₂, hsub₂, hmem₂, hO₂, hXV₂, hXB₂, hXo₂, hmv₂⟩ :=
    exists_blockReduction G₀ (baseGrid_blockData hA hJ) hA
  have hsort₂ : G₂.rows.Pairwise (hybLtS A (J + 1) 0) := (baseRows_sorted A (J + 1)).sublist hsub₂
  have hrow₂ : ∀ x, x ∈ G₂.rows ↔ BaseRow A J x := by
    intro x
    rw [hmem₂, baseGrid_rows, mem_baseRows, mem_wordArcs]
    constructor
    · rintro ⟨⟨b, hb, t, ht, c, rfl⟩, h1, h2⟩
      by_cases hb0 : b = 0
      · subst hb0
        have hc := c.isLt
        left
        rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 by omega) with hc0 | hc1 | hc2
        · exact absurd (by rw [show c = 0 from Fin.ext hc0]) (h2 t ht)
        · by_cases htA : t < A - 1
          · exact absurd (by rw [show c = 1 from Fin.ext hc1]) (h1 t htA)
          · refine ⟨0, by omega, ?_⟩
            rw [outArc_zero, show c = 1 from Fin.ext hc1, show t = A - 1 by omega]
        · refine ⟨A - t, by omega, ?_⟩
          rw [outArc_pos (by omega), show c = 2 from Fin.ext hc2, show A - (A - t) = t by omega]
      · exact Or.inr ⟨b, by omega, hb, t, ht, c, rfl⟩
    · rintro (⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩)
      · by_cases hr0 : r = 0
        · subst hr0
          rw [outArc_zero]
          refine ⟨⟨0, by omega, A - 1, by omega, 1, rfl⟩, ?_, ?_⟩
          · intro s hs h; simp only [arc_inj_iff] at h; omega
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
        · rw [outArc_pos hr0]
          refine ⟨⟨0, by omega, A - r, by omega, 2, rfl⟩, ?_, ?_⟩
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
          · intro s hs h; simp only [arc_inj_iff] at h; exact absurd h.2.2 (by decide)
      · refine ⟨⟨b, hb, t, ht, c, rfl⟩, ?_, ?_⟩
        · intro s hs h; simp only [arc_inj_iff] at h; omega
        · intro s hs h; simp only [arc_inj_iff] at h; omega
  have hshape : ∀ x, BaseRow A J x → ∃ b < J + 1, ∃ t < A, ∃ c : Fin 3, x = arc b t c := by
    rintro x (⟨r, hr, rfl⟩ | ⟨b, -, hb, t, ht, c, rfl⟩)
    · unfold outArc; split_ifs
      · exact ⟨0, by omega, A - 1, by omega, 1, rfl⟩
      · exact ⟨0, by omega, A - r, by omega, 2, rfl⟩
    · exact ⟨b, hb, t, ht, c, rfl⟩
  have ho₀ : outArc A 0 0 ∈ G₂.rows := (hrow₂ _).mpr (Or.inl ⟨0, by omega, rfl⟩)
  have hν : rRow 0 ∉ G₂.rows := fun h => by
    obtain ⟨b, -, t, -, c, h'⟩ := hshape _ ((hrow₂ _).mp h)
    exact arc_ne_rRow _ _ _ _ h'.symm
  have hκ : rCol 0 ∉ G₂.cols := by
    intro h
    rw [hc₂, List.mem_append, List.mem_append, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · simp at h
    · obtain ⟨s, -, -, h'⟩ := mem_blockBs.mp h; exact cor_ne_rCol _ _ _ _ h'.symm
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with h | h <;> exact cor_ne_rCol _ _ _ _ h.symm
    · exact rCol_not_mem_wordCols h
  have hOV : G₂.O (cor 0 (A - 1) 1) = outArc A 0 0 := by
    rw [hO₂, baseGrid_O, hybO_cor, outArc_zero]
  obtain ⟨m₁, m₂, hsplit⟩ := List.append_of_mem ho₀
  obtain ⟨G₃, hc₃, hr₃, hO₃, hX₃, hmv₃⟩ := G₂.exists_stabO (l₁ := blockBs 0 (A - 1))
    (l₂ := cor 0 (A - 1) 2 :: wordCols A 1 J) (d := cor 0 (A - 1) 1) (κ := rCol 0) (ν := rRow 0)
    (by rw [hc₂]; simp) (by rw [hOV]; exact hsplit) hκ hν
  rw [hOV] at hr₃ hO₃
  have hVκ : cor 0 (A - 1) 1 ≠ rCol 0 := cor_ne_rCol _ _ _ _
  have hnd₂ := G₂.rows_nodup
  rw [hsplit] at hnd₂
  have ho₀m₁ : outArc A 0 0 ∉ m₁ := fun h => (List.nodup_append.mp hnd₂).2.2 _ h _ (by simp) rfl
  have hsort₂' := hsort₂
  rw [hsplit, List.pairwise_append] at hsort₂'
  have hlvA := lvT_outArc (b := J) hA (le_refl A)
  have hlv0 := lvT_outArc (b := 0) (r := 0) hA (by omega)
  -- `ν` to the bottom
  obtain ⟨G₄, hc₄, hr₄, hO₄, hX₄, hmv₄⟩ := G₃.exists_moveRowDown (m₁ := []) (mid := m₁)
    (x := rRow 0) (m₂ := outArc A 0 0 :: m₂) (by rw [hr₃]; simp) (by
      intro z hz
      have hzr : z ∈ G₂.rows := by rw [hsplit]; simp [hz]
      have hzo := hsort₂'.2.2 z hz _ List.mem_cons_self
      unfold hybLtS at hzo
      rw [hlv0] at hzo
      rw [G₃.rowsNonint_comm]
      refine G₃.rowsNonint_of_short (cx := cor 0 (A - 1) 1) (cx' := rCol 0)
        (by rw [hc₃]; simp) (by rw [hc₃]; simp) (by rw [hO₃, Function.update_of_ne hVκ,
          Function.update_self]) (by rw [hX₃, Function.update_self]) ?_ ?_ ?_ ?_
      · left
        rw [G₃.cpos_of_cols_eq (l₁ := blockBs 0 (A - 1)) hc₃,
          G₃.cpos_of_cols_eq (l₁ := blockBs 0 (A - 1) ++ [cor 0 (A - 1) 1])
            (l₂ := cor 0 (A - 1) 2 :: wordCols A 1 J) (by rw [hc₃]; simp)]
        simp
      · exact fun h => hν (h ▸ hzr)
      · rw [hO₃, Function.update_self]; exact fun h => ho₀m₁ (h ▸ hz)
      · rw [hX₃, Function.update_of_ne hVκ, hXV₂]
        intro h; rw [h, hlvA] at hzo; omega)
  have hr₄' : G₄.rows = rRow 0 :: G₂.rows := by rw [hr₄, hsplit]; simp
  have hsort₄ : G₄.rows.Pairwise (hybLtS A (J + 1) 0) := by
    rw [hr₄']
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hsort₂⟩
    obtain ⟨b, hb, t, -, c, rfl⟩ := hshape _ ((hrow₂ y).mp hy)
    exact hybLtS_rRow_zero hb c
  have hmem₄ : ∀ x, x ∈ G₄.rows ↔ x = rRow 0 ∨ BaseRow A J x := fun x => by
    rw [hr₄', List.mem_cons, hrow₂]
  have rlt : ∀ a b, a ∈ G₄.rows → b ∈ G₄.rows → hybLtS A (J + 1) 0 a b → G₄.rpos a < G₄.rpos b :=
    fun a b ha hb h => G₄.rpos_lt_of_pairwise (fun _ _ => hybLtS_asymm) hsort₄ ha hb h
  have mo : ∀ r ≤ A, outArc A 0 r ∈ G₄.rows := fun r hr =>
    (hmem₄ _).mpr (Or.inr (Or.inl ⟨r, hr, rfl⟩))
  have mw : ∀ r ≤ A, outArc A J r ∈ G₄.rows := fun r hr => by
    refine (hmem₄ _).mpr (Or.inr (Or.inr ?_))
    unfold outArc; split_ifs
    · exact ⟨J, hJ, by omega, A - 1, by omega, 1, rfl⟩
    · exact ⟨J, hJ, by omega, A - r, by omega, 2, rfl⟩
  have mν : rRow 0 ∈ G₄.rows := (hmem₄ _).mpr (Or.inl rfl)
  have rν : ∀ x ∈ G₄.rows, x ≠ rRow 0 → G₄.rpos (rRow 0) < G₄.rpos x := by
    intro x hx hne
    rcases (hmem₄ x).mp hx with h | h
    · exact absurd h hne
    · obtain ⟨b, hb, t, -, c, rfl⟩ := hshape _ h
      exact rlt _ _ mν hx (hybLtS_rRow_zero hb c)
  have hlt_oo : ∀ {b r b' r' : ℕ}, r ≤ A → r' ≤ A →
      (hybLtS A (J + 1) 0 (outArc A b r) (outArc A b' r') ↔
      (4 * r < 4 * r' ∨ (4 * r = 4 * r' ∧ subSw A (J + 1) 0 (outArc A b r) <
        subSw A (J + 1) 0 (outArc A b' r')))) := fun hr hr' => by
    unfold hybLtS; rw [lvT_outArc hA hr, lvT_outArc hA hr']
  -- `κ` to the right of `B_0`
  have hBne : ∀ s, cor 0 s 2 ≠ cor 0 (A - 1) 1 := fun s h => by
    simp only [cor_inj_iff] at h; exact absurd h.2.2 (by decide)
  obtain ⟨G₅, hc₅, hr₅, hO₅, hX₅, hmv₅⟩ := G₄.exists_moveColRight
    (l₁ := blockBs 0 (A - 1) ++ [cor 0 (A - 1) 1]) (c := rCol 0) (mid := [cor 0 (A - 1) 2])
    (l₂ := wordCols A 1 J) (by rw [hc₄, hc₃]; simp) (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      subst hd
      unfold LabeledGrid.ColsNonint
      rw [hO₄, hX₄, hO₃, hX₃, Function.update_self, Function.update_self,
        Function.update_of_ne (cor_ne_rCol _ _ _ _), Function.update_of_ne (hBne _),
        Function.update_of_ne (cor_ne_rCol _ _ _ _), hO₂, baseGrid_O, hybO_cor,
        hXB₂ (A - 1) (by omega), show A - 1 - (A - 1) = 0 by omega,
        show arc 0 (A - 1) 2 = outArc A 0 1 by rw [outArc_pos one_ne_zero]]
      have h1 := rlt _ _ (mo 0 (by omega)) (mo 1 hA)
        ((hlt_oo (by omega) hA).mpr (Or.inl (by omega)))
      have h2 := rlt _ _ (mo 0 (by omega)) (mw 0 (by omega)) ((hlt_oo (by omega) (by omega)).mpr
        (Or.inr ⟨rfl, by
          rw [subSw_outArc hA (by omega), subSw_outArc hA (by omega)]
          simp [show J ≠ 0 by omega]⟩))
      have h3 := rν _ (mo 0 (by omega)) (outArc_ne_rRow0 A)
      apply nonintN_of_lt; left
      simp only [max_lt_iff, lt_min_iff]; omega)
  -- `V` to the left of the `B`'s
  obtain ⟨G₆, hc₆, hr₆, hO₆, hX₆, hmv₆⟩ := G₅.exists_moveColLeft (l₁ := [])
    (mid := blockBs 0 (A - 1)) (c := cor 0 (A - 1) 1)
    (l₂ := cor 0 (A - 1) 2 :: rCol 0 :: wordCols A 1 J) (by rw [hc₅]; simp) (by
      intro d hd
      obtain ⟨s, -, hs, rfl⟩ := mem_blockBs.mp hd
      unfold LabeledGrid.ColsNonint
      have hrp : ∀ x, G₅.rpos x = G₄.rpos x := fun x => by simp only [LabeledGrid.rpos, hr₅]
      have e1 : G₅.O (cor 0 s 2) = outArc A 0 (A - s) := by
        rw [hO₅, hO₄, hO₃, Function.update_of_ne (cor_ne_rCol _ _ _ _),
          Function.update_of_ne (hBne _), hO₂, baseGrid_O, hybO_cor, outArc_pos (by omega)]
        congr 1; omega
      have e2 : G₅.X (cor 0 s 2) = outArc A J (A - 1 - s) := by
        rw [hX₅, hX₄, hX₃, Function.update_of_ne (cor_ne_rCol _ _ _ _), hXB₂ s (by omega)]
      have e3 : G₅.O (cor 0 (A - 1) 1) = rRow 0 := by
        rw [hO₅, hO₄, hO₃, Function.update_of_ne hVκ, Function.update_self]
      have e4 : G₅.X (cor 0 (A - 1) 1) = outArc A J A := by
        rw [hX₅, hX₄, hX₃, Function.update_of_ne hVκ, hXV₂]
      rw [e1, e2, e3, e4, hrp, hrp, hrp, hrp]
      have h1 := rν _ (mo (A - s) (by omega)) (outArc_ne_rRow0 A)
      have h2 := rν _ (mw (A - 1 - s) (by omega)) (outArc_ne_rRow0 A)
      have h3 := rlt _ _ (mo (A - s) (by omega)) (mw A le_rfl) (by
        rw [hlt_oo (by omega) le_rfl, subSw_outArc hA (by omega), subSw_outArc hA le_rfl]
        by_cases hs0 : s = 0
        · right; subst hs0
          simp [show J ≠ 0 by omega, show A ≠ 0 by omega]
        · left; omega)
      have h4 := rlt _ _ (mw (A - 1 - s) (by omega)) (mw A le_rfl) (by
        rw [hlt_oo (by omega) le_rfl]; left; omega)
      apply nonintN_of_nested; left
      constructor <;> simp only [min_def, max_def] <;> split_ifs <;> omega)
  have hOchain : G₆.O = Function.update (Function.update G₂.O (cor 0 (A - 1) 1) (rRow 0))
      (rCol 0) (outArc A 0 0) := by rw [hO₆, hO₅, hO₄, hO₃]
  have hXchain : G₆.X = Function.update G₂.X (rCol 0) (rRow 0) := by rw [hX₆, hX₅, hX₄, hX₃]
  have hnotw : ∀ c ∈ wordCols A 1 J, c ≠ cor 0 (A - 1) 1 ∧ c ≠ rCol 0 ∧ ∀ s < A, c ≠ cor 0 s 2 := by
    intro c hc
    obtain ⟨b, hb, -, t, -, c', rfl⟩ := mem_wordCols.mp hc
    refine ⟨fun h => ?_, cor_ne_rCol _ _ _ _, fun s _ h => ?_⟩ <;> simp only [cor_inj_iff] at h <;>
      omega
  have hc₂w : ∀ c ∈ wordCols A 1 J, c ∈ G₂.cols := fun c hc => by
    rw [hc₂]; simp [hc]
  refine ⟨_, G₆, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hmv₂.trans (hmv₃.trans (hmv₄.trans (hmv₅.trans hmv₆)))⟩
  · rw [hc₆, blockBs_succ' hA]; simp
  · rw [hOchain, Function.update_of_ne hVκ, Function.update_self]
  · rw [hOchain, Function.update_self]
  · intro s hs
    rw [hOchain, Function.update_of_ne (cor_ne_rCol _ _ _ _), Function.update_of_ne (hBne _), hO₂,
      baseGrid_O, hybO_cor]
  · intro c hc
    rw [hOchain, Function.update_of_ne (hnotw c hc).2.1, Function.update_of_ne (hnotw c hc).1,
      hO₂, baseGrid_O]
  · rw [hXchain, Function.update_of_ne hVκ, hXV₂]
  · intro s hs; rw [hXchain, Function.update_of_ne (cor_ne_rCol _ _ _ _), hXB₂ s hs]
  · rw [hXchain, Function.update_self]
  · intro c hc
    rw [hXchain, Function.update_of_ne (hnotw c hc).2.1,
      hXo₂ c (hc₂w c hc) (hnotw c hc).1 (hnotw c hc).2.2, baseGrid_X]
  · intro x; rw [hr₆, hr₅]; exact hmem₄ x
  · rw [hr₆, hr₅]; exact hsort₄

/-! ### Exchanges and renaming -/

theorem blockBs_split {A s : ℕ} (hs : s < A) :
    blockBs 0 A = blockBs 0 s ++ cor 0 s 2 :: blockBs (s + 1) (A - s - 1) := by
  unfold blockBs
  rw [show A = s + (1 + (A - s - 1)) by omega, ← List.range'_append_1, ← List.range'_append_1]
  simp

theorem blockBs_length (t₀ k : ℕ) : (blockBs t₀ k).length = k := by simp [blockBs]

namespace BaseState

variable {n A J : ℕ} {G : LabeledGrid n TorusCol TorusRow}

theorem cpos_B (hG : BaseState A J G) {s : ℕ} (hs : s < A) : G.cpos (cor 0 s 2) = s + 1 := by
  rw [G.cpos_of_cols_eq (l₁ := [cor 0 (A - 1) 1] ++ blockBs 0 s)
    (l₂ := blockBs (s + 1) (A - s - 1) ++ [rCol 0] ++ wordCols A 1 J)
    (by rw [hG.cols, blockBs_split hs]; simp)]
  simp [blockBs_length]

theorem rowsNonint_outArc (hG : BaseState A J G) (hA : 1 ≤ A) (hJ : 1 ≤ J) {r : ℕ} (hr : r ≤ A) :
    G.RowsNonint (outArc A 0 r) (outArc A J r) := by
  have hpre : G.cols = ([cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0]) ++ wordCols A 1 J := hG.cols
  have hplen : ([cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0]).length = A + 2 := by
    simp [blockBs_length]
  have memB : ∀ s < A, cor 0 s 2 ∈ G.cols := fun s hs => by
    rw [hG.cols]; simp [mem_blockBs]; omega
  have memW : ∀ b t (c : Fin 3), 1 ≤ b → b < 1 + J → t < A → cor b t c ∈ G.cols :=
      fun b t c h1 h2 h3 => by
    rw [hpre, List.mem_append, mem_wordCols]; exact Or.inr ⟨b, h1, h2, t, h3, c, rfl⟩
  -- the `O`-column of the inner arc
  obtain ⟨ox, hox, eox, pox⟩ : ∃ ox ∈ G.cols, G.O ox = outArc A 0 r ∧ G.cpos ox = A - r + 1 := by
    by_cases h0 : r = 0
    · subst h0
      refine ⟨rCol 0, by rw [hG.cols]; simp, hG.O_κ, ?_⟩
      rw [G.cpos_of_cols_eq (l₁ := [cor 0 (A - 1) 1] ++ blockBs 0 A) (l₂ := wordCols A 1 J)
        (by rw [hG.cols]; simp)]
      simp [blockBs_length]
    · refine ⟨cor 0 (A - r) 2, memB _ (by omega), ?_, by rw [hG.cpos_B (by omega)]⟩
      rw [hG.O_B _ (by omega), outArc_pos h0]
  -- the `X`-column of the outer arc
  obtain ⟨xy, hxy, exy, pxy⟩ : ∃ xy ∈ G.cols, G.X xy = outArc A J r ∧ G.cpos xy = A - r := by
    by_cases hrA : r = A
    · subst hrA
      refine ⟨cor 0 (r - 1) 1, by rw [hG.cols]; simp, hG.X_V, ?_⟩
      rw [G.cpos_of_cols_eq (l₁ := []) (l₂ := blockBs 0 r ++ [rCol 0] ++ wordCols r 1 J)
        (by rw [hG.cols]; simp)]; simp
    · refine ⟨cor 0 (A - 1 - r) 2, memB _ (by omega), ?_, by
        rw [hG.cpos_B (by omega)]; omega⟩
      rw [hG.X_B _ (by omega)]; congr 1; omega
  -- the `X`-column of the inner arc, in block `1`
  obtain ⟨tx, cx, htx, exx, hxpos⟩ : ∃ (tx : ℕ) (cx : Fin 3), tx < A ∧
      G.X (cor 1 tx cx) = outArc A 0 r ∧
        3 * tx + cx.val = if r = A then 1 else 3 * (A - 1 - r) := by
    by_cases hrA : r = A
    · subst hrA
      refine ⟨0, 1, by omega, ?_, by simp⟩
      rw [hG.X_w _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, 0, by omega, 1, rfl⟩), baseX_cor]
      simp [corX, inW]
    · refine ⟨A - 1 - r, 0, by omega, ?_, by simp [hrA]⟩
      rw [hG.X_w _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, A - 1 - r, by omega, 0, rfl⟩), baseX_cor]
      simp only [corX, if_true, inW, one_ne_zero, if_false, Nat.sub_self]
      congr 1; omega
  -- the `O`-column of the outer arc, in block `J`
  obtain ⟨ty, cy, hty, eoy, hypos⟩ : ∃ (ty : ℕ) (cy : Fin 3), ty < A ∧
      G.O (cor J ty cy) = outArc A J r ∧ 3 * ty + cy.val = if r = 0 then 3 * (A - 1) + 1
        else 3 * (A - r) + 2 := by
    by_cases h0 : r = 0
    · subst h0
      refine ⟨A - 1, 1, by omega, ?_, by simp⟩
      rw [hG.O_w _ (mem_wordCols.mpr ⟨J, hJ, by omega, A - 1, by omega, 1, rfl⟩), hybO_cor,
        outArc_zero]
    · refine ⟨A - r, 2, by omega, ?_, by simp [h0]⟩
      rw [hG.O_w _ (mem_wordCols.mpr ⟨J, hJ, by omega, A - r, by omega, 2, rfl⟩), hybO_cor,
        outArc_pos h0]
  have hxm : cor 1 tx cx ∈ wordCols A 1 J :=
    mem_wordCols.mpr ⟨1, le_rfl, by omega, tx, htx, cx, rfl⟩
  have p1 := G.length_le_cpos_of_mem hpre hxm
  rw [hplen] at p1
  have p2 : G.cpos (cor 1 tx cx) < G.cpos (cor J ty cy) := by
    by_cases hJ1 : J = 1
    · subst hJ1
      have hc1 : G.cols =
          ([cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0]) ++ blockCols A 1 ++ [] := by
        rw [hpre, wordCols_succ]; simp [wordCols]
      rw [cpos_cor G hc1 htx, cpos_cor G hc1 hty]
      split_ifs at hxpos hypos <;> omega
    · have hc2 : G.cols =
          (([cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0]) ++ wordCols A 1 (J - 1)) ++
          blockCols A J := by
        rw [hpre]
        conv_lhs => rw [show J = J - 1 + 1 by omega, wordCols_succ', show 1 + (J - 1) = J by omega]
        simp
      exact G.cpos_lt_of_mem_append hc2
        (List.mem_append_right _ (mem_wordCols.mpr ⟨1, le_rfl, by omega, tx, htx, cx, rfl⟩))
        (mem_blockCols.mpr ⟨ty, hty, cy, rfl⟩)
  refine G.rowsNonint_of_cols hox (memW 1 tx cx le_rfl (by omega) htx)
    (memW J ty cy hJ (by omega) hty) hxy eox exx eoy exy ?_
  apply nonintN_of_nested; left
  rw [pox, pxy]
  constructor <;> simp only [min_def, max_def] <;> split_ifs <;> omega

end BaseState

/-- Renaming of the columns after the first block: `V ↦ ρ 0`, `B_r ↦ ρ (A - r)`, `κ ↦ ρ (A + 1)`,
and the blocks move down by one. -/
def baseF (A : ℕ) : TorusCol → TorusCol
  | Sum.inl _ => rCol (A + 1)
  | Sum.inr (b, t, c) => if b = 0 then (if c = 2 then rCol (t + 1) else rCol 0) else cor (b - 1) t c

/-- A left inverse of `baseF` on the prepared columns. -/
def baseFinv (A : ℕ) : TorusCol → TorusCol
  | Sum.inl c => if c = 0 then cor 0 (A - 1) 1 else if c = A + 1 then rCol 0 else cor 0 (c - 1) 2
  | Sum.inr (b, t, c) => cor (b + 1) t c

theorem baseF_rCol (A c : ℕ) : baseF A (rCol c) = rCol (A + 1) := rfl

theorem baseF_cor (A b t : ℕ) (c : Fin 3) : baseF A (cor b t c) =
    if b = 0 then (if c = 2 then rCol (t + 1) else rCol 0) else cor (b - 1) t c := rfl

theorem baseFinv_rCol (A c : ℕ) : baseFinv A (rCol c) =
    if c = 0 then cor 0 (A - 1) 1 else if c = A + 1 then rCol 0 else cor 0 (c - 1) 2 := rfl

theorem baseFinv_cor (A b t : ℕ) (c : Fin 3) : baseFinv A (cor b t c) = cor (b + 1) t c := rfl

theorem map_baseF_blockBs (A k : ℕ) : (blockBs 0 k).map (baseF A) = rColsR 1 k := by
  induction k with
  | zero => simp [blockBs, rColsR]
  | succ k ih =>
    rw [blockBs_succ, List.map_append, ih, rColsR_append]
    simp [baseF_cor, rColsR, add_comm]

theorem map_baseF_wordCols (A J : ℕ) :
    ∀ b₀, (wordCols A (b₀ + 1) J).map (baseF A) = wordCols A b₀ J := by
  induction J with
  | zero => intro b₀; simp [wordCols]
  | succ J ih =>
    intro b₀
    rw [wordCols_succ, List.map_append, ih (b₀ + 1), wordCols_succ]
    congr 1
    simp [blockCols, blockColsR, List.map_flatMap, baseF_cor]

theorem corX_inW_eq {A q b : ℕ} (hb : 1 ≤ b) (t : ℕ) (c : Fin 3) :
    corX A (inW A q) b t c = corX A (inRow A) b t c := by
  simp [corX, inW, inRow, show b ≠ 0 by omega]

theorem stRow_of_base {A J : ℕ} {x : TorusRow} (h : x = rRow 0 ∨ BaseRow A J x) :
    StRow A 1 J A x := by
  rcases h with rfl | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b, hb1, hb, t, ht, c, rfl⟩)))

theorem oRes_one_succ (A s : ℕ) : oRes A 1 (s + 1) = A + 1 - s := by
  unfold oRes; rw [if_neg (by omega)]; omega

theorem xRes_one_zero (A : ℕ) : xRes A 1 0 = A + 1 := by
  unfold xRes; rw [if_pos (by omega)]; omega

theorem xRes_one_succ (A s : ℕ) (hs : s ≤ A) : xRes A 1 (s + 1) = A - s := by
  unfold xRes; rw [if_pos (by omega)]; omega

theorem xRes_one_last (A : ℕ) : xRes A 1 (A + 1) = 0 := by
  unfold xRes; rw [if_pos le_rfl]; omega

theorem rCols_base (A : ℕ) : rCols (A + 1 + 1) = [rCol 0] ++ rColsR 1 A ++ [rCol (A + 1)] := by
  rw [rCols, show A + 1 + 1 = 1 + (A + 1) by ring, rColsR_append, rColsR_append]
  simp [rColsR, add_comm]

/-- After the exchanges, renaming the labels gives the hybrid grid `H_{A+1,1}(β^J)`. -/
theorem BaseState.exists_isHybrid {n A J : ℕ} {G : LabeledGrid n TorusCol TorusRow}
    (hG : BaseState A J G) (hA : 1 ≤ A) (hJ : 1 ≤ J) :
    ∃ G' : LabeledGrid n TorusCol TorusRow, IsHybrid A 1 J G' ∧ G.toGrid.MovesTo G'.toGrid := by
  have hshape : ∀ z ∈ G.rows, RowShape A (J + 1) z := by
    intro z hz
    rcases (hG.rows_iff z).mp hz with rfl | ⟨r, hr, rfl⟩ | ⟨b, -, hb, t, ht, c, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · unfold outArc; split_ifs
      · exact Or.inr (Or.inr ⟨0, by omega, A - 1, by omega, 1, rfl⟩)
      · exact Or.inr (Or.inr ⟨0, by omega, A - r, by omega, 2, rfl⟩)
    · exact Or.inr (Or.inr ⟨b, hb, t, ht, c, rfl⟩)
  have hJ' : J + 1 - 1 = J := by omega
  obtain ⟨G₁, hc, hO, hX, hm, hs, hmv⟩ := G.exists_swapOuts hA (by omega) hshape hG.sorted
    (fun r hr => by
      rw [hJ']
      refine ⟨(hG.rows_iff _).mpr (Or.inr (Or.inl ⟨r, hr, rfl⟩)), (hG.rows_iff _).mpr ?_⟩
      right; right
      unfold outArc
      split_ifs
      · exact ⟨J, hJ, by omega, A - 1, by omega, 1, rfl⟩
      · exact ⟨J, hJ, by omega, A - r, by omega, 2, rfl⟩)
    (fun r hr => by rw [hJ']; exact hG.rowsNonint_outArc hA hJ hr)
  have hrows : ∀ x, x ∈ G₁.rows ↔ x = rRow 0 ∨ BaseRow A J x :=
    fun x => (hm x).trans (hG.rows_iff x)
  have hcols : G₁.cols = [cor 0 (A - 1) 1] ++ blockBs 0 A ++ [rCol 0] ++ wordCols A 1 J :=
    hc.trans hG.cols
  have hmemc : ∀ c ∈ G₁.cols, c = cor 0 (A - 1) 1 ∨ (∃ s < A, c = cor 0 s 2) ∨ c = rCol 0 ∨
      ∃ b, 1 ≤ b ∧ b < 1 + J ∧ ∃ t < A, ∃ c' : Fin 3, c = cor b t c' := by
    intro c hcm
    rw [hcols] at hcm
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hcm
    rcases hcm with ((h | h) | h) | h
    · exact Or.inl h
    · obtain ⟨s, -, hs, rfl⟩ := mem_blockBs.mp h; exact Or.inr (Or.inl ⟨s, by omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (mem_wordCols.mp h)))
  have hf : ∀ c ∈ G₁.cols, baseFinv A (baseF A c) = c := by
    intro c hcm
    rcases hmemc c hcm with rfl | ⟨s, hs, rfl⟩ | rfl | ⟨b, hb1, -, t, -, c', rfl⟩
    · rw [baseF_cor, if_pos rfl, if_neg (by decide), baseFinv_rCol, if_pos rfl]
    · rw [baseF_cor, if_pos rfl, if_pos rfl, baseFinv_rCol, if_neg (by omega), if_neg (by omega)]
      congr 1
    · rw [baseF_rCol, baseFinv_rCol, if_neg (by omega), if_pos rfl]
    · rw [baseF_cor, if_neg (by omega), baseFinv_cor, Nat.sub_add_cancel hb1]
  have hg : ∀ x ∈ G₁.rows, absGinv A (absG A x) = x := by
    intro x hx
    rcases (hrows x).mp hx with rfl | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩
    · rfl
    · rw [absG_outArc hA hr]; simp [inRow]
    · rw [absG_arc, if_neg (by omega), absGinv_arc, Nat.sub_add_cancel hb1]
  refine ⟨G₁.relabel (baseF A) (baseFinv A) (absG A) (absGinv A) hf hg, ⟨?_, ?_, ?_, ?_, ?_⟩,
    hmv.trans (by rw [LabeledGrid.toGrid_relabel])⟩
  · change G₁.cols.map (baseF A) = hybCols A 1 J
    rw [hcols, hybCols, rCols_base, List.map_append, List.map_append, List.map_append,
      map_baseF_blockBs, map_baseF_wordCols A J 0]
    simp [baseF_cor, baseF_rCol]
  · intro c hcm
    change absG A (G₁.O (baseFinv A c)) = hybO A 1 c
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcm
    rw [hf c₀ hc₀, hO]
    rcases hmemc c₀ hc₀ with rfl | ⟨s, hs, rfl⟩ | rfl | ⟨b, hb1, hbJ, t, ht, c', rfl⟩
    · rw [hG.O_V, baseF_cor, if_pos rfl, if_neg (by decide), hybO_rCol]
      simp [absG_rRow, oRes, winO]
    · have h1 := oRes_one_succ A s
      rw [hG.O_B s hs, baseF_cor, if_pos rfl, if_pos rfl, hybO_rCol, absG_arc, h1]
      simp only [if_true]
      unfold winO
      rw [if_pos (by omega)]
      congr 1; omega
    · rw [hG.O_κ, baseF_rCol, hybO_rCol, absG_outArc hA (by omega)]
      simp [inRow, winO, oRes]
    · rw [hG.O_w _ (mem_wordCols.mpr ⟨b, hb1, hbJ, t, ht, c', rfl⟩), hybO_cor, baseF_cor,
        if_neg (by omega), hybO_cor, absG_arc, if_neg (by omega)]
  · intro c hcm
    change absG A (G₁.X (baseFinv A c)) = hybX A 1 J c
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hcm
    rw [hf c₀ hc₀, hX]
    rcases hmemc c₀ hc₀ with rfl | ⟨s, hs, rfl⟩ | rfl | ⟨b, hb1, hbJ, t, ht, c', rfl⟩
    · have h1 := xRes_one_zero A
      rw [hG.X_V, baseF_cor, if_pos rfl, if_neg (by decide), hybX_rCol, absG_outArc hA le_rfl,
        h1]
      unfold winX
      rw [if_pos (by omega)]
      congr 1
    · have h1 := xRes_one_succ A s (by omega)
      rw [hG.X_B s hs, baseF_cor, if_pos rfl, if_pos rfl, hybX_rCol, absG_outArc hA (by omega), h1]
      unfold winX
      rw [if_pos (by omega)]
      congr 1; omega
    · have h1 := xRes_one_last A
      rw [hG.X_κ, baseF_rCol, hybX_rCol, absG_rRow, if_pos rfl, h1]
      unfold winX
      rw [if_neg (by omega)]
    · rw [hG.X_w _ (mem_wordCols.mpr ⟨b, hb1, hbJ, t, ht, c', rfl⟩), baseX_cor,
        corX_inW_eq hb1, baseF_cor, if_neg (by omega), hybX_cor, absG_corX hA hb1 ht]
  · intro x
    change x ∈ G₁.rows.map (absG A) ↔ HybRow A 1 J x
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (hrows y).mp hy with rfl | ⟨r, hr, rfl⟩ | ⟨b, hb1, hb, t, ht, c, rfl⟩
      · exact Or.inl rfl
      · rw [absG_outArc hA hr]; exact Or.inr (Or.inr (Or.inl ⟨r, hr, by simp [inRow]⟩))
      · rw [absG_arc, if_neg (by omega)]
        exact Or.inr (Or.inr (Or.inr ⟨b - 1, by omega, t, ht, c, rfl⟩))
    · rintro (rfl | ⟨t, h1, h2, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨b, hb, t, ht, c, rfl⟩)
      · exact ⟨rRow 0, (hrows _).mpr (Or.inl rfl), rfl⟩
      · omega
      · exact ⟨outArc A 0 r, (hrows _).mpr (Or.inr (Or.inl ⟨r, hr, rfl⟩)),
          by rw [absG_outArc hA hr]; simp [inRow]⟩
      · refine ⟨arc (b + 1) t c, (hrows _).mpr (Or.inr (Or.inr ⟨b + 1, by omega, by omega, t, ht,
          c, rfl⟩)), ?_⟩
        rw [absG_arc, if_neg (by omega)]; rfl
  · change (G₁.rows.map (absG A)).Pairwise (hybLtS A J 0)
    exact List.pairwise_map.mpr (hs.imp_of_mem fun ha hb h =>
      absorb_mono (k := 1) hA (stRow_of_base ((hrows _).mp ha)) (stRow_of_base ((hrows _).mp hb)) h)

/-- **Lemma base case.** For `J ≥ 1`, the selected grid of `β^{J+1}` is related by grid moves to
the hybrid grid `H_{A+1,1}(β^J)`. -/
theorem exists_base {A J : ℕ} (hA : 1 ≤ A) (hJ : 1 ≤ J) :
    ∃ (n : ℕ) (G : LabeledGrid n TorusCol TorusRow), IsHybrid A 1 J G ∧
      (wordGrid (wordPow (betaWord A) (J + 1))).MovesTo G.toGrid := by
  obtain ⟨n, G, hG, hmv⟩ := exists_baseState hA hJ
  obtain ⟨G', hG', hmv'⟩ := hG.exists_isHybrid hA hJ
  exact ⟨n, G', hG', ((baseGrid_movesTo_wordGrid hA).symm.trans hmv).trans hmv'⟩

end OnLeConjecture.KnotTheory
