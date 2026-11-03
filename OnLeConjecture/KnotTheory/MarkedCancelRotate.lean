/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.MarkedCancelFwd
public import OnLeConjecture.KnotTheory.MarkedCancelSlide
public import OnLeConjecture.KnotTheory.SignedWordGridMovesTransport

/-!
# Slides and cyclic rotations of marked word grids

* `mfwd_slide`, `mfwd_slide_back`: the protected block slides from the arc leaving a corner `p`
  to the arc leaving `sM v p`, and back (`movesTo_insertBlock_slide`).
* `mfwd_rotate`: the cyclic rotation `x ++ y ↦ y ++ x` of the word lifts to marked word grids, with
  the marked corner transported by `SignedGrid.rotL`. The block is first moved after the columns
  of `x` (first framing fact), the columns are rotated cyclically, and the result is recognized
  through `toGrid_eq_of_image`. The matching is transported by `sM_symm_transport`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid

variable {m : ℕ}

/-! ### Slides -/

section Slides

variable (v : SignedAdjacentWord m) (hv : 0 < v.length) (p : Fin v.length × Fin 3)

theorem markBlock_hr_not_mem {k : ℕ} (κ : Fin v.length × Fin 3 → ℕ) (H : GridDiagram (k + 1))
    (hX : H.X 0 = 0) (hO : H.O (Fin.last k) = 0) (i : Fin (k + 2)) :
    (markBlock v H hX hO).hr i ∉ (plainGrid v κ hv).rows := by
  intro hi
  obtain ⟨q, hq⟩ := mem_plainGrid_rows.mp hi
  rw [stdBlock_hr] at hq
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hq
  have := q.1.isLt
  omega

/-- **Slide to the next arc.** -/
theorem mfwd_slide : MFwd v hv p v hv (sM v p) := by
  intro k H hX hO M hM
  obtain ⟨κ, hκ, rfl⟩ := hM
  refine ⟨_, ⟨κ, hκ, rfl⟩, ?_⟩
  have hz : (Sum.inr ((sM v p).1.val, (sM v p).2) : BCol) ∈ (plainGrid v κ hv).cols :=
    mem_plainGrid_cols.mpr ⟨_, rfl⟩
  exact movesTo_insertBlock_slide hz
    (by rw [plainGrid_X, Equiv.symm_apply_apply]) (plainGrid_O v κ hv _)
    (markBlock_hr_not_mem v hv κ H hX hO) _ _

/-- **Slide to the previous arc.** -/
theorem mfwd_slide_back : MFwd v hv p v hv ((sM v).symm p) := by
  intro k H hX hO M hM
  obtain ⟨κ, hκ, rfl⟩ := hM
  refine ⟨_, ⟨κ, hκ, rfl⟩, ?_⟩
  have hz : (Sum.inr (p.1.val, p.2) : BCol) ∈ (plainGrid v κ hv).cols :=
    mem_plainGrid_cols.mpr ⟨_, rfl⟩
  exact (movesTo_insertBlock_slide hz (plainGrid_X v κ hv p) (plainGrid_O v κ hv p)
    (markBlock_hr_not_mem v hv κ H hX hO) _ _).symm

end Slides

/-! ### Labeled grids at an equal size -/

section Cast

variable {n n' : ℕ} {C R : Type*}

/-- A labeled grid viewed at an equal size. -/
def castLG (h : n = n') (G : LabeledGrid n C R) : LabeledGrid n' C R := h ▸ G

theorem castLG_cols (h : n = n') (G : LabeledGrid n C R) : (castLG h G).cols = G.cols := by
  subst h; rfl

theorem castLG_rows (h : n = n') (G : LabeledGrid n C R) : (castLG h G).rows = G.rows := by
  subst h; rfl

theorem castLG_O (h : n = n') (G : LabeledGrid n C R) : (castLG h G).O = G.O := by
  subst h; rfl

theorem castLG_X (h : n = n') (G : LabeledGrid n C R) : (castLG h G).X = G.X := by
  subst h; rfl

theorem movesTo_castLG [DecidableEq R] (h : n = n') (G : LabeledGrid n C R) :
    G.toGrid.MovesTo (castLG h G).toGrid := by
  subst h; exact GridDiagram.MovesTo.refl _

end Cast

/-! ### Cyclic rotation of the columns of a labeled grid -/

section RotateCols

variable {n : ℕ} {C R : Type*} [DecidableEq R]

/-- **Cyclic rotation of columns.** -/
theorem movesTo_withCols_rotate (G : LabeledGrid n C R) {l₁ l₂ : List C}
    (h : G.cols = l₁ ++ l₂) :
    G.toGrid.MovesTo
      (G.withCols (l₂ ++ l₁) (by rw [h]; exact List.perm_append_comm)).toGrid := by
  induction l₁ generalizing G l₂ with
  | nil =>
    have he : (G.withCols (l₂ ++ []) (by rw [h]; exact List.perm_append_comm)).toGrid =
        G.toGrid := toGrid_eq_of_data _ _ (by change l₂ ++ [] = G.cols; rw [h]; simp) rfl
      (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he]
  | cons x l₁ ih =>
    have h' : G.cols = x :: (l₁ ++ l₂) := by rw [h]; rfl
    have hm1 := G.movesTo_rotateCols h'
    set G₁ := G.withCols ((l₁ ++ l₂) ++ [x])
      (by rw [h']; exact List.perm_append_singleton x _) with hG₁
    have hG₁c : G₁.cols = l₁ ++ (l₂ ++ [x]) := by simp [hG₁, withCols]
    have hm2 := ih G₁ hG₁c
    have he : (G₁.withCols ((l₂ ++ [x]) ++ l₁) (by rw [hG₁c]; exact
        List.perm_append_comm)).toGrid =
        (G.withCols (l₂ ++ x :: l₁) (by rw [h]; exact List.perm_append_comm)).toGrid :=
      toGrid_eq_of_data _ _ (by simp [withCols]) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    rw [he] at hm2
    exact hm1.trans hm2

end RotateCols

/-! ### Transport of the matching -/

section TransportM

variable {v v' : SignedAdjacentWord m}

/-- **The matching is transported** along a bijection of letters preserving the letters and the
cyclic gaps. -/
theorem sM_symm_transport (τ : Fin v.length ≃ Fin v'.length)
    (hlet : ∀ h, v'[(τ h).val] = v[h.val])
    (hgap : ∀ p q : Fin v.length × Fin 3,
      v'.cornerGap (τ p.1, p.2) (τ q.1, q.2) = v.cornerGap p q)
    (q : Fin v.length × Fin 3) :
    (sM v').symm (τ q.1, q.2) = (τ ((sM v).symm q).1, ((sM v).symm q).2) := by
  obtain ⟨hp1, hp2⟩ := sM_symm_min v q
  obtain ⟨hq1, hq2⟩ := sM_symm_min v' (τ q.1, q.2)
  obtain ⟨p₁, hp₁⟩ := transport_surj τ ((sM v').symm (τ q.1, q.2))
  have hh : v.oHeight2 p₁ = v.xHeight2 q := by
    rw [← oHeight2_transport τ hlet, hp₁, hq1, xHeight2_transport τ hlet]
  have h1 := hp2 p₁ hh
  have h2 := hq2 (τ ((sM v).symm q).1, ((sM v).symm q).2)
    (by rw [oHeight2_transport τ hlet, xHeight2_transport τ hlet, hp1])
  rw [← hp₁, hgap, hgap] at h2
  have he : p₁ = (sM v).symm q := gap_inj v (le_antisymm h2 h1)
  rw [← hp₁, he]

theorem sM_transport (τ : Fin v.length ≃ Fin v'.length)
    (hlet : ∀ h, v'[(τ h).val] = v[h.val])
    (hgap : ∀ p q : Fin v.length × Fin 3,
      v'.cornerGap (τ p.1, p.2) (τ q.1, q.2) = v.cornerGap p q)
    (p : Fin v.length × Fin 3) :
    sM v' (τ p.1, p.2) = (τ (sM v p).1, (sM v p).2) := by
  have h := sM_symm_transport τ hlet hgap (sM v p)
  rw [Equiv.symm_apply_apply] at h
  rw [← h, Equiv.apply_symm_apply]

end TransportM


/-! ### Cyclic rotation of marked word grids -/

section Rotate

variable (x y : SignedAdjacentWord m)

theorem rotL_symm_val (h : Fin (y ++ x).length) :
    ((rotL x y).symm h).val = if h.val < y.length then h.val + x.length else h.val - y.length :=
  rfl

/-- The corners of `y ++ x`, transported to `x ++ y`, are the corners of `y` followed by those of
`x`. -/
theorem sCols_rot : (sCols (y ++ x)).map (fun q => ((rotL x y).symm q.1, q.2)) =
    (sCols (x ++ y)).drop (x.length * 3) ++ (sCols (x ++ y)).take (x.length * 3) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_drop, List.length_take,
      sCols_length]
    omega
  · intro i h1 h2
    simp only [List.length_map, sCols_length, List.length_append] at h1
    have hd : ((sCols (x ++ y)).drop (x.length * 3)).length = y.length * 3 := by
      simp only [List.length_drop, sCols_length, List.length_append]; omega
    rw [List.getElem_map, sCols_getElem]
    by_cases hi : i < y.length * 3
    · rw [List.getElem_append_left (by rw [hd]; exact hi), List.getElem_drop, sCols_getElem]
      apply Prod.ext
      · apply Fin.ext
        rw [rotL_symm_val]
        simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat]
        rw [if_pos (by omega)]
        omega
      · apply Fin.ext
        simp only [finProdFinEquiv_symm_apply, Fin.coe_modNat]
        omega
    · rw [List.getElem_append_right (by rw [hd]; omega), List.getElem_take, sCols_getElem]
      simp only [hd]
      apply Prod.ext
      · apply Fin.ext
        rw [rotL_symm_val]
        simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat]
        rw [if_neg (by omega)]
        omega
      · apply Fin.ext
        simp only [finProdFinEquiv_symm_apply, Fin.coe_modNat]
        omega

theorem key_inj_of_lt {N a a' b b' : ℕ} (hb : b < N) (hb' : b' < N)
    (h : a * N + b = a' * N + b') : a = a' ∧ b = b' := by
  rcases Nat.lt_trichotomy a a' with ha | ha | ha
  · have := (key_lt_iff hb hb').mpr (Or.inl ha); omega
  · subst ha; constructor <;> omega
  · have := (key_lt_iff hb' hb).mpr (Or.inl ha); omega

/-- **Cyclic rotation of marked word grids.** -/
theorem mfwd_rotate (hxy : 0 < (x ++ y).length) (hyx : 0 < (y ++ x).length)
    (p : Fin (x ++ y).length × Fin 3) :
    MFwd (x ++ y) hxy p (y ++ x) hyx (rotL x y p.1, p.2) := by
  intro k H hX hO M hM
  obtain ⟨κ, hκ, rfl⟩ := hM
  have hlen : (x ++ y).length = (y ++ x).length := rot_length x y
  set N := (x ++ y).length * 3 with hN
  have hfpe : ∀ q : Fin (x ++ y).length × Fin 3, (finProdFinEquiv q).val < N :=
    fun q => (finProdFinEquiv q).isLt
  set κi : Fin (x ++ y).length × Fin 3 → ℕ := fun q => κ q * N + (finProdFinEquiv q).val
    with hκi
  have hκi_adm : ∀ a b, (x ++ y).oHeight2 a < (x ++ y).oHeight2 b → κi a < κi b := fun a b h =>
    (key_lt_iff (hfpe a) (hfpe b)).mpr (Or.inl (hκ a b h))
  have hκi_inj : ∀ a b, κi a = κi b → a = b := fun a b h => by
    have := (key_inj_of_lt (hfpe a) (hfpe b) h).2
    exact finProdFinEquiv.injective (Fin.ext this)
  have hm1 := markedGrid_movesTo_of_keys (x ++ y) hxy p H hX hO hκ hκi_adm
  -- the transported corners
  set τc : Fin (y ++ x).length × Fin 3 → Fin (x ++ y).length × Fin 3 :=
    fun q => ((rotL x y).symm q.1, q.2) with hτc
  have hτc_inj : ∀ a b, τc a = τc b → a = b := fun a b h => by
    simp only [hτc, Prod.mk.injEq] at h
    exact Prod.ext ((rotL x y).symm.injective h.1) h.2
  have hτc_up : ∀ q : Fin (x ++ y).length × Fin 3, τc (rotL x y q.1, q.2) = q := fun q => by
    simp [hτc]
  have hτc_surj : ∀ q, ∃ q', τc q' = q := fun q => ⟨_, hτc_up q⟩
  have hoH : ∀ q, (y ++ x).oHeight2 q = (x ++ y).oHeight2 (τc q) := fun q => by
    have := oHeight2_transport (rotL x y) (rotL_getElem x y) (τc q)
    rw [show ((rotL x y) (τc q).1, (τc q).2) = q by simp [hτc]] at this
    exact this
  have hsMτ : ∀ q, τc ((sM (y ++ x)).symm q) = (sM (x ++ y)).symm (τc q) := fun q => by
    have h := sM_symm_transport (rotL x y) (rotL_getElem x y) (rotL_gap x y) (τc q)
    rw [show ((rotL x y) (τc q).1, (τc q).2) = q by simp [hτc]] at h
    rw [h, hτc_up]
  set κ' : Fin (y ++ x).length × Fin 3 → ℕ := fun q => κi (τc q) with hκ'
  have hκ'_adm : ∀ a b, (y ++ x).oHeight2 a < (y ++ x).oHeight2 b → κ' a < κ' b :=
    fun a b h => hκi_adm _ _ (by rw [← hoH, ← hoH]; exact h)
  have hκ'_inj : ∀ a b, κ' a = κ' b → a = b := fun a b h => hτc_inj _ _ (hκi_inj _ _ h)
  set p' : Fin (y ++ x).length × Fin 3 := (rotL x y p.1, p.2) with hp'
  have hτp : τc p' = p := hτc_up p
  refine ⟨(markedGrid (y ++ x) κ' hyx p' H hX hO).toGrid, ⟨κ', hκ'_adm, rfl⟩, ?_⟩
  -- the sorted corners
  have hsortT : (sRows (y ++ x) κ').map τc = sRows (x ++ y) κi := by
    apply eq_of_pairwise_key (K := κi)
    · rw [List.pairwise_map]
      have h := (sRows_sorted (y ++ x) κ').and
        (List.nodup_iff_pairwise_ne.mp (sRows_nodup (y ++ x) κ'))
      exact h.imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 (fun e => h2 (hκ'_inj _ _ e))
    · have h := (sRows_sorted (x ++ y) κi).and
        (List.nodup_iff_pairwise_ne.mp (sRows_nodup (x ++ y) κi))
      exact h.imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 (fun e => h2 (hκi_inj _ _ e))
    · intro a
      simp only [List.mem_map]
      constructor
      · rintro ⟨q, -, rfl⟩; exact mem_sRows _ _ _
      · intro _
        obtain ⟨q, rfl⟩ := hτc_surj a
        exact ⟨q, mem_sRows _ _ _, rfl⟩
  -- the block after the columns of `x`
  set P := markBlock (x ++ y) H hX hO with hPdef
  set D₁ := (markData (x ++ y) κi hxy p H hX hO).atPos (x.length * 3) with hD₁
  have hm2 := movesTo_insertBlock (markData (x ++ y) κi hxy p H hX hO) D₁
  set M₁ := insertBlock (plainGrid (x ++ y) κi hxy) (markRow (x ++ y) p) P D₁ with hM₁
  set PC := (plainGrid (x ++ y) κi hxy).cols with hPC
  have hM₁c : M₁.cols = (PC.take (x.length * 3) ++ P.cols) ++ PC.drop (x.length * 3) := by
    rw [hM₁, insertBlock_cols]; rfl
  have hm3 := movesTo_withCols_rotate M₁ hM₁c
  set M₂ := M₁.withCols (PC.drop (x.length * 3) ++ (PC.take (x.length * 3) ++ P.cols))
    (by rw [hM₁c]; exact List.perm_append_comm) with hM₂
  -- the target, viewed at the size of `x ++ y`
  set P' := markBlock (y ++ x) H hX hO with hP'def
  set L := insertBlock (plainGrid (y ++ x) κ' hyx) (markRow (y ++ x) p') P'
    (endData (y ++ x) κ' hyx p' H hX hO) with hL
  have hsz : (y ++ x).length * 3 + k + 1 = (x ++ y).length * 3 + k + 1 := by rw [hlen]
  have hm5 := movesTo_insertBlock (endData (y ++ x) κ' hyx p' H hX hO)
    (markData (y ++ x) κ' hyx p' H hX hO)
  -- the maps of labels
  set f : BCol → BCol := fun c => match c with
    | Sum.inl a => Sum.inl a
    | Sum.inr q => if hq : q.1 < (y ++ x).length then
        Sum.inr (((rotL x y).symm ⟨q.1, hq⟩).val, q.2) else Sum.inr q with hf
  set g : BRow → BRow := fun c => match c with
    | Sum.inl a => Sum.inl a
    | Sum.inr q => if hq : q.1 < (y ++ x).length then
        Sum.inr (((rotL x y).symm ⟨q.1, hq⟩).val, q.2) else Sum.inr q with hg
  have hfw : ∀ q : Fin (y ++ x).length × Fin 3,
      f (Sum.inr (q.1.val, q.2)) = Sum.inr ((τc q).1.val, (τc q).2) := fun q => by
    simp only [hf, hτc]; rw [dif_pos q.1.isLt]
  have hgw : ∀ q : Fin (y ++ x).length × Fin 3,
      g (Sum.inr (q.1.val, q.2)) = Sum.inr ((τc q).1.val, (τc q).2) := fun q => by
    simp only [hg, hτc]; rw [dif_pos q.1.isLt]
  have hfb : ∀ j, f (P'.hc j) = P.hc j := fun j => by
    rw [stdBlock_hc, stdBlock_hc]
    simp only [hf]
    rw [dif_neg (by omega), hlen]
  have hgb : ∀ i, g (P'.hr i) = P.hr i := fun i => by
    rw [stdBlock_hr, stdBlock_hr]
    simp only [hg]
    rw [dif_neg (by omega), hlen]
  have hgo : ∀ i, g (P'.oRow i) = P.oRow i := fun i => by
    unfold ProtBlock.oRow
    change g (if H.O i = 0 then _ else _) = (if H.O i = 0 then _ else _)
    split_ifs <;> exact hgb _
  have hLcols : L.cols = (sCols (y ++ x)).map (sfCol 0 (y ++ x)) ++ P'.cols := by
    rw [hL, insertBlock_cols]; simp [endData, plainGrid_cols]
  have hcolL : ∀ c ∈ L.cols, (∃ q : Fin (y ++ x).length × Fin 3, c = Sum.inr (q.1.val, q.2)) ∨
      ∃ j, c = P'.hc j := by
    intro c hc
    rw [hLcols, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
      exact Or.inl ⟨q, sfCol_zero _ q⟩
    · obtain ⟨j, rfl⟩ := P'.mem_cols.mp hc
      exact Or.inr ⟨j, rfl⟩
  have hrowL : ∀ r ∈ L.rows, (∃ q : Fin (y ++ x).length × Fin 3, q ≠ p' ∧
      r = Sum.inr (q.1.val, q.2)) ∨ ∃ j, r = P'.hr j := by
    intro r hr
    rw [hL, insertBlock_rows] at hr
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · have hmem : r ∈ (plainGrid (y ++ x) κ' hyx).rows := by
        rw [(endData (y ++ x) κ' hyx p' H hX hO).rows_eq]; simp [hr]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData (y ++ x) κ' hyx p' H hX hO).not_mem_m₁ ?_, rfl⟩
      subst e; exact hr
    · obtain ⟨j, rfl⟩ := P'.mem_rows.mp hr
      exact Or.inr ⟨j, rfl⟩
    · have hmem : r ∈ (plainGrid (y ++ x) κ' hyx).rows := by
        rw [(endData (y ++ x) κ' hyx p' H hX hO).rows_eq]; simp [hr]
      obtain ⟨q, rfl⟩ := mem_plainGrid_rows.mp hmem
      refine Or.inl ⟨q, fun e => (endData (y ++ x) κ' hyx p' H hX hO).not_mem_m₂ ?_, rfl⟩
      subst e; exact hr
  have hcorner_ne : ∀ (q : Fin (y ++ x).length × Fin 3) (i : Fin (k + 2)),
      (Sum.inr ((τc q).1.val, (τc q).2) : BRow) ≠ P.hr i := fun q i e => by
    rw [stdBlock_hr] at e
    simp only [Sum.inr.injEq, Prod.mk.injEq] at e
    have := (τc q).1.isLt; omega
  have hcorner_ne' : ∀ (q : Fin (y ++ x).length × Fin 3) (j : Fin (k + 1)),
      (Sum.inr ((τc q).1.val, (τc q).2) : BCol) ≠ P.hc j := fun q j e => by
    rw [stdBlock_hc] at e
    simp only [Sum.inr.injEq, Prod.mk.injEq] at e
    have := (τc q).1.isLt; omega
  have hτinj' : ∀ q q' : Fin (y ++ x).length × Fin 3,
      (Sum.inr ((τc q).1.val, (τc q).2) : BRow) = Sum.inr ((τc q').1.val, (τc q').2) → q = q' :=
    fun q q' h => by
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact hτc_inj _ _ (Prod.ext (Fin.ext h.1) h.2)
  have hplain_map : (plainGrid (y ++ x) κ' hyx).rows.map g =
      (plainGrid (x ++ y) κi hxy).rows := by
    rw [plainGrid_rows, plainGrid_rows, ← hsortT, List.map_map, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp, sfCol_zero]
    exact hgw q
  have hsplit : (endData (y ++ x) κ' hyx p' H hX hO).m₁.map g = D₁.m₁ ∧
      (endData (y ++ x) κ' hyx p' H hX hO).m₂.map g = D₁.m₂ := by
    have h1 : (plainGrid (x ++ y) κi hxy).rows =
        (endData (y ++ x) κ' hyx p' H hX hO).m₁.map g ++
          markRow (x ++ y) p :: (endData (y ++ x) κ' hyx p' H hX hO).m₂.map g := by
      rw [← hplain_map, (endData (y ++ x) κ' hyx p' H hX hO).rows_eq, List.map_append,
        List.map_cons]
      congr 2
      rw [hgw, hτp]
    exact D₁.m_of_split h1 |>.imp (fun h => h.symm) (fun h => h.symm)
  have hrec : M₂.toGrid = (castLG hsz L).toGrid := by
    apply toGrid_eq_of_image (castLG hsz L) M₂ f g
    · rintro c hc c' hc' h
      rw [castLG_cols] at hc hc'
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩ <;> rcases hcolL c' hc' with ⟨q', rfl⟩ | ⟨j', rfl⟩
      · rw [hfw, hfw] at h
        have : q = q' := hτinj' q q' (by simpa using h)
        rw [this]
      · rw [hfw, hfb] at h; exact absurd h (hcorner_ne' q j')
      · rw [hfw, hfb] at h; exact absurd h.symm (hcorner_ne' q' j)
      · rw [hfb, hfb] at h; rw [P.hc_inj h]
    · rintro r hr r' hr' h
      rw [castLG_rows] at hr hr'
      rcases hrowL r hr with ⟨q, -, rfl⟩ | ⟨j, rfl⟩ <;>
        rcases hrowL r' hr' with ⟨q', -, rfl⟩ | ⟨j', rfl⟩
      · rw [hgw, hgw] at h; rw [hτinj' q q' h]
      · rw [hgw, hgb] at h; exact absurd h (hcorner_ne q j')
      · rw [hgw, hgb] at h; exact absurd h.symm (hcorner_ne q' j)
      · rw [hgb, hgb] at h; rw [P.hr_inj h]
    · rw [castLG_cols, hLcols, List.map_append]
      change PC.drop (x.length * 3) ++ (PC.take (x.length * 3) ++ P.cols) = _
      have e1 : P'.cols.map f = P.cols := by
        change (List.ofFn _).map f = List.ofFn _
        rw [List.map_ofFn]; congr 1; funext j; exact hfb j
      have e2 : ((sCols (y ++ x)).map (sfCol 0 (y ++ x))).map f =
          PC.drop (x.length * 3) ++ PC.take (x.length * 3) := by
        rw [hPC, plainGrid_cols, ← List.map_drop, ← List.map_take, ← List.map_append,
          ← sCols_rot, List.map_map, List.map_map]
        apply List.map_congr_left
        intro q _
        simp only [Function.comp, sfCol_zero]
        exact hfw q
      rw [e1, e2, List.append_assoc]
    · rw [castLG_rows]
      change D₁.m₁ ++ P.rows ++ D₁.m₂ = _
      rw [hL, insertBlock_rows, List.map_append, List.map_append, hsplit.1, hsplit.2]
      congr 2
      change List.ofFn _ = (List.ofFn _).map g
      rw [List.map_ofFn]; congr 1; funext i; exact (hgb i).symm
    · intro c hc
      rw [castLG_cols] at hc
      rw [castLG_O]
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · rw [hfw]
        change blockO _ _ _ (Sum.inr ((τc q).1.val, (τc q).2)) =
          g (blockO _ _ _ (Sum.inr (q.1.val, q.2)))
        rw [D₁.blockO_old (by
            rw [plainGrid_cols]; exact List.mem_map.mpr ⟨τc q, mem_sCols _ _, sfCol_zero _ _⟩),
          (endData (y ++ x) κ' hyx p' H hX hO).blockO_old (by
            rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols _ _, sfCol_zero _ _⟩),
          plainGrid_O, plainGrid_O]
        by_cases hq : q = p'
        · rw [if_pos (by rw [hq, hτp]), if_pos (by rw [hq]), hgb]
        · rw [if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact hτc_inj _ _ (by rw [hτp]; exact Prod.ext (Fin.ext e.1) e.2))),
            if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact Prod.ext (Fin.ext e.1) e.2)), hgw]
      · rw [hfb]
        change blockO _ _ _ (P.hc j) = g (blockO _ _ _ (P'.hc j))
        rw [blockO_hc, blockO_hc, hgo]
    · intro c hc
      rw [castLG_cols] at hc
      rw [castLG_X]
      rcases hcolL c hc with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · rw [hfw]
        change blockX _ _ _ (Sum.inr ((τc q).1.val, (τc q).2)) =
          g (blockX _ _ _ (Sum.inr (q.1.val, q.2)))
        rw [D₁.blockX_old (by
            rw [plainGrid_cols]; exact List.mem_map.mpr ⟨τc q, mem_sCols _ _, sfCol_zero _ _⟩),
          (endData (y ++ x) κ' hyx p' H hX hO).blockX_old (by
            rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols _ _, sfCol_zero _ _⟩),
          plainGrid_X, plainGrid_X, ← hsMτ]
        by_cases hq : (sM (y ++ x)).symm q = p'
        · rw [if_pos (by rw [hq, hτp]), if_pos (by rw [hq]), hgb]
        · rw [if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact hτc_inj _ _ (by rw [hτp]; exact Prod.ext (Fin.ext e.1) e.2))),
            if_neg (fun e => hq (by
              simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
              exact Prod.ext (Fin.ext e.1) e.2)), hgw]
      · rw [hfb]
        change blockX _ _ _ (P.hc j) = g (blockX _ _ _ (P'.hc j))
        rw [blockX_hc, blockX_hc]
        exact (hgb _).symm
  have hm4 : (castLG hsz L).toGrid.MovesTo L.toGrid := (movesTo_castLG hsz L).symm
  exact hm1.trans (hm2.trans (hm3.trans (by rw [hrec]; exact hm4.trans hm5)))

end Rotate

end OnLeConjecture.KnotTheory.MarkedCancel
