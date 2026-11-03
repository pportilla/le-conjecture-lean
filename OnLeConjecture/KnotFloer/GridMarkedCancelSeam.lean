/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlockGrid
public import OnLeConjecture.KnotFloer.GridEndpointCleanupMarkedStatement
public import OnLeConjecture.KnotTheory.MarkedCancelRotate
public import OnLeConjecture.KnotTheory.PositiveWordGridMovesTransport

/-!
# The seam with a frame preparation is a marked word grid

Let `G` be a signed word grid of a word `v` whose closing arc lies in the bottom row
(`GridFull.ClosingRowBottom`), and let `H` be triply prepared. The binary seam
`Σ(H, framePrep G)` is related by grid moves to a marked word grid of `v` with the protected grid
`H` inserted into the closing arc (`seam_movesTo_marked`). This identifies the protected seam
summand of the written proof of Statement E (`statement_E_complete_proof.tex`, Section 10,
"Preparation at a specified arc") with the framed insertion of Section 8.

In the seam, the stabilization column of `framePrep G` subdivides the input row of the block, and
the last column of `H` is fused with the first column of `G`. One `X` merge in each of the two
grids, after a cyclic rotation of the seam, gives the same grid (`toGrid_eq_of_image`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid LabeledGrid OnLeConjecture.KnotFloer.GridFull
  BraidWindow

/-! ### The markings of the seam -/

section SeamValues

variable {k n : ℕ} (H : GridDiagram (k + 1)) (hH : TriplyPrepared H) (G : GridDiagram n)
  (hC : ClosingRowBottom G)

/-- The seam of `H` with the frame preparation of `G`. -/
abbrev seamS : GridDiagram (k + n + 1) :=
  connectedSumSeamGrid H (framePrep G hC) hH.2.2 (framePrep_triplyPrepared G hC).1

theorem seamS_O_val (j : ℕ) (hj : j < k + n + 1) :
    ((seamS H hH G hC).O ⟨j, hj⟩).val =
      seamFun (gridRowVal H.O) (gridRowVal (framePrep G hC).O) k n j := by
  rw [← gridRowVal_mk _ _ hj, gridRowVal_seam_O]

theorem seamS_X_val (j : ℕ) (hj : j < k + n + 1) :
    ((seamS H hH G hC).X ⟨j, hj⟩).val =
      seamFun (gridRowVal H.X) (gridRowVal (framePrep G hC).X) k n j := by
  rw [← gridRowVal_mk _ _ hj, gridRowVal_seam_X]

theorem seamS_O_left {j : ℕ} (hj : j < k) :
    ((seamS H hH G hC).O ⟨j, by omega⟩).val = (H.O ⟨j, by omega⟩).val := by
  rw [seamS_O_val, seamFun, if_pos hj, gridRowVal_mk _ _ (by omega)]

theorem seamS_X_left {j : ℕ} (hj : j < k) :
    ((seamS H hH G hC).X ⟨j, by omega⟩).val = (H.X ⟨j, by omega⟩).val := by
  rw [seamS_X_val, seamFun, if_pos hj, gridRowVal_mk _ _ (by omega)]

theorem seamS_O_right {i : ℕ} (hi : i < n) :
    ((seamS H hH G hC).O ⟨k + i, by omega⟩).val =
      if (G.O ⟨i, hi⟩).val = 0 then k + n else k + (G.O ⟨i, hi⟩).val := by
  rw [seamS_O_val, seamFun, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
    gridRowVal_framePrep_O G hC hi, gridRowVal_mk _ _ hi]
  split_ifs <;> omega

theorem seamS_O_last :
    ((seamS H hH G hC).O ⟨k + n, by omega⟩).val = 0 := by
  rw [seamS_O_val, seamFun, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have h1 := gridRowVal_val (framePrep G hC).O (Fin.last n)
  rw [(framePrep_triplyPrepared G hC).2.1] at h1
  simp only [Fin.val_last, Fin.val_zero] at h1
  rw [h1, if_pos rfl]
  have h2 := gridRowVal_val H.O (Fin.last k)
  rw [hH.2.1] at h2
  simpa using h2

theorem seamS_X_first :
    ((seamS H hH G hC).X ⟨k, by omega⟩).val = k := by
  rw [seamS_X_val, seamFun, if_neg (by omega), if_pos (by omega), Nat.sub_self,
    gridRowVal_framePrep_X_zero, if_pos rfl]
  have h2 := gridRowVal_val H.X (Fin.last k)
  rw [hH.2.2] at h2
  simpa using h2

theorem seamS_X_right {i : ℕ} (hi0 : 0 < i) (hi : i < n) :
    ((seamS H hH G hC).X ⟨k + i, by omega⟩).val =
      if (G.X ⟨i, hi⟩).val = 0 then k + n else k + (G.X ⟨i, hi⟩).val := by
  rw [seamS_X_val, seamFun, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
    gridRowVal_framePrep_X G hC hi0 hi, gridRowVal_mk _ _ hi]
  split_ifs <;> omega

theorem seamS_X_last :
    ((seamS H hH G hC).X ⟨k + n, by omega⟩).val = k + n := by
  rw [seamS_X_val, seamFun, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have h1 := gridRowVal_val (framePrep G hC).X (Fin.last n)
  rw [(framePrep_triplyPrepared G hC).2.2] at h1
  simp only [Fin.val_last] at h1
  rw [h1, if_neg (by have := hC.1; omega)]

end SeamValues

/-! ### The identification -/

section Seam

variable {m : ℕ}

/-- The last corner of a nonempty word. -/
def lastCorner (v : SignedAdjacentWord m) (hL : 0 < v.length) : Fin v.length × Fin 3 :=
  (⟨v.length - 1, by omega⟩, 2)

theorem fpe_lastCorner (v : SignedAdjacentWord m) (hL : 0 < v.length) :
    (finProdFinEquiv (lastCorner v hL)).val = v.length * 3 - 1 := by
  rw [finProdFinEquiv_val3]; simp [lastCorner]; omega

theorem fpe_zero_corner (v : SignedAdjacentWord m) (hL : 0 < v.length) :
    (finProdFinEquiv ((⟨0, hL⟩, 0) : Fin v.length × Fin 3)).val = 0 := by
  rw [finProdFinEquiv_val3]; rfl

theorem two_le_of_triplyPrepared {k : ℕ} {H : GridDiagram (k + 1)} (hH : TriplyPrepared H) :
    1 ≤ k := by
  by_contra h
  have hk : k = 0 := by omega
  subst hk
  have h1 := hH.1
  have h2 := hH.2.1
  exact H.disjoint 0 (h2.trans h1.symm)

/-- **The seam with a frame preparation is a marked word grid.** -/
theorem seam_movesTo_marked {k : ℕ} (v : SignedAdjacentWord m) (hL : 0 < v.length)
    (G : GridDiagram (v.length * 3)) (hG : IsSignedWordGrid v G) (hC : ClosingRowBottom G)
    (H : GridDiagram (k + 1)) (hH : TriplyPrepared H) :
    ∃ M : GridDiagram (v.length * 3 + k + 1),
      IsMarkedGrid v hL (lastCorner v hL) H hH.1 hH.2.1 M ∧
        (seamS H hH G hC).MovesTo M := by
  have hk1 := two_le_of_triplyPrepared hH
  have hn0 : 0 < (v.length * 3) := by omega
  set p₀ := lastCorner v hL with hp₀
  set z₀ : Fin v.length × Fin 3 := (⟨0, hL⟩, 0) with hz₀
  set κ : Fin v.length × Fin 3 → ℕ := fun q => (G.O (finProdFinEquiv q)).val with hκ
  have hκ_adm : ∀ a b, v.oHeight2 a < v.oHeight2 b → κ a < κ b := fun a b h => hG.O_lt a b h
  have hκ_inj : ∀ a b, κ a = κ b → a = b := fun a b h =>
    finProdFinEquiv.injective (G.O.toPerm.injective (Fin.ext h))
  have hκ_lt : ∀ q, κ q < (v.length * 3) := fun q => (G.O _).isLt
  obtain ⟨hn', hO, hX⟩ := id hC
  have hκp₀ : κ p₀ = 0 := by
    have e : finProdFinEquiv p₀ = ⟨(v.length * 3) - 1, by omega⟩ := Fin.ext (fpe_lastCorner v hL)
    simp only [hκ, e]
    rw [hO]
  have hκpos : ∀ q, q ≠ p₀ → 1 ≤ κ q := fun q hq => by
    by_contra h; exact hq (hκ_inj _ _ (by omega))
  have hsMp₀ : sM v p₀ = z₀ := by
    have h1 := X_eq_sM hG z₀
    have e0 : finProdFinEquiv z₀ = ⟨0, by omega⟩ := Fin.ext (fpe_zero_corner v hL)
    rw [e0, hX] at h1
    have e1 : finProdFinEquiv p₀ = ⟨(v.length * 3) - 1, by omega⟩ := Fin.ext (fpe_lastCorner v hL)
    have h2 : G.O (finProdFinEquiv ((sM v).symm z₀)) = G.O (finProdFinEquiv p₀) := by
      rw [← h1, e1, hO]
    have h3 := finProdFinEquiv.injective (G.O.toPerm.injective h2)
    rw [← h3, Equiv.apply_symm_apply]
  have hz₀p₀ : z₀ ≠ p₀ := fun e => by
    have := congrArg Prod.snd e; simp [hz₀, hp₀, lastCorner] at this
  -- the sorted corners start with `p₀`
  obtain ⟨b, hsR⟩ : ∃ b, sRows v κ = p₀ :: b := by
    obtain ⟨a, b, hab⟩ := List.append_of_mem (mem_sRows v κ p₀)
    have hsort := sRows_sorted v κ
    rw [hab] at hsort
    have hnd := sRows_nodup v κ
    rw [hab] at hnd
    cases a with
    | nil => exact ⟨b, by simpa using hab⟩
    | cons x a =>
      exfalso
      have h1 := (List.pairwise_append.mp hsort).2.2 x (by simp) p₀ (by simp)
      rw [hκp₀] at h1
      have hx : x = p₀ := hκ_inj _ _ (by omega)
      have := (List.nodup_append.mp hnd).2.2 x (by simp) x (by simp [hx]) rfl
      exact this
  -- the marked grid with the block before all columns
  set P := markBlock v H hH.1 hH.2.1 with hPdef
  have hplainR : (plainGrid v κ hL).rows = markRow v p₀ :: b.map (sfCol 0 v) := by
    rw [plainGrid_rows, hsR, List.map_cons, sfCol_zero]
  let Df : InsertData (plainGrid v κ hL) (markRow v p₀) P :=
    { l₁ := [], l₂ := (plainGrid v κ hL).cols, m₁ := [], m₂ := b.map (sfCol 0 v),
      cols_eq := rfl, rows_eq := hplainR,
      cols_fresh := (markData v κ hL p₀ H hH.1 hH.2.1).cols_fresh,
      rows_fresh := (markData v κ hL p₀ H hH.1 hH.2.1).rows_fresh }
  have hmI := movesTo_insertBlock Df (markData v κ hL p₀ H hH.1 hH.2.1)
  set I := insertBlock (plainGrid v κ hL) (markRow v p₀) P Df with hIdef
  set Pc := List.ofFn (fun j : Fin k => P.hc j.castSucc) with hPc
  set Pr := List.ofFn (fun i : Fin k => P.hr i.castSucc.castSucc) with hPr
  set z : BCol := Sum.inr (0, 0) with hz
  have hsC : sCols v = z₀ :: (sCols v).tail := by
    have hne : sCols v ≠ [] := by
      intro h; have := sCols_length v; rw [h, List.length_nil] at this; omega
    obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil hne
    have h0 : 0 < (sCols v).length := by rw [sCols_length]; omega
    have hx0 : (sCols v)[0]'h0 = x := by simp [hxt]
    have := sCols_getElem v 0 h0
    rw [hx0] at this
    rw [hxt]; congr 1
    exact this.trans (by
      apply Prod.ext <;> apply Fin.ext <;> simp [finProdFinEquiv_symm_apply, hz₀])
  set PT := ((sCols v).tail).map (sfCol 0 v) with hPT
  have hIcols : I.cols = Pc ++ P.hc (Fin.last k) :: z :: PT := by
    rw [hIdef, insertBlock_cols, P.cols_eq_last]
    change [] ++ _ ++ (sCols v).map (sfCol 0 v) = _
    rw [hsC, List.map_cons, sfCol_zero]
    simp [hz₀, hz, hPc, hPT]
  have hProws : P.rows = Pr ++ [P.hr (Fin.last k).castSucc, P.hr (Fin.last (k + 1))] := by
    change List.ofFn P.hr = _
    rw [ofFn_succ_last, ofFn_succ_last]
    simp [hPr]
  have hIrows : I.rows = Pr ++ P.hr (Fin.last k).castSucc ::
      ([] ++ P.hr (Fin.last (k + 1)) :: b.map (sfCol 0 v)) := by
    rw [hIdef, insertBlock_rows]
    change [] ++ P.rows ++ b.map (sfCol 0 v) = _
    rw [hProws]; simp
  have hzmem : z ∈ (plainGrid v κ hL).cols := by
    rw [hz, ← sfCol_zero v z₀]
    exact List.mem_map.mpr ⟨z₀, mem_sCols v z₀, rfl⟩
  have hzz : z = Sum.inr (z₀.1.val, z₀.2) := by simp [hz, hz₀]
  have hIOz : I.O z = Sum.inr (0, 0) := by
    rw [hIdef, insertBlock_O, Df.blockO_old hzmem, hzz, plainGrid_O]
    rw [if_neg (fun e => hz₀p₀ (by
      simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
      exact Prod.ext (Fin.ext e.1) e.2))]
  have hIXz : I.X z = P.hr (Fin.last (k + 1)) := by
    rw [hIdef, insertBlock_X, Df.blockX_old hzmem, hzz, plainGrid_X, ← hsMp₀,
      Equiv.symm_apply_apply, if_pos rfl]
  obtain ⟨I3, hc3, hr3, hO3, hX3, hm3⟩ := I.exists_mergeX_down (l₁ := Pc) (l₂ := PT)
    (c := P.hc (Fin.last k)) (d := z) (m₁ := Pr) (mid := []) (m₂ := b.map (sfCol 0 v))
    (e := P.hr (Fin.last (k + 1))) (z := P.hr (Fin.last k).castSucc) (Or.inl hIcols) hIrows
    (by rw [hIdef, insertBlock_O, blockO_hc, ProtBlock.oRow_last])
    (by
      rw [hIdef, insertBlock_X, blockX_hc]
      change P.hr (H.X (Fin.last k)).castSucc = _
      rw [hH.2.2])
    hIXz (by rw [hIOz, stdBlock_hr]; simp) (by simp)
  -- the seam with position labels
  set S := seamS H hH G hC with hSdef
  set S0 := LabeledGrid.ofGrid S with hS0
  set init := (List.finRange (k + v.length * 3)).map Fin.castSucc with hinit
  set lst : Fin (k + v.length * 3 + 1) := Fin.last (k + v.length * 3) with hlst
  have hfr : List.finRange (k + v.length * 3 + 1) = init ++ [lst] := List.finRange_succ_last
  have hm1 := movesTo_withCols_rotate S0 (l₁ := init) (l₂ := [lst]) hfr
  have hp1 : ([lst] ++ init).Perm S0.cols := by
    rw [show S0.cols = init ++ [lst] from hfr]; exact List.perm_append_comm
  set S1 := S0.withCols ([lst] ++ init) hp1 with hS1
  have hm2 := movesTo_withRows_rotate S1 (l₁ := init) (l₂ := [lst]) hfr
  have hp2 : ([lst] ++ init).Perm S1.rows := by
    rw [show S1.rows = init ++ [lst] from hfr]; exact List.perm_append_comm
  set S2 := S1.withRows ([lst] ++ init) hp2 with hS2
  set c₀ : Fin (k + v.length * 3 + 1) := ⟨0, by omega⟩ with hc₀
  have hinit_ne : init ≠ [] := by
    intro h; have := congrArg List.length h; simp [hinit] at this; omega
  obtain ⟨y, tailL, hyt⟩ := List.exists_cons_of_ne_nil hinit_ne
  have hy : y = c₀ := by
    have h0 : 0 < init.length := by simp [hinit]; omega
    have : init[0]'h0 = y := by simp [hyt]
    rw [← this]; simp [hinit, hc₀]
  rw [hy] at hyt
  have hS2O : ∀ c, S2.O c = S.O c := fun c => rfl
  have hS2X : ∀ c, S2.X c = S.X c := fun c => rfl
  have hSOl : S.O lst = c₀ := Fin.ext (seamS_O_last H hH G hC)
  have hSXl : S.X lst = lst := Fin.ext (seamS_X_last H hH G hC)
  have hSX0 : S.X c₀ = c₀ := by
    apply Fin.ext
    have h1 : (S.X c₀).val = (H.X ⟨0, by omega⟩).val := seamS_X_left H hH G hC (j := 0) (by omega)
    rw [h1, show (⟨0, by omega⟩ : Fin (k + 1)) = 0 from rfl, hH.1]; rfl
  obtain ⟨S3, hcS, hrS, hOS, hXS, hmS⟩ := S2.exists_mergeX_down (l₁ := []) (l₂ := tailL)
    (c := lst) (d := c₀) (m₁ := []) (mid := []) (m₂ := tailL) (e := c₀) (z := lst)
    (Or.inl (by change [lst] ++ init = _; rw [hyt]; rfl))
    (by change [lst] ++ init = _; rw [hyt]; rfl)
    (by rw [hS2O, hSOl]) (by rw [hS2X, hSXl]) (by rw [hS2X, hSX0])
    (by
      rw [hS2O]; intro e
      have h1 : (S.O c₀).val = (H.O ⟨0, by omega⟩).val :=
        seamS_O_left H hH G hC (j := 0) (by omega)
      have h2 := congrArg Fin.val e
      have h3 := (H.O ⟨0, by omega⟩).isLt
      simp only [hlst, Fin.val_last] at h2
      omega)
    (by simp)
  -- the maps of labels
  let fC : BCol → Fin (k + v.length * 3 + 1) := fun c => match c with
    | Sum.inl _ => c₀
    | Sum.inr q => if hq : q.1 < v.length then ⟨k + (q.2.val + 3 * q.1), by have := q.2.isLt; omega⟩
        else if hj : q.1 - v.length < k then ⟨q.1 - v.length, by omega⟩ else c₀
  let gR : BRow → Fin (k + v.length * 3 + 1) := fun x => match x with
    | Sum.inl _ => c₀
    | Sum.inr q => if hq : q.1 < v.length then
          ⟨k + (G.O (finProdFinEquiv (⟨q.1, hq⟩, q.2))).val, by
            have := (G.O (finProdFinEquiv (⟨q.1, hq⟩, q.2))).isLt; omega⟩
        else if q.1 = v.length then lst
        else if hj : q.1 - v.length ≤ k then ⟨q.1 - v.length, by omega⟩ else c₀
  have hfC_P : ∀ j : Fin k, fC (P.hc j.castSucc) = ⟨j.val, by omega⟩ := fun j => by
    rw [stdBlock_hc]; simp only [fC, Fin.val_castSucc]
    rw [dif_neg (by omega), dif_pos (by omega)]
    simp
  have hfC_q : ∀ q : Fin v.length × Fin 3, fC (Sum.inr (q.1.val, q.2)) =
      ⟨k + (finProdFinEquiv q).val, by have := (finProdFinEquiv q).isLt; omega⟩ := fun q => by
    simp only [fC]; rw [dif_pos q.1.isLt]; simp
  have hgR_q : ∀ q : Fin v.length × Fin 3, gR (Sum.inr (q.1.val, q.2)) =
      ⟨k + κ q, by have := hκ_lt q; omega⟩ := fun q => by
    simp only [gR]; rw [dif_pos q.1.isLt]
  have hgR_0 : gR (P.hr 0) = lst := by
    rw [stdBlock_hr]; simp only [gR]; rw [dif_neg (by simp), if_pos (by simp)]
  have hgR_P : ∀ i : Fin (k + 2), 1 ≤ i.val → i.val ≤ k → gR (P.hr i) = ⟨i.val, by omega⟩ := by
    intro i h1 h2
    rw [stdBlock_hr]; simp only [gR]
    rw [dif_neg (by omega), if_neg (by omega), dif_pos (by omega)]
    simp
  -- the corners other than `p₀`, by their keys
  have hκsurj : ∀ i, i < v.length * 3 → ∃ q, κ q = i := fun i hi =>
    ⟨finProdFinEquiv.symm (G.O.toPerm.symm ⟨i, hi⟩), by
      change (G.O.toPerm (finProdFinEquiv (finProdFinEquiv.symm _))).val = i
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩
  have hbmem : ∀ q, q ∈ b ↔ q ≠ p₀ := by
    intro q
    have hnd := sRows_nodup v κ
    rw [hsR] at hnd
    constructor
    · intro hq e; subst e; exact (List.nodup_cons.mp hnd).1 hq
    · intro hq
      have := mem_sRows v κ q
      rw [hsR] at this
      rcases List.mem_cons.mp this with h | h
      · exact absurd h hq
      · exact h
  have hbsort : b.Pairwise (fun a c => κ a < κ c) := by
    have h := (sRows_sorted v κ).and (List.nodup_iff_pairwise_ne.mp (sRows_nodup v κ))
    rw [hsR] at h
    exact (List.pairwise_cons.mp h).2.imp fun ⟨h1, h2⟩ =>
      lt_of_le_of_ne h1 (fun e => h2 (hκ_inj _ _ e))
  -- the recognition
  have hsz : v.length * 3 + k = k + v.length * 3 := by omega
  have hI3O : ∀ c, (castLG hsz I3).O c = I.O c := fun c => by rw [castLG_O, hO3]
  have hI3X : ∀ c, (castLG hsz I3).X c =
      Function.update I.X z (P.hr (Fin.last k).castSucc) c := fun c => by rw [castLG_X, hX3]
  have hS3O : ∀ c, S3.O c = S.O c := fun c => by rw [hOS]; rfl
  have hS3X : ∀ c, S3.X c = Function.update S.X c₀ lst c := fun c => by rw [hXS]; rfl
  have hzPT : z :: PT = (sCols v).map (sfCol 0 v) := by
    conv_rhs => rw [hsC]
    rw [List.map_cons, sfCol_zero]
  have hcolI3 : ∀ c ∈ (castLG hsz I3).cols, (∃ j : Fin k, c = P.hc j.castSucc) ∨
      ∃ q : Fin v.length × Fin 3, c = Sum.inr (q.1.val, q.2) := by
    intro c hc
    rw [castLG_cols, hc3] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc; exact Or.inl ⟨j, rfl⟩
    · rw [hzPT] at hc
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
      exact Or.inr ⟨q, sfCol_zero v q⟩
  have hrowI3 : ∀ x ∈ (castLG hsz I3).rows, (∃ i : Fin (k + 2), i.val ≤ k ∧ x = P.hr i) ∨
      ∃ q : Fin v.length × Fin 3, q ≠ p₀ ∧ x = Sum.inr (q.1.val, q.2) := by
    intro x hx
    rw [castLG_rows, hr3] at hx
    simp only [List.mem_append, List.mem_cons, List.nil_append] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact Or.inl ⟨i.castSucc.castSucc, by simp only [Fin.val_castSucc]; omega, rfl⟩
    · exact Or.inl ⟨(Fin.last k).castSucc, by simp, hx⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨q, (hbmem q).mp hq, sfCol_zero v q⟩
  have hgR_hr : ∀ i : Fin (k + 2), i.val ≤ k →
      (gR (P.hr i)).val = if i.val = 0 then k + v.length * 3 else i.val := by
    intro i hi
    split_ifs with h0
    · have : i = 0 := Fin.ext h0
      rw [this, hgR_0]; simp [hlst]
    · rw [hgR_P i (by omega) hi]
  have hIO_P : ∀ j : Fin (k + 1), I.O (P.hc j) = P.oRow j := fun j => by
    rw [hIdef, insertBlock_O, blockO_hc]
  have hIX_P : ∀ j : Fin (k + 1), I.X (P.hc j) = P.xRow j := fun j => by
    rw [hIdef, insertBlock_X, blockX_hc]
  have hqmem : ∀ q : Fin v.length × Fin 3,
      (Sum.inr (q.1.val, q.2) : BCol) ∈ (plainGrid v κ hL).cols := fun q => by
    rw [plainGrid_cols]; exact List.mem_map.mpr ⟨q, mem_sCols v q, sfCol_zero v q⟩
  have hIO_q : ∀ q : Fin v.length × Fin 3, I.O (Sum.inr (q.1.val, q.2)) =
      if q = p₀ then P.hr 0 else Sum.inr (q.1.val, q.2) := fun q => by
    rw [hIdef, insertBlock_O, Df.blockO_old (hqmem q), plainGrid_O]
    by_cases hq : q = p₀
    · rw [if_pos (by rw [hq]), if_pos hq]
    · rw [if_neg (fun e => hq (by
          simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
          exact Prod.ext (Fin.ext e.1) e.2)), if_neg hq]
  have hIX_q : ∀ q : Fin v.length × Fin 3, I.X (Sum.inr (q.1.val, q.2)) =
      if (sM v).symm q = p₀ then P.hr (Fin.last (k + 1))
      else Sum.inr (((sM v).symm q).1.val, ((sM v).symm q).2) := fun q => by
    rw [hIdef, insertBlock_X, Df.blockX_old (hqmem q), plainGrid_X]
    by_cases hq : (sM v).symm q = p₀
    · rw [if_pos (by rw [hq]), if_pos hq]
    · rw [if_neg (fun e => hq (by
          simp only [markRow, Sum.inr.injEq, Prod.mk.injEq] at e
          exact Prod.ext (Fin.ext e.1) e.2)), if_neg hq]
  have hmapval : ∀ N : ℕ, (List.finRange N).map Fin.val = List.range N := fun N => by
    apply List.ext_getElem <;> simp
  have hrec : S3.toGrid = (castLG hsz I3).toGrid := by
    apply toGrid_eq_of_image (castLG hsz I3) S3 fC gR
    · rintro c hc c' hc' h
      rcases hcolI3 c hc with ⟨j, rfl⟩ | ⟨q, rfl⟩ <;>
        rcases hcolI3 c' hc' with ⟨j', rfl⟩ | ⟨q', rfl⟩
      · rw [hfC_P, hfC_P] at h
        have := congrArg Fin.val h; simp only at this
        rw [Fin.ext this]
      · rw [hfC_P, hfC_q] at h
        have := congrArg Fin.val h; simp only at this; have := j.isLt; omega
      · rw [hfC_P, hfC_q] at h
        have := congrArg Fin.val h; simp only at this; have := j'.isLt; omega
      · rw [hfC_q, hfC_q] at h
        have := congrArg Fin.val h; simp only at this
        have e : q = q' := finProdFinEquiv.injective (Fin.ext (by omega))
        rw [e]
    · rintro x hx x' hx' h
      rcases hrowI3 x hx with ⟨i, hi, rfl⟩ | ⟨q, hq, rfl⟩ <;>
        rcases hrowI3 x' hx' with ⟨i', hi', rfl⟩ | ⟨q', hq', rfl⟩
      · have h1 := hgR_hr i hi
        have h2 := hgR_hr i' hi'
        rw [h] at h1
        rw [h1] at h2
        have hii : i = i' := Fin.ext (by split_ifs at h2 <;> omega)
        rw [hii]
      · have h1 := hgR_hr i hi
        rw [h, hgR_q] at h1
        have := hκpos q' hq'; have := hκ_lt q'
        simp only at h1
        split_ifs at h1 <;> omega
      · have h1 := hgR_hr i' hi'
        rw [← h, hgR_q] at h1
        have := hκpos q hq; have := hκ_lt q
        simp only at h1
        split_ifs at h1 <;> omega
      · rw [hgR_q, hgR_q] at h
        have := congrArg Fin.val h; simp only at this
        rw [hκ_inj q q' (by omega)]
    · -- the columns
      apply List.map_injective_iff.mpr Fin.val_injective
      have L1 : S3.cols.map Fin.val = List.range (k + v.length * 3) := by
        rw [hcS]
        change (c₀ :: tailL).map Fin.val = _
        rw [← hyt, hinit, List.map_map]
        rw [show (Fin.val ∘ Fin.castSucc : Fin (k + v.length * 3) → ℕ) = Fin.val from rfl]
        exact hmapval _
      have L2 : ((castLG hsz I3).cols.map fC).map Fin.val = List.range (k + v.length * 3) := by
        rw [castLG_cols, hc3, hzPT]
        apply List.ext_getElem
        · simp [hPc, sCols_length]
        · intro i h1 h2
          rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_append]
          split_ifs with hik
          · simp only [hPc, List.getElem_ofFn]
            rw [hfC_P ⟨i, by simpa [hPc] using hik⟩]
          · simp only [hPc, List.length_ofFn] at hik
            rw [List.getElem_map, sCols_getElem, sfCol_zero, hfC_q]
            simp only [Equiv.apply_symm_apply, hPc, List.length_ofFn]
            omega
      rw [L1, L2]
    · -- the rows
      rw [hrS, castLG_rows, hr3]
      simp only [List.nil_append]
      have hlstc : lst ≠ c₀ := fun e => by
        have := congrArg Fin.val e; simp [hlst, hc₀] at this; omega
      -- the values of the positions
      have hinitv : init.map Fin.val = List.range (k + v.length * 3) := by
        rw [hinit, List.map_map]
        rw [show (Fin.val ∘ Fin.castSucc : Fin (k + v.length * 3) → ℕ) = Fin.val from rfl]
        exact hmapval _
      have hinitP : init.Pairwise (fun a c => a.val < c.val) := by
        have := List.pairwise_lt_range (n := k + v.length * 3)
        rw [← hinitv, List.pairwise_map] at this
        exact this
      rw [hyt] at hinitP
      have hmem_init : ∀ x : Fin (k + v.length * 3 + 1), x ∈ init ↔ x ≠ lst := by
        intro x
        constructor
        · intro hx e
          have := List.mem_map_of_mem (f := Fin.val) hx
          rw [hinitv, List.mem_range, e] at this
          simp [hlst] at this
        · intro hx
          have hlt : x.val < k + v.length * 3 := by
            have h1 := x.isLt
            have h2 : x.val ≠ k + v.length * 3 := fun e => hx (Fin.ext (by simp [hlst, e]))
            omega
          rw [hinit]
          exact List.mem_map.mpr ⟨⟨x.val, hlt⟩, List.mem_finRange _, rfl⟩
      have hnd_init : (c₀ :: tailL).Nodup := hinitP.imp fun h e => by
        rw [e] at h; exact lt_irrefl _ h
      set K : Fin (k + v.length * 3 + 1) → ℕ := fun x => if x = lst then 0 else x.val + 1
        with hK
      apply eq_of_pairwise_key (K := K)
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, ?_⟩
        · have hx' : x ≠ lst := (hmem_init x).mp (by rw [hyt]; exact List.mem_cons_of_mem _ hx)
          simp only [hK, if_pos rfl, if_neg hx']; omega
        · refine (List.pairwise_cons.mp hinitP).2.imp_of_mem fun {x y} hx hy hxy => ?_
          have hx' : x ≠ lst := (hmem_init x).mp (by rw [hyt]; exact List.mem_cons_of_mem _ hx)
          have hy' : y ≠ lst := (hmem_init y).mp (by rw [hyt]; exact List.mem_cons_of_mem _ hy)
          simp only [hK, if_neg hx', if_neg hy']; omega
      · have hKP : ∀ i : Fin (k + 2), i.val ≤ k →
            K (gR (P.hr i)) = if i.val = 0 then 0 else i.val + 1 := by
          intro i hi
          have h1 := hgR_hr i hi
          by_cases h0 : i.val = 0
          · have : i = 0 := Fin.ext h0
            rw [this, hgR_0]; simp [hK]
          · rw [if_neg h0] at h1
            have hne : gR (P.hr i) ≠ lst := fun e => by
              rw [e] at h1; simp [hlst] at h1; omega
            simp only [hK, if_neg hne, if_neg h0, h1]
        have hKq : ∀ q : Fin v.length × Fin 3, q ≠ p₀ →
            K (gR (Sum.inr (q.1.val, q.2))) = k + κ q + 1 := by
          intro q hq
          rw [hgR_q]
          have hne : (⟨k + κ q, by have := hκ_lt q; omega⟩ : Fin (k + v.length * 3 + 1)) ≠ lst :=
            fun e => by have := congrArg Fin.val e; simp [hlst] at this; have := hκ_lt q; omega
          simp only [hK, if_neg hne]
        rw [List.pairwise_map, List.pairwise_append]
        refine ⟨?_, ?_, ?_⟩
        · rw [hPr, List.pairwise_ofFn]
          intro i i' hii'
          rw [hKP _ (by simp only [Fin.val_castSucc]; omega),
            hKP _ (by simp only [Fin.val_castSucc]; omega)]
          simp only [Fin.val_castSucc]
          rw [Fin.lt_def] at hii'
          split_ifs <;> omega
        · rw [List.pairwise_cons]
          refine ⟨fun y hy => ?_, ?_⟩
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
            rw [sfCol_zero, hKq q ((hbmem q).mp hq), hKP _ (by simp)]
            simp only [Fin.val_castSucc, Fin.val_last]
            have := hκpos q ((hbmem q).mp hq)
            split_ifs <;> omega
          · rw [List.pairwise_map]
            refine hbsort.imp_of_mem fun {q q'} hq hq' h => ?_
            rw [sfCol_zero, sfCol_zero, hKq q ((hbmem q).mp hq), hKq q' ((hbmem q').mp hq')]
            omega
        · intro x hx y hy
          rw [hPr] at hx
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          rw [hKP _ (by simp only [Fin.val_castSucc]; omega)]
          simp only [Fin.val_castSucc] at *
          rcases List.mem_cons.mp hy with rfl | hy
          · rw [hKP _ (by simp)]
            simp only [Fin.val_castSucc, Fin.val_last]
            have := i.isLt
            split_ifs <;> omega
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
            rw [sfCol_zero, hKq q ((hbmem q).mp hq)]
            have := i.isLt
            split_ifs <;> omega
      · intro x
        have hL1 : x ∈ lst :: tailL ↔ x ≠ c₀ := by
          constructor
          · rintro hx rfl
            rcases List.mem_cons.mp hx with h | h
            · exact hlstc h.symm
            · exact (List.nodup_cons.mp hnd_init).1 h
          · intro hx
            by_cases h : x = lst
            · rw [h]; exact List.mem_cons_self
            · have := (hmem_init x).mpr h
              rw [hyt] at this
              rcases List.mem_cons.mp this with h' | h'
              · exact absurd h' hx
              · exact List.mem_cons_of_mem _ h'
        rw [hL1]
        constructor
        · intro hx
          rw [List.mem_map]
          by_cases hxl : x = lst
          · refine ⟨P.hr 0, List.mem_append_left _ ?_, by rw [hgR_0, hxl]⟩
            rw [hPr]
            exact List.mem_ofFn.mpr ⟨⟨0, by omega⟩, rfl⟩
          · have hx1 : 1 ≤ x.val := Nat.one_le_iff_ne_zero.mpr (fun e => hx (Fin.ext e))
            have hx2 : x.val < k + v.length * 3 := by
              have h1 := x.isLt
              have : x.val ≠ k + v.length * 3 := fun e => hxl (Fin.ext (by simp [hlst, e]))
              omega
            by_cases hxk : x.val ≤ k
            · refine ⟨P.hr ⟨x.val, by omega⟩, ?_, ?_⟩
              · by_cases hxk' : x.val < k
                · apply List.mem_append_left; rw [hPr]
                  exact List.mem_ofFn.mpr ⟨⟨x.val, hxk'⟩, rfl⟩
                · apply List.mem_append_right
                  have : (⟨x.val, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc :=
                    Fin.ext (by simp; omega)
                  rw [this]; exact List.mem_cons_self
              · rw [hgR_P _ (by simpa using hx1) (by simpa using hxk)]
            · obtain ⟨q, hq⟩ := hκsurj (x.val - k) (by omega)
              have hqp : q ≠ p₀ := fun e => by rw [e, hκp₀] at hq; omega
              refine ⟨Sum.inr (q.1.val, q.2), List.mem_append_right _ (List.mem_cons_of_mem _
                (List.mem_map.mpr ⟨q, (hbmem q).mpr hqp, sfCol_zero v q⟩)), ?_⟩
              rw [hgR_q]; exact Fin.ext (by simp only; omega)
        · intro hx e
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          rcases List.mem_append.mp hy with hy | hy
          · rw [hPr] at hy
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
            have h1 := hgR_hr i.castSucc.castSucc (by simp only [Fin.val_castSucc]; omega)
            rw [e] at h1
            simp only [Fin.val_castSucc, hc₀] at h1
            split_ifs at h1 with h0 <;> omega
          · rcases List.mem_cons.mp hy with hy | hy
            · rw [hy] at e
              have h1 := hgR_hr (Fin.last k).castSucc (by simp)
              rw [e] at h1
              simp only [Fin.val_castSucc, Fin.val_last, hc₀] at h1
              split_ifs at h1 <;> omega
            · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
              rw [sfCol_zero, hgR_q] at e
              have := congrArg Fin.val e
              simp only [hc₀] at this
              omega
    · -- the `O` markings
      intro c hc
      rw [hS3O, hI3O]
      rcases hcolI3 c hc with ⟨j, rfl⟩ | ⟨q, rfl⟩
      · have hj : H.O j.castSucc ≠ 0 := fun e => by
          have := H.O.toPerm.injective (e.trans hH.2.1.symm)
          exact Fin.castSucc_ne_last j this
        have hj1 : 1 ≤ ((H.O j.castSucc).castSucc : Fin (k + 2)).val := by
          simp only [Fin.val_castSucc]
          exact Nat.one_le_iff_ne_zero.mpr (fun e => hj (Fin.ext e))
        have hj2 : ((H.O j.castSucc).castSucc : Fin (k + 2)).val ≤ k := by
          simp only [Fin.val_castSucc]; have := (H.O j.castSucc).isLt; omega
        have hoR : P.oRow j.castSucc = P.hr (H.O j.castSucc).castSucc := by
          unfold ProtBlock.oRow; exact if_neg hj
        rw [hfC_P, hIO_P, hoR, hgR_P _ hj1 hj2]
        apply Fin.ext
        simp only [Fin.val_castSucc]
        exact seamS_O_left H hH G hC (j := j.val) j.isLt
      · rw [hfC_q, hIO_q]
        have hS := seamS_O_right H hH G hC (i := (finProdFinEquiv q).val)
          (finProdFinEquiv q).isLt
        by_cases hq : q = p₀
        · rw [if_pos hq, hgR_0]
          apply Fin.ext
          rw [hS]
          have : (G.O ⟨(finProdFinEquiv q).val, (finProdFinEquiv q).isLt⟩).val = 0 := by
            rw [← hκp₀, hq]
          rw [if_pos this]; simp [hlst]
        · rw [if_neg hq, hgR_q]
          apply Fin.ext
          rw [hS]
          have h0 : (G.O (finProdFinEquiv q)).val ≠ 0 := by
            have := hκpos q hq; simp only [hκ] at this; omega
          rw [if_neg h0]
    · -- the `X` markings
      intro c hc
      rw [hS3X, hI3X]
      rcases hcolI3 c hc with ⟨j, rfl⟩ | ⟨q, rfl⟩
      · have hjz : P.hc j.castSucc ≠ z := by
          rw [stdBlock_hc, hz]; simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
          intro h; omega
        rw [Function.update_of_ne hjz, hfC_P, hIX_P]
        by_cases hj0 : j.val = 0
        · have hj' : j.castSucc = (0 : Fin (k + 1)) := Fin.ext (by simp [hj0])
          have e : (⟨j.val, by omega⟩ : Fin (k + v.length * 3 + 1)) = c₀ := Fin.ext hj0
          rw [e, Function.update_self]
          have hx : P.xRow j.castSucc = P.hr 0 := by
            unfold ProtBlock.xRow
            change P.hr (H.X j.castSucc).castSucc = _
            rw [hj', hH.1]; rfl
          rw [hx, hgR_0]
        · rw [Function.update_of_ne (fun e => hj0 (congrArg Fin.val e))]
          have hx : H.X j.castSucc ≠ 0 := fun e => by
            have := H.X.toPerm.injective (e.trans hH.1.symm)
            exact hj0 (by have := congrArg Fin.val this; simpa using this)
          have hxl : (H.X j.castSucc).val < k := by
            have h1 := (H.X j.castSucc).isLt
            have h2 : H.X j.castSucc ≠ Fin.last k := fun e => by
              have := H.X.toPerm.injective (e.trans hH.2.2.symm)
              exact Fin.castSucc_ne_last j this
            have : (H.X j.castSucc).val ≠ k := fun e => h2 (Fin.ext (by simpa using e))
            omega
          have hxR : P.xRow j.castSucc = P.hr (H.X j.castSucc).castSucc := rfl
          have hj1 : 1 ≤ ((H.X j.castSucc).castSucc : Fin (k + 2)).val := by
            simp only [Fin.val_castSucc]
            exact Nat.one_le_iff_ne_zero.mpr (fun e => hx (Fin.ext e))
          have hj2 : ((H.X j.castSucc).castSucc : Fin (k + 2)).val ≤ k := by
            simp only [Fin.val_castSucc]; omega
          rw [hxR, hgR_P _ hj1 hj2]
          apply Fin.ext
          simp only [Fin.val_castSucc]
          exact seamS_X_left H hH G hC (j := j.val) j.isLt
      · rw [hfC_q]
        have hk' : (⟨k + (finProdFinEquiv q).val, by
            have := (finProdFinEquiv q).isLt; omega⟩ : Fin (k + v.length * 3 + 1)) ≠ c₀ :=
          fun e => by have := congrArg Fin.val e; simp [hc₀] at this; omega
        rw [Function.update_of_ne hk']
        by_cases hqz : q = z₀
        · have e : (Sum.inr (q.1.val, q.2) : BCol) = z := by rw [hqz, hz]
          rw [e, Function.update_self, hgR_P _ (by simp; omega) (by simp)]
          apply Fin.ext
          have h0 : (finProdFinEquiv q).val = 0 := by rw [hqz]; exact fpe_zero_corner v hL
          simp only [h0, Nat.add_zero, Fin.val_castSucc, Fin.val_last]
          exact seamS_X_first H hH G hC
        · have hne : (Sum.inr (q.1.val, q.2) : BCol) ≠ z := fun e => hqz (by
            rw [hz] at e; simp only [Sum.inr.injEq, Prod.mk.injEq] at e
            exact Prod.ext (Fin.ext (by simp [hz₀, e.1])) (by simp [hz₀, e.2]))
          rw [Function.update_of_ne hne, hIX_q]
          have hsq : (sM v).symm q ≠ p₀ := fun e => hqz (by
            rw [← hsMp₀, ← e, Equiv.apply_symm_apply])
          rw [if_neg hsq]
          have hgq := hgR_q ((sM v).symm q)
          rw [hgq]
          have hfq : (finProdFinEquiv q).val ≠ 0 := fun e => hqz (by
            apply finProdFinEquiv.injective
            exact Fin.ext (e.trans (fpe_zero_corner v hL).symm))
          apply Fin.ext
          rw [seamS_X_right H hH G hC (i := (finProdFinEquiv q).val) (by omega)
            (finProdFinEquiv q).isLt]
          have hXq := X_eq_sM hG q
          have hX0 : (G.X (finProdFinEquiv q)).val ≠ 0 := by
            intro e
            have h1 : G.X (finProdFinEquiv q) = G.X ⟨0, hn'⟩ := by
              rw [hX]; exact Fin.ext e
            exact hfq (congrArg Fin.val (G.X.toPerm.injective h1))
          rw [if_neg hX0]
          simp only [hκ]
          rw [← hXq]
  refine ⟨(markedGrid v κ hL p₀ H hH.1 hH.2.1).toGrid, ⟨κ, hκ_adm, rfl⟩, ?_⟩
  have hS0g : S0.toGrid = S := toGrid_ofGrid S
  rw [← hS0g]
  exact hm1.trans (hm2.trans (hmS.trans (by
    rw [hrec]
    exact (movesTo_castLG hsz I3).symm.trans (hm3.symm.trans hmI))))

end Seam

end OnLeConjecture.KnotTheory.MarkedCancel
