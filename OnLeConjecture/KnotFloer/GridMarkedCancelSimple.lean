/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridMarkedCancelLift
public import OnLeConjecture.KnotFloer.GridExteriorSimpleFactor

/-!
# The seam with the simple factor is a marked word grid of `σ_0`

Let `H` be triply prepared. The binary seam `Σ(H, simpleFactorGrid)` is related by grid moves to
the marked word grid of the one-letter word `σ_0` with the marked arc leaving the corner of height
`0` (the corner `1`) and the protected grid `H` (`simple_seam_movesTo_marked`). After a cyclic
rotation of the columns of the seam by two positions, the seam is the marked word grid with the
block inserted after the column of the marked corner, read through a relabelling of rows and
columns (`toGrid_eq_of_image`). This identifies the unknotted seam summand of a simple factor in
the written proof of Statement E (`statement_E_complete_proof.tex`, Section 10) with the marked
core `σ_0` of Section 8.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory SignedGrid BraidWindow LabeledGrid
  OnLeConjecture.KnotFloer.GridFull SignedAdjacentWord

variable {S : ℕ}

/-- The word `σ_0` on `S ≥ 2` strands. -/
def sigma0Word (hS : 2 ≤ S) : SignedAdjacentWord S := [(⟨0, by omega⟩, 1)]

section Sigma0

variable (hS : 2 ≤ S)

theorem sigma0Word_length : (sigma0Word hS).length = 1 := rfl

/-- The corner `c` of the letter of `σ_0`. -/
abbrev s0c (c : Fin 3) : Fin (sigma0Word hS).length × Fin 3 := (⟨0, by simp [sigma0Word]⟩, c)

theorem s0c_eq (p : Fin (sigma0Word hS).length × Fin 3) : p = s0c hS p.2 :=
  Prod.ext (Fin.ext (by have := p.1.isLt; simp only [sigma0Word_length] at this; simp; omega)) rfl

theorem sigma0_oHeight2 (c : Fin 3) :
    (sigma0Word hS).oHeight2 (s0c hS c) = if c = 0 then 1 else if c = 1 then 0 else 2 := by
  simp only [SignedAdjacentWord.oHeight2, sigma0Word, signedOHeight2]
  fin_cases c <;> simp

theorem sigma0_xHeight2 (c : Fin 3) :
    (sigma0Word hS).xHeight2 (s0c hS c) = if c = 0 then 0 else if c = 1 then 2 else 1 := by
  simp only [SignedAdjacentWord.xHeight2, sigma0Word, signedXHeight2]
  fin_cases c <;> simp

theorem sigma0_occ_zero (k : Fin (sigma0Word hS).length) : k = ⟨0, by simp [sigma0Word]⟩ :=
  Fin.ext (by have := k.isLt; simp only [sigma0Word_length] at this; simp; omega)

theorem sigma0_sM1 : sM (sigma0Word hS) (s0c hS 1) = s0c hS 0 := by
  apply sM_eq_of_spec _ _ _ (show (1 : Fin 3) ≠ 0 by decide)
  · rw [sigma0_xHeight2, sigma0_oHeight2]; simp
  · right
    refine ⟨le_rfl, fun k _ => ?_⟩
    rw [sigma0_occ_zero hS k]
    exact ⟨le_rfl, le_rfl⟩

theorem sigma0_sM2 : sM (sigma0Word hS) (s0c hS 2) = s0c hS 1 := by
  apply sM_eq_of_spec _ _ _ (show (2 : Fin 3) ≠ 0 by decide)
  · rw [sigma0_xHeight2, sigma0_oHeight2]; simp
  · right
    refine ⟨le_rfl, fun k _ => ?_⟩
    rw [sigma0_occ_zero hS k]
    exact ⟨le_rfl, le_rfl⟩

theorem sigma0_sM0 : sM (sigma0Word hS) (s0c hS 0) = s0c hS 2 := sM_middle _ _

theorem sigma0_sM_symm0 : (sM (sigma0Word hS)).symm (s0c hS 0) = s0c hS 1 := by
  rw [Equiv.symm_apply_eq, sigma0_sM1]

theorem sigma0_sM_symm1 : (sM (sigma0Word hS)).symm (s0c hS 1) = s0c hS 2 := by
  rw [Equiv.symm_apply_eq, sigma0_sM2]

theorem sigma0_sM_symm2 : (sM (sigma0Word hS)).symm (s0c hS 2) = s0c hS 0 := by
  rw [Equiv.symm_apply_eq, sigma0_sM0]

theorem admKey_s0c (c : Fin 3) :
    admKey (sigma0Word hS) (s0c hS c) =
      (if c = 0 then 1 else if c = 1 then 0 else 2) * 3 + c.val := by
  have e : (finProdFinEquiv (s0c hS c)).val = c.val := by rw [finProdFinEquiv_val3]; simp
  simp only [admKey, sigma0_oHeight2, sigma0Word_length, one_mul]
  congr 1

theorem sigma0_sRows :
    sRows (sigma0Word hS) (admKey _) = [s0c hS 1, s0c hS 0, s0c hS 2] := by
  apply eq_of_pairwise_key (K := admKey (sigma0Word hS))
  · have h := (sRows_sorted (sigma0Word hS) (admKey _)).and
      (List.nodup_iff_pairwise_ne.mp (sRows_nodup (sigma0Word hS) (admKey _)))
    refine h.imp (fun {a b} hab => lt_of_le_of_ne hab.1 (fun e => hab.2 ?_))
    rw [s0c_eq hS a, s0c_eq hS b] at e ⊢
    rw [admKey_s0c, admKey_s0c] at e
    congr 1
    have ha := a.2.isLt
    have hb := b.2.isLt
    apply Fin.ext
    revert e
    generalize a.2 = x
    generalize b.2 = y
    fin_cases x <;> fin_cases y <;> simp
  · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      false_imp_iff, implies_true, List.Pairwise.nil, and_true, admKey_s0c]
    decide
  · intro x
    rw [s0c_eq hS x]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro _
      generalize x.2 = c
      fin_cases c <;> simp
    · intro _; exact mem_sRows _ _ _

theorem sigma0_sCols : sCols (sigma0Word hS) = [s0c hS 0, s0c hS 1, s0c hS 2] := by
  apply List.ext_getElem (by rw [sCols_length]; rfl)
  intro i h₁ h₂
  rw [sCols_getElem]
  rw [sCols_length, sigma0Word_length] at h₁
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [finProdFinEquiv_val3]
  interval_cases i <;> rfl

end Sigma0

/-! ### The simple seam -/

/-- The column labels of the marked word grid of `σ_0` read in the rotated seam. -/
def simC (k : ℕ) : BCol → Fin (k + 3 + 1)
  | Sum.inl _ => 0
  | Sum.inr (h, c) => if h = 0 then (if c = 0 then ⟨k + 2, by omega⟩ else if c = 1 then
      ⟨k + 3, by omega⟩ else ⟨k + 1, by omega⟩) else if hh : h - 1 < k + 4 then ⟨h - 1, hh⟩ else 0

/-- The row labels of the marked word grid of `σ_0` read in the rotated seam. -/
def simR (k : ℕ) : BRow → Fin (k + 3 + 1)
  | Sum.inl _ => 0
  | Sum.inr (h, c) => if h = 0 then (if c = 0 then ⟨k + 2, by omega⟩ else ⟨k + 3, by omega⟩)
      else if hh : h - 1 < k + 4 then ⟨h - 1, hh⟩ else 0

theorem simC_block (k j : ℕ) (hj : j < k + 4) : simC k (Sum.inr (1 + j, 0)) = ⟨j, hj⟩ := by
  simp only [simC]
  rw [if_neg (by omega), dif_pos (by omega)]
  congr 1; omega

theorem simR_block (k i : ℕ) (hi : i < k + 4) : simR k (Sum.inr (1 + i, 1)) = ⟨i, hi⟩ := by
  simp only [simR]
  rw [if_neg (by omega), dif_pos (by omega)]
  congr 1; omega

/-- **The seam with the simple factor.** -/
theorem simple_seam_movesTo_marked {k : ℕ} (hS : 2 ≤ S) (H : GridDiagram (k + 1))
    (hH : TriplyPrepared H) :
    ∃ M : GridDiagram ((sigma0Word hS).length * 3 + k + 1),
      IsMarkedGrid (sigma0Word hS) (by simp [sigma0Word]) (s0c hS 1) H hH.1 hH.2.1 M ∧
      (connectedSumSeamGrid H simpleFactorGrid hH.2.2 simpleFactorGrid_X_zero).MovesTo M := by
  have hk := two_le_of_triplyPrepared hH
  have hL : 0 < (sigma0Word hS).length := by simp [sigma0Word]
  set v := sigma0Word hS with hv
  set κ := admKey v with hκ
  set P := markBlock v H hH.1 hH.2.1 with hPdef
  have hv1 : v.length = 1 := rfl
  -- the plain grid of `σ_0`
  have hplainC : (plainGrid v κ hL).cols = [Sum.inr (0, 0), Sum.inr (0, 1), Sum.inr (0, 2)] := by
    rw [plainGrid_cols, sigma0_sCols]; simp [sfCol_zero]
  have hplainR : (plainGrid v κ hL).rows = [Sum.inr (0, 1), Sum.inr (0, 0), Sum.inr (0, 2)] := by
    rw [plainGrid_rows, hκ, sigma0_sRows]; simp [sfCol_zero]
  have hpO : ∀ c : Fin 3, (plainGrid v κ hL).O (Sum.inr (0, c)) = Sum.inr (0, c) :=
    fun c => plainGrid_O v κ hL (s0c hS c)
  have hpX : ∀ c : Fin 3, (plainGrid v κ hL).X (Sum.inr (0, c)) =
      Sum.inr (0, ((sM v).symm (s0c hS c)).2) := by
    intro c
    rw [show (Sum.inr (0, c) : BCol) = Sum.inr ((s0c hS c).1.val, (s0c hS c).2) from rfl,
      plainGrid_X]
    congr 2
    rw [s0c_eq hS ((sM v).symm (s0c hS c))]
  have hpmem : ∀ c : Fin 3, (Sum.inr (0, c) : BCol) ∈ (plainGrid v κ hL).cols := by
    intro c; rw [hplainC]; fin_cases c <;> simp
  -- the marked grid with the block after the marked column
  let Dk : InsertData (plainGrid v κ hL) (markRow v (s0c hS 1)) P :=
    { l₁ := [Sum.inr (0, 0), Sum.inr (0, 1)], l₂ := [Sum.inr (0, 2)], m₁ := [],
      m₂ := [Sum.inr (0, 0), Sum.inr (0, 2)]
      cols_eq := by rw [hplainC]; rfl
      rows_eq := by rw [hplainR]; rfl
      cols_fresh := (markData v κ hL (s0c hS 1) H hH.1 hH.2.1).cols_fresh
      rows_fresh := (markData v κ hL (s0c hS 1) H hH.1 hH.2.1).rows_fresh }
  have hmI := movesTo_insertBlock Dk (markData v κ hL (s0c hS 1) H hH.1 hH.2.1)
  set I := insertBlock (plainGrid v κ hL) (markRow v (s0c hS 1)) P Dk with hIdef
  have hIc : I.cols = [Sum.inr (0, 0), Sum.inr (0, 1)] ++ P.cols ++ [Sum.inr (0, 2)] := rfl
  have hIr : I.rows = [] ++ P.rows ++ [Sum.inr (0, 0), Sum.inr (0, 2)] := rfl
  have hα : markRow v (s0c hS 1) = Sum.inr (0, 1) := rfl
  -- the seam
  set Sg := connectedSumSeamGrid H simpleFactorGrid hH.2.2 simpleFactorGrid_X_zero with hSg
  have hSgO : ∀ j (hj : j < k + 3 + 1), (Sg.O ⟨j, hj⟩).val =
      seamFun (gridRowVal H.O) (gridRowVal simpleFactorGrid.O) k 3 j := fun j hj => by
    rw [← gridRowVal_mk _ _ hj, hSg, gridRowVal_seam_O]
  have hSgX : ∀ j (hj : j < k + 3 + 1), (Sg.X ⟨j, hj⟩).val =
      seamFun (gridRowVal H.X) (gridRowVal simpleFactorGrid.X) k 3 j := fun j hj => by
    rw [← gridRowVal_mk _ _ hj, hSg, gridRowVal_seam_X]
  have hHOk : gridRowVal H.O k = 0 := by
    rw [gridRowVal_mk _ _ (by omega)]; exact congrArg Fin.val hH.2.1
  have hHXk : gridRowVal H.X k = k := by
    rw [gridRowVal_mk _ _ (by omega)]; exact congrArg Fin.val hH.2.2
  -- the rotated labeled seam
  set L := LabeledGrid.ofGrid Sg with hLdef
  have hLc : L.cols = (List.finRange (k + 3 + 1)).take (k + 2) ++
      (List.finRange (k + 3 + 1)).drop (k + 2) := (List.take_append_drop _ _).symm
  have m1 := movesTo_withCols_rotate L hLc
  have hcast : k + 3 + 1 = v.length * 3 + k + 1 := by rw [hv1]; omega
  have m2 := movesTo_castLG hcast (L.withCols ((List.finRange (k + 3 + 1)).drop (k + 2) ++
      (List.finRange (k + 3 + 1)).take (k + 2)) (by rw [hLc]; exact List.perm_append_comm))
  set L₂ := castLG hcast (L.withCols ((List.finRange (k + 3 + 1)).drop (k + 2) ++
      (List.finRange (k + 3 + 1)).take (k + 2)) (by rw [hLc]; exact List.perm_append_comm))
    with hL₂
  have hL₂c : L₂.cols = (List.finRange (k + 3 + 1)).drop (k + 2) ++
      (List.finRange (k + 3 + 1)).take (k + 2) := by rw [hL₂, castLG_cols]; rfl
  have hL₂r : L₂.rows = List.finRange (k + 3 + 1) := by rw [hL₂, castLG_rows]; rfl
  have hL₂O : L₂.O = Sg.O := by rw [hL₂, castLG_O]; rfl
  have hL₂X : L₂.X = Sg.X := by rw [hL₂, castLG_X]; rfl
  -- the lists of labels
  have hdrop : (List.finRange (k + 3 + 1)).drop (k + 2) =
      [⟨k + 2, by omega⟩, ⟨k + 3, by omega⟩] := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_drop, List.length_finRange] at h₁
    have hi2 : i < 2 := by omega
    rw [List.getElem_drop, List.getElem_finRange]
    interval_cases i <;> rfl
  have htake : (List.finRange (k + 3 + 1)).take (k + 2) =
      List.ofFn (fun j : Fin (k + 1) => (⟨j.val, by omega⟩ : Fin (k + 3 + 1))) ++
        [⟨k + 1, by omega⟩] := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_take, List.length_finRange] at h₁
    rw [List.getElem_take, List.getElem_finRange]
    by_cases hi : i < k + 1
    · rw [List.getElem_append_left (by simpa using hi), List.getElem_ofFn]; rfl
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.length_ofFn]
      have : i - (k + 1) = 0 := by omega
      simp only [this, List.getElem_cons_zero]
      apply Fin.ext; simp; omega
  have hfin : List.finRange (k + 3 + 1) =
      List.ofFn (fun i : Fin (k + 2) => (⟨i.val, by omega⟩ : Fin (k + 3 + 1))) ++
        [⟨k + 2, by omega⟩, ⟨k + 3, by omega⟩] := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_finRange] at h₁
    rw [List.getElem_finRange]
    by_cases hi : i < k + 2
    · rw [List.getElem_append_left (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
      rfl
    · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
      simp only [List.length_ofFn]
      have : i = k + 2 ∨ i = k + 3 := by omega
      rcases this with rfl | rfl <;> simp
  have hPc : P.cols.map (simC k) =
      List.ofFn (fun j : Fin (k + 1) => (⟨j.val, by omega⟩ : Fin (k + 3 + 1))) := by
    change (List.ofFn P.hc).map (simC k) = _
    rw [List.map_ofFn]
    congr 1; funext j
    change simC k (Sum.inr (1 + j.val, 0)) = _
    exact simC_block k j.val (by omega)
  have hPr : P.rows.map (simR k) =
      List.ofFn (fun i : Fin (k + 2) => (⟨i.val, by omega⟩ : Fin (k + 3 + 1))) := by
    change (List.ofFn P.hr).map (simR k) = _
    rw [List.map_ofFn]
    congr 1; funext i
    change simR k (Sum.inr (1 + i.val, 1)) = _
    exact simR_block k i.val (by omega)
  have hc : L₂.cols = I.cols.map (simC k) := by
    rw [hL₂c, hdrop, htake, hIc, List.map_append, List.map_append, hPc]
    rfl
  have hr : L₂.rows = I.rows.map (simR k) := by
    rw [hL₂r, hfin, hIr, List.map_append, List.map_append, hPr]
    rfl
  -- the values of the labels
  have hC0 : simC k (Sum.inr (0, 0)) = ⟨k + 2, by omega⟩ := by simp [simC]
  have hC1 : simC k (Sum.inr (0, 1)) = ⟨k + 3, by omega⟩ := by simp [simC]
  have hC2 : simC k (Sum.inr (0, 2)) = ⟨k + 1, by omega⟩ := by simp [simC]
  have hR0 : simR k (Sum.inr (0, 0)) = ⟨k + 2, by omega⟩ := by simp [simR]
  have hR2 : simR k (Sum.inr (0, 2)) = ⟨k + 3, by omega⟩ := by simp [simR]
  have hCb : ∀ j : Fin (k + 1), simC k (P.hc j) = ⟨j.val, by omega⟩ := fun j => by
    change simC k (Sum.inr (1 + j.val, 0)) = _
    exact simC_block k j.val (by omega)
  have hRb : ∀ i (hi : i < k + 3 + 1), simR k (Sum.inr (v.length + i, 1)) = ⟨i, hi⟩ :=
    fun i hi => simR_block k i hi
  -- the markings of the seam
  have hSO : ∀ j (hj : j < k + 3 + 1), (Sg.O ⟨j, hj⟩).val =
      if j < k then gridRowVal H.O j else if j = k then k + 1 else if j = k + 1 then k + 3
        else if j = k + 2 then k + 2 else 0 := by
    intro j hj
    rw [hSgO, seamFun]
    by_cases h1 : j < k
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_pos (by omega), gridRowVal_simpleFactorGrid_O]
      have : j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp [hHOk]
  have hSX : ∀ j (hj : j < k + 3 + 1), (Sg.X ⟨j, hj⟩).val =
      if j < k then gridRowVal H.X j else if j = k then k else if j = k + 1 then k + 2
        else if j = k + 2 then k + 1 else k + 3 := by
    intro j hj
    rw [hSgX, seamFun]
    by_cases h1 : j < k
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_pos (by omega), gridRowVal_simpleFactorGrid_X]
      have : j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp [hHXk]
  -- the markings of the marked grid
  have hIO : ∀ c : Fin 3, I.O (Sum.inr (0, c)) =
      if c = 1 then P.hr 0 else Sum.inr (0, c) := by
    intro c
    rw [hIdef, insertBlock_O, Dk.blockO_old (hpmem c), hpO c, hα]
    by_cases h : c = 1
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  have hIX : ∀ c : Fin 3, I.X (Sum.inr (0, c)) =
      if ((sM v).symm (s0c hS c)).2 = 1 then P.hr (Fin.last (k + 1))
        else Sum.inr (0, ((sM v).symm (s0c hS c)).2) := by
    intro c
    rw [hIdef, insertBlock_X, Dk.blockX_old (hpmem c), hpX c, hα]
    by_cases h : ((sM v).symm (s0c hS c)).2 = 1
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  have hIOb : ∀ j, I.O (P.hc j) = P.oRow j := fun j => by
    rw [hIdef, insertBlock_O, blockO_hc]
  have hIXb : ∀ j, I.X (P.hc j) = P.xRow j := fun j => by
    rw [hIdef, insertBlock_X, blockX_hc]
  have hHO0 : ∀ j : Fin (k + 1), j.val < k → H.O j ≠ 0 := fun j hj e => by
    have := H.O.toPerm.injective (e.trans hH.2.1.symm)
    rw [this] at hj; simp at hj
  have hrec : L₂.toGrid = I.toGrid := by
    apply toGrid_eq_of_image I L₂ (simC k) (simR k)
    · intro c hc' c' hc'' h
      exact List.inj_on_of_nodup_map (hc ▸ L₂.cols_nodup) hc' hc'' h
    · intro z hz z' hz' h
      exact List.inj_on_of_nodup_map (hr ▸ L₂.rows_nodup) hz hz' h
    · exact hc
    · exact hr
    · intro c hc'
      rw [hL₂O]
      rw [hIc] at hc'
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc'
      rcases hc' with ((rfl | rfl) | hc') | rfl
      · rw [hIO 0, if_neg (by decide), hC0, hR0]
        apply Fin.ext; rw [hSO]; simp
      · rw [hIO 1, if_pos rfl, hC1, stdBlock_hr, hRb _ (lt_of_lt_of_le (Fin.isLt _) (by omega))]
        apply Fin.ext; rw [hSO]; simp
      · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc'
        rw [hIOb, hCb, stdBlock_oRow]
        apply Fin.ext
        rw [hSO]
        by_cases hj : j.val < k
        · rw [if_pos hj, if_neg (hHO0 j hj), hRb _ (lt_of_lt_of_le (Fin.isLt _) (by omega)),
            gridRowVal_mk _ _ (by omega)]
        · have hjk : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
          rw [if_neg hj, if_pos (by rw [hjk]; rfl), hjk, if_pos hH.2.1, hRb _ (by omega)]
      · rw [hIO 2, if_neg (by decide), hC2, hR2]
        apply Fin.ext; rw [hSO]; simp
    · intro c hc'
      rw [hL₂X]
      rw [hIc] at hc'
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc'
      rcases hc' with ((rfl | rfl) | hc') | rfl
      · rw [hIX 0, sigma0_sM_symm0, if_pos rfl, hC0, stdBlock_hr,
          hRb _ (lt_of_lt_of_le (Fin.isLt _) (by omega))]
        apply Fin.ext; rw [hSX]; simp
      · rw [hIX 1, sigma0_sM_symm1, if_neg (show ¬ (2 : Fin 3) = 1 by decide), hC1, hR2]
        apply Fin.ext; rw [hSX]; simp
      · obtain ⟨j, rfl⟩ := P.mem_cols.mp hc'
        rw [hIXb, hCb, stdBlock_xRow]
        apply Fin.ext
        rw [hSX]
        by_cases hj : j.val < k
        · rw [if_pos hj, hRb _ (lt_of_lt_of_le (Fin.isLt _) (by omega)),
            gridRowVal_mk _ _ (by omega)]
        · have hjk : j = Fin.last k := Fin.ext (by have := j.isLt; simp; omega)
          rw [if_neg hj, if_pos (by rw [hjk]; rfl), hjk, hH.2.2,
            hRb _ (lt_of_lt_of_le (Fin.isLt _) (by omega))]
          simp
      · rw [hIX 2, sigma0_sM_symm2, if_neg (show ¬ (0 : Fin 3) = 1 by decide), hC2, hR0]
        apply Fin.ext; rw [hSX]; simp
  refine ⟨(markedGrid v κ hL (s0c hS 1) H hH.1 hH.2.1).toGrid, ⟨κ, admKey_mono v, rfl⟩, ?_⟩
  have h0 : Sg.MovesTo L.toGrid := by
    rw [hLdef, LabeledGrid.toGrid_ofGrid]
  rw [hrec] at m2
  exact h0.trans (m1.trans (m2.trans hmI))

end OnLeConjecture.KnotTheory.MarkedCancel
