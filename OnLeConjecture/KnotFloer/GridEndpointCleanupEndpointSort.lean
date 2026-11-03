/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupBlockRows

/-!
# Sorting the rows of a scissor endpoint into blocks

A scissor endpoint grid `phaseGrid (listPerm ℓ) μ` (`IsScissorEndpointGrid`) is presented as the
labeled grid `endpointLabeled` whose columns are the columns of the product, whose rows are labeled
by the columns of their `O` markings, in the order `ℓ`, and whose `X` markings are given by `μ⁻¹`
(`toGrid_endpointLabeled`).

Its rows can be sorted into the block row order `endRows` by row commutations
(`endpoint_movesTo_endRows`), as in the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 10, "The raw scissor endpoint is already this cyclic
grid"): the segment of a row of a factor lies in the block of that factor, except for the
connecting rank-`0` row leaving the factor, whose segment joins two cyclically consecutive
columns. Hence rows of different factors do not interleave, and the connecting row does not
interleave any row (`nonintN_connecting`). Inside a factor the two orders agree except for the
connecting row. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-- **A segment between cyclically consecutive positions** does not interleave any other segment,
except possibly at a shared endpoint; the two shared configurations that occur are allowed. -/
theorem nonintN_connecting {n a b u v : ℕ} (hn : 4 ≤ n) (ha : a < n) (hb : b < n)
    (hab : b = a + 1 ∨ (a + 1 = n ∧ b = 0)) (hu : u < n) (hv : v < n) (hua : u ≠ a)
    (hvb : v ≠ b) (huv : u ≠ v) (h1 : u = b → v = b + 2) (h2 : v = a → u + 2 = a) :
    NonintN a b u v := by
  unfold NonintN CIooN
  rcases hab with rfl | ⟨rfl, rfl⟩
  · by_cases hub : u = a + 1
    · have := h1 hub
      constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
    · by_cases hva : v = a
      · have := h2 hva
        constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
      · constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
  · by_cases hub : u = 0
    · have := h1 hub
      constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
    · by_cases hva : v = a
      · have := h2 hva
        constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega
      · constructor <;> constructor <;> intro hh <;> split_ifs at hh ⊢ <;> omega

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)

/-! ### Columns of a factor and the component permutation -/

theorem colZ_zero_val (l : Fin (N + B)) :
    (colZ F hS l (rank0 hS)).val = factorStart F l + factorSize F l - 1 := by
  rw [← colG_lastLocal F hS, colG_val]
  simp only [lastLocal]
  have := factorSize_pos F hS l
  omega

/-- The first local column of a factor. -/
def firstLocal (l : Fin (N + B)) : Fin (factorSize F l) := ⟨0, factorSize_pos F hS l⟩

theorem colF_zero_eq (l : Fin (N + B)) : colF F hS l (rank0 hS) = colG F l (firstLocal F hS l) := by
  rw [colF, colG, ← globC_lfC _ _ hS]
  congr 2
  apply (Equiv.eq_symm_apply _).mpr
  apply Fin.ext
  rw [finProdFinEquiv_val3]
  simp [lfC, firstLocal]

theorem localMatch_firstLocal (l : Fin (N + B)) :
    (localMatch F l (firstLocal F hS l)).val = 2 := by
  have h : firstLocal F hS l = finProdFinEquiv ((⟨0, by
      have := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge; omega⟩ :
      Fin (F.factor l).length), (0 : Fin 3)) := by
    apply Fin.ext; rw [finProdFinEquiv_val3]; rfl
  rw [h, localMatch_apply, sM_middle, finProdFinEquiv_val3]
  rfl

theorem localMatch_symm_lastLocal (l : Fin (N + B)) :
    ((localMatch F l).symm (lastLocal F hS l)).val + 3 = factorSize F l := by
  have hlen := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge
  have h : lastLocal F hS l = finProdFinEquiv ((⟨(F.factor l).length - 1, by omega⟩ :
      Fin (F.factor l).length), (2 : Fin 3)) := by
    apply Fin.ext; rw [finProdFinEquiv_val3]; simp [lastLocal, factorSize]; omega
  have e : (localMatch F l).symm (finProdFinEquiv ((⟨(F.factor l).length - 1, by omega⟩ :
      Fin (F.factor l).length), (2 : Fin 3))) = finProdFinEquiv ((⟨(F.factor l).length - 1,
        by omega⟩ : Fin (F.factor l).length), (0 : Fin 3)) := by
    rw [Equiv.symm_apply_eq, localMatch_apply, sM_middle]
  rw [h, e, finProdFinEquiv_val3]
  simp [factorSize]
  omega

variable {F hS}

section Mu

variable {μ : Equiv.Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ)
include hμ

theorem mu_colZ_zero (l : Fin (N + B)) :
    μ (colZ F hS l (rank0 hS)) = colF F hS (finRotate (N + B) l) (rank0 hS) := by
  rw [hμ.2 _ (fun l' x hx h => by
    have := (colZ_injective F hS h).2
    subst this
    simp at hx), prodPerm_colZ]

/-- Every row other than a connecting row has its segment in the block of its factor. -/
theorem mu_colG_mem (l : Fin (N + B)) (j : Fin (factorSize F l)) (hj : j ≠ lastLocal F hS l) :
    factorStart F l ≤ (μ (colG F l j)).val ∧
      (μ (colG F l j)).val < factorStart F l + factorSize F l := by
  rw [mu_colG hμ l j hj, colG_val]
  have := (localMatch F l j).isLt
  omega

end Mu

/-! ### The endpoint as a labeled grid -/

variable (F) {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)

/-- The scissor endpoint grid as a labeled grid: the rows are labeled by the columns of their `O`
markings, in the order `ℓ`. -/
def endpointLabeled (μ : Equiv.Perm (Fin (prodSize F))) (hμ : ∀ c, μ c ≠ c) :
    LabeledGrid (prodSize F) (Fin (prodSize F)) (Fin (prodSize F)) where
  cols := List.finRange _
  rows := ℓ
  O := id
  X := μ.symm
  cols_length := List.length_finRange
  rows_length := hl
  cols_nodup := List.nodup_finRange _
  rows_nodup := hnd
  O_mem c _ := mem_of_listPerm ℓ hnd hl c
  X_mem c _ := mem_of_listPerm ℓ hnd hl _
  O_inj _ _ _ _ h := h
  X_inj _ _ _ _ h := μ.symm.injective h
  O_ne_X c _ h := hμ c (by
    change c = μ.symm c at h
    conv_lhs => rw [h]
    exact Equiv.apply_symm_apply _ _)

theorem listPerm_symm_val (c : Fin (prodSize F)) :
    ((listPerm ℓ hnd hl).symm c).val = ℓ.idxOf c := by
  have hc : c ∈ ℓ := mem_of_listPerm ℓ hnd hl c
  have hi : ℓ.idxOf c < prodSize F := lt_of_lt_of_eq (List.idxOf_lt_length_iff.mpr hc) hl
  have : listPerm ℓ hnd hl ⟨ℓ.idxOf c, hi⟩ = c := by
    rw [listPerm_apply]; exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hc)
  rw [(Equiv.symm_apply_eq _).mpr this.symm]

theorem toGrid_endpointLabeled (μ : Equiv.Perm (Fin (prodSize F))) (hμ : ∀ c, μ c ≠ c) :
    (endpointLabeled F hnd hl μ hμ).toGrid = phaseGrid (listPerm ℓ hnd hl) μ hμ := by
  ext c
  · rw [LabeledGrid.toGrid_O_val, phaseGrid_O_apply, listPerm_symm_val]
    simp [endpointLabeled, LabeledGrid.colAt, LabeledGrid.rpos]
  · rw [LabeledGrid.toGrid_X_val, phaseGrid_X_apply, listPerm_symm_val]
    simp [endpointLabeled, LabeledGrid.colAt, LabeledGrid.rpos]

theorem rowsNonint_endpointLabeled {μ : Equiv.Perm (Fin (prodSize F))} (hμ : ∀ c, μ c ≠ c)
    {x y : Fin (prodSize F)} (h : NonintN x.val (μ x).val y.val (μ y).val) :
    (endpointLabeled F hnd hl μ hμ).RowsNonint x y := by
  intro a a' b b' _ _ _ _ e1 e2 e3 e4
  change a = x at e1
  change μ.symm a' = x at e2
  change b = y at e3
  change μ.symm b' = y at e4
  have e2' : a' = μ x := by rw [← e2, Equiv.apply_symm_apply]
  have e4' : b' = μ y := by rw [← e4, Equiv.apply_symm_apply]
  subst e1 e3 e2' e4'
  simpa [endpointLabeled, LabeledGrid.cpos] using h

/-! ### Non-interleaving of the rows of the endpoint -/

theorem finRotate_val_succ {r : ℕ} (l : Fin r) (h : l.val + 1 < r) :
    (finRotate r l).val = l.val + 1 := by
  cases r with
  | zero => exact l.elim0
  | succ k => exact coe_finRotate_of_ne_last (fun e => by rw [e] at h; simp at h)

theorem finRotate_val_last {r : ℕ} (l : Fin r) (h : l.val + 1 = r) : (finRotate r l).val = 0 := by
  cases r with
  | zero => exact l.elim0
  | succ k =>
    have : l = Fin.last k := Fin.ext (by simp; omega)
    rw [this, finRotate_last]
    rfl

theorem factorStart_succ (l : Fin (N + B)) (h : l.val + 1 < N + B) :
    factorStart F ⟨l.val + 1, h⟩ = factorStart F l + factorSize F l := by
  simp only [factorStart, factorSize]
  rw [factorOffset_succ F.factor l]
  ring

theorem factorStart_last (l : Fin (N + B)) (h : l.val + 1 = N + B) :
    factorStart F l + factorSize F l = prodSize F := by
  simp only [factorStart, factorSize, prodSize]
  have := factorOffset_succ F.factor l
  rw [h, factorOffset_r] at this
  rw [this]
  ring

theorem factorStart_lt_of_lt {l l' : Fin (N + B)} (h : l.val < l'.val) :
    factorStart F l + factorSize F l ≤ factorStart F l' := by
  simp only [factorStart, factorSize]
  have := factorOffset_mono F.factor (show l.val + 1 ≤ l'.val by omega)
  rw [factorOffset_succ] at this
  omega

include hS in
theorem six_le_factorSize (l : Fin (N + B)) : 6 ≤ factorSize F l := by
  have := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge
  simp only [factorSize]
  omega

include hS in
theorem four_le_prodSize (l : Fin (N + B)) : 4 ≤ prodSize F := by
  have := factorStart_add_le F l
  have := six_le_factorSize F (hS := hS) l
  omega

section Pairs

variable {μ : Equiv.Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ)
  (hμ' : ∀ c, μ c ≠ c)
include hμ hμ'

/-- **A connecting row does not interleave any other row.** -/
theorem nonintN_colZ (l : Fin (N + B)) (y : Fin (prodSize F)) (hy : y ≠ colZ F hS l (rank0 hS)) :
    NonintN (colZ F hS l (rank0 hS)).val (μ (colZ F hS l (rank0 hS))).val y.val (μ y).val := by
  have hn := four_le_prodSize F (hS := hS) l
  have hZ := colZ_zero_val F hS l
  have hmuZ : (μ (colZ F hS l (rank0 hS))).val = factorStart F (finRotate (N + B) l) := by
    rw [mu_colZ_zero hμ, colF_zero_eq, colG_val]
    rfl
  have he := six_le_factorSize F (hS := hS) l
  refine nonintN_connecting hn (Fin.isLt _) (Fin.isLt _) ?_ y.isLt (Fin.isLt _) ?_ ?_ ?_ ?_ ?_
  · rw [hZ, hmuZ]
    by_cases h : l.val + 1 < N + B
    · left
      have : finRotate (N + B) l = ⟨l.val + 1, h⟩ := Fin.ext (finRotate_val_succ l h)
      rw [this, factorStart_succ F l h]
      omega
    · right
      have h' : l.val + 1 = N + B := by omega
      refine ⟨by rw [factorStart_last F l h']; omega, ?_⟩
      have : finRotate (N + B) l = ⟨0, by omega⟩ := Fin.ext (finRotate_val_last l h')
      rw [this]
      simp [factorStart, factorOffset_zero]
  · exact fun h => hy (Fin.ext h)
  · exact fun h => hy (μ.injective (Fin.ext h))
  · exact fun h => hμ' y (Fin.ext h.symm)
  · intro h
    set l₁ := finRotate (N + B) l
    have hne : firstLocal F hS l₁ ≠ lastLocal F hS l₁ := by
      intro e
      have := congrArg Fin.val e
      simp only [firstLocal, lastLocal] at this
      have := six_le_factorSize F (hS := hS) l₁
      omega
    have hy' : y = colG F l₁ (firstLocal F hS l₁) := Fin.ext (by
      rw [h, colG_val, hmuZ]; rfl)
    rw [hy', mu_colG hμ _ _ hne, colG_val, localMatch_firstLocal, hmuZ]
  · intro h
    obtain ⟨l', j', rfl⟩ := exists_colG F y
    by_cases hj' : j' = lastLocal F hS l'
    · exfalso
      rw [hj', colG_lastLocal F hS, mu_colZ_zero hμ] at h
      exact colF_ne_colZ F hS _ _ _ _ (Fin.ext h)
    · have e : μ (colG F l' j') = colZ F hS l (rank0 hS) := Fin.ext h
      rw [mu_colG hμ l' j' hj', ← colG_lastLocal F hS] at e
      have hl' : l' = l := colG_eq_colG F e
      subst hl'
      have e2 := colG_injective F l' e
      have hj2 : j' = (localMatch F l').symm (lastLocal F hS l') := by
        rw [← e2, Equiv.symm_apply_apply]
      have := localMatch_symm_lastLocal F hS l'
      rw [colG_val, hj2, hZ]
      omega

omit hμ' in
/-- **Rows of different factors do not interleave.** -/
theorem nonintN_colG_of_ne {l l' : Fin (N + B)} (hll' : l ≠ l') (j : Fin (factorSize F l))
    (j' : Fin (factorSize F l')) (hj : j ≠ lastLocal F hS l) (hj' : j' ≠ lastLocal F hS l') :
    NonintN (colG F l j).val (μ (colG F l j)).val (colG F l' j').val (μ (colG F l' j')).val := by
  have h1 := mu_colG_mem hμ l j hj
  have h2 := mu_colG_mem hμ l' j' hj'
  have h3 := colG_val F l j
  have h4 := colG_val F l' j'
  have h5 := j.isLt
  have h6 := j'.isLt
  apply nonintN_of_lt
  rcases Nat.lt_or_gt_of_ne (fun e => hll' (Fin.ext e)) with h | h
  · have := factorStart_lt_of_lt (F := F) h
    left; simp only [max_lt_iff, lt_min_iff]; omega
  · have := factorStart_lt_of_lt (F := F) h
    right; simp only [max_lt_iff, lt_min_iff]; omega

/-- **The inverted pairs of the block row order do not interleave.** -/
theorem nonintN_of_inverted {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup)
    (hl : ℓ.length = prodSize F) {x y : Fin (prodSize F)} (hx : x ∈ ℓ) (hy : y ∈ ℓ)
    (h1 : ℓ.idxOf x < ℓ.idxOf y) (h2 : (endRows F hS (ℓ := ℓ)).idxOf y <
      (endRows F hS (ℓ := ℓ)).idxOf x) :
    NonintN x.val (μ x).val y.val (μ y).val := by
  have hxy : x ≠ y := fun e => by subst e; omega
  obtain ⟨l, j, rfl⟩ := exists_colG F x
  obtain ⟨l', j', rfl⟩ := exists_colG F y
  by_cases hj : j = lastLocal F hS l
  · subst hj
    rw [colG_lastLocal F hS] at hxy ⊢
    exact nonintN_colZ F hμ hμ' l _ (Ne.symm hxy)
  · by_cases hj' : j' = lastLocal F hS l'
    · subst hj'
      rw [colG_lastLocal F hS] at hxy ⊢
      exact nonintN_comm.mp (nonintN_colZ F hμ hμ' l' _ hxy)
    · by_cases hll' : l = l'
      · subst hll'
        exfalso
        rw [idxOf_endRows F hS hnd hl, idxOf_endRows F hS hnd hl] at h2
        have e1 := blockPos_of_ne F hS hnd hl l hj
        have e2 := blockPos_of_ne F hS hnd hl l hj'
        set f : Fin (prodSize F) → Option (Fin (factorSize F l)) :=
          fun c => if c = colZ F hS l (rank0 hS) then none else locOf F l c with hf
        have hfx : ∀ k : Fin (factorSize F l), k ≠ lastLocal F hS l → f (colG F l k) = some k := by
          intro k hk
          simp only [hf]
          rw [if_neg, locOf_colG]
          rw [← colG_lastLocal F hS]
          exact fun e => hk (colG_injective F l e)
        have hinj : ∀ a a' b, f a = some b → f a' = some b → a = a' := by
          intro a a' b ha ha'
          simp only [hf] at ha ha'
          split_ifs at ha ha'
          rw [eq_colG_of_locOf F ha, eq_colG_of_locOf F ha']
        have h3 := idxOf_filterMap_lt hnd hinj hx hy (hfx j hj) (hfx j' hj') h1
        have e3 : (localRows F hS ℓ l).idxOf j = (ℓ.filterMap f).idxOf j + 1 := by
          simp only [localRows, ← hf]
          rw [List.idxOf_cons_ne _ (Ne.symm hj)]
        have e4 : (localRows F hS ℓ l).idxOf j' = (ℓ.filterMap f).idxOf j' + 1 := by
          simp only [localRows, ← hf]
          rw [List.idxOf_cons_ne _ (Ne.symm hj')]
        omega
      · exact nonintN_colG_of_ne F hμ hll' j j' hj hj'

end Pairs

/-- **Sorting the rows of a scissor endpoint into blocks.** -/
theorem endpoint_movesTo_endRows {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup)
    (hl : ℓ.length = prodSize F) {μ : Equiv.Perm (Fin (prodSize F))}
    (hμ : IsScissorEndpointPerm F hS μ) (hμ' : ∀ c, μ c ≠ c) :
    (phaseGrid (listPerm ℓ hnd hl) μ hμ').MovesTo
      ((endpointLabeled F hnd hl μ hμ').withRows (endRows F hS (ℓ := ℓ))
        (perm_endRows F hS hnd hl)).toGrid := by
  rw [← toGrid_endpointLabeled F hnd hl μ hμ']
  apply LabeledGrid.movesTo_withRows_of_inverted
  intro x hx y hy h1 h2
  exact rowsNonint_endpointLabeled F hnd hl hμ'
    (nonintN_of_inverted F hμ hμ' hnd hl hx hy h1 h2)

end OnLeConjecture.KnotFloer.GridFull
