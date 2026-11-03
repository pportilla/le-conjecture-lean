/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupEndpointSort
public import OnLeConjecture.KnotFloer.GridEndpointCleanupFactors

/-!
# The raw scissor endpoint is the cyclic block grid

This file proves the statement of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 10, "The raw scissor endpoint is already this cyclic
grid"): after sorting its rows into blocks (`endpoint_movesTo_endRows`), a scissor endpoint grid
is the cyclic block grid (`cyclicBlockGrid`) of the frame preparations of the local grids of the
factors (`endpointBlockGrid_eq_cyclicBlockGrid`). Consequently it is related by grid moves to the
seam chain of these frame preparations (`endpoint_movesTo_seamChain`). For a single factor the
sorted endpoint is the corner destabilization of the frame preparation of its local grid, and the
endpoint is related by grid moves to that frame preparation (`endpoint_movesTo_framePrep`). All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-! ### Coordinates of the frame preparation -/

theorem val_finRotate_symm {n : ℕ} (v : Fin n) :
    ((finRotate n).symm v).val = if v.val = 0 then n - 1 else v.val - 1 := by
  cases n with
  | zero => exact v.elim0
  | succ m =>
    split_ifs with h
    · have : v = 0 := Fin.ext h
      subst this
      have e : (finRotate (m + 1)).symm 0 = Fin.last m := by
        rw [Equiv.symm_apply_eq, finRotate_last]
      rw [e]
      simp
    · have hv : (finRotate (m + 1)) ⟨v.val - 1, by omega⟩ = v := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (by intro e; have := congrArg Fin.val e; simp at this; omega)]
        simp; omega
      have e : (finRotate (m + 1)).symm v = ⟨v.val - 1, by omega⟩ := by
        rw [Equiv.symm_apply_eq, hv]
      rw [e]

section FramePrep

variable {n : ℕ} (G : GridDiagram n) (hG : ClosingRowBottom G)

theorem gridRowVal_framePrep_O {j : ℕ} (hj : j < n) :
    gridRowVal (framePrep G hG).O j = if gridRowVal G.O j = 0 then n else gridRowVal G.O j := by
  rw [framePrep, GridDiagram.stabilizeX_O, gridRowVal_insertPoint]
  simp only [Fin.val_last, Fin.val_zero, natSuccAbove, natPredAbove, show ¬ j = n by omega,
    show j < n + 1 by omega, hj, ↓reduceIte, Nat.not_lt_zero]
  rw [gridRowVal_mk _ _ hj, gridRowVal_mk _ _ hj, GridDiagram.relabelRows_O,
    GridState.relabelRows_apply, val_finRotate_symm]
  split_ifs <;> omega

theorem gridRowVal_framePrep_X {j : ℕ} (hj0 : 0 < j) (hj : j < n) :
    gridRowVal (framePrep G hG).X j = if gridRowVal G.X j = 0 then n else gridRowVal G.X j := by
  rw [framePrep, GridDiagram.stabilizeX_X, gridRowVal_splitPoint]
  simp only [Fin.val_last, Fin.val_zero, natSuccAbove, natPredAbove, show ¬ j = n by omega,
    show (0 : ℕ) < n by omega, show ¬ j = 0 by omega, show j < n + 1 by omega, hj, ↓reduceIte,
    Nat.not_lt_zero]
  rw [gridRowVal_mk _ _ hj, gridRowVal_mk _ _ hj, GridDiagram.relabelRows_X,
    GridState.relabelRows_apply, val_finRotate_symm]
  split_ifs <;> omega

theorem gridRowVal_framePrep_X_zero : gridRowVal (framePrep G hG).X 0 = 0 := by
  have h := (framePrep_triplyPrepared G hG).1
  have := gridRowVal_val (framePrep G hG).X 0
  rw [h] at this
  simpa using this

end FramePrep

theorem seamChainOffset_succ {M : ℕ} (p : Fin (M + 1) → ℕ) (k : ℕ) (hk : k + 1 < M + 1) :
    seamChainOffset p ⟨k + 1, hk⟩ = seamChainOffset p ⟨k, by omega⟩ + p ⟨k, by omega⟩ := by
  simp only [seamChainOffset]
  rw [Fin.sum_univ_castSucc]
  rfl


variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)
  {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)
  {μ : Equiv.Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ) (hμ' : ∀ c, μ c ≠ c)

/-! ### The sorted endpoint -/

/-- The scissor endpoint with its rows in the block row order. -/
def endpointBlockGrid : GridDiagram (prodSize F) :=
  ((endpointLabeled F hnd hl μ hμ').withRows (endRows F hS (ℓ := ℓ))
    (perm_endRows F hS hnd hl)).toGrid

theorem endpointBlockGrid_O_val (c : Fin (prodSize F)) :
    ((endpointBlockGrid F hS hnd hl hμ').O c).val = (endRows F hS (ℓ := ℓ)).idxOf c := by
  rw [endpointBlockGrid, LabeledGrid.toGrid_O_val]
  simp [endpointLabeled, LabeledGrid.withRows, LabeledGrid.colAt, LabeledGrid.rpos]

theorem endpointBlockGrid_X_val (c : Fin (prodSize F)) :
    ((endpointBlockGrid F hS hnd hl hμ').X c).val = (endRows F hS (ℓ := ℓ)).idxOf (μ.symm c) := by
  rw [endpointBlockGrid, LabeledGrid.toGrid_X_val]
  simp [endpointLabeled, LabeledGrid.withRows, LabeledGrid.colAt, LabeledGrid.rpos]

/-- The frame preparation of the local grid of a factor. -/
abbrev localFrame (l : Fin (N + B)) : GridDiagram (factorSize F l + 1) :=
  framePrep (localGrid F hS hnd hl l).toGrid (closingRowBottom_localGrid F hS hnd hl l)

/-- **Coordinates of the sorted endpoint, `O` markings.** -/
theorem endpointBlockGrid_O_colG (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    gridRowVal (endpointBlockGrid F hS hnd hl hμ').O (factorStart F l + j.val) + 1 =
      factorStart F l + gridRowVal (localFrame F hS hnd hl l).O j.val := by
  rw [gridRowVal_framePrep_O _ _ j.isLt, gridRowVal_val, localGrid_O_val,
    show factorStart F l + j.val = (colG F l j).val from (colG_val F l j).symm, gridRowVal_val,
    endpointBlockGrid_O_val, idxOf_endRows F hS hnd hl]
  by_cases hj : j = lastLocal F hS l
  · subst hj
    have := blockPos_lastLocal F hS hnd hl l
    simp [localRows]
    omega
  · have := blockPos_of_ne F hS hnd hl l hj
    rw [if_neg (by omega)]
    omega

include hμ in
/-- **Coordinates of the sorted endpoint, `X` markings away from the first column of a block.** -/
theorem endpointBlockGrid_X_colG (l : Fin (N + B)) (j : Fin (factorSize F l)) (hj0 : 0 < j.val) :
    gridRowVal (endpointBlockGrid F hS hnd hl hμ').X (factorStart F l + j.val) + 1 =
      factorStart F l + gridRowVal (localFrame F hS hnd hl l).X j.val := by
  have hne : (localMatch F l).symm j ≠ lastLocal F hS l := by
    intro e
    rw [Equiv.symm_apply_eq, localMatch_lastLocal F hS] at e
    rw [e] at hj0
    simp at hj0
  have hmu : μ.symm (colG F l j) = colG F l ((localMatch F l).symm j) := by
    rw [Equiv.symm_apply_eq, mu_colG hμ l _ hne, Equiv.apply_symm_apply]
  rw [gridRowVal_framePrep_X _ _ hj0 j.isLt, gridRowVal_val, localGrid_X_val,
    show factorStart F l + j.val = (colG F l j).val from (colG_val F l j).symm, gridRowVal_val,
    endpointBlockGrid_X_val, hmu, idxOf_endRows F hS hnd hl]
  have := blockPos_of_ne F hS hnd hl l hne
  rw [if_neg (by omega)]
  omega

include hμ in
/-- **Coordinates of the sorted endpoint, `X` markings in the first column of a block.** The `X`
marking of the first column of a block lies in the last row of the preceding block, cyclically. -/
theorem endpointBlockGrid_X_first (l : Fin (N + B)) :
    gridRowVal (endpointBlockGrid F hS hnd hl hμ').X (factorStart F l) + 1 =
      factorStart F ((finRotate (N + B)).symm l) + factorSize F ((finRotate (N + B)).symm l) := by
  set l' := (finRotate (N + B)).symm l with hl'
  have hmu : μ.symm (colG F l (firstLocal F hS l)) = colG F l' (lastLocal F hS l') := by
    rw [Equiv.symm_apply_eq, colG_lastLocal F hS, mu_colZ_zero hμ, hl', Equiv.apply_symm_apply,
      colF_zero_eq]
  have h1 : factorStart F l = (colG F l (firstLocal F hS l)).val := by
    rw [colG_val]; rfl
  rw [h1, gridRowVal_val, endpointBlockGrid_X_val, hmu, idxOf_endRows F hS hnd hl]
  have := blockPos_lastLocal F hS hnd hl l'
  omega

/-! ### The cyclic block grid -/

theorem factorStart_zero (l : Fin (N + B)) (h : l.val = 0) : factorStart F l = 0 := by
  simp [factorStart, h, factorOffset_zero]

/-- The offsets of the seam chain of the frame preparations are the block starts. -/
theorem seamChainOffset_factorSize {M : ℕ} (hM : N + B = M + 1) (i : Fin (M + 1)) :
    seamChainOffset (fun i => factorSize F (Fin.cast hM.symm i)) i =
      factorStart F (Fin.cast hM.symm i) := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    rw [factorStart_zero F _ rfl]
    simp [seamChainOffset]
  | succ k ih =>
    rw [seamChainOffset_succ (fun i => factorSize F (Fin.cast hM.symm i)) k hk, ih (by omega)]
    have := factorStart_succ F (Fin.cast hM.symm ⟨k, by omega⟩) (by simp; omega)
    exact this.symm

include hμ in
/-- **The raw scissor endpoint is the cyclic block grid.** -/
theorem endpointBlockGrid_eq_cyclicBlockGrid (M : ℕ) (hM : N + B = M + 1 + 1) :
    (⟨_, endpointBlockGrid F hS hnd hl hμ'⟩ : Σ k, GridDiagram k) =
      ⟨_, cyclicBlockGrid M (p := fun i => factorSize F (Fin.cast hM.symm i))
        (fun i => localFrame F hS hnd hl (Fin.cast hM.symm i))
        (fun _ => (framePrep_triplyPrepared _ _).1) (fun _ => framePrep_triplyPrepared _ _)⟩ := by
  set p : Fin (M + 1 + 1) → ℕ := fun i => factorSize F (Fin.cast hM.symm i) with hp
  generalize hC : cyclicBlockGrid M (p := fun i => factorSize F (Fin.cast hM.symm i))
    (fun i => localFrame F hS hnd hl (Fin.cast hM.symm i))
    (fun i => (framePrep_triplyPrepared _ _).1) (fun i => framePrep_triplyPrepared _ _) = C
  have hCO := gridRowVal_cyclicBlockGrid M (p := fun i => factorSize F (Fin.cast hM.symm i))
    (fun i => localFrame F hS hnd hl (Fin.cast hM.symm i))
    (fun i => (framePrep_triplyPrepared _ _).1) (fun i => framePrep_triplyPrepared _ _)
  have hCX0 := gridRowVal_cyclicBlockGrid_X_zero M (p := fun i => factorSize F (Fin.cast hM.symm i))
    (fun i => localFrame F hS hnd hl (Fin.cast hM.symm i))
    (fun i => (framePrep_triplyPrepared _ _).1) (fun i => framePrep_triplyPrepared _ _)
  rw [hC] at hCO hCX0
  have hsz : prodSize F = seamChainSize (M + 1) p := by
    have h1 : seamChainSize (M + 1) p =
        seamChainOffset p (Fin.last (M + 1)) + p (Fin.last (M + 1)) := by
      rw [seamChainOffset_last]; rfl
    rw [h1, seamChainOffset_factorSize F hM]
    exact (factorStart_last F _ (by simp [hM])).symm
  refine (gridCast_sigma hsz _).symm.trans ?_
  congr 1
  have hdecomp : ∀ k, k < seamChainSize (M + 1) p → ∃ (l : Fin (N + B)) (j : Fin (factorSize F l)),
      k = factorStart F l + j.val := by
    intro k hk
    obtain ⟨l, j, hc⟩ := exists_colG F ⟨k, lt_of_lt_of_eq hk hsz.symm⟩
    refine ⟨l, j, ?_⟩
    have := congrArg Fin.val hc
    rw [colG_val] at this
    exact this.symm
  have hoff : ∀ l : Fin (N + B), seamChainOffset p (Fin.cast hM l) = factorStart F l := fun l =>
    seamChainOffset_factorSize F hM (Fin.cast hM l)
  apply gridDiagram_ext_gridRowVal
  · intro k hk
    rw [gridRowVal_gridCast_O]
    obtain ⟨l, j, rfl⟩ := hdecomp k hk
    have h1 := endpointBlockGrid_O_colG F hS hnd hl hμ' l j
    have h2 : gridRowVal C.O (seamChainOffset p (Fin.cast hM l) + j.val)
        + 1 = seamChainOffset p (Fin.cast hM l) +
          gridRowVal (localFrame F hS hnd hl l).O j.val :=
      (hCO (Fin.cast hM l) (j := j.val) j.isLt).1
    rw [hoff] at h2
    omega
  · intro k hk
    rw [gridRowVal_gridCast_X]
    obtain ⟨l, j, rfl⟩ := hdecomp k hk
    by_cases hj0 : 0 < j.val
    · have h1 := endpointBlockGrid_X_colG F hS hnd hl hμ hμ' l j hj0
      have h2 : gridRowVal C.X
          (seamChainOffset p (Fin.cast hM l) + j.val) + 1 = seamChainOffset p (Fin.cast hM l) +
            gridRowVal (localFrame F hS hnd hl l).X j.val :=
        (hCO (Fin.cast hM l) (j := j.val) j.isLt).2 (by omega)
      rw [hoff] at h2
      omega
    · have hj : j.val = 0 := by omega
      have h1 := endpointBlockGrid_X_first F hS hnd hl hμ hμ' l
      rw [hj, Nat.add_zero]
      by_cases hl0 : l.val = 0
      · have h2 := hCX0
        rw [factorStart_zero F l hl0] at h1 ⊢
        have h3 : (finRotate (N + B)).symm l = ⟨N + B - 1, by omega⟩ := by
          rw [Equiv.symm_apply_eq]
          apply Fin.ext
          rw [finRotate_val_last _ (by simp; omega), hl0]
        rw [h3, factorStart_last F _ (by simp; omega)] at h1
        have h2' := h2.trans hsz.symm
        omega
      · have hpos : 0 < factorStart F l := by
          have := factorStart_lt_of_lt (F := F) (l := ⟨0, by omega⟩) (l' := l) (by simp; omega)
          have := factorSize_pos F hS ⟨0, by omega⟩
          omega
        have h2 : gridRowVal C.X
            (seamChainOffset p (Fin.cast hM l) + 0) + 1 = seamChainOffset p (Fin.cast hM l) +
              gridRowVal (localFrame F hS hnd hl l).X 0 :=
          (hCO (Fin.cast hM l) (j := 0) (factorSize_pos F hS l)).2 (by rw [hoff]; omega)
        rw [hoff, gridRowVal_framePrep_X_zero] at h2
        simp only [Nat.add_zero] at h2
        have h3 : (finRotate (N + B)).symm l = ⟨l.val - 1, by omega⟩ := by
          rw [Equiv.symm_apply_eq]
          apply Fin.ext
          rw [finRotate_val_succ _ (by simp; omega)]
          simp; omega
        have e5 : factorStart F ((finRotate (N + B)).symm l) +
            factorSize F ((finRotate (N + B)).symm l) = factorStart F l := by
          rw [h3, ← factorStart_succ F ⟨l.val - 1, by omega⟩ (by simp; omega)]
          congr 1
          exact Fin.ext (by simp; omega)
        omega

include hμ in
/-- **The raw scissor endpoint and the seam chain.** For at least two factors, a scissor endpoint
grid is related by grid moves to the seam chain of the frame preparations of the local grids of
its factors. -/
theorem endpoint_movesTo_seamChain (hsort : ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b))
    (M : ℕ) (hM : N + B = M + 1 + 1) :
    (phaseGrid (listPerm ℓ hnd hl) μ hμ').MovesTo
      (chainOf (M + 1) (fun i => ⟨factorSize F (Fin.cast hM.symm i),
        localFrame F hS hnd hl (Fin.cast hM.symm i)⟩) fun i =>
          framePrep_triplyPrepared (localGrid F hS hnd hl (Fin.cast hM.symm i)).toGrid
            (closingRowBottom_localGrid F hS hnd hl _)) := by
  have _ := hsort
  refine (endpoint_movesTo_endRows F hnd hl hμ hμ').trans ?_
  refine (movesTo_of_sigma_eq (endpointBlockGrid_eq_cyclicBlockGrid F hS hnd hl hμ hμ' M hM)).trans
    ?_
  exact (seamChainGrid_movesTo_cyclicBlockGrid M _ _ _).symm

include hμ in
/-- **A single factor.** For one factor, a scissor endpoint grid is related by grid moves to the
frame preparation of the local grid of its factor. -/
theorem endpoint_movesTo_framePrep (h1 : N + B = 1) :
    (phaseGrid (listPerm ℓ hnd hl) μ hμ').MovesTo
      (localFrame F hS hnd hl ⟨0, by omega⟩) := by
  set l₀ : Fin (N + B) := ⟨0, by omega⟩
  set T := localFrame F hS hnd hl l₀ with hT
  have ht : TriplyPrepared T := framePrep_triplyPrepared _ _
  have hd := factorSize_pos F hS l₀
  have hc : T.O 0 ≠ Fin.last (factorSize F l₀) := by
    intro h
    have h1 := gridRowVal_framePrep_O (localGrid F hS hnd hl l₀).toGrid
      (closingRowBottom_localGrid F hS hnd hl l₀) (j := 0) hd
    have h0 : gridRowVal T.O 0 = factorSize F l₀ := by
      rw [gridRowVal_mk _ _ (by omega)]
      change (T.O 0).val = _
      rw [h]; rfl
    have hG0 : gridRowVal (localGrid F hS hnd hl l₀).toGrid.O 0 =
        (localRows F hS ℓ l₀).idxOf ⟨0, hd⟩ := by
      rw [gridRowVal_mk _ _ hd, localGrid_O_val]
    have hne : (⟨0, hd⟩ : Fin (factorSize F l₀)) ≠ lastLocal F hS l₀ := by
      intro e; have := congrArg Fin.val e; simp [lastLocal] at this
      have := six_le_factorSize F (hS := hS) l₀; omega
    have h2 : (localRows F hS ℓ l₀).idxOf ⟨0, hd⟩ ≠ 0 := by
      simp only [localRows]
      rw [List.idxOf_cons_ne _ (Ne.symm hne)]
      omega
    have h3 := List.idxOf_lt_length_iff.mpr (mem_localRows F hS hnd hl l₀ ⟨0, hd⟩)
    rw [length_localRows F hS hnd hl] at h3
    change gridRowVal T.O 0 = _ at h1
    rw [h0, hG0] at h1
    split_ifs at h1 <;> omega
  have hsz : prodSize F = factorSize F l₀ := by
    have := factorStart_last F l₀ (by simp [l₀, h1])
    rw [factorStart_zero F l₀ rfl] at this
    omega
  have heq : (⟨_, endpointBlockGrid F hS hnd hl hμ'⟩ : Σ k, GridDiagram k) =
      ⟨_, cornerDestabilization T ht hc⟩ := by
    refine (gridCast_sigma hsz _).symm.trans ?_
    congr 1
    have hall : ∀ l : Fin (N + B), l = l₀ := fun l => Fin.ext (by have := l.isLt; simp [l₀]; omega)
    apply gridDiagram_ext_gridRowVal
    · intro k hk
      rw [gridRowVal_gridCast_O]
      have h1 := endpointBlockGrid_O_colG F hS hnd hl hμ' l₀ ⟨k, hk⟩
      have h2 := gridRowVal_cornerDestabilization_O T ht hc hk
      rw [factorStart_zero F l₀ rfl, Nat.zero_add, Nat.zero_add, ← hT] at h1
      simp only at h1
      omega
    · intro k hk
      rw [gridRowVal_gridCast_X]
      by_cases hk0 : 0 < k
      · have h1 := endpointBlockGrid_X_colG F hS hnd hl hμ hμ' l₀ ⟨k, hk⟩ hk0
        have h2 := gridRowVal_cornerDestabilization_X T ht hc hk0 hk
        rw [factorStart_zero F l₀ rfl, Nat.zero_add, Nat.zero_add, ← hT] at h1
        simp only at h1
        omega
      · have hk0' : k = 0 := by omega
        subst hk0'
        have h1 := endpointBlockGrid_X_first F hS hnd hl hμ hμ' l₀
        have h2 := gridRowVal_cornerDestabilization_X_zero T ht hc
        rw [hall ((finRotate (N + B)).symm l₀), factorStart_zero F l₀ rfl] at h1
        omega
  refine (endpoint_movesTo_endRows F hnd hl hμ hμ').trans ?_
  exact (movesTo_of_sigma_eq heq).trans (movesTo_cornerDestabilization T ht hc).symm

end OnLeConjecture.KnotFloer.GridFull
