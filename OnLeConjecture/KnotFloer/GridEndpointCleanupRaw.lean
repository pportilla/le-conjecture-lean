/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridScissorSequenceRoute
public import OnLeConjecture.KnotFloer.GridEndpointCleanupMarkedStatement
public import OnLeConjecture.KnotTheory.EndpointCleanupLocal
public import OnLeConjecture.KnotTheory.EndpointCleanupSort

/-!
# The factors of the scissor endpoint as separate signed word grids

This file describes the columns of a scissor endpoint grid factor by factor, as in the written
proof of Statement E (`statement_E_complete_proof.tex`, Section 10, "The raw scissor endpoint is
already this cyclic grid").

The columns of the factor `l` of a normalized factorization `F` form the block of the
`factorSize F l` consecutive columns starting at `factorStart F l`; the local column `j` is the
column `colG F l j` of the product. The component permutation of a scissor endpoint
(`IsScissorEndpointPerm`) acts on every column of the factor `l`, except its last column, as the
matching of the separate factor word (`mu_colG`). The last column carries the connecting rank-`0`
arc to the next factor.

For a row order `ℓ` of a scissor endpoint grid, sorted by height, the *local grid* of the factor `l`
(`localGrid`) has the rows of the factor `l` in the order of `ℓ`, except that the closing rank-`0`
row of the factor is the bottom row. It is a signed word grid of the factor word
(`isSignedWordGrid_localGrid`) whose closing row lies at the bottom (`closingRowBottom_localGrid`),
so that the marked factor cleanup applies to it. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-! ### Lists sorted by a key -/

theorem idxOf_lt_of_key_lt {α : Type*} [DecidableEq α] {K : α → ℕ} {l : List α}
    (hl : l.Pairwise (fun a b => K a ≤ K b)) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : K x < K y) : l.idxOf x < l.idxOf y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hax : a = x
    · subst hax
      have hya : y ≠ a := fun h => by subst h; omega
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hya)]
      omega
    · have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      have hay : a ≠ y := by
        intro h; subst h
        have := hl.1 x hx'; omega
      have hy' : y ∈ l := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h.symm hay
        · exact h
      rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay]
      have := ih hl.2 hx' hy'
      omega

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)

/-! ### The columns of a factor -/

/-- The number of columns of the factor `l`. -/
abbrev factorSize (l : Fin (N + B)) : ℕ := (F.factor l).length * 3

/-- The first column of the factor `l`. -/
abbrev factorStart (l : Fin (N + B)) : ℕ := 3 * factorOffset F.factor l.val

theorem factorStart_add_le (l : Fin (N + B)) : factorStart F l + factorSize F l ≤ prodSize F := by
  have := factorOffset_succ_le F.factor l
  simp only [factorStart, factorSize, prodSize]
  omega

include hS in
theorem factorSize_pos (l : Fin (N + B)) : 0 < factorSize F l := by
  have := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge
  simp only [factorSize]
  omega

/-- The column of the product of a local column of the factor `l`. -/
def colG (l : Fin (N + B)) (j : Fin (factorSize F l)) : Fin (prodSize F) :=
  col F (globC F.factor l (finProdFinEquiv.symm j))

theorem colG_val (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    (colG F l j).val = factorStart F l + j.val := by
  have h1 := fpe_val (factorProduct F.factor) (globC F.factor l (finProdFinEquiv.symm j))
  have h2 := finProdFinEquiv_val3 (finProdFinEquiv.symm j)
  rw [Equiv.apply_symm_apply] at h2
  simp only [colG, col, h1, globC_fst_val, globC_snd, factorStart]
  omega

theorem colG_injective (l : Fin (N + B)) : Function.Injective (colG F l) := by
  intro j j' h
  have := congrArg Fin.val h
  rw [colG_val, colG_val] at this
  exact Fin.ext (by omega)

/-- The local column of a column of the product, if it lies in the block of the factor `l`. -/
def locOf (l : Fin (N + B)) (c : Fin (prodSize F)) : Option (Fin (factorSize F l)) :=
  if h : factorStart F l ≤ c.val ∧ c.val < factorStart F l + factorSize F l then
    some ⟨c.val - factorStart F l, by omega⟩
  else none

theorem locOf_colG (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    locOf F l (colG F l j) = some j := by
  unfold locOf
  rw [dif_pos (by rw [colG_val]; omega)]
  congr 1
  apply Fin.ext
  simp [colG_val]

theorem eq_colG_of_locOf {l : Fin (N + B)} {c : Fin (prodSize F)} {j : Fin (factorSize F l)}
    (h : locOf F l c = some j) : c = colG F l j := by
  unfold locOf at h
  split_ifs at h with h1
  simp only [Option.some.injEq] at h
  apply Fin.ext
  rw [colG_val, ← h]
  simp only
  omega

/-- The local matching of the factor `l`: the matching of the factor word, on columns. -/
def localMatch (l : Fin (N + B)) : Equiv.Perm (Fin (factorSize F l)) :=
  finProdFinEquiv.permCongr (sM (F.factor l))

theorem localMatch_apply (l : Fin (N + B)) (p : Fin (F.factor l).length × Fin 3) :
    localMatch F l (finProdFinEquiv p) = finProdFinEquiv (sM (F.factor l) p) := by
  simp [localMatch, Equiv.permCongr_apply]

/-- The last local column of the factor `l`, which carries its closing rank-`0` arc. -/
def lastLocal (l : Fin (N + B)) : Fin (factorSize F l) :=
  ⟨factorSize F l - 1, by have := factorSize_pos F hS l; omega⟩

/-- The rank `0`. -/
abbrev rank0 : Fin S := ⟨0, by omega⟩

theorem fpe_llC_zero (l : Fin (N + B)) :
    finProdFinEquiv (llC F.factor (SignedGrid.NormalizedFactorization.factor_isPadded F) hS l
      (rank0 hS)) = lastLocal F hS l := by
  apply Fin.ext
  rw [finProdFinEquiv_val3]
  have := (SignedGrid.NormalizedFactorization.factor_isPadded F l).length_ge
  simp [llC, lastLocal, factorSize]
  omega

theorem colG_lastLocal (l : Fin (N + B)) :
    colG F l (lastLocal F hS l) = colZ F hS l (rank0 hS) := by
  rw [colG, ← fpe_llC_zero F hS l, Equiv.symm_apply_apply, globC_llC _ _ hS]
  rfl

theorem localMatch_lastLocal (l : Fin (N + B)) :
    localMatch F l (lastLocal F hS l) = ⟨0, factorSize_pos F hS l⟩ := by
  rw [← fpe_llC_zero F hS l, localMatch_apply, sM_llC _ _ hS]
  apply Fin.ext
  rw [finProdFinEquiv_val3]
  simp [lfC]

variable {F hS}

/-- **The component permutation on a factor.** On every column of the factor `l` except its last
one, the component permutation of a scissor endpoint is the local matching of the factor. -/
theorem mu_colG {μ : Equiv.Perm (Fin (prodSize F))} (hμ : IsScissorEndpointPerm F hS μ)
    (l : Fin (N + B)) (j : Fin (factorSize F l)) (hj : j ≠ lastLocal F hS l) :
    μ (colG F l j) = colG F l (localMatch F l j) := by
  set hq := SignedGrid.NormalizedFactorization.factor_isPadded F
  set p := finProdFinEquiv.symm j with hp
  have hj' : j = finProdFinEquiv p := by rw [hp, Equiv.apply_symm_apply]
  by_cases hll : ∃ x : Fin S, p = llC F.factor hq hS l x
  · obtain ⟨x, hx⟩ := hll
    have hx0 : x ≠ rank0 hS := by
      rintro rfl
      apply hj
      rw [hj', hx, fpe_llC_zero]
    have hx1 : 1 ≤ x.val := by
      have : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
      omega
    have hc : colG F l j = colZ F hS l x := by
      rw [colG, ← hp, hx, globC_llC _ _ hS]; rfl
    rw [hc, hμ.1 l x hx1, hj', localMatch_apply, hx, sM_llC _ _ hS, colG,
      Equiv.symm_apply_apply, globC_lfC _ _ hS]
    rfl
  · push Not at hll
    have hne : ∀ (l' : Fin (N + B)) (x : Fin S), 1 ≤ x.val → colG F l j ≠ colZ F hS l' x := by
      intro l' x _ h
      rw [colG, colZ, ← hp, ← globC_llC _ _ hS] at h
      have h1 := finProdFinEquiv.injective h
      have hl : l = l' := by
        have := congrArg (fun t => segOf F.factor t.1) h1
        simpa only [segOf_globC] using this
      subst hl
      exact hll x (globC_injective _ l h1)
    rw [hμ.2 _ hne, colG, ← hp, prodPerm_apply, sM_globC_of_ne _ _ hS l p hll, hj',
      localMatch_apply, colG, Equiv.symm_apply_apply]

/-! ### The local grid of a factor -/

variable (F hS)

/-- The rows of the local grid of the factor `l`: the closing row first, then the other rows of
the factor in the order of `ℓ`. -/
def localRows (ℓ : List (Fin (prodSize F))) (l : Fin (N + B)) : List (Fin (factorSize F l)) :=
  lastLocal F hS l :: ℓ.filterMap fun c => if c = colZ F hS l (rank0 hS) then none else locOf F l c

variable {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)

include hnd in
theorem nodup_localRows (l : Fin (N + B)) : (localRows F hS ℓ l).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hm
    obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hm
    split_ifs at hc with h1
    rw [eq_colG_of_locOf F hc, colG_lastLocal F hS] at h1
    exact h1 rfl
  · refine hnd.filterMap fun c c' j hj hj' => ?_
    rw [Option.mem_def] at hj hj'
    by_cases h1 : c = colZ F hS l (rank0 hS)
    · rw [if_pos h1] at hj; exact absurd hj (by simp)
    · by_cases h2 : c' = colZ F hS l (rank0 hS)
      · rw [if_pos h2] at hj'; exact absurd hj' (by simp)
      · rw [if_neg h1] at hj
        rw [if_neg h2] at hj'
        rw [eq_colG_of_locOf F hj, eq_colG_of_locOf F hj']

include hnd hl in
theorem mem_localRows (l : Fin (N + B)) (j : Fin (factorSize F l)) : j ∈ localRows F hS ℓ l := by
  by_cases hj : j = lastLocal F hS l
  · rw [hj]; exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨colG F l j, ?_, ?_⟩)
    · exact mem_of_listPerm ℓ hnd hl _
    · rw [if_neg, locOf_colG]
      rw [← colG_lastLocal F hS]
      exact fun h => hj (colG_injective F l h)

include hnd hl in
theorem length_localRows (l : Fin (N + B)) : (localRows F hS ℓ l).length = factorSize F l := by
  have hp : (localRows F hS ℓ l).Perm (List.finRange (factorSize F l)) :=
    (List.perm_ext_iff_of_nodup (nodup_localRows F hS hnd l) (List.nodup_finRange _)).mpr
      fun j => by simp [mem_localRows F hS hnd hl l j]
  rw [hp.length_eq, List.length_finRange]

/-- The height of a local column. -/
def localHeight (l : Fin (N + B)) (j : Fin (factorSize F l)) : ℕ :=
  (F.factor l).oHeight2 (finProdFinEquiv.symm j)

theorem colHeight_colG (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    colHeight F (colG F l j) = localHeight F l j := by
  rw [colG, colHeight_col, oHeight2_globC]
  rfl

theorem localHeight_lastLocal (l : Fin (N + B)) : localHeight F l (lastLocal F hS l) = 0 := by
  rw [← colHeight_colG, colG_lastLocal F hS, colHeight_colZ]
  rfl

include hS in
theorem sorted_localRows (hsort : ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b))
    (l : Fin (N + B)) :
    (localRows F hS ℓ l).Pairwise (fun a b => localHeight F l a ≤ localHeight F l b) := by
  refine List.pairwise_cons.mpr ⟨fun j _ => ?_, ?_⟩
  · rw [localHeight_lastLocal F hS]; exact Nat.zero_le _
  · refine hsort.filterMap _ fun c c' hcc' j hj j' hj' => ?_
    by_cases h1 : c = colZ F hS l (rank0 hS)
    · rw [if_pos h1] at hj; exact absurd hj (by simp)
    · by_cases h2 : c' = colZ F hS l (rank0 hS)
      · rw [if_pos h2] at hj'; exact absurd hj' (by simp)
      · rw [if_neg h1] at hj
        rw [if_neg h2] at hj'
        rw [eq_colG_of_locOf F hj, eq_colG_of_locOf F hj', colHeight_colG,
          colHeight_colG] at hcc'
        exact hcc'

/-- **The local grid of a factor.** -/
def localGrid (l : Fin (N + B)) :
    LabeledGrid (factorSize F l) (Fin (factorSize F l)) (Fin (factorSize F l)) where
  cols := List.finRange _
  rows := localRows F hS ℓ l
  O := id
  X := (localMatch F l).symm
  cols_length := List.length_finRange
  rows_length := length_localRows F hS hnd hl l
  cols_nodup := List.nodup_finRange _
  rows_nodup := nodup_localRows F hS hnd l
  O_mem c _ := mem_localRows F hS hnd hl l c
  X_mem c _ := mem_localRows F hS hnd hl l _
  O_inj _ _ _ _ h := h
  X_inj _ _ _ _ h := (localMatch F l).symm.injective h
  O_ne_X c _ := by
    intro h
    have h' : localMatch F l c = c := by
      conv_lhs => rw [show c = (localMatch F l).symm c from h]
      exact Equiv.apply_symm_apply _ _
    obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective c
    rw [localMatch_apply] at h'
    have := sM_height (F.factor l) p
    rw [finProdFinEquiv.injective h'] at this
    exact oHeight2_ne_xHeight2 _ p this.symm

theorem localGrid_O_val (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    ((localGrid F hS hnd hl l).toGrid.O j).val = (localRows F hS ℓ l).idxOf j := by
  rw [LabeledGrid.toGrid_O_val]
  simp [localGrid, LabeledGrid.colAt, LabeledGrid.rpos]

theorem localGrid_X_val (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    ((localGrid F hS hnd hl l).toGrid.X j).val =
      (localRows F hS ℓ l).idxOf ((localMatch F l).symm j) := by
  rw [LabeledGrid.toGrid_X_val]
  simp [localGrid, LabeledGrid.colAt, LabeledGrid.rpos]

include hS in
/-- **The local grid is a signed word grid of the factor word.** -/
theorem isSignedWordGrid_localGrid (hsort : ℓ.Pairwise (fun a b => colHeight F a ≤ colHeight F b))
    (l : Fin (N + B)) : IsSignedWordGrid (F.factor l) (localGrid F hS hnd hl l).toGrid := by
  rw [isSignedWordGrid_iff]
  refine ⟨fun p p' hpp' => ?_, fun q' => ?_⟩
  · rw [Fin.lt_def, localGrid_O_val, localGrid_O_val]
    apply idxOf_lt_of_key_lt (sorted_localRows F hS hsort l) (mem_localRows F hS hnd hl l _)
      (mem_localRows F hS hnd hl l _)
    unfold localHeight
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hpp'
  · apply Fin.ext
    have e : (localMatch F l).symm (finProdFinEquiv q') =
        finProdFinEquiv ((sM (F.factor l)).symm q') := by
      rw [Equiv.symm_apply_eq, localMatch_apply, Equiv.apply_symm_apply]
    rw [localGrid_X_val, localGrid_O_val, e]

/-- **The closing row of the local grid is its bottom row.** -/
theorem closingRowBottom_localGrid (l : Fin (N + B)) :
    ClosingRowBottom (localGrid F hS hnd hl l).toGrid := by
  refine ⟨factorSize_pos F hS l, ?_, ?_⟩
  · apply Fin.ext
    rw [localGrid_O_val]
    change (localRows F hS ℓ l).idxOf (lastLocal F hS l) = 0
    simp [localRows]
  · apply Fin.ext
    rw [localGrid_X_val]
    have h : (localMatch F l).symm ⟨0, factorSize_pos F hS l⟩ = lastLocal F hS l := by
      rw [Equiv.symm_apply_eq, localMatch_lastLocal F hS]
    rw [h]
    simp [localRows]

end OnLeConjecture.KnotFloer.GridFull
