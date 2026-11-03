/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEndpointCleanupRaw

/-!
# The block row order of a scissor endpoint

For a row order `ℓ` of a scissor endpoint grid, sorted by height, the *block row order*
(`endRows`) lists the rows factor by factor: for each factor `l`, the rows of the factor in the
order of `ℓ`, except that the connecting rank-`0` row leaving the factor is the last one. This is
the row order of the cyclic block grid of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 10, "The raw scissor endpoint is already this cyclic
grid"). The position of the row of a column `colG F l j` in the block row order is
`factorStart F l + blockPos F hS ℓ l j` (`idxOf_endRows`), where `blockPos` is the position in
the local grid rotated by one row (`blockPos_eq`). All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti OnLeConjecture.KnotTheory OnLeConjecture.KnotTheory.SignedGrid
  OnLeConjecture.KnotTheory.NormalizedFactorization

/-! ### Positions in lists -/

section Lists

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Positions in the image of a list under an injective map. -/
theorem idxOf_map_of_injective {f : α → β} (hf : Function.Injective f) (l : List α) (a : α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases h : b = a
    · subst h; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun e => h (hf e)), List.idxOf_cons_ne _ h, ih]

/-- Positions in a flattened family of lists. -/
theorem idxOf_flatten_ofFn {r : ℕ} (f : Fin r → List α) (l : Fin r) {x : α} (hx : x ∈ f l)
    (hdisj : ∀ i, i ≠ l → x ∉ f i) :
    (List.ofFn f).flatten.idxOf x =
      ((List.ofFn fun i => (f i).length).take l.val).sum + (f l).idxOf x := by
  induction r with
  | zero => exact l.elim0
  | succ r ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ]
    by_cases hl : l = 0
    · subst hl
      rw [List.idxOf_append_of_mem hx]
      simp
    · obtain ⟨l', rfl⟩ := Fin.exists_succ_eq.mpr hl
      have hx0 : x ∉ f 0 := hdisj 0 (Ne.symm hl)
      rw [List.idxOf_append_of_notMem hx0,
        ih (fun i => f i.succ) l' hx
          (fun i hi => hdisj i.succ (fun e => hi (Fin.succ_injective _ e)))]
      simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons]
      omega

/-- Positions in a filtered list are in the order of the positions in the list. -/
theorem idxOf_filterMap_lt {f : α → Option β} {l : List α} (hnd : l.Nodup)
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') {a a' : α} {b b' : β}
    (ha : a ∈ l) (ha' : a' ∈ l) (hb : f a = some b) (hb' : f a' = some b')
    (h : l.idxOf a < l.idxOf a') : (l.filterMap f).idxOf b < (l.filterMap f).idxOf b' := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    have hc := (List.nodup_cons.mp hnd)
    by_cases hca : c = a
    · subst hca
      have hca' : c ≠ a' := fun e => by subst e; simp at h
      have ha'l : a' ∈ l := by
        rcases List.mem_cons.mp ha' with e | e
        · exact absurd e.symm hca'
        · exact e
      have hbb' : b ≠ b' := fun e => hca' (hf c a' b hb (e ▸ hb'))
      rw [List.filterMap_cons_some hb, List.idxOf_cons_self, List.idxOf_cons_ne _ hbb']
      omega
    · have hal : a ∈ l := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e.symm hca
        · exact e
      have hca' : c ≠ a' := fun e => by
        subst e
        rw [List.idxOf_cons_self] at h
        omega
      have ha'l : a' ∈ l := by
        rcases List.mem_cons.mp ha' with e | e
        · exact absurd e.symm hca'
        · exact e
      have h' : l.idxOf a < l.idxOf a' := by
        rw [List.idxOf_cons_ne _ hca, List.idxOf_cons_ne _ hca'] at h
        omega
      have ih' := ih hc.2 hal ha'l h'
      rcases hfc : f c with _ | d
      · rw [List.filterMap_cons_none hfc]; exact ih'
      · rw [List.filterMap_cons_some hfc]
        have hdb : d ≠ b := fun e => hca (hf c a b (by rw [hfc, e]) hb)
        have hdb' : d ≠ b' := fun e => hca' (hf c a' b' (by rw [hfc, e]) hb')
        rw [List.idxOf_cons_ne _ hdb, List.idxOf_cons_ne _ hdb']
        omega

end Lists

variable {S N B : ℕ} (F : NormalizedFactorization S N B) (hS : 2 ≤ S)

/-! ### Blocks of columns -/

/-- Every column of the product is a column of exactly one factor. -/
theorem exists_colG (c : Fin (prodSize F)) : ∃ (l : Fin (N + B)) (j : Fin (factorSize F l)),
    colG F l j = c := by
  obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective c
  obtain ⟨l, p', rfl⟩ := exists_globC F.factor p
  exact ⟨l, finProdFinEquiv p', by rw [colG, Equiv.symm_apply_apply]⟩

theorem colG_eq_colG {l l' : Fin (N + B)} {j : Fin (factorSize F l)} {j' : Fin (factorSize F l')}
    (h : colG F l j = colG F l' j') : l = l' := by
  have := congrArg (fun c => segOf F.factor (finProdFinEquiv.symm c).1) h
  simpa only [colG, col, Equiv.symm_apply_apply, segOf_globC] using this

theorem factorStart_eq_sum (l : Fin (N + B)) :
    factorStart F l = ((List.ofFn fun i => factorSize F i).take l.val).sum := by
  have e : (List.ofFn fun i => factorSize F i) =
      (List.ofFn F.factor).map (fun w => w.length * 3) := by
    rw [List.map_ofFn]; rfl
  rw [e, ← List.map_take, List.sum_map_mul_right]
  simp only [factorStart, factorOffset]
  ring

/-! ### The block row order -/

variable {ℓ : List (Fin (prodSize F))} (hnd : ℓ.Nodup) (hl : ℓ.length = prodSize F)

/-- The local rows of the factor `l` rotated by one: the closing row last. -/
def rotRows (l : Fin (N + B)) : List (Fin (factorSize F l)) :=
  (localRows F hS ℓ l).tail ++ [lastLocal F hS l]

/-- The rows of the factor `l` in the block row order. -/
def blockRows (l : Fin (N + B)) : List (Fin (prodSize F)) :=
  (rotRows F hS (ℓ := ℓ) l).map (colG F l)

/-- **The block row order.** -/
def endRows : List (Fin (prodSize F)) := (List.ofFn fun l => blockRows F hS (ℓ := ℓ) l).flatten

/-- The position of a local column in the rotated local rows. -/
def blockPos (l : Fin (N + B)) (j : Fin (factorSize F l)) : ℕ := (rotRows F hS (ℓ := ℓ) l).idxOf j

include hnd in
theorem notMem_tail_localRows (l : Fin (N + B)) :
    lastLocal F hS l ∉ (localRows F hS ℓ l).tail :=
  (List.nodup_cons.mp (nodup_localRows F hS hnd l)).1

include hnd hl in
theorem length_rotRows (l : Fin (N + B)) : (rotRows F hS (ℓ := ℓ) l).length = factorSize F l := by
  have := length_localRows F hS hnd hl l
  simp only [rotRows, List.length_append, List.length_tail, List.length_singleton]
  have := factorSize_pos F hS l
  omega

include hnd hl in
theorem mem_rotRows (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    j ∈ rotRows F hS (ℓ := ℓ) l := by
  by_cases hj : j = lastLocal F hS l
  · simp [rotRows, hj]
  · have := mem_localRows F hS hnd hl l j
    simp only [localRows, List.mem_cons, hj, false_or] at this
    simp [rotRows, localRows, this]

include hnd in
theorem nodup_rotRows (l : Fin (N + B)) : (rotRows F hS (ℓ := ℓ) l).Nodup := by
  have h := nodup_localRows F hS hnd l
  simp only [localRows, List.nodup_cons] at h
  rw [rotRows, List.nodup_append]
  refine ⟨h.2, by simp, ?_⟩
  intro a ha b hb e
  simp only [List.mem_singleton] at hb
  subst hb e
  exact h.1 ha

include hnd hl in
/-- The position of the closing row in the rotated local rows. -/
theorem blockPos_lastLocal (l : Fin (N + B)) :
    blockPos F hS (ℓ := ℓ) l (lastLocal F hS l) + 1 = factorSize F l := by
  have := length_localRows F hS hnd hl l
  have h1 := notMem_tail_localRows F hS hnd l
  simp only [blockPos, rotRows]
  rw [List.idxOf_append_of_notMem h1]
  simp only [List.idxOf_cons_self, List.length_tail]
  have := factorSize_pos F hS l
  omega

include hnd hl in
/-- The position of any other row in the rotated local rows. -/
theorem blockPos_of_ne (l : Fin (N + B)) {j : Fin (factorSize F l)} (hj : j ≠ lastLocal F hS l) :
    blockPos F hS (ℓ := ℓ) l j + 1 = (localRows F hS ℓ l).idxOf j := by
  have hm : j ∈ (localRows F hS ℓ l).tail := by
    have := mem_localRows F hS hnd hl l j
    simp only [localRows, List.mem_cons, hj, false_or] at this
    simpa [localRows] using this
  simp only [blockPos, rotRows]
  rw [List.idxOf_append_of_mem hm]
  simp only [localRows, List.tail_cons, List.idxOf_cons_ne _ (Ne.symm hj)]

include hnd hl in
theorem blockPos_lt (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    blockPos F hS (ℓ := ℓ) l j < factorSize F l := by
  rw [← length_rotRows F hS hnd hl l]
  exact List.idxOf_lt_length_iff.mpr (mem_rotRows F hS hnd hl l j)

theorem mem_blockRows_iff (l l' : Fin (N + B)) (j : Fin (factorSize F l')) :
    colG F l' j ∈ blockRows F hS (ℓ := ℓ) l → l' = l := by
  intro h
  obtain ⟨j', _, e⟩ := List.mem_map.mp h
  exact (colG_eq_colG F e).symm

include hnd hl in
/-- **Positions in the block row order.** -/
theorem idxOf_endRows (l : Fin (N + B)) (j : Fin (factorSize F l)) :
    (endRows F hS (ℓ := ℓ)).idxOf (colG F l j) = factorStart F l + blockPos F hS (ℓ := ℓ) l j := by
  have hx : colG F l j ∈ blockRows F hS (ℓ := ℓ) l :=
    List.mem_map.mpr ⟨j, mem_rotRows F hS hnd hl l j, rfl⟩
  rw [endRows, idxOf_flatten_ofFn _ l hx (fun i hi h => hi (mem_blockRows_iff F hS i l j h).symm)]
  congr 1
  · rw [factorStart_eq_sum]
    congr 2
    exact List.ofFn_inj.mpr (funext fun i => by
      rw [blockRows, List.length_map, length_rotRows F hS hnd hl])
  · rw [blockRows, idxOf_map_of_injective (colG_injective F l)]
    rfl

include hnd in
theorem nodup_endRows : (endRows F hS (ℓ := ℓ)).Nodup := by
  rw [endRows, List.nodup_flatten]
  refine ⟨fun L hL => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hL
    exact (nodup_rotRows F hS hnd l).map (colG_injective F l)
  · rw [List.pairwise_ofFn]
    intro i i' hii' c hc hc'
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    exact absurd (mem_blockRows_iff F hS i' i j hc') (ne_of_lt hii')

include hnd hl in
theorem mem_endRows (c : Fin (prodSize F)) : c ∈ endRows F hS (ℓ := ℓ) := by
  obtain ⟨l, j, rfl⟩ := exists_colG F c
  exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨l, rfl⟩,
    List.mem_map.mpr ⟨j, mem_rotRows F hS hnd hl l j, rfl⟩⟩

include hnd hl in
theorem perm_endRows : (endRows F hS (ℓ := ℓ)).Perm ℓ :=
  (List.perm_ext_iff_of_nodup (nodup_endRows F hS hnd) hnd).mpr fun c =>
    ⟨fun _ => mem_of_listPerm ℓ hnd hl c, fun _ => mem_endRows F hS hnd hl c⟩

end OnLeConjecture.KnotFloer.GridFull
