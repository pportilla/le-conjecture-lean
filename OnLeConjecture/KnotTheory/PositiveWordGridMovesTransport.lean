/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros
public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissibleDeletion

/-! # Rotations and far commutations of word grids

Let `w, w'` be positive words of the same length and `τ` a bijection of their letter positions
with `w'[τ h] = w[h]`. If `τ` carries the cyclic successor of every occurrence of every rank in
`w` to the cyclic successor in `w'`, then the horizontal matchings correspond
(`positiveRectilinearWordMatching_transport`), and the grid obtained from an admissible grid of
`w` by renaming the columns along `τ` is an admissible grid of `w'`
(`IsAdmissibleWordGrid.transport`).

Two cases are used.

* A rotation `u i ↦ i u` renames the columns by three cyclic permutations of columns
  (`wordGrid_movesTo_rotate`).
* A far commutation `u i j v ↦ u j i v` with `|i - j| ≥ 2` exchanges the three columns of
  the two letters by nine column commutations; the rows of the two letters have separated
  heights (`wordGrid_movesTo_far`).

This is the part of record M413 concerning rotations and far commutations. The written proof is
Section 4 of `docs/route-n/J09-word-grid-moves.tex`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-! ### The trivially labeled grid of a grid diagram -/

namespace LabeledGrid

/-- A grid diagram viewed as a labeled grid whose labels are the positions themselves. -/
def ofGrid {n : ℕ} (G : GridDiagram n) : LabeledGrid n (Fin n) (Fin n) where
  cols := List.finRange n
  rows := List.finRange n
  O := G.O
  X := G.X
  cols_length := List.length_finRange
  rows_length := List.length_finRange
  cols_nodup := List.nodup_finRange n
  rows_nodup := List.nodup_finRange n
  O_mem _ _ := List.mem_finRange _
  X_mem _ _ := List.mem_finRange _
  O_inj _ _ _ _ h := G.O.toPerm.injective h
  X_inj _ _ _ _ h := G.X.toPerm.injective h
  O_ne_X c _ := G.disjoint c

theorem ofGrid_colAt {n : ℕ} (G : GridDiagram n) (i : Fin n) : (ofGrid G).colAt i = i := by
  simp [colAt, ofGrid]

theorem ofGrid_rpos {n : ℕ} (G : GridDiagram n) (r : Fin n) : (ofGrid G).rpos r = r.val :=
  List.idxOf_finRange r

theorem ofGrid_cpos {n : ℕ} (G : GridDiagram n) (c : Fin n) : (ofGrid G).cpos c = c.val :=
  List.idxOf_finRange c

theorem toGrid_ofGrid {n : ℕ} (G : GridDiagram n) : (ofGrid G).toGrid = G := by
  ext i
  · rw [toGrid_O_val, ofGrid_colAt, ofGrid_rpos]; rfl
  · rw [toGrid_X_val, ofGrid_colAt, ofGrid_rpos]; rfl

end LabeledGrid

/-! ### Transport of admissible grids -/

section Transport

variable {m : ℕ} {w w' : PositiveAdjacentWord m}

/-- The occurrence of a rank in `w'` corresponding to an occurrence in `w`. -/
def occTransport (τ : Fin w.length ≃ Fin w'.length) (hlet : ∀ h, w'[(τ h).val] = w[h.val])
    {r : Fin m} (j : PositiveRectilinearRowOccurrences w r) :
    PositiveRectilinearRowOccurrences w' r :=
  ⟨τ j.val, by rw [hlet]; exact j.property⟩

/-- If the letter bijection carries cyclic successors of occurrences to cyclic successors, the
horizontal matchings correspond. -/
theorem positiveRectilinearWordMatching_transport (τ : Fin w.length ≃ Fin w'.length)
    (hlet : ∀ h, w'[(τ h).val] = w[h.val])
    (hsucc : ∀ (r : Fin m) (j : PositiveRectilinearRowOccurrences w r),
      positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w' r)
          (occTransport τ hlet j) =
        occTransport τ hlet (positiveRectilinearSortedSuccessor _ j))
    (p : Fin w.length × Fin 3) :
    positiveRectilinearWordMatching w' (τ p.1, p.2) =
      ((τ (positiveRectilinearWordMatching w p).1), (positiveRectilinearWordMatching w p).2) := by
  obtain ⟨a, rfl⟩ := (positiveRectilinearOutgoingArc w).symm.surjective p
  rcases a with h | ⟨r, j⟩
  · change positiveRectilinearWordMatching w' (τ h, 0) =
      (τ (positiveRectilinearWordMatching w (h, 0)).1, (positiveRectilinearWordMatching w (h, 0)).2)
    rw [positiveRectilinearWordMatching_middle, positiveRectilinearWordMatching_middle]
  · have hout : ((τ ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, j⟩)).1),
        ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, j⟩)).2) =
        (positiveRectilinearOutgoingArc w').symm (Sum.inr ⟨r, occTransport τ hlet j⟩) := by
      rw [positiveRectilinearOutgoingArc_symm_inr, positiveRectilinearOutgoingArc_symm_inr]
      simp only [occTransport, hlet]
    rw [hout, positiveRectilinearWordMatching_outgoingArc_symm_inr,
      positiveRectilinearWordMatching_outgoingArc_symm_inr, hsucc,
      positiveRectilinearIncomingArc_symm_inr, positiveRectilinearIncomingArc_symm_inr]
    simp only [occTransport, hlet]

/-- Transport a grid of `w` to a grid of `w'` along a bijection of letter positions: the column
of the corner `(h, c)` of `w` becomes the column of the corner `(τ h, c)` of `w'`. -/
def transportGrid (hL : w.length = w'.length) (τ : Fin w.length ≃ Fin w'.length)
    (G : GridDiagram (w.length * 3)) : GridDiagram (w'.length * 3) :=
  let σ : Fin w.length × Fin 3 ≃ Fin w'.length × Fin 3 := τ.prodCongr (Equiv.refl _)
  let κ : Fin (w'.length * 3) ≃ Fin (w.length * 3) :=
    finProdFinEquiv.symm.trans (σ.symm.trans finProdFinEquiv)
  have hL3 : w.length * 3 = w'.length * 3 := by rw [hL]
  { O := ⟨κ.trans (G.O.toPerm.trans (finCongr hL3))⟩
    X := ⟨κ.trans (G.X.toPerm.trans (finCongr hL3))⟩
    disjoint := fun c h => G.disjoint (κ c) ((finCongr hL3).injective h) }

theorem transportGrid_O (hL : w.length = w'.length) (τ : Fin w.length ≃ Fin w'.length)
    (G : GridDiagram (w.length * 3)) (p : Fin w.length × Fin 3) :
    ((transportGrid hL τ G).O (finProdFinEquiv (τ p.1, p.2))).val =
      (G.O (finProdFinEquiv p)).val := by
  simp [transportGrid]

theorem transportGrid_X (hL : w.length = w'.length) (τ : Fin w.length ≃ Fin w'.length)
    (G : GridDiagram (w.length * 3)) (p : Fin w.length × Fin 3) :
    ((transportGrid hL τ G).X (finProdFinEquiv (τ p.1, p.2))).val =
      (G.X (finProdFinEquiv p)).val := by
  simp [transportGrid]

/-- **Transport of admissibility.** -/
theorem IsAdmissibleWordGrid.transport (hL : w.length = w'.length)
    (τ : Fin w.length ≃ Fin w'.length) (hlet : ∀ h, w'[(τ h).val] = w[h.val])
    (hsucc : ∀ (r : Fin m) (j : PositiveRectilinearRowOccurrences w r),
      positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w' r)
          (occTransport τ hlet j) =
        occTransport τ hlet (positiveRectilinearSortedSuccessor _ j))
    {G : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G) :
    IsAdmissibleWordGrid w' (transportGrid hL τ G) := by
  have hsurj : ∀ a' : Fin w'.length × Fin 3, ∃ p : Fin w.length × Fin 3, (τ p.1, p.2) = a' :=
    fun a' => ⟨(τ.symm a'.1, a'.2), by simp⟩
  have hrow : ∀ p : Fin w.length × Fin 3,
      positiveRectilinearWordArcRow w' (τ p.1, p.2) = positiveRectilinearWordArcRow w p := by
    intro p
    rw [positiveRectilinearWordArcRow_eq, positiveRectilinearWordArcRow_eq]
    simp only [hlet]
  have hM := positiveRectilinearWordMatching_transport τ hlet hsucc
  have hMs : ∀ p : Fin w.length × Fin 3,
      (positiveRectilinearWordMatching w').symm (τ p.1, p.2) =
        (τ ((positiveRectilinearWordMatching w).symm p).1,
          ((positiveRectilinearWordMatching w).symm p).2) := by
    intro p
    rw [Equiv.symm_apply_eq, hM, Equiv.apply_symm_apply]
  constructor
  · intro a'
    obtain ⟨p, rfl⟩ := hsurj a'
    apply Fin.ext
    rw [transportGrid_X, hMs, transportGrid_O, hG.X_eq]
  · intro a' b' hab
    obtain ⟨p, rfl⟩ := hsurj a'
    obtain ⟨q, rfl⟩ := hsurj b'
    rw [hrow, hrow] at hab
    have := hG.O_lt_of_arcRow_lt p q hab
    rw [Fin.lt_def, transportGrid_O, transportGrid_O]
    exact this

end Transport


/-! ### Cyclic rotation of columns -/

theorem finRotate_val_eq {N : ℕ} (x : Fin N) :
    (finRotate N x).val = if x.val + 1 < N then x.val + 1 else 0 := by
  split_ifs with h
  · exact GridMoves.finRotate_val_of_lt x h
  · cases N with
    | zero => exact x.elim0
    | succ n =>
      have : x = Fin.last n := Fin.ext (by simp; omega)
      rw [this, finRotate_last]; rfl

theorem finRotate_pow_three_val {N : ℕ} (x : Fin N) (hN : 3 ≤ N) :
    ((finRotate N ^ 3) x).val = if x.val + 3 < N then x.val + 3 else x.val + 3 - N := by
  have hx := x.isLt
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
  rw [finRotate_val_eq, finRotate_val_eq, finRotate_val_eq]
  split_ifs <;> omega

section Rotation

variable {m : ℕ} (u : PositiveAdjacentWord m) (i : Fin (m - 1))

theorem rotate_length : (u ++ [i]).length = (i :: u).length := by simp

/-- The letter bijection of a rotation `u i ↦ i u`. -/
def rotateLetters : Fin (u ++ [i]).length ≃ Fin (i :: u).length :=
  (finCongr (rotate_length u i)).trans (finRotate _)

theorem rotateLetters_val (h : Fin (u ++ [i]).length) :
    (rotateLetters u i h).val = if h.val = u.length then 0 else h.val + 1 := by
  have hh := h.isLt
  simp only [List.length_append, List.length_singleton] at hh
  rw [rotateLetters, Equiv.trans_apply, finRotate_val_eq]
  simp only [finCongr_apply, Fin.val_cast, List.length_cons]
  split_ifs <;> omega

theorem rotateLetters_getElem (h : Fin (u ++ [i]).length) :
    (i :: u)[(rotateLetters u i h).val] = (u ++ [i])[h.val] := by
  have hh := h.isLt
  simp only [List.length_append, List.length_singleton] at hh
  have hv := rotateLetters_val u i h
  by_cases h1 : h.val = u.length
  · simp only [h1, if_true] at hv
    simp only [hv, List.getElem_cons_zero]
    rw [List.getElem_append_right (by omega)]
    simp [h1]
  · simp only [h1, if_false] at hv
    simp only [hv, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega)]

theorem rotateLetters_succ (r : Fin m) (j : PositiveRectilinearRowOccurrences (u ++ [i]) r) :
    positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences (i :: u) r)
        (occTransport (rotateLetters u i) (rotateLetters_getElem u i) j) =
      occTransport (rotateLetters u i) (rotateLetters_getElem u i)
        (positiveRectilinearSortedSuccessor _ j) := by
  set τ := rotateLetters u i
  set T := occTransport τ (rotateLetters_getElem u i) (r := r)
  have hval : ∀ b : PositiveRectilinearRowOccurrences (u ++ [i]) r,
      (T b).val.val = if b.val.val = u.length then 0 else b.val.val + 1 :=
    fun b => rotateLetters_val u i b.val
  have hsurj : ∀ b' : PositiveRectilinearRowOccurrences (i :: u) r, ∃ b, T b = b' := by
    intro b'
    have hletter : (u ++ [i])[(τ.symm b'.val).val] = (i :: u)[b'.val.val] := by
      have := rotateLetters_getElem u i (τ.symm b'.val)
      simp only [τ, Equiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨⟨τ.symm b'.val, by rw [hletter]; exact b'.property⟩, ?_⟩
    apply Subtype.ext
    simp [T, occTransport, τ]
  have hlen : ∀ b : PositiveRectilinearRowOccurrences (u ++ [i]) r, b.val.val ≤ u.length := by
    intro b; have := b.val.isLt; simp at this; omega
  obtain ⟨q, hqdef⟩ : ∃ q, positiveRectilinearSortedSuccessor
      (PositiveRectilinearRowOccurrences (u ++ [i]) r) j = q := ⟨_, rfl⟩
  rw [hqdef]
  apply positiveRectilinearSortedSuccessor_eq_of_spec
  have hlt : ∀ x y : PositiveRectilinearRowOccurrences (i :: u) r, x < y ↔ x.val.val < y.val.val :=
    fun _ _ => Iff.rfl
  have hle : ∀ x y : PositiveRectilinearRowOccurrences (i :: u) r, x ≤ y ↔ x.val.val ≤ y.val.val :=
    fun _ _ => Iff.rfl
  have hlt0 : ∀ x y : PositiveRectilinearRowOccurrences (u ++ [i]) r,
      x < y ↔ x.val.val < y.val.val := fun _ _ => Iff.rfl
  have hle0 : ∀ x y : PositiveRectilinearRowOccurrences (u ++ [i]) r,
      x ≤ y ↔ x.val.val ≤ y.val.val := fun _ _ => Iff.rfl
  have hj := hlen j
  have hq := hlen q
  have hnext := positiveRectilinearSortedSuccessor_next
    (PositiveRectilinearRowOccurrences (u ++ [i]) r) j
  rw [hqdef] at hnext
  rcases hnext with ⟨hjq, hmin⟩ | ⟨hqj, hall⟩
  · rw [hlt0] at hjq
    by_cases hql : q.val.val = u.length
    · right
      refine ⟨by rw [hle, hval, hval]; split_ifs <;> omega, fun b' => ?_⟩
      obtain ⟨b, rfl⟩ := hsurj b'
      refine ⟨by rw [hle, hval, hval]; split_ifs <;> omega, ?_⟩
      rw [hle, hval, hval]
      have hb := hlen b
      by_cases hbj : j.val.val < b.val.val
      · have := hmin b ((hlt0 _ _).mpr hbj); rw [hle0] at this; split_ifs <;> omega
      · split_ifs <;> omega
    · left
      refine ⟨by rw [hlt, hval, hval]; split_ifs <;> omega, fun b' hb' => ?_⟩
      obtain ⟨b, rfl⟩ := hsurj b'
      rw [hlt, hval, hval] at hb'
      rw [hle, hval, hval]
      have hb := hlen b
      by_cases hbl : b.val.val = u.length
      · split_ifs at hb' ⊢ <;> omega
      · have hjb : j.val.val < b.val.val := by split_ifs at hb' <;> omega
        have := hmin b ((hlt0 _ _).mpr hjb); rw [hle0] at this; split_ifs <;> omega
  · rw [hle0] at hqj
    by_cases hjl : j.val.val = u.length
    · by_cases hqe : q.val.val = u.length
      · right
        refine ⟨by rw [hle, hval, hval]; split_ifs <;> omega, fun b' => ?_⟩
        obtain ⟨b, rfl⟩ := hsurj b'
        have h1 := (hall b).1; have h2 := (hall b).2
        rw [hle0] at h1 h2
        rw [hle, hle, hval, hval, hval]
        constructor <;> split_ifs <;> omega
      · left
        refine ⟨by rw [hlt, hval, hval]; split_ifs <;> omega, fun b' hb' => ?_⟩
        obtain ⟨b, rfl⟩ := hsurj b'
        have h1 := (hall b).1; have h2 := (hall b).2
        rw [hle0] at h1 h2
        rw [hlt, hval, hval] at hb'
        rw [hle, hval, hval]
        split_ifs at hb' ⊢ <;> omega
    · right
      refine ⟨by rw [hle, hval, hval]; split_ifs <;> omega, fun b' => ?_⟩
      obtain ⟨b, rfl⟩ := hsurj b'
      have h1 := (hall b).1; have h2 := (hall b).2
      rw [hle0] at h1 h2
      rw [hle, hle, hval, hval, hval]
      constructor <;> split_ifs <;> omega

/-- **Rotation.** The selected grids of `u i` and `i u` are related by grid moves. -/
theorem wordGrid_movesTo_rotate : (wordGrid (u ++ [i])).MovesTo (wordGrid (i :: u)) := by
  have hL := rotate_length u i
  have hadm := IsAdmissibleWordGrid.transport hL (rotateLetters u i) (rotateLetters_getElem u i)
    (rotateLetters_succ u i) (wordGrid_isAdmissible (u ++ [i]))
  refine GridDiagram.MovesTo.trans ?_ hadm.movesTo_wordGrid
  have hN : 3 ≤ (u ++ [i]).length * 3 := by simp
  have hL3 : (u ++ [i]).length * 3 = (i :: u).length * 3 := by rw [hL]
  have heq : transportGrid hL (rotateLetters u i) (wordGrid (u ++ [i])) =
      GridDiagram.castSize hL3 ((wordGrid (u ++ [i])).relabelColumns (finRotate _ ^ 3)) := by
    have key : ∀ p : Fin (u ++ [i]).length × Fin 3,
        (finRotate _ ^ 3) (finProdFinEquiv p) =
          Fin.cast hL3.symm (finProdFinEquiv (rotateLetters u i p.1, p.2)) := by
      intro p
      apply Fin.ext
      have hv := rotateLetters_val u i p.1
      rw [finRotate_pow_three_val _ hN]
      simp only [Fin.val_cast, finProdFinEquiv_apply_val]
      have h1 := p.1.isLt; have h2 := p.2.isLt
      simp only [List.length_append, List.length_singleton] at h1 hN ⊢
      split_ifs at hv ⊢ <;> omega
    have hsurj : ∀ c : Fin ((i :: u).length * 3), ∃ p : Fin (u ++ [i]).length × Fin 3,
        finProdFinEquiv (rotateLetters u i p.1, p.2) = c := by
      intro c
      refine ⟨((rotateLetters u i).symm (finProdFinEquiv.symm c).1,
        (finProdFinEquiv.symm c).2), ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact finProdFinEquiv.apply_symm_apply c
    ext c
    · obtain ⟨p, rfl⟩ := hsurj c
      rw [transportGrid_O, GridDiagram.castSize_O_apply, Fin.val_cast,
        GridDiagram.relabelColumns_O_apply]
      congr 2
      rw [eq_comm, Equiv.symm_apply_eq, key]
    · obtain ⟨p, rfl⟩ := hsurj c
      rw [transportGrid_X, GridDiagram.castSize_X_apply, Fin.val_cast,
        GridDiagram.relabelColumns_X_apply]
      congr 2
      rw [eq_comm, Equiv.symm_apply_eq, key]
  rw [heq]
  exact (GridDiagram.movesTo_relabelColumns_finRotate_pow _ 3).trans
    (GridDiagram.movesTo_castSize hL3 _)

end Rotation


/-! ### Order isomorphisms of occurrences -/

/-- A bijection of occurrences preserving their order carries cyclic successors to cyclic
successors. -/
theorem sortedSuccessor_transport_of_strictMono {m : ℕ} {w w' : PositiveAdjacentWord m}
    {r : Fin m} (T : PositiveRectilinearRowOccurrences w r → PositiveRectilinearRowOccurrences w' r)
    (hT : ∀ b b', b < b' ↔ T b < T b') (hsurj : ∀ b', ∃ b, T b = b')
    (j : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearSortedSuccessor _ (T j) = T (positiveRectilinearSortedSuccessor _ j) := by
  have hle : ∀ b b', b ≤ b' ↔ T b ≤ T b' := fun b b' => by
    rw [← not_lt, ← not_lt, hT]
  apply positiveRectilinearSortedSuccessor_eq_of_spec
  rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r) j with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨(hT _ _).mp h1, fun b' hb' => ?_⟩
    obtain ⟨b, rfl⟩ := hsurj b'
    exact (hle _ _).mp (h2 b ((hT _ _).mpr hb'))
  · right
    refine ⟨(hle _ _).mp h1, fun b' => ?_⟩
    obtain ⟨b, rfl⟩ := hsurj b'
    exact ⟨(hle _ _).mp (h2 b).1, (hle _ _).mp (h2 b).2⟩

/-! ### Far commutation -/

/-- The heights of the two arcs at a corner lie between the two ranks of its letter. -/
theorem arcRow_bounds {m : ℕ} (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) :
    (w[p.1.val].val : ℝ) ≤ positiveRectilinearWordArcRow w p ∧
      positiveRectilinearWordArcRow w p ≤ (w[p.1.val].val : ℝ) + 1 ∧
      (w[p.1.val].val : ℝ) ≤ positiveRectilinearWordArcRow w
        ((positiveRectilinearWordMatching w).symm p) ∧
      positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm p) ≤
        (w[p.1.val].val : ℝ) + 1 := by
  obtain ⟨h, c⟩ := p
  rw [positiveRectilinearWordArcRow_eq, positiveRectilinearWordArcRow_matching_symm]
  fin_cases c <;> simp <;> norm_num


/-! ### Exchanging two blocks of three columns -/

/-- The position map of the exchange of the columns `p, p+1, p+2` with `p+3, p+4, p+5`. -/
def blockSwapVal (p k : ℕ) : ℕ :=
  if p ≤ k ∧ k < p + 3 then k + 3 else if p + 3 ≤ k ∧ k < p + 6 then k - 3 else k

/-- If every column of the first block has a segment that does not interleave the segment of any
column of the second block, the two blocks can be exchanged by grid moves. -/
theorem exists_movesTo_blockSwap {n : ℕ} (G : GridDiagram n) (p : ℕ) (hp : p + 6 ≤ n)
    (hni : ∀ c c' : Fin 3, NonintN (G.O ⟨p + c, by omega⟩).val (G.X ⟨p + c, by omega⟩).val
      (G.O ⟨p + 3 + c', by omega⟩).val (G.X ⟨p + 3 + c', by omega⟩).val) :
    ∃ G' : GridDiagram n, G.MovesTo G' ∧
      ∀ k : Fin n, (G'.O k).val = (G.O ⟨blockSwapVal p k.val, by
          unfold blockSwapVal; have := k.isLt; split_ifs <;> omega⟩).val ∧
        (G'.X k).val = (G.X ⟨blockSwapVal p k.val, by
          unfold blockSwapVal; have := k.isLt; split_ifs <;> omega⟩).val := by
  set L := LabeledGrid.ofGrid G
  let e : ℕ → Fin n := fun k => ⟨min k (n - 1), by omega⟩
  have he : ∀ k (hk : k < n), e k = ⟨k, hk⟩ := fun k hk => Fin.ext (by simp [e]; omega)
  set A := (List.finRange n).take p
  set B := (List.finRange n).drop (p + 6)
  have hlen : (List.finRange n).length = n := List.length_finRange
  have hdrop : ∀ k (hk : k < n), (List.finRange n).drop k =
      e k :: (List.finRange n).drop (k + 1) := by
    intro k hk
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact hk), List.getElem_finRange, he k hk]
    rfl
  have hcols : L.cols = A ++ [e p, e (p + 1), e (p + 2)] ++ e (p + 3) ::
      ([e (p + 4), e (p + 5)] ++ B) := by
    change List.finRange n = _
    conv_lhs => rw [← List.take_append_drop p (List.finRange n)]
    rw [hdrop p (by omega), hdrop (p + 1) (by omega), hdrop (p + 2) (by omega),
      hdrop (p + 3) (by omega), hdrop (p + 4) (by omega), hdrop (p + 5) (by omega)]
    simp [A, B]
  have hNI : ∀ (M : LabeledGrid n (Fin n) (Fin n)), M.rows = L.rows → M.O = L.O → M.X = L.X →
      ∀ c c' : Fin 3, M.ColsNonint (e (p + c)) (e (p + 3 + c')) := by
    intro M hr hO hX c c'
    unfold LabeledGrid.ColsNonint
    have hrp : ∀ r, M.rpos r = r.val := fun r => by
      simp only [LabeledGrid.rpos, hr]; exact List.idxOf_finRange r
    rw [hrp, hrp, hrp, hrp, hO, hX, he _ (by omega), he _ (by omega)]
    exact hni c c'
  obtain ⟨M₁, c₁, r₁, O₁, X₁, m₁⟩ := L.exists_moveColLeft (l₁ := A)
    (mid := [e p, e (p + 1), e (p + 2)]) (c := e (p + 3)) (l₂ := [e (p + 4), e (p + 5)] ++ B)
    hcols (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simpa using hNI L rfl rfl rfl 0 0
      · simpa using hNI L rfl rfl rfl 1 0
      · simpa using hNI L rfl rfl rfl 2 0)
  have hc₁ : M₁.cols = (A ++ [e (p + 3)]) ++ [e p, e (p + 1), e (p + 2)] ++ e (p + 4) ::
      ([e (p + 5)] ++ B) := by rw [c₁]; simp
  obtain ⟨M₂, c₂, r₂, O₂, X₂, m₂⟩ := M₁.exists_moveColLeft hc₁ (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simpa using hNI M₁ r₁ O₁ X₁ 0 1
      · simpa using hNI M₁ r₁ O₁ X₁ 1 1
      · simpa using hNI M₁ r₁ O₁ X₁ 2 1)
  have hc₂ : M₂.cols = (A ++ [e (p + 3), e (p + 4)]) ++ [e p, e (p + 1), e (p + 2)] ++
      e (p + 5) :: B := by rw [c₂]; simp
  obtain ⟨M₃, c₃, r₃, O₃, X₃, m₃⟩ := M₂.exists_moveColLeft hc₂ (by
      intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simpa using hNI M₂ (r₂.trans r₁) (O₂.trans O₁) (X₂.trans X₁) 0 2
      · simpa using hNI M₂ (r₂.trans r₁) (O₂.trans O₁) (X₂.trans X₁) 1 2
      · simpa using hNI M₂ (r₂.trans r₁) (O₂.trans O₁) (X₂.trans X₁) 2 2)
  refine ⟨M₃.toGrid, ?_, ?_⟩
  · rw [← LabeledGrid.toGrid_ofGrid G]; exact m₁.trans (m₂.trans m₃)
  · have hc3' : M₃.cols = A ++ ([e (p + 3), e (p + 4), e (p + 5), e p, e (p + 1), e (p + 2)] ++
        B) := by rw [c₃]; simp
    have hAl : A.length = p := by simp [A, hlen]; omega
    have hcol : ∀ k : Fin n, (M₃.colAt k).val = blockSwapVal p k.val := by
      intro k
      have hk := k.isLt
      rw [M₃.colAt_eq_of_cols hc3']
      unfold blockSwapVal
      by_cases h1 : k.val < p
      · rw [if_neg (by omega), if_neg (by omega), List.getElem_append_left (by omega)]
        simp [A]
      · rw [List.getElem_append_right (by omega)]
        by_cases h2 : k.val < p + 6
        · rw [List.getElem_append_left (by simp; omega)]
          obtain ⟨t, ht⟩ : ∃ t, k.val = p + t := ⟨k.val - p, by omega⟩
          have htl : t < 6 := by omega
          simp only [ht, hAl, show p + t - p = t by omega]
          interval_cases t <;> simp [e] <;> omega
        · rw [if_neg (by omega), if_neg (by omega), List.getElem_append_right (by simp; omega)]
          simp [B, hAl]
          omega
    have hr3 : ∀ r : Fin n, M₃.rpos r = r.val := fun r => by
      simp only [LabeledGrid.rpos, r₃, r₂, r₁]; exact List.idxOf_finRange r
    intro k
    constructor
    · rw [M₃.toGrid_O_val, hr3, O₃, O₂, O₁]
      exact congrArg (fun x => (G.O x).val) (Fin.ext (hcol k))
    · rw [M₃.toGrid_X_val, hr3, X₃, X₂, X₁]
      exact congrArg (fun x => (G.X x).val) (Fin.ext (hcol k))

section Far

variable {m : ℕ} (u v : PositiveAdjacentWord m) (i j : Fin (m - 1))

theorem far_length : (u ++ i :: j :: v).length = (u ++ j :: i :: v).length := by simp

/-- The letter bijection of a far commutation. -/
def farLetters : Fin (u ++ i :: j :: v).length ≃ Fin (u ++ j :: i :: v).length :=
  (finCongr (far_length u v i j)).trans (Equiv.swap ⟨u.length, by simp⟩ ⟨u.length + 1, by simp⟩)

theorem farLetters_val (h : Fin (u ++ i :: j :: v).length) :
    (farLetters u v i j h).val =
      if h.val = u.length then u.length + 1 else if h.val = u.length + 1 then u.length
      else h.val := by
  rw [farLetters, Equiv.trans_apply, Equiv.swap_apply_def]
  simp only [finCongr_apply, Fin.ext_iff, Fin.val_cast]
  split_ifs <;> simp_all

theorem farLetters_getElem (h : Fin (u ++ i :: j :: v).length) :
    (u ++ j :: i :: v)[(farLetters u v i j h).val] = (u ++ i :: j :: v)[h.val] := by
  have hv := farLetters_val u v i j h
  have hh := h.isLt
  simp only [List.length_append, List.length_cons] at hh
  by_cases h1 : h.val = u.length
  · simp only [h1, if_true] at hv
    simp only [hv, h1]
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp
  · by_cases h2 : h.val = u.length + 1
    · rw [if_neg h1, if_pos h2] at hv
      simp only [hv, h2]
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp
    · simp only [h1, h2, if_false] at hv
      simp only [hv]
      by_cases h3 : h.val < u.length
      · rw [List.getElem_append_left h3, List.getElem_append_left h3]
      · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        obtain ⟨t, ht⟩ : ∃ t, h.val - u.length = t + 2 := ⟨h.val - u.length - 2, by omega⟩
        simp only [ht, List.getElem_cons_succ]

theorem farLetters_succ (hij : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) (r : Fin m)
    (k : PositiveRectilinearRowOccurrences (u ++ i :: j :: v) r) :
    positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences (u ++ j :: i :: v) r)
        (occTransport (farLetters u v i j) (farLetters_getElem u v i j) k) =
      occTransport (farLetters u v i j) (farLetters_getElem u v i j)
        (positiveRectilinearSortedSuccessor _ k) := by
  apply sortedSuccessor_transport_of_strictMono
  · -- the two letters do not both involve `r`
    have hnot : ∀ b b' : PositiveRectilinearRowOccurrences (u ++ i :: j :: v) r,
        b.val.val = u.length → b'.val.val = u.length + 1 → False := by
      intro b b' hb hb'
      have e1 : (u ++ i :: j :: v)[b.val.val] = i := by
        simp only [hb]; rw [List.getElem_append_right (by omega)]; simp
      have e2 : (u ++ i :: j :: v)[b'.val.val] = j := by
        simp only [hb']; rw [List.getElem_append_right (by omega)]; simp
      have p1 := b.property; have p2 := b'.property
      rw [e1] at p1; rw [e2] at p2
      simp only [Fin.ext_iff, adjacentLower, adjacentUpper] at p1 p2
      omega
    intro b b'
    change b.val.val < b'.val.val ↔ (farLetters u v i j b.val).val < (farLetters u v i j b'.val).val
    rw [farLetters_val, farLetters_val]
    constructor <;> intro h <;> split_ifs at h ⊢ with h1 h2 h3 h4 <;>
      first | omega | exact absurd (hnot b b' (by omega) (by omega)) id |
        exact absurd (hnot b' b (by omega) (by omega)) id
  · intro b'
    have hletter : (u ++ i :: j :: v)[((farLetters u v i j).symm b'.val).val] =
        (u ++ j :: i :: v)[b'.val.val] := by
      have := farLetters_getElem u v i j ((farLetters u v i j).symm b'.val)
      simp only [Equiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨⟨(farLetters u v i j).symm b'.val, by rw [hletter]; exact b'.property⟩, ?_⟩
    apply Subtype.ext
    simp [occTransport]

/-- In an admissible grid of `u i j v` with `|i - j| ≥ 2`, every column of the letter `i` and
every column of the letter `j` have non-interleaving segments. -/
theorem far_colsNonint (hij : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val)
    {G : GridDiagram ((u ++ i :: j :: v).length * 3)}
    (hG : IsAdmissibleWordGrid (u ++ i :: j :: v) G) (c c' : Fin 3) :
    let pA : Fin (u ++ i :: j :: v).length × Fin 3 := (⟨u.length, by simp⟩, c)
    let pB : Fin (u ++ i :: j :: v).length × Fin 3 := (⟨u.length + 1, by simp⟩, c')
    NonintN (G.O (finProdFinEquiv pA)).val (G.X (finProdFinEquiv pA)).val
      (G.O (finProdFinEquiv pB)).val (G.X (finProdFinEquiv pB)).val := by
  intro pA pB
  have hwa : (u ++ i :: j :: v)[u.length] = i := by
    rw [List.getElem_append_right (by simp)]; simp
  have hwb : (u ++ i :: j :: v)[u.length + 1] = j := by
    rw [List.getElem_append_right (by simp)]; simp
  have hA := arcRow_bounds (u ++ i :: j :: v) pA
  have hB := arcRow_bounds (u ++ i :: j :: v) pB
  simp only [pA, pB, hwa, hwb] at hA hB
  rw [hG.X_eq pA, hG.X_eq pB]
  set M := positiveRectilinearWordMatching (u ++ i :: j :: v)
  apply nonintN_of_lt
  rcases hij with hij | hij
  · left
    have hi : ((i : ℕ) : ℝ) + 1 < ((j : ℕ) : ℝ) := by
      have : (i.val : ℝ) + 2 ≤ j.val := by exact_mod_cast hij
      linarith
    have l1 := hG.O_lt_of_arcRow_lt pA pB (by simp only [pA, pB]; linarith [hA.2.1, hB.1])
    have l2 := hG.O_lt_of_arcRow_lt pA (M.symm pB)
      (by simp only [pA, pB]; linarith [hA.2.1, hB.2.2.1])
    have l3 := hG.O_lt_of_arcRow_lt (M.symm pA) pB
      (by simp only [pA, pB]; linarith [hA.2.2.2, hB.1])
    have l4 := hG.O_lt_of_arcRow_lt (M.symm pA) (M.symm pB)
      (by simp only [pA, pB]; linarith [hA.2.2.2, hB.2.2.1])
    simp only [Fin.lt_def] at l1 l2 l3 l4
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨l1, l3⟩, l2, l4⟩
  · right
    have hj : ((j : ℕ) : ℝ) + 1 < ((i : ℕ) : ℝ) := by
      have : (j.val : ℝ) + 2 ≤ i.val := by exact_mod_cast hij
      linarith
    have l1 := hG.O_lt_of_arcRow_lt pB pA (by simp only [pA, pB]; linarith [hB.2.1, hA.1])
    have l2 := hG.O_lt_of_arcRow_lt pB (M.symm pA)
      (by simp only [pA, pB]; linarith [hB.2.1, hA.2.2.1])
    have l3 := hG.O_lt_of_arcRow_lt (M.symm pB) pA
      (by simp only [pA, pB]; linarith [hB.2.2.2, hA.1])
    have l4 := hG.O_lt_of_arcRow_lt (M.symm pB) (M.symm pA)
      (by simp only [pA, pB]; linarith [hB.2.2.2, hA.2.2.1])
    simp only [Fin.lt_def] at l1 l2 l3 l4
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨l1, l3⟩, l2, l4⟩

/-- **Far commutation.** If `|i - j| ≥ 2`, the selected grids of `u i j v` and `u j i v` are
related by grid moves. -/
theorem wordGrid_movesTo_far (hij : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
    (wordGrid (u ++ i :: j :: v)).MovesTo (wordGrid (u ++ j :: i :: v)) := by
  have hL := far_length u v i j
  have hG := wordGrid_isAdmissible (u ++ i :: j :: v)
  have hadm := IsAdmissibleWordGrid.transport hL (farLetters u v i j)
    (farLetters_getElem u v i j) (farLetters_succ u v i j hij) hG
  refine GridDiagram.MovesTo.trans ?_ hadm.movesTo_wordGrid
  have hn : 3 * u.length + 6 ≤ (u ++ i :: j :: v).length * 3 := by simp; omega
  have hL3 : (u ++ i :: j :: v).length * 3 = (u ++ j :: i :: v).length * 3 := by rw [hL]
  have hlenu : u.length < (u ++ i :: j :: v).length := by simp
  have hlenu1 : u.length + 1 < (u ++ i :: j :: v).length := by simp
  obtain ⟨G', hm, hG'⟩ := exists_movesTo_blockSwap (wordGrid (u ++ i :: j :: v)) (3 * u.length)
    hn (by
      intro c c'
      have h := far_colsNonint u v i j hij hG c c'
      simp only at h
      have e1 : (⟨3 * u.length + c.val, by omega⟩ : Fin ((u ++ i :: j :: v).length * 3)) =
          finProdFinEquiv ((⟨u.length, hlenu⟩ : Fin (u ++ i :: j :: v).length), c) := by
        apply Fin.ext; simp [finProdFinEquiv_apply_val]; ring
      have e2 : (⟨3 * u.length + 3 + c'.val, by omega⟩ :
          Fin ((u ++ i :: j :: v).length * 3)) =
          finProdFinEquiv ((⟨u.length + 1, hlenu1⟩ : Fin (u ++ i :: j :: v).length), c') := by
        apply Fin.ext; simp [finProdFinEquiv_apply_val]; ring
      rw [e1, e2]
      exact h)
  have heq : transportGrid hL (farLetters u v i j) (wordGrid (u ++ i :: j :: v)) =
      GridDiagram.castSize hL3 G' := by
    have hsurj : ∀ c : Fin ((u ++ j :: i :: v).length * 3),
        ∃ q : Fin (u ++ i :: j :: v).length × Fin 3,
        finProdFinEquiv (farLetters u v i j q.1, q.2) = c := by
      intro c
      refine ⟨((farLetters u v i j).symm (finProdFinEquiv.symm c).1,
        (finProdFinEquiv.symm c).2), ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact finProdFinEquiv.apply_symm_apply c
    have key : ∀ q : Fin (u ++ i :: j :: v).length × Fin 3,
        blockSwapVal (3 * u.length) (finProdFinEquiv (farLetters u v i j q.1, q.2)).val =
          (finProdFinEquiv q).val := by
      intro q
      have hv := farLetters_val u v i j q.1
      have h2 := q.2.isLt
      simp only [finProdFinEquiv_apply_val, blockSwapVal]
      split_ifs at hv ⊢ <;> omega
    ext c
    · obtain ⟨q, rfl⟩ := hsurj c
      rw [transportGrid_O, GridDiagram.castSize_O_apply, Fin.val_cast, (hG' _).1]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (key q).symm
    · obtain ⟨q, rfl⟩ := hsurj c
      rw [transportGrid_X, GridDiagram.castSize_X_apply, Fin.val_cast, (hG' _).2]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (key q).symm
  rw [heq]
  exact hm.trans (GridDiagram.movesTo_castSize hL3 _)

end Far

end OnLeConjecture.KnotTheory
