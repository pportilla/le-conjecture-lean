/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Move.Basic
public import OnLeConjecture.External.TauCeti.Data.Fin.Basic

/-! # Recognition of grid moves from local marking data

This module recognizes TauCeti's elementary grid moves (`GridDiagram.IsMove`) from explicit
marking data, and assembles them into longer sequences of moves (`GridDiagram.MovesTo`). The
grid-level declarations extend the namespaces `TauCeti.GridState` and `TauCeti.GridDiagram`.
Index identities in finite ordinals are in `OnLeConjecture.KnotTheory.GridMoves`.

## Commutations and cyclic permutations

* `GridDiagram.movesTo_swapRows_of_val_eq_succ`: swapping two linearly adjacent rows with
  non-interleaving marking segments is a grid move.
* `GridDiagram.columnsNoninterleaving_of_adjacent_rows` and
  `GridDiagram.rowsNoninterleaving_of_adjacent_columns`: a column whose markings lie in
  cyclically adjacent rows commutes with every column avoiding those rows, and similarly for
  rows.
* `GridDiagram.movesTo_relabelColumns_finRotate_pow` and
  `GridDiagram.movesTo_of_columns_finRotate`: cyclic permutations of the columns.

## Erasing a corner

For a grid diagram `G` of size `n + 1`, let `c` be a column and let `d` be the column carrying
the `X`-marking of the row `G.O c`. If the corner `(d, G.X c)` carries no `O`-marking, then
`GridDiagram.eraseOCorner G c d hd h4` is the grid diagram of size `n` obtained by deleting
column `c` and row `G.O c`, and moving the `X`-marking of column `d` to the row `G.X c`. The
remaining columns and rows keep their relative order (`succAbove_eraseOCorner_O`,
`succAbove_eraseOCorner_X`).

* `GridDiagram.isXStabilization_eraseOCorner`: if `c` and `d` are cyclically adjacent and the two
  rows of column `c` are cyclically adjacent, then `G` is an `X`-stabilization of the erased
  diagram. This is the recognition of a destabilization from a local `2 × 2` pattern, with the
  explicit reindexing of the remaining columns and rows.
* `GridDiagram.movesTo_eraseOCorner`: in general, `G` is related to the erased diagram by grid
  moves, provided that no column strictly between `c` and `d`, in the cyclic order from `c` to
  `d`, has its `O`-marking in the row `G.X c`, and that every row strictly between the two rows of
  column `c` has a marking segment that does not interleave with the columns `c` and `d`. The
  proof first moves the row `G.O c` towards the row `G.X c` by row commutations, then moves
  column `c` towards column `d` by column commutations, and finally destabilizes. A column
  commutation across the cyclic seam changes the erased diagram by a cyclic permutation of
  columns.

## Row permutations

* `GridDiagram.movesTo_relabelRows_of_monotone`: a row permutation that preserves the level sets
  of a monotone function of the rows is a sequence of row commutations, provided that any two
  rows in a common level set have non-interleaving marking segments.

## Restrictions of marking functions

`GridDiagram.IsMarkingRestriction G Of Xf κ ρ` says that the markings of `G` are the restrictions
of the functions `Of` and `Xf` along strictly increasing column and row embeddings `κ` and `ρ`.
It allows a sequence of erased corners to be tracked in the coordinates of the original diagram
(`IsMarkingRestriction.exists_movesTo_eraseOCorner_of_ambient`).

## Switches of `X`-markings and sizes

* `GridDiagram.switchAdjacentX`: the diagram obtained by exchanging the `X`-markings of a column
  and of its cyclic successor.
* `GridDiagram.castSize`: transport of a diagram along an equality of sizes, which is related to
  the original diagram by the empty sequence of moves (`GridDiagram.movesTo_castSize`).

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.GridMoves

/-! ### Index identities in finite ordinals -/

/-- The native column of the corner `(j, c)` is `3 j + c`. -/
theorem finProdFinEquiv_val_three {L : ℕ} (a : Fin L × Fin 3) :
    (finProdFinEquiv a).val = a.2.val + 3 * a.1.val :=
  finProdFinEquiv_apply_val a

/-- The cyclic successor of a point that is not the last point. -/
theorem finRotate_val_of_lt {N : ℕ} (x : Fin N) (h : x.val + 1 < N) :
    (finRotate N x).val = x.val + 1 := by
  cases N with
  | zero => exact x.elim0
  | succ n =>
    rw [coe_finRotate_of_ne_last]
    intro he
    rw [he, Fin.val_last] at h
    omega

/-- If `b` follows `a` and `r` is one of them, the transposition of `a` and `b` carries the
embedding skipping `r` to the embedding skipping the other point. -/
theorem swap_apply_succAbove_of_val_eq_succ {n : ℕ} {a b r : Fin (n + 1)}
    (hab : b.val = a.val + 1) (hr : r = a ∨ r = b) (i : Fin n) :
    Equiv.swap a b (r.succAbove i) = (Equiv.swap a b r).succAbove i := by
  have hi := i.isLt
  have hv := Fin.val_succAbove r i
  rcases hr with rfl | rfl
  · rw [Equiv.swap_apply_left]
    have hw := Fin.val_succAbove b i
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp only [Fin.ext_iff] at * <;> split_ifs at hv hw <;> omega
  · rw [Equiv.swap_apply_right]
    have hw := Fin.val_succAbove a i
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp only [Fin.ext_iff] at * <;> split_ifs at hv hw <;> omega

/-- The transposition of `c` and its cyclic successor carries the embedding skipping the
successor to the embedding skipping `c`, composed with a cyclic rotation when `c` is the last
point. -/
theorem swap_finRotate_apply_finRotate_succAbove {n : ℕ} (c : Fin (n + 1)) (i : Fin n) :
    Equiv.swap c (finRotate (n + 1) c) ((finRotate (n + 1) c).succAbove i) =
      c.succAbove (if c = Fin.last n then finRotate n i else i) := by
  have hi := i.isLt
  have hc := c.isLt
  by_cases hl : c = Fin.last n
  · subst hl
    rw [if_pos rfl, finRotate_last, Fin.succAbove_zero, Fin.succAbove_last]
    cases n with
    | zero => exact i.elim0
    | succ m =>
      have hq : (finRotate (m + 1) i).val = if i = Fin.last m then 0 else i.val + 1 :=
        coe_finRotate i
      rw [Equiv.swap_apply_def]
      split_ifs with h1 h2 <;> simp only [Fin.ext_iff, Fin.val_last, Fin.val_succ,
        Fin.val_zero, Fin.val_castSucc] at * <;> split_ifs at hq <;> omega
  · rw [if_neg hl]
    have hr : (finRotate (n + 1) c).val = c.val + 1 := by
      have := coe_finRotate c
      rw [if_neg hl] at this
      exact this
    rw [Fin.ext_iff, Fin.val_last] at hl
    have hv := Fin.val_succAbove (finRotate (n + 1) c) i
    have hw := Fin.val_succAbove c i
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2 <;> simp only [Fin.ext_iff] at * <;> split_ifs at hv hw <;> omega

/-- Conjugating the transposition of `b` and `c` by the transposition of `a` and `b` gives the
transposition of `a` and `c`, for three distinct points. -/
theorem swap_apply_swap_apply_of_ne {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (y : α) :
    Equiv.swap a b (Equiv.swap b c y) = Equiv.swap a c (Equiv.swap a b y) := by
  by_cases hya : y = a
  · subst hya
    simp [Equiv.swap_apply_def, hab, hac, hab.symm, hbc]
  by_cases hyb : y = b
  · subst hyb
    simp [Equiv.swap_apply_def, hac.symm, hbc.symm]
  by_cases hyc : y = c
  · subst hyc
    simp [Equiv.swap_apply_def, hac.symm, hbc.symm]
  simp [Equiv.swap_apply_def, hya, hyb, hyc]

/-- The cyclic successor of a point is its linear successor when the latter exists. -/
theorem finRotate_eq_of_val_eq_succ {n : ℕ} {a b : Fin (n + 1)} (h : b.val = a.val + 1) :
    finRotate (n + 1) a = b := by
  have hb := b.isLt
  ext
  rw [coe_finRotate_of_ne_last (fun he => by rw [he, Fin.val_last] at h; omega), h]

/-- The cyclic successor of `c` lies in the open cyclic interval from `c` to `d` unless it is
`d`. -/
theorem finRotate_mem_cIoo {n : ℕ} {c d : Fin (n + 1)} (hcd : c ≠ d)
    (h : finRotate (n + 1) c ≠ d) : finRotate (n + 1) c ∈ TauCeti.Grid.cIoo c d := by
  have hr : (finRotate (n + 1) c).val = if c = Fin.last n then 0 else c.val + 1 :=
    coe_finRotate c
  have hc := c.isLt
  have hd := d.isLt
  rw [TauCeti.Grid.mem_cIoo]
  rw [Ne, Fin.ext_iff] at hcd h
  by_cases hl : c = Fin.last n
  · rw [if_pos hl] at hr
    rw [Fin.ext_iff, Fin.val_last] at hl
    refine ⟨fun he => hcd (by rw [he]), ?_⟩
    split_ifs <;> omega
  · rw [if_neg hl] at hr
    rw [Fin.ext_iff, Fin.val_last] at hl
    refine ⟨fun he => hcd (by rw [he]), ?_⟩
    split_ifs <;> omega

/-- Two distinct points of `Fin (n + 1)` exist only when `n + 1` is at least two. -/
theorem one_lt_of_ne {n : ℕ} {c d : Fin (n + 1)} (h : c ≠ d) : 1 < n + 1 := by
  rcases Nat.lt_or_ge 1 (n + 1) with hn | hn
  · exact hn
  · exact absurd (Fin.ext (by have := d.isLt; have := c.isLt; omega)) h

/-- A strictly increasing map between finite ordinals preserves open cyclic intervals. -/
theorem mem_cIoo_iff_of_strictMono {k n : ℕ} {κ : Fin k → Fin n} (hκ : StrictMono κ)
    (a b x : Fin k) : κ x ∈ TauCeti.Grid.cIoo (κ a) (κ b) ↔ x ∈ TauCeti.Grid.cIoo a b := by
  have hlt : ∀ y z : Fin k, (κ y).val < (κ z).val ↔ y.val < z.val := fun y z => by
    rw [← Fin.lt_def, ← Fin.lt_def, hκ.lt_iff_lt]
  simp only [TauCeti.Grid.mem_cIoo, hκ.injective.ne_iff, hlt]

/-- A strictly increasing map between finite ordinals preserves non-interleaving. -/
theorem noninterleaving_iff_of_strictMono {k n : ℕ} {κ : Fin k → Fin n} (hκ : StrictMono κ)
    (a₀ a₁ b₀ b₁ : Fin k) :
    TauCeti.Grid.Noninterleaving (κ a₀) (κ a₁) (κ b₀) (κ b₁) ↔
      TauCeti.Grid.Noninterleaving a₀ a₁ b₀ b₁ := by
  simp only [TauCeti.Grid.Noninterleaving, mem_cIoo_iff_of_strictMono hκ]

end OnLeConjecture.KnotTheory.GridMoves

namespace TauCeti

open OnLeConjecture.KnotTheory.GridMoves

namespace GridState

variable {n : ℕ}

/-- Erase the point of a grid state in column `c`, whose row is `r`. The remaining point
`(c.succAbove k, r.succAbove l)` becomes the point `(k, l)`. -/
def erasePoint (x : GridState (n + 1)) (c r : Fin (n + 1)) (_h : x c = r) : GridState n where
  toPerm := Equiv.removeNone ((finSuccEquiv' c).symm.trans (x.toPerm.trans (finSuccEquiv' r)))

/-- The defining equation of `GridState.erasePoint`. -/
theorem succAbove_erasePoint (x : GridState (n + 1)) (c r : Fin (n + 1)) (h : x c = r)
    (k : Fin n) : r.succAbove (x.erasePoint c r h k) = x (c.succAbove k) := by
  have hne : x (c.succAbove k) ≠ r := fun he =>
    Fin.succAbove_ne c k (x.toPerm.injective (he.trans h.symm))
  obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hne
  have hsome : ((finSuccEquiv' c).symm.trans (x.toPerm.trans (finSuccEquiv' r))) (some k) =
      some y := by
    simp only [Equiv.trans_apply, finSuccEquiv'_symm_some]
    change finSuccEquiv' r (x (c.succAbove k)) = some y
    rw [← hy, finSuccEquiv'_succAbove]
  have hrm := Equiv.removeNone_some _ ⟨y, hsome⟩
  rw [hsome] at hrm
  change r.succAbove (Equiv.removeNone _ k) = _
  rw [Option.some_inj.mp hrm, hy]

end GridState

namespace GridDiagram

variable {n : ℕ}

/-- In a grid diagram, a column differs from its cyclic successor, because grid diagrams of size
one do not exist. -/
theorem column_ne_finRotate (G : GridDiagram n) (b : Fin n) : b ≠ finRotate n b := by
  have hn : 1 < n := by
    rcases Nat.lt_or_ge 1 n with h | h
    · exact h
    · exfalso
      have hn1 : n = 1 := by have := b.isLt; omega
      subst hn1
      exact IsEmpty.false G
  exact (Grid.finRotate_ne_self hn b).symm

/-! ### Commutations and cyclic permutations -/

/-- A column whose two markings lie in cyclically adjacent rows does not interleave with any
column whose markings avoid those two rows. -/
theorem columnsNoninterleaving_of_adjacent_rows (G : GridDiagram n) {a b : Fin n}
    (ha : finRotate n (G.O a) = G.X a ∨ finRotate n (G.X a) = G.O a)
    (hbO : G.O b ≠ G.X a) (hbX : G.X b ≠ G.O a) : G.ColumnsNoninterleaving a b := by
  by_cases hab : b = a
  · subst hab; exact G.columnsNoninterleaving_self b
  rcases ha with h | h
  · exact G.columnsNoninterleaving_of_X_eq_finRotate_O h.symm b
  · exact Grid.noninterleaving_of_finRotate_eq h.symm
      (fun he => hab (G.O.toPerm.injective he)) hbO hbX
      (fun he => hab (G.X.toPerm.injective he))

/-- A row whose two markings lie in cyclically adjacent columns does not interleave with any row
whose markings avoid those two columns. -/
theorem rowsNoninterleaving_of_adjacent_columns (G : GridDiagram n) {a b : Fin n}
    (ha : finRotate n (G.O.transpose a) = G.X.transpose a ∨
      finRotate n (G.X.transpose a) = G.O.transpose a)
    (hbO : G.O.transpose b ≠ G.X.transpose a) (hbX : G.X.transpose b ≠ G.O.transpose a) :
    G.RowsNoninterleaving a b := by
  rw [← columnsNoninterleaving_transpose]
  exact G.transpose.columnsNoninterleaving_of_adjacent_rows ha hbO hbX

/-- Every power of the cyclic permutation of the columns is a sequence of grid moves. -/
theorem movesTo_relabelColumns_finRotate_pow (G : GridDiagram n) (k : ℕ) :
    MovesTo G (G.relabelColumns (finRotate n ^ k)) := by
  induction k with
  | zero => rw [pow_zero]; exact MovesTo.refl _
  | succ k ih =>
    have h := ih.trans (cyclicColumns_movesTo (G.relabelColumns (finRotate n ^ k)))
    rw [relabelColumns_relabelColumns] at h
    have he : (finRotate n ^ k).trans (finRotate n) = finRotate n ^ (k + 1) := by
      rw [pow_succ']; rfl
    rw [he] at h
    exact h

/-! ### Erasing an `O` corner -/

/-- If column `d` carries the `X`-marking of the row `G.O c`, then after swapping the
`X`-markings of columns `c` and `d` the column `c` carries its `X`-marking in that row. -/
theorem swapColumns_X_apply_of_X_eq (G : GridDiagram (n + 1)) {c d : Fin (n + 1)}
    (hd : G.X d = G.O c) : (G.X.swapColumns c d) c = G.O c := by
  rw [GridState.swapColumns_apply, Equiv.swap_apply_left, hd]

/-- Erase the `O`-marking of column `c`. Column `d` carries the `X`-marking of the row `G.O c`,
and the corner `(d, G.X c)` carries no `O`-marking. The result deletes column `c` and row
`G.O c`, and moves the `X`-marking of column `d` to the row `G.X c`. -/
def eraseOCorner (G : GridDiagram (n + 1)) (c d : Fin (n + 1)) (hd : G.X d = G.O c)
    (h4 : G.O d ≠ G.X c) : GridDiagram n where
  O := G.O.erasePoint c (G.O c) rfl
  X := (G.X.swapColumns c d).erasePoint c (G.O c) (G.swapColumns_X_apply_of_X_eq hd)
  disjoint := by
    intro k he
    have h1 := congrArg (G.O c).succAbove he
    rw [GridState.succAbove_erasePoint, GridState.succAbove_erasePoint,
      GridState.swapColumns_apply] at h1
    by_cases hk : c.succAbove k = d
    · rw [hk, Equiv.swap_apply_right] at h1
      exact h4 h1
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne c k) hk] at h1
      exact G.disjoint _ h1

/-- The `O`-markings of an erased corner diagram are the remaining `O`-markings of `G`. -/
theorem succAbove_eraseOCorner_O (G : GridDiagram (n + 1)) (c d : Fin (n + 1))
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c) (k : Fin n) :
    (G.O c).succAbove ((G.eraseOCorner c d hd h4).O k) = G.O (c.succAbove k) :=
  GridState.succAbove_erasePoint G.O c (G.O c) rfl k

/-- The `X`-markings of an erased corner diagram are the remaining `X`-markings of `G`, except
that the column `d` receives the `X`-marking of the erased column `c`. -/
theorem succAbove_eraseOCorner_X (G : GridDiagram (n + 1)) (c d : Fin (n + 1))
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c) (k : Fin n) :
    (G.O c).succAbove ((G.eraseOCorner c d hd h4).X k) =
      G.X (Equiv.swap c d (c.succAbove k)) := by
  rw [← GridState.swapColumns_apply]
  exact GridState.succAbove_erasePoint _ c (G.O c) (G.swapColumns_X_apply_of_X_eq hd) k

/-- An erased `O` corner is an `X`-destabilization when the columns `c` and `d` are cyclically
adjacent and the two rows of column `c` are cyclically adjacent. -/
theorem isXStabilization_eraseOCorner (G : GridDiagram (n + 1)) (c d : Fin (n + 1))
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c)
    (hcol : finRotate (n + 1) c = d ∨ finRotate (n + 1) d = c)
    (hrow : finRotate (n + 1) (G.O c) = G.X c ∨ finRotate (n + 1) (G.X c) = G.O c) :
    IsXStabilization (G.eraseOCorner c d hd h4) G := by
  have hdc : d ≠ c := by
    intro he
    rw [he] at hd
    exact G.disjoint c hd.symm
  obtain ⟨s, hs⟩ := Fin.exists_succAbove_eq hdc
  have hXs : (G.O c).succAbove ((G.eraseOCorner c d hd h4).X s) = G.X c := by
    rw [succAbove_eraseOCorner_X, hs, Equiv.swap_apply_right]
  refine (isXStabilization_iff _ _).mpr ⟨c, G.O c, s, ?_, ?_, ?_⟩
  · rw [hs]; exact hcol
  · rw [hXs]; exact hrow
  · ext1
    · refine GridState.ext fun x => ?_
      induction x using Fin.succAboveCases c with
      | x => simp
      | p k => rw [stabilizeX_O, GridState.insertPoint_apply_succAbove,
          succAbove_eraseOCorner_O]
    · refine GridState.ext fun x => ?_
      rw [stabilizeX_X]
      induction x using Fin.succAboveCases c with
      | x => rw [GridState.splitPoint_apply_newColumn, hXs]
      | p k =>
        rw [GridState.splitPoint_apply_succAbove]
        split_ifs with hk
        · subst hk
          rw [hs, hd]
        · rw [succAbove_eraseOCorner_X, Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne c k)]
          rw [← hs]
          exact fun he => hk (Fin.succAbove_right_injective he)

/-- A grid diagram whose columns are cyclically shifted by one is related by grid moves to the
unshifted diagram. -/
theorem movesTo_of_columns_finRotate (D D' : GridDiagram n)
    (hO : ∀ k, D'.O k = D.O (finRotate n k)) (hX : ∀ k, D'.X k = D.X (finRotate n k)) :
    MovesTo D' D := by
  have hD : D' = D.relabelColumns (finRotate n).symm := by
    ext1
    · exact GridState.ext fun k => by rw [relabelColumns_O, GridState.relabelColumns_apply,
        Equiv.symm_symm, hO]
    · exact GridState.ext fun k => by rw [relabelColumns_X, GridState.relabelColumns_apply,
        Equiv.symm_symm, hX]
  have h := cyclicColumns_movesTo D'
  rw [hD, relabelColumns_relabelColumns, Equiv.symm_trans_self, relabelColumns_refl] at h
  rw [hD]
  exact h

/-- Swapping two linearly adjacent rows, one of which carries the erased `O`-marking, does not
change the result of erasing that corner. -/
theorem eraseOCorner_swapRows (G : GridDiagram (n + 1)) {a b : Fin (n + 1)}
    (hab : b.val = a.val + 1) {c d : Fin (n + 1)} (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c)
    (hc : G.O c = a ∨ G.O c = b)
    (hd' : (G.swapRows a b).X d = (G.swapRows a b).O c)
    (h4' : (G.swapRows a b).O d ≠ (G.swapRows a b).X c) :
    (G.swapRows a b).eraseOCorner c d hd' h4' = G.eraseOCorner c d hd h4 := by
  have key : ∀ i : Fin n,
      Equiv.swap a b ((G.O c).succAbove i) = ((G.swapRows a b).O c).succAbove i := fun i =>
    swap_apply_succAbove_of_val_eq_succ hab hc i
  ext1
  · refine GridState.ext fun k => ?_
    apply ((G.swapRows a b).O c).succAbove_right_injective
    rw [succAbove_eraseOCorner_O, ← key, succAbove_eraseOCorner_O]
    rfl
  · refine GridState.ext fun k => ?_
    apply ((G.swapRows a b).O c).succAbove_right_injective
    rw [succAbove_eraseOCorner_X, ← key, succAbove_eraseOCorner_X]
    rfl

/-- A version of `eraseOCorner_swapRows` for a diagram given up to equality. -/
theorem eraseOCorner_of_eq_swapRows (G : GridDiagram (n + 1)) {G' : GridDiagram (n + 1)}
    {a b : Fin (n + 1)} (hG' : G' = G.swapRows a b) (hab : b.val = a.val + 1)
    {c d : Fin (n + 1)} (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c)
    (hc : G.O c = a ∨ G.O c = b) (hd' : G'.X d = G'.O c) (h4' : G'.O d ≠ G'.X c) :
    G'.eraseOCorner c d hd' h4' = G.eraseOCorner c d hd h4 := by
  subst hG'
  exact G.eraseOCorner_swapRows hab hd h4 hc hd' h4'

/-- Moving the column of an erased `O`-marking one step to the right changes the erased diagram
at most by a cyclic permutation of its columns. -/
theorem movesTo_eraseOCorner_swapColumns (G : GridDiagram (n + 1)) {c d : Fin (n + 1)}
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c) (hcd : finRotate (n + 1) c ≠ d)
    (hd' : (G.swapColumns c (finRotate (n + 1) c)).X d =
      (G.swapColumns c (finRotate (n + 1) c)).O (finRotate (n + 1) c))
    (h4' : (G.swapColumns c (finRotate (n + 1) c)).O d ≠
      (G.swapColumns c (finRotate (n + 1) c)).X (finRotate (n + 1) c)) :
    MovesTo ((G.swapColumns c (finRotate (n + 1) c)).eraseOCorner (finRotate (n + 1) c) d hd'
      h4') (G.eraseOCorner c d hd h4) := by
  set c' := finRotate (n + 1) c with hc'
  set G' := G.swapColumns c c'
  have hdc : d ≠ c := by
    intro he
    rw [he] at hd
    exact G.disjoint c hd.symm
  have hcc' : c ≠ c' := (Grid.finRotate_ne_self (one_lt_of_ne hdc) c).symm
  have hOc : G'.O c' = G.O c := by
    change G.O (Equiv.swap c c' c') = G.O c
    rw [Equiv.swap_apply_right]
  let τ : Fin n → Fin n := fun k => if c = Fin.last n then finRotate n k else k
  have key : ∀ k, Equiv.swap c c' (c'.succAbove k) = c.succAbove (τ k) := fun k =>
    swap_finRotate_apply_finRotate_succAbove c k
  have hOk : ∀ k, (G'.eraseOCorner c' d hd' h4').O k = (G.eraseOCorner c d hd h4).O (τ k) := by
    intro k
    apply (G'.O c').succAbove_right_injective
    rw [succAbove_eraseOCorner_O, hOc, succAbove_eraseOCorner_O, ← key]
    rfl
  have hXk : ∀ k, (G'.eraseOCorner c' d hd' h4').X k = (G.eraseOCorner c d hd h4).X (τ k) := by
    intro k
    apply (G'.O c').succAbove_right_injective
    rw [succAbove_eraseOCorner_X, hOc, succAbove_eraseOCorner_X, ← key]
    change G.X (Equiv.swap c c' (Equiv.swap c' d (c'.succAbove k))) = _
    rw [swap_apply_swap_apply_of_ne hcc' hdc.symm hcd]
  by_cases hl : c = Fin.last n
  · apply movesTo_of_columns_finRotate
    · intro k; rw [hOk]; simp only [τ, if_pos hl]
    · intro k; rw [hXk]; simp only [τ, if_pos hl]
  · have hD : G'.eraseOCorner c' d hd' h4' = G.eraseOCorner c d hd h4 := by
      ext1
      · exact GridState.ext fun k => by rw [hOk]; simp only [τ, if_neg hl]
      · exact GridState.ext fun k => by rw [hXk]; simp only [τ, if_neg hl]
    rw [hD]

/-- The column phase of erasing an `O` corner. When the two markings of column `c` lie in
cyclically adjacent rows, column `c` is moved to the right until it is adjacent to column `d`,
and the corner is then removed by an `X`-destabilization. -/
theorem movesTo_eraseOCorner_of_adjacent_rows (G : GridDiagram (n + 1)) (c d : Fin (n + 1))
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c)
    (hrow : finRotate (n + 1) (G.O c) = G.X c ∨ finRotate (n + 1) (G.X c) = G.O c)
    (hcols : ∀ k ∈ Grid.cIoo c d, G.O k ≠ G.X c) :
    MovesTo G (G.eraseOCorner c d hd h4) := by
  suffices H : ∀ m (G : GridDiagram (n + 1)) (c : Fin (n + 1)), (Grid.cIoo c d).card = m →
      ∀ (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c),
      (finRotate (n + 1) (G.O c) = G.X c ∨ finRotate (n + 1) (G.X c) = G.O c) →
      (∀ k ∈ Grid.cIoo c d, G.O k ≠ G.X c) → MovesTo G (G.eraseOCorner c d hd h4) from
    H _ G c rfl hd h4 hrow hcols
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G c hm hd h4 hrow hcols
  have hdc : d ≠ c := by
    intro he
    rw [he] at hd
    exact G.disjoint c hd.symm
  by_cases hcd : finRotate (n + 1) c = d
  · exact IsDestabilization.movesTo ((isDestabilization_iff_isStabilization _ _).mpr
      ((isStabilization_iff _ _).mpr
        (Or.inr (G.isXStabilization_eraseOCorner c d hd h4 (Or.inl hcd) hrow))))
  set c' := finRotate (n + 1) c with hc'
  have hcc' : c ≠ c' := (Grid.finRotate_ne_self (one_lt_of_ne hdc) c).symm
  have hmem : c' ∈ Grid.cIoo c d := finRotate_mem_cIoo hdc.symm hcd
  have hnon : G.ColumnsNoninterleaving c c' := by
    rcases hrow with h | h
    · exact G.columnsNoninterleaving_of_X_eq_finRotate_O h.symm c'
    · exact Grid.noninterleaving_of_finRotate_eq h.symm
        (fun he => hcc' (G.O.toPerm.injective he).symm) (hcols c' hmem)
        (fun he => hcd (G.X.toPerm.injective (he.trans hd.symm)))
        (fun he => hcc' (G.X.toPerm.injective he).symm)
  have hmove : MovesTo G (G.swapColumns c c') := movesTo_swapColumns G c hnon
  set G' := G.swapColumns c c' with hG'
  have hOc' : G'.O c' = G.O c := by
    change G.O (Equiv.swap c c' c') = G.O c
    rw [Equiv.swap_apply_right]
  have hXc' : G'.X c' = G.X c := by
    change G.X (Equiv.swap c c' c') = G.X c
    rw [Equiv.swap_apply_right]
  have hfix : ∀ k, k ≠ c → k ≠ c' → Equiv.swap c c' k = k := fun k h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  have hXd : G'.X d = G.X d := by
    change G.X (Equiv.swap c c' d) = G.X d
    rw [hfix d hdc (Ne.symm hcd)]
  have hOd : G'.O d = G.O d := by
    change G.O (Equiv.swap c c' d) = G.O d
    rw [hfix d hdc (Ne.symm hcd)]
  have hd' : G'.X d = G'.O c' := by rw [hXd, hOc', hd]
  have h4' : G'.O d ≠ G'.X c' := by rw [hOd, hXc']; exact h4
  have hsub : Grid.cIoo c' d ⊆ Grid.cIoo c d := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hmem
  have hcols' : ∀ k ∈ Grid.cIoo c' d, G'.O k ≠ G'.X c' := by
    intro k hk
    have hkc' : k ≠ c' := Grid.ne_left_of_mem_cIoo hk
    have hkc : k ≠ c := fun he => Grid.left_notMem_cIoo c d (he ▸ hsub hk)
    rw [hXc']
    change G.O (Equiv.swap c c' k) ≠ G.X c
    rw [hfix k hkc hkc']
    exact hcols k (hsub hk)
  have hrow' : finRotate (n + 1) (G'.O c') = G'.X c' ∨
      finRotate (n + 1) (G'.X c') = G'.O c' := by
    rw [hOc', hXc']; exact hrow
  have hlt : (Grid.cIoo c' d).card < m := by
    rw [← hm]
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he =>
      Grid.left_notMem_cIoo c' d (he ▸ hmem)⟩
  have h1 := ih _ hlt G' c' rfl hd' h4' hrow' hcols'
  exact hmove.trans (h1.trans (G.movesTo_eraseOCorner_swapColumns hd h4 hcd hd' h4'))

/-- Swapping two linearly adjacent rows with non-interleaving markings is a grid move. -/
theorem movesTo_swapRows_of_val_eq_succ (G : GridDiagram n) {a b : Fin n}
    (hab : b.val = a.val + 1) (h : G.RowsNoninterleaving a b) :
    MovesTo G (G.swapRows a b) := by
  cases n with
  | zero => exact a.elim0
  | succ n =>
    have hb : finRotate (n + 1) a = b := finRotate_eq_of_val_eq_succ hab
    have h' := movesTo_swapRows G a (hb ▸ h)
    rw [hb] at h'
    exact h'

/-- Erasing an `O` corner by grid moves. Column `c` carries the erased `O`-marking, and column
`d` carries the `X`-marking of the same row. The hypotheses say that the corner `(d, G.X c)`
carries no `O`-marking, that no column strictly between `c` and `d`, in the cyclic order from
`c` to `d`, has its `O`-marking in the row `G.X c`, and that every row strictly between the two
rows of column `c` has a marking segment, from its `O` column `k` to its `X` column `k'`, that
does not interleave with the segment from `c` to `d`. -/
theorem movesTo_eraseOCorner (G : GridDiagram (n + 1)) (c d : Fin (n + 1))
    (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c)
    (hcols : ∀ k ∈ Grid.cIoo c d, G.O k ≠ G.X c)
    (hrows : ∀ k k' : Fin (n + 1),
      (G.X c < G.O k ∧ G.O k < G.O c ∨ G.O c < G.O k ∧ G.O k < G.X c) →
      G.X k' = G.O k → Grid.Noninterleaving k k' c d) :
    MovesTo G (G.eraseOCorner c d hd h4) := by
  suffices H : ∀ m (G : GridDiagram (n + 1)),
      (G.O c).val - (G.X c).val + ((G.X c).val - (G.O c).val) = m →
      ∀ (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c),
      (∀ k ∈ Grid.cIoo c d, G.O k ≠ G.X c) →
      (∀ k k' : Fin (n + 1),
        (G.X c < G.O k ∧ G.O k < G.O c ∨ G.O c < G.O k ∧ G.O k < G.X c) →
        G.X k' = G.O k → Grid.Noninterleaving k k' c d) →
      MovesTo G (G.eraseOCorner c d hd h4) from H _ G rfl hd h4 hcols hrows
  intro m
  induction m with
  | zero =>
    intro G hm hd h4 _ _
    exact absurd (Fin.ext (by omega)) (G.disjoint c)
  | succ m ih =>
  intro G hm hd h4 hcols hrows
  have hne := G.disjoint c
  rw [Ne, Fin.ext_iff] at hne
  -- When the two rows of column `c` are adjacent, the column phase applies.
  by_cases hm0 : m = 0
  · subst hm0
    apply movesTo_eraseOCorner_of_adjacent_rows G c d hd h4 _ hcols
    by_cases hlt : (G.O c).val < (G.X c).val
    · exact Or.inl (finRotate_eq_of_val_eq_succ (by omega))
    · exact Or.inr (finRotate_eq_of_val_eq_succ (by omega))
  -- Otherwise the row `G.O c` moves one step towards the row `G.X c`.
  have hrc := (G.O c).isLt
  have hxc := (G.X c).isLt
  obtain ⟨p, hp, hpb⟩ : ∃ p : Fin (n + 1),
      ((G.O c).val = p.val + 1 ∨ p.val = (G.O c).val + 1) ∧
      (G.X c < p ∧ p < G.O c ∨ G.O c < p ∧ p < G.X c) := by
    by_cases hlt : (G.O c).val < (G.X c).val
    · refine ⟨⟨(G.O c).val + 1, by omega⟩, Or.inr rfl, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp only [Fin.lt_def] <;> omega
    · refine ⟨⟨(G.O c).val - 1, by omega⟩, Or.inl (by simp; omega), Or.inl ⟨?_, ?_⟩⟩ <;>
        simp only [Fin.lt_def] <;> omega
  have hnon : G.RowsNoninterleaving p (G.O c) := by
    have h1 := hrows (G.O.transpose p) (G.X.transpose p)
      (by rw [GridState.apply_transpose_apply]; exact hpb)
      (by rw [GridState.apply_transpose_apply, GridState.apply_transpose_apply])
    change Grid.Noninterleaving (G.O.transpose p) (G.X.transpose p)
      (G.O.transpose (G.O c)) (G.X.transpose (G.O c))
    rw [GridState.transpose_apply_apply, ← hd, GridState.transpose_apply_apply]
    exact h1
  set G' := G.relabelRows (Equiv.swap p (G.O c)) with hG'
  have hmove : MovesTo G G' := by
    rcases hp with h | h
    · exact movesTo_swapRows_of_val_eq_succ G h hnon
    · have h1 := movesTo_swapRows_of_val_eq_succ G h ((G.rowsNoninterleaving_comm).mp hnon)
      rw [swapRows, Equiv.swap_comm] at h1
      exact h1
  have hO' : ∀ k, G'.O k = Equiv.swap p (G.O c) (G.O k) := fun k => rfl
  have hX' : ∀ k, G'.X k = Equiv.swap p (G.O c) (G.X k) := fun k => rfl
  have hXc_ne_p : G.X c ≠ p := by
    intro he; rw [← he] at hpb
    rcases hpb with h | h
    · exact lt_irrefl _ h.1
    · exact lt_irrefl _ h.2
  have hXc' : G'.X c = G.X c := by
    rw [hX', Equiv.swap_apply_of_ne_of_ne hXc_ne_p (fun he => G.disjoint c he.symm)]
  have hOc' : G'.O c = p := by rw [hO', Equiv.swap_apply_right]
  have hd' : G'.X d = G'.O c := by rw [hX', hd, Equiv.swap_apply_right, hOc']
  have h4' : G'.O d ≠ G'.X c := by
    rw [hO', hX']; exact fun he => h4 ((Equiv.swap _ _).injective he)
  have hcols' : ∀ k ∈ Grid.cIoo c d, G'.O k ≠ G'.X c := by
    intro k hk; rw [hO', hX']; exact fun he => hcols k hk ((Equiv.swap _ _).injective he)
  have hrows' : ∀ k k' : Fin (n + 1),
      (G'.X c < G'.O k ∧ G'.O k < G'.O c ∨ G'.O c < G'.O k ∧ G'.O k < G'.X c) →
      G'.X k' = G'.O k → Grid.Noninterleaving k k' c d := by
    intro k k' hk hkk'
    rw [hXc', hOc'] at hk
    have hOk_ne_p : G'.O k ≠ p := by
      intro he; rw [he] at hk
      rcases hk with h | h
      · exact lt_irrefl _ h.2
      · exact lt_irrefl _ h.1
    have hOk_ne : G'.O k ≠ G.O c := by
      intro he; rw [he] at hk
      rcases hk with h | h <;> rcases hpb with h' | h' <;> simp only [Fin.lt_def] at h h' <;>
        omega
    have hfix : Equiv.swap p (G.O c) (G'.O k) = G'.O k :=
      Equiv.swap_apply_of_ne_of_ne hOk_ne_p hOk_ne
    have hOk : G.O k = G'.O k := by
      rw [← hfix, hO' k, Equiv.swap_apply_self]
    apply hrows k k'
    · rw [hOk]
      rcases hk with h | h <;> rcases hpb with h' | h' <;> simp only [Fin.lt_def] at h h' ⊢ <;>
        omega
    · have h2 : Equiv.swap p (G.O c) (G.X k') = Equiv.swap p (G.O c) (G'.O k) := by
        rw [← hX', hkk', hfix]
      exact ((Equiv.swap _ _).injective h2).trans hOk.symm
  have hm' : (G'.O c).val - (G'.X c).val + ((G'.X c).val - (G'.O c).val) = m := by
    rw [hOc', hXc']
    rcases hp with h | h <;> rcases hpb with h' | h' <;> simp only [Fin.lt_def] at h' <;> omega
  have h1 := ih G' hm' hd' h4' hcols' hrows'
  have hD : G'.eraseOCorner c d hd' h4' = G.eraseOCorner c d hd h4 := by
    rcases hp with h | h
    · exact G.eraseOCorner_of_eq_swapRows rfl h hd h4 (Or.inr rfl) hd' h4'
    · exact G.eraseOCorner_of_eq_swapRows (by rw [hG', swapRows, Equiv.swap_comm]) h hd h4
        (Or.inl rfl) hd' h4'
  exact hmove.trans (hD ▸ h1)

/-! ### Row permutations inside blocks of non-interleaving rows -/

/-- A row that does not interleave with the rows above it, up to a row `t`, can be moved up to
position `t` by grid moves. The resulting row permutation sends `p` to `t` and fixes every row
outside the interval from `p` to `t`. -/
theorem exists_movesTo_relabelRows_up (G : GridDiagram n) (p t : Fin n) (hpt : p ≤ t)
    (h : ∀ r, p < r → r ≤ t → G.RowsNoninterleaving p r) :
    ∃ ρ : Equiv.Perm (Fin n), ρ p = t ∧ (∀ r, r < p ∨ t < r → ρ r = r) ∧
      MovesTo G (G.relabelRows ρ) := by
  suffices H : ∀ m (G : GridDiagram n) (p : Fin n), t.val - p.val = m → p ≤ t →
      (∀ r, p < r → r ≤ t → G.RowsNoninterleaving p r) →
      ∃ ρ : Equiv.Perm (Fin n), ρ p = t ∧ (∀ r, r < p ∨ t < r → ρ r = r) ∧
        MovesTo G (G.relabelRows ρ) from H _ G p rfl hpt h
  intro m
  induction m with
  | zero =>
    intro G p hm hpt _
    have hpt' : p = t := le_antisymm hpt (by rw [Fin.le_def]; omega)
    exact ⟨Equiv.refl _, hpt', fun _ _ => rfl, by rw [relabelRows_refl]⟩
  | succ m ih =>
    intro G p hm hpt h
    have ht := t.isLt
    rw [Fin.le_def] at hpt
    set q : Fin n := ⟨p.val + 1, by omega⟩ with hq
    have hpq : p < q := by rw [Fin.lt_def]; simp [hq]
    have hqt : q ≤ t := by rw [Fin.le_def]; simp [hq]; omega
    have hmove : MovesTo G (G.swapRows p q) :=
      movesTo_swapRows_of_val_eq_succ G rfl (h q hpq hqt)
    have h' : ∀ r, q < r → r ≤ t → (G.swapRows p q).RowsNoninterleaving q r := by
      intro r hqr hrt
      have hrp : r ≠ p := fun he => by rw [he] at hqr; exact lt_asymm hpq hqr
      have hrq : r ≠ q := ne_of_gt hqr
      change G.RowsNoninterleaving ((Equiv.swap p q).symm q) ((Equiv.swap p q).symm r)
      rw [Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hrp hrq]
      exact h r (hpq.trans hqr) hrt
    obtain ⟨ρ, hρq, hρfix, hρmove⟩ := ih (G.swapRows p q) q (by simp [hq]; omega) hqt h'
    refine ⟨(Equiv.swap p q).trans ρ, ?_, ?_, ?_⟩
    · simp [hρq]
    · intro r hr
      have hrp : r ≠ p := fun he => by
        rw [he] at hr; rcases hr with h1 | h1
        · exact lt_irrefl _ h1
        · rw [Fin.lt_def] at h1; omega
      have hrq : r ≠ q := fun he => by
        rw [he] at hr; rcases hr with h1 | h1
        · exact lt_asymm hpq h1
        · exact absurd h1 (not_lt.mpr hqt)
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hrp hrq]
      apply hρfix
      rcases hr with h1 | h1
      · exact Or.inl (h1.trans hpq)
      · exact Or.inr h1
    · exact hmove.trans hρmove

/-- A row permutation preserving the level sets of a monotone function of the rows is a sequence
of grid moves, provided that any two rows in a common level set do not interleave. -/
theorem movesTo_relabelRows_of_monotone {α : Type*} [LinearOrder α] (G : GridDiagram n)
    (β : Fin n → α) (hβ : Monotone β)
    (hG : ∀ r r', β r = β r' → G.RowsNoninterleaving r r')
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ r, β (σ r) = β r) :
    MovesTo G (G.relabelRows σ) := by
  suffices H : ∀ k, k ≤ n → ∀ (G : GridDiagram n),
      (∀ r r', β r = β r' → G.RowsNoninterleaving r r') →
      ∀ σ : Equiv.Perm (Fin n), (∀ r, β (σ r) = β r) → (∀ r : Fin n, k ≤ r.val → σ r = r) →
      MovesTo G (G.relabelRows σ) from
    H n le_rfl G hG σ hσ (fun r hr => absurd r.isLt (by omega))
  intro k
  induction k with
  | zero =>
    intro _ G _ σ _ hfix
    have : σ = Equiv.refl _ := Equiv.ext fun r => hfix r (Nat.zero_le _)
    rw [this, relabelRows_refl]
  | succ k ih =>
    intro hk G hG σ hσ hfix
    set t : Fin n := ⟨k, by omega⟩ with ht
    set p := σ.symm t with hp
    have hσp : σ p = t := by simp [hp]
    have hpt : p ≤ t := by
      by_contra hlt
      rw [not_le] at hlt
      have := hfix p (by rw [Fin.lt_def] at hlt; simp [ht] at hlt; omega)
      rw [hσp] at this
      exact absurd this (ne_of_lt hlt)
    have hβpt : β p = β t := by rw [← hσp, hσ]
    have hband : ∀ y, p ≤ y → y ≤ t → β y = β p := fun y h1 h2 =>
      le_antisymm (hβpt ▸ hβ h2) (hβ h1)
    obtain ⟨ρ, hρp, hρfix, hρmove⟩ := G.exists_movesTo_relabelRows_up p t hpt
      (fun r h1 h2 => hG p r (hband r h1.le h2).symm)
    have hρβ : ∀ x, β (ρ x) = β x := by
      intro x
      by_cases hx : x < p ∨ t < x
      · rw [hρfix x hx]
      · simp only [not_or, not_lt] at hx
        have hρx : ¬ (ρ x < p ∨ t < ρ x) := by
          intro hy
          have := hρfix (ρ x) hy
          have hxx := ρ.injective this
          rw [hxx] at hy
          rcases hy with h1 | h1
          · exact absurd hx.1 (not_le.mpr h1)
          · exact absurd hx.2 (not_le.mpr h1)
        simp only [not_or, not_lt] at hρx
        rw [hband _ hρx.1 hρx.2, hband _ hx.1 hx.2]
    have hG1 : ∀ r r', β r = β r' → (G.relabelRows ρ).RowsNoninterleaving r r' := by
      intro r r' hrr'
      rw [GridDiagram.rowsNoninterleaving_relabelRows]
      apply hG
      have h1 := hρβ (ρ.symm r)
      have h2 := hρβ (ρ.symm r')
      rw [Equiv.apply_symm_apply] at h1 h2
      rw [← h1, ← h2, hrr']
    have hσ' : ∀ r, β ((ρ.symm.trans σ) r) = β r := by
      intro r
      rw [Equiv.trans_apply, hσ]
      have h1 := hρβ (ρ.symm r)
      rw [Equiv.apply_symm_apply] at h1
      exact h1.symm
    have hfix' : ∀ r : Fin n, k ≤ r.val → (ρ.symm.trans σ) r = r := by
      intro r hr
      rw [Equiv.trans_apply]
      by_cases hrt : r = t
      · have h1 : ρ.symm t = p := by rw [Equiv.symm_apply_eq, hρp]
        rw [hrt, h1, hσp]
      · have hr' : k + 1 ≤ r.val := by
          rw [Fin.ext_iff] at hrt; simp [ht] at hrt; omega
        have htr : t < r := by rw [Fin.lt_def]; simp [ht]; omega
        have h1 : ρ.symm r = r := by
          rw [Equiv.symm_apply_eq]; exact (hρfix r (Or.inr htr)).symm
        rw [h1, hfix r hr']
    have h1 := ih (by omega) (G.relabelRows ρ) hG1 (ρ.symm.trans σ) hσ' hfix'
    rw [relabelRows_relabelRows] at h1
    have he : ρ.trans (ρ.symm.trans σ) = σ := Equiv.ext fun x => by simp
    rw [he] at h1
    exact hρmove.trans h1

/-! ### Restrictions of marking functions -/

/-- The diagram `G` is the restriction of the marking functions `Of` and `Xf` along strictly
increasing column and row embeddings `κ` and `ρ`: the `O`-marking of column `c` lies in the row
`r` with `ρ r = Of (κ c)`, and similarly for the `X`-markings. -/
structure IsMarkingRestriction {k : ℕ} (G : GridDiagram k) (Of Xf : Fin n → Fin n)
    (κ ρ : Fin k → Fin n) : Prop where
  col_strictMono : StrictMono κ
  row_strictMono : StrictMono ρ
  O_eq : ∀ c, ρ (G.O c) = Of (κ c)
  X_eq : ∀ c, ρ (G.X c) = Xf (κ c)

/-- Every diagram is the restriction of its own markings along the identity embeddings. -/
theorem isMarkingRestriction_self (G : GridDiagram n) :
    IsMarkingRestriction G G.O G.X id id :=
  ⟨strictMono_id, strictMono_id, fun _ => rfl, fun _ => rfl⟩

/-- Erasing an `O` corner of a restriction gives a restriction of the modified `X` function,
along the column embedding with the erased column removed. -/
theorem IsMarkingRestriction.eraseOCorner {k : ℕ} {G : GridDiagram (k + 1)}
    {Of Xf : Fin n → Fin n} {κ ρ : Fin (k + 1) → Fin n}
    (hR : IsMarkingRestriction G Of Xf κ ρ)
    {c d : Fin (k + 1)} (hd : G.X d = G.O c) (h4 : G.O d ≠ G.X c) :
    IsMarkingRestriction (G.eraseOCorner c d hd h4) Of (Function.update Xf (κ d) (Xf (κ c)))
      (κ ∘ c.succAbove) (ρ ∘ (G.O c).succAbove) where
  col_strictMono := hR.col_strictMono.comp (Fin.strictMono_succAbove c)
  row_strictMono := hR.row_strictMono.comp (Fin.strictMono_succAbove (G.O c))
  O_eq x := by
    simp only [Function.comp_apply]
    rw [succAbove_eraseOCorner_O, hR.O_eq]
  X_eq x := by
    simp only [Function.comp_apply]
    rw [succAbove_eraseOCorner_X]
    by_cases hx : c.succAbove x = d
    · rw [hx, Equiv.swap_apply_right, hR.X_eq, Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne c x) hx, hR.X_eq,
        Function.update_of_ne (fun he => hx (hR.col_strictMono.injective he))]

/-- Erasing an `O` corner of a restriction by grid moves. All hypotheses of
`GridDiagram.movesTo_eraseOCorner` are stated for the ambient marking functions. -/
theorem IsMarkingRestriction.exists_movesTo_eraseOCorner {k : ℕ} {G : GridDiagram (k + 1)}
    {Of Xf : Fin n → Fin n} {κ ρ : Fin (k + 1) → Fin n}
    (hR : IsMarkingRestriction G Of Xf κ ρ)
    (c d : Fin (k + 1)) (hd : Xf (κ d) = Of (κ c)) (h4 : Of (κ d) ≠ Xf (κ c))
    (hcols : ∀ x, κ x ∈ Grid.cIoo (κ c) (κ d) → Of (κ x) ≠ Xf (κ c))
    (hrows : ∀ x x' : Fin (k + 1),
      (Xf (κ c) < Of (κ x) ∧ Of (κ x) < Of (κ c) ∨
        Of (κ c) < Of (κ x) ∧ Of (κ x) < Xf (κ c)) →
      Xf (κ x') = Of (κ x) → Grid.Noninterleaving (κ x) (κ x') (κ c) (κ d)) :
    ∃ (G' : GridDiagram k) (ρ' : Fin k → Fin n), MovesTo G G' ∧
      IsMarkingRestriction G' Of (Function.update Xf (κ d) (Xf (κ c))) (κ ∘ c.succAbove) ρ' := by
  have hρ := hR.row_strictMono
  have hd' : G.X d = G.O c := hρ.injective (by rw [hR.X_eq, hR.O_eq, hd])
  have h4' : G.O d ≠ G.X c := fun he => h4 (by rw [← hR.O_eq, ← hR.X_eq, he])
  refine ⟨G.eraseOCorner c d hd' h4', ρ ∘ (G.O c).succAbove, ?_, hR.eraseOCorner hd' h4'⟩
  apply G.movesTo_eraseOCorner c d hd' h4'
  · intro x hx he
    apply hcols x ((mem_cIoo_iff_of_strictMono hR.col_strictMono c d x).mpr hx)
    rw [← hR.O_eq, ← hR.X_eq, he]
  · intro x x' hx hxx'
    rw [← noninterleaving_iff_of_strictMono hR.col_strictMono]
    apply hrows x x'
    · rw [← hR.O_eq, ← hR.O_eq, ← hR.X_eq, hρ.lt_iff_lt, hρ.lt_iff_lt, hρ.lt_iff_lt,
        hρ.lt_iff_lt]
      exact hx
    · rw [← hR.O_eq, ← hR.X_eq, hxx']

/-- A version of `IsMarkingRestriction.exists_movesTo_eraseOCorner` in which the erased column
and the column of the other marking of its row are named by their ambient columns `C` and `D`,
and the hypotheses are required for all ambient columns. -/
theorem IsMarkingRestriction.exists_movesTo_eraseOCorner_of_ambient {k : ℕ}
    {G : GridDiagram (k + 1)} {Of Xf : Fin n → Fin n} {κ ρ : Fin (k + 1) → Fin n}
    (hR : IsMarkingRestriction G Of Xf κ ρ) {C D : Fin n} (c d : Fin (k + 1)) (hc : κ c = C)
    (hD : κ d = D) (hd : Xf D = Of C) (h4 : Of D ≠ Xf C)
    (hcols : ∀ K ∈ Grid.cIoo C D, Of K ≠ Xf C)
    (hrows : ∀ K K' : Fin n,
      (Xf C < Of K ∧ Of K < Of C ∨ Of C < Of K ∧ Of K < Xf C) →
      Xf K' = Of K → Grid.Noninterleaving K K' C D) :
    ∃ (G' : GridDiagram k) (ρ' : Fin k → Fin n), MovesTo G G' ∧
      IsMarkingRestriction G' Of (Function.update Xf D (Xf C)) (κ ∘ c.succAbove) ρ' := by
  subst hc hD
  exact hR.exists_movesTo_eraseOCorner c d hd h4 (fun x hx => hcols (κ x) hx)
    (fun x x' hx hxx' => hrows (κ x) (κ x') hx hxx')

/-- Switch the `X`-markings of column `b` and of its cyclic successor. The hypotheses say that
neither switched column receives the row of its `O`-marking. -/
def switchAdjacentX (G : GridDiagram n) (b : Fin n) (h1 : G.O b ≠ G.X (finRotate n b))
    (h2 : G.O (finRotate n b) ≠ G.X b) : GridDiagram n where
  O := G.O
  X := G.X.swapColumns b (finRotate n b)
  disjoint := by
    intro k
    rw [GridState.swapColumns_apply]
    by_cases hkb : k = b
    · subst hkb; rw [Equiv.swap_apply_left]; exact h1
    · by_cases hkc : k = finRotate n b
      · subst hkc; rw [Equiv.swap_apply_right]; exact h2
      · rw [Equiv.swap_apply_of_ne_of_ne hkb hkc]; exact G.disjoint k

/-- The `O`-markings of a switched diagram. -/
theorem switchAdjacentX_O (G : GridDiagram n) (b : Fin n) (h1 : G.O b ≠ G.X (finRotate n b))
    (h2 : G.O (finRotate n b) ≠ G.X b) : (G.switchAdjacentX b h1 h2).O = G.O :=
  rfl

/-- The `X`-markings of a switched diagram. -/
theorem switchAdjacentX_X (G : GridDiagram n) (b : Fin n) (h1 : G.O b ≠ G.X (finRotate n b))
    (h2 : G.O (finRotate n b) ≠ G.X b) :
    (G.switchAdjacentX b h1 h2).X = G.X.swapColumns b (finRotate n b) :=
  rfl

/-! ### Changing the size index -/

/-- Transport a grid diagram along an equality of sizes. -/
def castSize {m : ℕ} (h : n = m) (G : GridDiagram n) : GridDiagram m := h ▸ G

/-- The `O`-markings of a transported diagram. -/
theorem castSize_O_apply {m : ℕ} (h : n = m) (G : GridDiagram n) (c : Fin m) :
    (G.castSize h).O c = Fin.cast h (G.O (Fin.cast h.symm c)) := by
  subst h; rfl

/-- The `X`-markings of a transported diagram. -/
theorem castSize_X_apply {m : ℕ} (h : n = m) (G : GridDiagram n) (c : Fin m) :
    (G.castSize h).X c = Fin.cast h (G.X (Fin.cast h.symm c)) := by
  subst h; rfl

/-- Transport along an equality of sizes is related to the original diagram by the empty
sequence of grid moves. -/
theorem movesTo_castSize {m : ℕ} (h : n = m) (G : GridDiagram n) : MovesTo G (G.castSize h) := by
  subst h; exact MovesTo.refl G

/-- A transported restriction is a restriction along the transported embeddings. -/
theorem IsMarkingRestriction.castSize {k m : ℕ} {G : GridDiagram k} {Of Xf : Fin n → Fin n}
    {κ ρ : Fin k → Fin n} (hR : IsMarkingRestriction G Of Xf κ ρ) (h : k = m) :
    IsMarkingRestriction (G.castSize h) Of Xf (κ ∘ Fin.cast h.symm) (ρ ∘ Fin.cast h.symm) := by
  subst h
  exact hR

end GridDiagram

end TauCeti
