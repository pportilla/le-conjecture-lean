/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridEmptyAnnuli
public import OnLeConjecture.KnotFloer.GridFullDifferentialBasic

/-!
# Annular cancellation in the full rectangle differential

The returning empty decompositions are the thin column annuli and the thin row annuli.
Each O marking contributes its variable once in each list. Their total is zero in
characteristic two, even though individual annular terms need not vanish.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-- The decomposition covering the full column beginning at `c`. -/
noncomputable def columnAnnulus (hn : 1 < n) (x : GridState n) (c : Fin n) :
    GridRectangleDecomposition x x where
  middle := x.swapColumns c (finRotate n c)
  first := GridRectangleBetween.ofSwapColumns x (x.swapColumns c (finRotate n c))
    c (finRotate n c) (Grid.finRotate_ne_self hn c).symm rfl
  second := GridRectangleBetween.ofSwapColumns (x.swapColumns c (finRotate n c)) x
    c (finRotate n c) (Grid.finRotate_ne_self hn c).symm
    (x.swapColumns_swapColumns c (finRotate n c)).symm

@[simp] theorem columnAnnulus_first_left (hn : 1 < n) (x : GridState n) (c : Fin n) :
    (columnAnnulus hn x c).first.left = c := by simp [columnAnnulus]
@[simp] theorem columnAnnulus_first_right (hn : 1 < n) (x : GridState n) (c : Fin n) :
    (columnAnnulus hn x c).first.right = finRotate n c := by simp [columnAnnulus]
@[simp] theorem columnAnnulus_second_left (hn : 1 < n) (x : GridState n) (c : Fin n) :
    (columnAnnulus hn x c).second.left = c := by simp [columnAnnulus]
@[simp] theorem columnAnnulus_second_right (hn : 1 < n) (x : GridState n) (c : Fin n) :
    (columnAnnulus hn x c).second.right = finRotate n c := by simp [columnAnnulus]

/-- The canonical column annulus has two empty rectangles. -/
theorem columnAnnulus_mem (hn : 1 < n) (x : GridState n) (c : Fin n) :
    columnAnnulus hn x c ∈ emptyDecompositions x x := by
  rw [mem_emptyDecompositions]
  constructor <;> apply GridRectangleBetween.isEmpty_of_right_eq_finRotate <;> simp

/-- The decomposition covering the full row beginning at `r`. -/
noncomputable def rowAnnulus (hn : 1 < n) (x : GridState n) (r : Fin n) :
    GridRectangleDecomposition x x := (columnAnnulus hn x.transpose r).transpose

@[simp] theorem rowAnnulus_first_bottom (hn : 1 < n) (x : GridState n) (r : Fin n) :
    (rowAnnulus hn x r).first.bottom = r := by
  exact (GridRectangleDecomposition.transpose_first_bottom
    (columnAnnulus hn x.transpose r)).trans (columnAnnulus_first_left hn x.transpose r)
@[simp] theorem rowAnnulus_second_bottom (hn : 1 < n) (x : GridState n) (r : Fin n) :
    (rowAnnulus hn x r).second.bottom = r := by
  exact (GridRectangleDecomposition.transpose_second_bottom
    (columnAnnulus hn x.transpose r)).trans (columnAnnulus_second_left hn x.transpose r)

/-- The canonical row annulus has two empty rectangles. -/
theorem rowAnnulus_mem (hn : 1 < n) (x : GridState n) (r : Fin n) :
    rowAnnulus hn x r ∈ emptyDecompositions x x := by
  rw [mem_emptyDecompositions]
  have h := (mem_emptyDecompositions _).mp (columnAnnulus_mem hn x.transpose r)
  exact ⟨(GridRectangleDecomposition.isEmpty_transpose_first _).mpr h.1,
    (GridRectangleDecomposition.isEmpty_transpose_second _).mpr h.2⟩

/-- A vertical empty annulus is uniquely determined by its column. -/
theorem eq_columnAnnulus (hn : 1 < n) (x : GridState n)
    (D : GridRectangleDecomposition x x) (hD : D ∈ emptyDecompositions x x)
    (hleft : D.second.left = D.first.left) :
    D = columnAnnulus hn x D.first.left := by
  have h := (mem_emptyDecompositions D).mp hD
  have hr := GridEmptyAnnuli.right_eq_finRotate_left D.first D.second h.1 h.2 hleft
  apply GridRectangleDecomposition.ext
  · simp
  · simpa using hr
  · simpa using hleft
  · simpa using (D.first.right_eq_right_of_left_eq_left D.second hleft).trans hr

/-- A horizontal empty annulus is uniquely determined by its row. -/
theorem eq_rowAnnulus (hn : 1 < n) (x : GridState n)
    (D : GridRectangleDecomposition x x) (hD : D ∈ emptyDecompositions x x)
    (hleft : D.second.left = D.first.right) :
    D = rowAnnulus hn x D.first.bottom := by
  have hDt : D.transpose ∈ emptyDecompositions x.transpose x.transpose := by
    simpa [mem_emptyDecompositions] using hD
  have hl : D.transpose.second.left = D.transpose.first.left := by
    simp only [GridRectangleDecomposition.transpose_second_left,
      GridRectangleDecomposition.transpose_first_left]
    exact D.first.bottom_eq_bottom_of_left_eq_right D.second hleft
  have heq := congrArg GridRectangleDecomposition.transpose
    (eq_columnAnnulus hn x.transpose D.transpose hDt hl)
  simpa [rowAnnulus] using heq

/-- All returning empty decompositions are the column annuli and row annuli. -/
theorem emptyDecompositions_self (hn : 1 < n) (x : GridState n) :
    emptyDecompositions x x = Finset.univ.image (columnAnnulus hn x) ∪
      Finset.univ.image (rowAnnulus hn x) := by
  classical
  ext D
  constructor
  · intro hD
    rcases D.first.left_right_eq_cases D.second with ⟨h, _⟩ | ⟨h, _⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨D.first.left, Finset.mem_univ _, (eq_columnAnnulus hn x D hD h).symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨D.first.bottom, Finset.mem_univ _, (eq_rowAnnulus hn x D hD h).symm⟩)
  · intro hD
    rcases Finset.mem_union.mp hD with hD | hD
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hD
      exact columnAnnulus_mem hn x c
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hD
      exact rowAnnulus_mem hn x r

/-- Column and row annuli are distinct decompositions, including in grids of size two. -/
theorem columnAnnulus_ne_rowAnnulus (hn : 1 < n) (x : GridState n) (c r : Fin n) :
    columnAnnulus hn x c ≠ rowAnnulus hn x r := by
  intro h
  have hb := congrArg (fun D : GridRectangleDecomposition x x => D.second.bottom) h
  have ha := congrArg (fun D : GridRectangleDecomposition x x => D.first.bottom) h
  have hrow : (columnAnnulus hn x c).second.bottom =
      (columnAnnulus hn x c).first.bottom := by
    rw [rowAnnulus_second_bottom] at hb
    rw [rowAnnulus_first_bottom] at ha
    exact hb.trans ha.symm
  have hbot := (columnAnnulus hn x c).first.bottom_eq_top_of_left_eq_left
    (columnAnnulus hn x c).second (by simp)
  exact (columnAnnulus hn x c).first.bottom_ne_top (hrow.symm.trans hbot)

variable (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- The O weight of a thin column annulus is the variable of its unique O marking. -/
theorem columnAnnulus_weight (hn : 1 < n) (x : GridState n) (c : Fin n) :
    G.unblockedDecompositionWeight R (columnAnnulus hn x c) = MvPolynomial.X c := by
  let D := columnAnnulus hn x c
  have hD := (mem_emptyDecompositions D).mp (columnAnnulus_mem hn x c)
  have hl : D.second.left = D.first.left := by simp [D]
  rw [GridDiagram.unblockedDecompositionWeight_def,
    G.OMonomial_eq_prod_coveredSquares, G.OMonomial_eq_prod_coveredSquares,
    ← Finset.prod_union (D.first.disjoint_coveredSquares D.second),
    D.first.coveredSquares_union_coveredSquares_of_left_eq_left D.second hl,
    GridEmptyAnnuli.coveredColumns_eq_singleton D.first D.second hD.1 hD.2 hl]
  simp [D, GridDiagram.mem_OSet]

/-- The O weight of a thin row annulus is the variable of its unique O marking. -/
theorem rowAnnulus_weight (hn : 1 < n) (x : GridState n) (r : Fin n) :
    G.unblockedDecompositionWeight R (rowAnnulus hn x r) =
      MvPolynomial.X (G.O.toPerm.symm r) := by
  let D := rowAnnulus hn x r
  have hD := (mem_emptyDecompositions D).mp (rowAnnulus_mem hn x r)
  have hb : D.second.bottom = D.first.bottom := by simp [D]
  have hl : D.second.left = D.first.right := by
    rcases D.first.left_right_eq_cases D.second with ⟨h, _⟩ | ⟨h, _⟩
    · exact False.elim (D.first.bottom_ne_top
        (hb.symm.trans (D.first.bottom_eq_top_of_left_eq_left D.second h)))
    · exact h
  rw [GridDiagram.unblockedDecompositionWeight_def,
    G.OMonomial_eq_prod_coveredSquares, G.OMonomial_eq_prod_coveredSquares,
    ← Finset.prod_union (D.first.disjoint_coveredSquares D.second),
    D.first.coveredSquares_union_coveredSquares_of_left_eq_right D.second hl,
    GridEmptyAnnuli.coveredRows_eq_singleton D.first D.second hD.1 hD.2 hl]
  simp only [Finset.prod_product, D, rowAnnulus_first_bottom,
    Finset.prod_singleton, GridDiagram.mem_OSet]
  have heq (c : Fin n) : G.O c = r ↔ c = G.O.toPerm.symm r :=
    G.O.toPerm.eq_symm_apply.symm
  simp_rw [heq]
  simp

/-- The diagonal sum is twice the sum of the O variables. -/
theorem sum_emptyDecompositionWeight_self (hn : 1 < n) (x : GridState n) :
    ∑ D ∈ emptyDecompositions x x, G.unblockedDecompositionWeight R D =
      (∑ c : Fin n, MvPolynomial.X c) + (∑ c : Fin n, MvPolynomial.X c) := by
  classical
  have hdisjoint : Disjoint (Finset.univ.image (columnAnnulus hn x))
      (Finset.univ.image (rowAnnulus hn x)) := by
    rw [Finset.disjoint_left]
    intro D hD hE
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨r, _, h⟩ := Finset.mem_image.mp hE
    exact columnAnnulus_ne_rowAnnulus hn x c r h.symm
  have hc : Function.Injective (columnAnnulus hn x) := by
    intro a b h
    simpa using congrArg (fun D : GridRectangleDecomposition x x => D.first.left) h
  have hr : Function.Injective (rowAnnulus hn x) := by
    intro a b h
    simpa using congrArg (fun D : GridRectangleDecomposition x x => D.first.bottom) h
  rw [emptyDecompositions_self hn x, Finset.sum_union hdisjoint,
    Finset.sum_image (fun a _ b _ h => hc h), Finset.sum_image (fun a _ b _ h => hr h)]
  simp only [columnAnnulus_weight, rowAnnulus_weight]
  congr 1
  exact Equiv.sum_comp G.O.toPerm.symm (fun c => MvPolynomial.X c)

/-- Annular contributions cancel in characteristic two without excluding X markings. -/
theorem sum_emptyDecompositionWeight_self_eq_zero [CharP R 2] (x : GridState n) :
    ∑ D ∈ emptyDecompositions x x, G.unblockedDecompositionWeight R D = 0 := by
  by_cases hn : 1 < n
  · rw [sum_emptyDecompositionWeight_self G R hn]
    exact CharTwo.add_self_eq_zero _
  · apply Finset.sum_eq_zero
    intro D _
    have hcard : 1 < Fintype.card (Fin n) :=
      Fintype.one_lt_card_iff.mpr ⟨D.first.left, D.first.right, D.first.left_ne_right⟩
    exact (hn (by simpa using hcard)).elim

end OnLeConjecture.KnotFloer.GridFull
