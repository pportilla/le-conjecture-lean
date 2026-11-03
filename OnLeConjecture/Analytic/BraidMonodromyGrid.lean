/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyHomotopy

/-!
# The boundary of a grid as a product of conjugated cell loops

This module proves the topological core of the global factorization of Section 3 of the written
proof of Statement E (`statement-E-complete-proof.tex`, subsection "Global factorization,
exponent count, and transitivity"), on a square grid instead of a triangulated cut disc.

Consider an `n × n` grid with vertices `(a, b)`, `0 ≤ a, b ≤ n`. A word `h a b` is attached to the
horizontal edge from `(a, b)` to `(a + 1, b)` and a word `v a b` to the vertical edge from `(a, b)`
to `(a, b + 1)`. The loop of the cell `(a, b)` is `ℓ_{ab} = h_{ab} v_{a+1,b} h_{a,b+1}⁻¹ v_{ab}⁻¹`,
read counterclockwise from its lower left corner (`cellLoop`). The boundary word reads the bottom
row, the right column, the top row backwards and the left column backwards (`boundaryWord`).

* `boundaryWord_equiv_gridProduct`: the boundary word is equivalent, by free cancellation only,
  to the product over the rows `b = 0, …, n - 1` and, within a row, over `a = n - 1, …, 0` of the
  conjugates `γ_{ab} ℓ_{ab} γ_{ab}⁻¹`, where `γ_{ab}` is the word of the grid path from `(0, 0)` up
  the left column to `(0, b)` and along the row to `(a, b)` (`cellConjugator`).
* `boundaryWord_equiv_markedProduct`: if every unmarked cell satisfies the cell relation
  `h_{ab} v_{a+1,b} ≡ v_{ab} h_{a,b+1}`, the unmarked factors can be dropped.
* `cellRelation_of_rectangle`: the cell relation holds when the four edge words are the path
  words of the four sides of a jointly continuous family of configurations of distinct points
  over the cell (`isPathWord_homotopy`).

For a family of configurations over a square base with finitely many marked cells around the
critical values, the boundary word of the base is thus a product of conjugates of the loops
around the marked cells. The grid paths play the role of the cut system of the written proof.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ} (h v : ℕ → ℕ → SignedAdjacentWord S)

/-- The word of the row `b` from `(0, b)` to `(a, b)`. -/
def rowWord (b a : ℕ) : SignedAdjacentWord S := (List.range a).flatMap fun a' => h a' b

/-- The word of the column `a` from `(a, 0)` to `(a, b)`. -/
def colWord (a b : ℕ) : SignedAdjacentWord S := (List.range b).flatMap fun b' => v a b'

/-- The loop of the cell `(a, b)`, counterclockwise from its lower left corner. -/
def cellLoop (a b : ℕ) : SignedAdjacentWord S :=
  h a b ++ v (a + 1) b ++ inv (h a (b + 1)) ++ inv (v a b)

/-- The word of the grid path from `(0, 0)` to the corner `(a, b)` of a cell. -/
def cellConjugator (a b : ℕ) : SignedAdjacentWord S := colWord v 0 b ++ rowWord h b a

/-- The boundary word of the `n × n` grid, counterclockwise from `(0, 0)`. -/
def boundaryWord (n : ℕ) : SignedAdjacentWord S :=
  rowWord h 0 n ++ colWord v n n ++ inv (rowWord h n n) ++ inv (colWord v 0 n)

/-- The conjugated cell loops of the row `b`, for the cells `a' < a`, in decreasing order. -/
def rowProduct (b a : ℕ) : SignedAdjacentWord S :=
  (List.range a).reverse.flatMap fun a' => conjugateWord (rowWord h b a') (cellLoop h v a' b)

/-- The product of the conjugated cell loops of the rows `b' < b`. -/
def gridProduct (n b : ℕ) : SignedAdjacentWord S :=
  (List.range b).flatMap fun b' => conjugateWord (colWord v 0 b') (rowProduct h v b' n)

theorem rowWord_succ (b a : ℕ) : rowWord h b (a + 1) = rowWord h b a ++ h a b := by
  simp [rowWord, List.range_succ]

theorem colWord_succ (a b : ℕ) : colWord v a (b + 1) = colWord v a b ++ v a b := by
  simp [colWord, List.range_succ]

theorem rowProduct_succ (b a : ℕ) : rowProduct h v b (a + 1) =
    conjugateWord (rowWord h b a) (cellLoop h v a b) ++ rowProduct h v b a := by
  simp [rowProduct, List.range_succ]

theorem gridProduct_succ (n b : ℕ) : gridProduct h v n (b + 1) =
    gridProduct h v n b ++ conjugateWord (colWord v 0 b) (rowProduct h v b n) := by
  simp [gridProduct, List.range_succ]

/-- The cell loop absorbs the difference of the two paths around a cell. -/
theorem cell_split (a b : ℕ) :
    SignedBraidEquiv (h a b ++ v (a + 1) b) (cellLoop h v a b ++ v a b ++ h a (b + 1)) := by
  have h1 := SignedBraidEquiv.cancel_inv_mid' (h a b ++ v (a + 1) b ++ inv (h a (b + 1)))
    (v a b) (h a (b + 1))
  have h2 := SignedBraidEquiv.cancel_inv_mid' (h a b ++ v (a + 1) b) (h a (b + 1)) []
  simp only [List.append_nil, List.append_assoc] at h1 h2
  simp only [cellLoop, List.append_assoc]
  exact (h1.trans h2).symm

/-- Moving a word `x` across a prefix `p`: `p x ≡ (p x p⁻¹) p`. -/
theorem conj_split (p x y : SignedAdjacentWord S) :
    SignedBraidEquiv (p ++ x ++ y) (conjugateWord p x ++ p ++ y) := by
  have := SignedBraidEquiv.cancel_inv_mid' (p ++ x) p y
  simp only [conjugateWord, List.append_assoc] at this ⊢
  exact this.symm

/-- The row relation: along the row `b`, the lower path followed by the vertical edge at `a` is
the conjugated cell loops followed by the left edge and the upper path. -/
theorem row_relation (b : ℕ) : ∀ a, SignedBraidEquiv (rowWord h b a ++ v a b)
    (rowProduct h v b a ++ v 0 b ++ rowWord h (b + 1) a) := by
  intro a
  induction a with
  | zero => simpa [rowWord, rowProduct] using SignedBraidEquiv.refl (v 0 b)
  | succ a ih =>
    rw [rowWord_succ, List.append_assoc]
    have h1 := (SignedBraidEquiv.refl (rowWord h b a)).append (cell_split h v a b)
    refine h1.trans ?_
    have h2 := conj_split (rowWord h b a) (cellLoop h v a b) (v a b ++ h a (b + 1))
    simp only [List.append_assoc] at h2 ⊢
    refine h2.trans ?_
    have h3 := (SignedBraidEquiv.refl (conjugateWord (rowWord h b a) (cellLoop h v a b))).append
      (ih.append (SignedBraidEquiv.refl [] |>.append (SignedBraidEquiv.refl (h a (b + 1)))))
    simp only [List.append_assoc, List.nil_append] at h3
    refine h3.trans (SignedBraidEquiv.of_eq ?_)
    rw [rowProduct_succ, rowWord_succ]
    simp [List.append_assoc]

/-- The column relation over the rows `b' < b`. -/
theorem column_relation (n : ℕ) : ∀ b, SignedBraidEquiv (rowWord h 0 n ++ colWord v n b)
    (gridProduct h v n b ++ colWord v 0 b ++ rowWord h b n) := by
  intro b
  induction b with
  | zero => simpa [colWord, gridProduct] using SignedBraidEquiv.refl (rowWord h 0 n)
  | succ b ih =>
    rw [colWord_succ, ← List.append_assoc]
    have h1 := ih.append (SignedBraidEquiv.refl (v n b))
    refine h1.trans ?_
    have h2 := (SignedBraidEquiv.refl (gridProduct h v n b ++ colWord v 0 b)).append
      (row_relation h v b n)
    simp only [List.append_assoc] at h1 h2 ⊢
    refine h2.trans ?_
    have h3 := conj_split (colWord v 0 b) (rowProduct h v b n) (v 0 b ++ rowWord h (b + 1) n)
    have h4 := (SignedBraidEquiv.refl (gridProduct h v n b)).append h3
    simp only [List.append_assoc] at h4
    refine h4.trans (SignedBraidEquiv.of_eq ?_)
    rw [gridProduct_succ, colWord_succ]
    simp [List.append_assoc]

/-- **The boundary of the grid** is the product of the conjugated cell loops. -/
theorem boundaryWord_equiv_gridProduct (n : ℕ) :
    SignedBraidEquiv (boundaryWord h v n) (gridProduct h v n n) := by
  have h1 := (column_relation h v n n).append
    (SignedBraidEquiv.refl (inv (rowWord h n n) ++ inv (colWord v 0 n)))
  have h2 := SignedBraidEquiv.cancel_inv_mid (gridProduct h v n n ++ colWord v 0 n)
    (rowWord h n n) (inv (colWord v 0 n))
  have h3 := SignedBraidEquiv.cancel_inv_mid (gridProduct h v n n) (colWord v 0 n) []
  simp only [boundaryWord, List.append_assoc, List.append_nil] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

/-- Conjugation distributes over products. -/
theorem conjugateWord_append (c x y : SignedAdjacentWord S) :
    SignedBraidEquiv (conjugateWord c (x ++ y)) (conjugateWord c x ++ conjugateWord c y) := by
  have := SignedBraidEquiv.cancel_inv_mid' (c ++ x) c (y ++ inv c)
  simp only [conjugateWord, List.append_assoc] at this ⊢
  exact this.symm

theorem conjugateWord_conjugateWord (c p x : SignedAdjacentWord S) :
    conjugateWord c (conjugateWord p x) = conjugateWord (c ++ p) x := by
  simp [conjugateWord, inv_append, List.append_assoc]

theorem conjugateWord_flatMap {α : Type*} (c : SignedAdjacentWord S)
    (f : α → SignedAdjacentWord S) :
    ∀ l : List α, SignedBraidEquiv (conjugateWord c (l.flatMap f))
      ((l.flatMap fun x => conjugateWord c (f x)))
  | [] => by simpa [conjugateWord] using SignedBraidEquiv.append_inv_self c
  | x :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (conjugateWord_append c (f x) (l.flatMap f)).trans
      ((SignedBraidEquiv.refl _).append (conjugateWord_flatMap c f l))

theorem flatMap_equiv_of_mem {α : Type*} {f g : α → SignedAdjacentWord S} :
    ∀ {l : List α}, (∀ x ∈ l, SignedBraidEquiv (f x) (g x)) →
      SignedBraidEquiv (l.flatMap f) (l.flatMap g)
  | [], _ => SignedBraidEquiv.refl _
  | x :: l, hfg => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (hfg x (List.mem_cons_self ..)).append
      (flatMap_equiv_of_mem fun y hy => hfg y (List.mem_cons_of_mem _ hy))

/-- **Marked cells.** If every unmarked cell `(a, b)`, `a, b < n`, satisfies the cell relation
`h_{ab} v_{a+1,b} ≡ v_{ab} h_{a,b+1}`, the boundary word of the grid is equivalent to the product,
over the rows `b = 0, …, n - 1` and within a row over `a = n - 1, …, 0`, of the conjugates
`γ_{ab} ℓ_{ab} γ_{ab}⁻¹` of the loops of the marked cells. -/
theorem boundaryWord_equiv_markedProduct (n : ℕ) (marked : ℕ → ℕ → Prop) [DecidableRel marked]
    (hcell : ∀ a < n, ∀ b < n, ¬ marked a b →
      SignedBraidEquiv (h a b ++ v (a + 1) b) (v a b ++ h a (b + 1))) :
    SignedBraidEquiv (boundaryWord h v n)
      ((List.range n).flatMap fun b => (List.range n).reverse.flatMap fun a =>
        if marked a b then conjugateWord (cellConjugator h v a b) (cellLoop h v a b) else []) := by
  refine (boundaryWord_equiv_gridProduct h v n).trans ?_
  unfold gridProduct
  refine flatMap_equiv_of_mem (fun b hb => ?_)
  unfold rowProduct
  refine (conjugateWord_flatMap _ _ _).trans (flatMap_equiv_of_mem fun a ha => ?_)
  have ha' : a < n := by simpa using ha
  have hb' : b < n := by simpa using hb
  rw [conjugateWord_conjugateWord]
  by_cases hm : marked a b
  · rw [if_pos hm]; exact SignedBraidEquiv.refl _
  · rw [if_neg hm]
    -- The loop of an unmarked cell is trivial.
    have hl : SignedBraidEquiv (cellLoop h v a b) [] := by
      have h1 := (cell_split h v a b).symm.trans (hcell a ha' b hb' hm)
      have h2 := h1.append (SignedBraidEquiv.refl (inv (h a (b + 1)) ++ inv (v a b)))
      have c1 := SignedBraidEquiv.cancel_inv_mid (cellLoop h v a b ++ v a b) (h a (b + 1))
        (inv (v a b))
      have c2 := SignedBraidEquiv.cancel_inv_mid (cellLoop h v a b) (v a b) []
      have c3 := SignedBraidEquiv.cancel_inv_mid (v a b) (h a (b + 1)) (inv (v a b))
      have c4 := SignedBraidEquiv.append_inv_self (v a b)
      simp only [List.append_assoc, List.append_nil] at h2 c1 c2 c3 c4
      exact ((c1.trans c2).symm.trans h2).trans (c3.trans c4)
    set c := colWord v 0 b ++ rowWord h b a
    have h5 := (SignedBraidEquiv.refl c).append (hl.append (SignedBraidEquiv.refl (inv c)))
    simp only [List.nil_append] at h5
    simpa [conjugateWord, List.append_assoc] using h5.trans (SignedBraidEquiv.append_inv_self c)

/-- **The cell relation from a family of configurations over the cell.** If the configurations
`H s · t` over the cell, `(s, t) ∈ [0, 1] × [u, w]`, are jointly continuous with distinct points,
and the four edge words are path words of the four sides (bottom `H 0`, top `H 1`, left
`s ↦ H s · u`, right `s ↦ H s · w`), then `bottom · right ≡ left · top`. -/
theorem cellRelation_of_rectangle {H : ℝ → Fin S → ℝ → ℂ} {u w : ℝ} (huw : u < w)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H p.1 k p.2) (Icc 0 1 ×ˢ Icc u w))
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u w, Injective fun k => H s k t)
    {bottom top left right : SignedAdjacentWord S}
    (hb : IsPathWord (H 0) u w bottom) (ht : IsPathWord (H 1) u w top)
    (hl : IsPathWord (fun k s => H s k u) 0 1 left)
    (hr : IsPathWord (fun k s => H s k w) 0 1 right) :
    SignedBraidEquiv (bottom ++ right) (left ++ top) :=
  isPathWord_homotopy huw hcont hinj hb ht hl hr

end OnLeConjecture.Analytic
