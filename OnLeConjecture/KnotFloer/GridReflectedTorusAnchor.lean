/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusBasic
public import OnLeConjecture.KnotFloer.GridFullLaurentMaslov

/-!
# Maslov grading of the reflected torus anchor

The reflected diagonal corner state has Maslov degree zero. The proof
evaluates the four finite counts in the grading formula. This is the
grading needed for the two proposed normalized torus representatives.
Nonvanishing of its homology class is a separate obligation.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

theorem reflectedTorusAnchor_val (n : ℕ) (c : Fin (consecutiveTorusGridSize n)) :
    (reflectedTorusAnchor n c : ℕ) =
      if c = 0 then 0 else consecutiveTorusGridSize n - c.val := by
  rw [reflectedTorusAnchor_apply]
  change (finRotate (n + 1 + (n + 1) + 1) c.rev : ℕ) = _
  rw [coe_finRotate]
  simp only [Fin.ext_iff, Fin.val_last, Fin.val_rev, Fin.val_zero]
  have hc := c.isLt
  unfold consecutiveTorusGridSize at *
  split_ifs <;> omega

/-- The anchor is in the absolute Maslov degree used for the distinguished
knot class. This statement alone does not prove that its class is nonzero. -/
theorem maslovO_reflectedTorusAnchor (n : ℕ) :
    (reflectedTorusGrid n).maslovOℤ (reflectedTorusAnchor n) = 0 := by
  classical
  let N := consecutiveTorusGridSize n
  let x := reflectedTorusAnchor n
  let G := reflectedTorusGrid n
  have hz : (0 : Fin N).val = 0 := rfl
  have hxx : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1 < p.2 ∧ x p.1 < x p.2) =
      ({0} : Finset (Fin N)) ×ˢ (Finset.univ.erase 0) := by
    ext p
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_erase, and_true, Fin.lt_def, x,
      reflectedTorusAnchor_val, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hxO : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1 ≤ p.2 ∧ x p.1 ≤ G.O p.2) =
      ({0} : Finset (Fin N)) ×ˢ Finset.univ := by
    ext p
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true, Fin.le_def, x, G,
      reflectedTorusAnchor_val, reflectedTorusGrid_O_apply, Fin.val_rev,
      Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hOx : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1 < p.2 ∧ G.O p.1 < x p.2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p _
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [Fin.lt_def, x, G, reflectedTorusAnchor_val,
      reflectedTorusGrid_O_apply, Fin.val_rev, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> omega
  have hOO : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1 < p.2 ∧ G.O p.1 < G.O p.2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p _
    have ha := p.1.isLt
    have hb := p.2.isLt
    simp only [Fin.lt_def, G, reflectedTorusGrid_O_apply, Fin.val_rev]
    omega
  change G.maslovOℤ x = 0
  rw [GridDiagram.maslovOℤ_eq_card, hxx, hxO, hOx, hOO]
  simp only [Finset.card_product, Finset.card_singleton, one_mul,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin N)),
    Finset.card_univ, Fintype.card_fin, Finset.card_empty]
  have hN : 0 < N := by dsimp [N, consecutiveTorusGridSize]; omega
  omega

/-- The actual Laurent cycle is a degree-zero chain. -/
theorem reflectedTorusAnchor_mem_maslovPiece (n : ℕ) (R : Type*) [CommSemiring R] :
    (Finsupp.single (reflectedTorusAnchor n) 1 : LaurentChain R (consecutiveTorusGridSize n)) ∈
      laurentMaslovPiece (reflectedTorusGrid n) R 0 := by
  simpa only [laurentMaslovDegree_zero, maslovO_reflectedTorusAnchor,
    laurentMonomialGenerator, LaurentPolynomial.T_zero] using
    laurentMonomialGenerator_mem_laurentMaslovPiece
      (reflectedTorusGrid n) R 0 (reflectedTorusAnchor n)

end OnLeConjecture.KnotFloer.GridFull
