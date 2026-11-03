/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: Pablo Portilla Cuadrado, The Tau Ceti contributors
-/
module

public import OnLeConjecture.KnotFloer.GridFullReflection
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Explicit full Laurent cycles from reflected cyclic states

Every oriented rectangle into a cyclic-shift state is empty. The two rectangles
between any fixed distinct states have the same O count, by the Maslov grading
formula. Their Laurent weights therefore cancel in characteristic two.
The reflection correspondence turns this vanishing column of the differential
into a genuine cycle in the reflected diagram's full Laurent complex.

The emptiness proof generalizes the cyclic-shift marking-state proof in
TauCeti's `KnotTheory/Grid/Unblocked.lean`, commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, under Apache 2.0.
The result applies to the shifted diagonal states occurring in the torus-grid
family. It does not prove that these cycles represent nonzero homology classes
or identify the complex with a staircase.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable {n : ℕ}

/-- Every rectangle into a cyclic-shift state has empty interior. -/
theorem isEmpty_of_target_toPerm_eq_finRotate_pow {x y : GridState n} {k : ℕ}
    (hy : y.toPerm = finRotate n ^ k) (r : GridRectangleBetween x y) : r.IsEmpty := by
  rw [isEmpty_iff_forall_notMem_cIoo_target]
  intro c hc hcy
  rw [hy, Grid.mem_cIoo_finRotate_pow_finRotate_pow] at hcy
  exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap r.left r.right) hc hcy

/-- Hence the empty-rectangle collection into a cyclic-shift state is the whole collection. -/
theorem emptyRectangles_eq_univ_of_target_cyclic {x y : GridState n} {k : ℕ}
    (hy : y.toPerm = finRotate n ^ k) : emptyRectangles x y = Finset.univ := by
  ext r
  simp only [mem_emptyRectangles, Finset.mem_univ, iff_true]
  exact isEmpty_of_target_toPerm_eq_finRotate_pow hy r

/-- The Maslov formula determines the O count of an empty rectangle from its endpoints. -/
theorem card_OColumns_eq_of_isEmpty (G : GridDiagram n) {x y : GridState n}
    (r s : GridRectangleBetween x y) (hr : r.IsEmpty) (hs : s.IsEmpty) :
    (G.OColumns r.toGridRectangle).card = (G.OColumns s.toGridRectangle).card := by
  have h₁ := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  have h₂ := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hs
  have h : ((G.OColumns r.toGridRectangle).card : ℚ) =
      ((G.OColumns s.toGridRectangle).card : ℚ) := by linarith
  exact_mod_cast h

/-- All full Laurent coefficients into a cyclic-shift state vanish by paired cancellation. -/
theorem laurentCoefficient_eq_zero_of_target_cyclic (G : GridDiagram n)
    (R : Type*) [CommSemiring R] [CharP R 2] {x y : GridState n} {k : ℕ}
    (hy : y.toPerm = finRotate n ^ k) : laurentCoefficient G R x y = 0 := by
  classical
  rw [laurentCoefficient_eq, emptyRectangles_eq_univ_of_target_cyclic hy]
  rcases isEmpty_or_nonempty (GridRectangleBetween x y) with h | h
  · simp
  · obtain ⟨r⟩ := h
    let : Nonempty (GridRectangleBetween x y) := ⟨r⟩
    have hcount (s : GridRectangleBetween x y) :
        (G.OColumns s.toGridRectangle).card = (G.OColumns r.toGridRectangle).card :=
      card_OColumns_eq_of_isEmpty G s r
        (isEmpty_of_target_toPerm_eq_finRotate_pow hy s)
        (isEmpty_of_target_toPerm_eq_finRotate_pow hy r)
    simp_rw [hcount]
    rw [Finset.sum_const, Finset.card_univ, card_eq_two_of_nonempty, two_nsmul]
    ext j
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero,
      Finsupp.add_apply, Finsupp.zero_apply, CharTwo.add_self_eq_zero]

/-- Reflection of any cyclic-shift state is a cycle of the actual full Laurent differential. -/
theorem laurentDifferential_reflected_cyclic_state (G : GridDiagram n)
    (R : Type*) [CommSemiring R] [CharP R 2] {y : GridState n} {k : ℕ}
    (hy : y.toPerm = finRotate n ^ k) :
    laurentDifferential (reflectedDiagram G) R (Finsupp.single (reflectedState y) 1) = 0 := by
  apply Finsupp.ext
  intro x
  rw [laurentDifferential_single, laurentOnGenerator_apply, Finsupp.zero_apply]
  rw [← reflectedState_reflectedState x, laurentCoefficient_reflectedDiagram]
  exact laurentCoefficient_eq_zero_of_target_cyclic G R hy

end OnLeConjecture.KnotFloer.GridFull
