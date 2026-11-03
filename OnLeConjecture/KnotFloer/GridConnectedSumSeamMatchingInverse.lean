/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamBlockFreeOrder
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite matrix inversion for the complementary-state matching

The concrete rectangle order excludes every alternating cycle. The
number of strict predecessors then bounds every internal path, yielding
nilpotence at the number of complementary pairs. A finite geometric
series is proved to be a two-sided inverse of the normalized full matrix.
No filtered contraction or transferred tensor identification is asserted.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n m : ℕ}

instance seamMatchingSourceFintype : Fintype (SeamMatchingSource n m) :=
  Fintype.ofFinite _

/-- Subtracting the diagonal preserves the source-grading exponent constraint. -/
theorem seamMatchingTransitionMatrix_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingTransitionMatrix G H hG hH R y x).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ y.val.val -
      (connectedSumSeamGrid G H hG hH).maslovOℤ x.val.val := by
  by_cases hxy : x = y
  · subst y
    rw [seamMatchingTransitionMatrix_diag] at hj
    simp at hj
  · rw [seamMatchingTransitionMatrix_offDiag G H hG hH R x y hxy] at hj
    exact seamMatchingMatrix_support_maslov G H hG hH R x y hj

/-- Exponents telescope along every nonzero coefficient of an actual matrix power. -/
theorem seamMatchingTransitionMatrix_pow_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (k : ℕ) (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ ((seamMatchingTransitionMatrix G H hG hH R ^ k) y x).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ y.val.val -
      (connectedSumSeamGrid G H hG hH).maslovOℤ x.val.val := by
  classical
  induction k generalizing x y j with
  | zero =>
    by_cases hxy : y = x
    · subst y
      simp only [pow_zero, Matrix.one_apply_eq] at hj
      have hh : j ∈ (Finsupp.single (0 : ℤ) (1 : R)).support := hj
      have hj0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      subst j
      simp
    · simp [pow_zero, hxy] at hj
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, AddMonoidAlgebra.coeff_sum] at hj
    obtain ⟨z, hz, hjz⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hjz)
    have hp := ih z y ha
    have he := seamMatchingTransitionMatrix_support_maslov G H hG hH R x z hb
    omega


private theorem matrix_pow_entry_zero_of_rank {α S : Type*}
    [Fintype α] [DecidableEq α] [Semiring S] (A : Matrix α α S)
    (rank : α → ℕ) (hA : ∀ x y, A y x ≠ 0 → rank x < rank y) :
    ∀ (k : ℕ) (x y : α), rank y < rank x + k → (A ^ k) y x = 0 := by
  intro k
  induction k with
  | zero =>
    intro x y h
    have hxy : y ≠ x := by rintro rfl; omega
    simp [hxy]
  | succ k ih =>
    intro x y h
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hzx : A z x = 0
    · simp [hzx]
    · have hr := hA x z hzx
      rw [ih z y (by omega), zero_mul]

private theorem matrix_pow_card_zero_of_rank {α S : Type*}
    [Fintype α] [DecidableEq α] [Semiring S] (A : Matrix α α S)
    (rank : α → ℕ) (hA : ∀ x y, A y x ≠ 0 → rank x < rank y)
    (hbound : ∀ x, rank x < Fintype.card α) : A ^ Fintype.card α = 0 := by
  ext y x
  exact matrix_pow_entry_zero_of_rank A rank hA _ x y (by have := hbound y; omega)

private def matchingLex (x y : SeamMatchingSource n m) : Prop :=
  (x.val.val (seamComplementFirst x.val)).val <
      (y.val.val (seamComplementFirst y.val)).val ∨
    ((x.val.val (seamComplementFirst x.val)).val =
        (y.val.val (seamComplementFirst y.val)).val ∧
      (seamComplementFirst y.val).val < (seamComplementFirst x.val).val)

private theorem matchingLex_trans {x y z : SeamMatchingSource n m}
    (hxy : matchingLex x y) (hyz : matchingLex y z) : matchingLex x z := by
  unfold matchingLex at *
  omega

private theorem matchingLex_irrefl (x : SeamMatchingSource n m) : ¬ matchingLex x x := by
  unfold matchingLex
  omega

private theorem matchingTransGen_lex_of_return
    (horder : ∀ x y : SeamMatchingSource n m, SeamMatchingStep x y →
      Relation.ReflTransGen SeamMatchingStep y x → matchingLex x y)
    {x y : SeamMatchingSource n m} (hp : Relation.TransGen SeamMatchingStep x y)
    (hret : Relation.ReflTransGen SeamMatchingStep y x) : matchingLex x y := by
  revert hret
  induction hp with
  | single h => exact horder _ _ h
  | @tail z y hp hzy ih =>
    intro hret
    have hxz := ih ((Relation.ReflTransGen.single hzy).trans hret)
    have hzy' := horder _ _ hzy (hret.trans hp.to_reflTransGen)
    exact matchingLex_trans hxz hzy'

private theorem matching_no_cycle_of_return_order
    (horder : ∀ x y : SeamMatchingSource n m, SeamMatchingStep x y →
      Relation.ReflTransGen SeamMatchingStep y x → matchingLex x y)
    (x : SeamMatchingSource n m) : ¬ Relation.TransGen SeamMatchingStep x x := by
  intro hp
  exact matchingLex_irrefl x (matchingTransGen_lex_of_return horder hp .refl)

/-- The number of strict predecessors under actual empty-rectangle matching paths. -/
def seamMatchingRank (x : SeamMatchingSource n m) : ℕ := by
  classical
  exact (Finset.univ.filter fun y => Relation.TransGen SeamMatchingStep y x).card

private theorem seamMatchingRank_lt_card_of_no_cycle
    (hcycle : ∀ x : SeamMatchingSource n m, ¬ Relation.TransGen SeamMatchingStep x x)
    (x : SeamMatchingSource n m) : seamMatchingRank x < Fintype.card (SeamMatchingSource n m) := by
  classical
  rw [seamMatchingRank, ← Finset.card_univ]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hx : x ∈ Finset.univ.filter fun y => Relation.TransGen SeamMatchingStep y x := by
    rw [he]
    exact Finset.mem_univ x
  exact hcycle x (Finset.mem_filter.mp hx).2

private theorem seamMatchingRank_step_lt_of_no_cycle
    (hcycle : ∀ x : SeamMatchingSource n m, ¬ Relation.TransGen SeamMatchingStep x x)
    {x y : SeamMatchingSource n m} (hxy : SeamMatchingStep x y) :
    seamMatchingRank x < seamMatchingRank y := by
  classical
  unfold seamMatchingRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.tail hxy⟩
  · intro he
    have hx : x ∈ Finset.univ.filter fun z => Relation.TransGen SeamMatchingStep z y :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, Relation.TransGen.single hxy⟩
    rw [← he] at hx
    exact hcycle x (Finset.mem_filter.mp hx).2

private theorem seamMatchingTransitionMatrix_pow_card_zero_of_no_cycle
    (hcycle : ∀ x : SeamMatchingSource n m, ¬ Relation.TransGen SeamMatchingStep x x)
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingTransitionMatrix G H hG hH R ^ Fintype.card (SeamMatchingSource n m) = 0 := by
  classical
  apply matrix_pow_card_zero_of_rank _ seamMatchingRank
  · intro x y h
    exact seamMatchingRank_step_lt_of_no_cycle hcycle
      (seamMatchingStep_of_transition_ne_zero G H hG hH R x y h)
  · exact seamMatchingRank_lt_card_of_no_cycle hcycle

/-- The finite geometric series of the normalized off-diagonal matrix. -/
def seamMatchingMatrixInverse
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (LaurentPolynomial R) :=
  ∑ j ∈ Finset.range (Fintype.card (SeamMatchingSource n m)),
    (-seamMatchingTransitionMatrix G H hG hH R) ^ j

/-- Restoring the unit diagonal recovers the full normalized matrix. -/
theorem one_add_seamMatchingTransitionMatrix
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    1 + seamMatchingTransitionMatrix G H hG hH R = seamMatchingMatrix G H hG hH R := by
  unfold seamMatchingTransitionMatrix
  abel

private theorem seamMatchingMatrix_mul_inverse_of_no_cycle
    (hcycle : ∀ x : SeamMatchingSource n m, ¬ Relation.TransGen SeamMatchingStep x x)
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingMatrix G H hG hH R * seamMatchingMatrixInverse G H hG hH R = 1 := by
  have h := mul_neg_geom_sum (-seamMatchingTransitionMatrix G H hG hH R)
    (Fintype.card (SeamMatchingSource n m))
  rw [sub_neg_eq_add, one_add_seamMatchingTransitionMatrix,
    neg_pow, seamMatchingTransitionMatrix_pow_card_zero_of_no_cycle hcycle,
    mul_zero, sub_zero] at h
  exact h

private theorem seamMatchingMatrix_inverse_mul_of_no_cycle
    (hcycle : ∀ x : SeamMatchingSource n m, ¬ Relation.TransGen SeamMatchingStep x x)
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingMatrixInverse G H hG hH R * seamMatchingMatrix G H hG hH R = 1 := by
  have h := geom_sum_mul_neg (-seamMatchingTransitionMatrix G H hG hH R)
    (Fintype.card (SeamMatchingSource n m))
  rw [sub_neg_eq_add, one_add_seamMatchingTransitionMatrix,
    neg_pow, seamMatchingTransitionMatrix_pow_card_zero_of_no_cycle hcycle,
    mul_zero, sub_zero] at h
  exact h

/-- Every term of the finite inverse has the same source-grading exponent constraint. -/
theorem seamMatchingMatrixInverse_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (x y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (seamMatchingMatrixInverse G H hG hH R y x).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ y.val.val -
      (connectedSumSeamGrid G H hG hH).maslovOℤ x.val.val := by
  classical
  rw [seamMatchingMatrixInverse, Matrix.sum_apply, AddMonoidAlgebra.coeff_sum] at hj
  obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_pow] at hjk
    exact seamMatchingTransitionMatrix_pow_support_maslov G H hG hH R k x y hjk
  · rw [ho.neg_pow, Matrix.neg_apply, AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] at hjk
    exact seamMatchingTransitionMatrix_pow_support_maslov G H hG hH R k x y hjk

/-- No nonempty alternating path of full empty rectangles returns to its source. -/
theorem seamMatchingStep_no_cycle (x : SeamMatchingSource n m) :
    ¬ Relation.TransGen SeamMatchingStep x x := by
  apply matching_no_cycle_of_return_order
  intro a b h hp
  obtain ⟨hne, r, hr⟩ := h
  exact seamMatchingRectangle_blockFree_order hne r hr
    (seamMatchingRectangle_blockFree_of_return_path a b r hr hp)

/-- The actual finite predecessor rank strictly increases along every nonmatching rectangle step. -/
theorem seamMatchingRank_step_lt {x y : SeamMatchingSource n m} (h : SeamMatchingStep x y) :
    seamMatchingRank x < seamMatchingRank y :=
  seamMatchingRank_step_lt_of_no_cycle seamMatchingStep_no_cycle h

/-- The rank is bounded by the number of complementary pairs. -/
theorem seamMatchingRank_lt_card (x : SeamMatchingSource n m) :
    seamMatchingRank x < Fintype.card (SeamMatchingSource n m) :=
  seamMatchingRank_lt_card_of_no_cycle seamMatchingStep_no_cycle x

/-- The actual normalized off-diagonal matrix vanishes at this explicit finite power. -/
theorem seamMatchingTransitionMatrix_pow_card_eq_zero
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingTransitionMatrix G H hG hH R ^ Fintype.card (SeamMatchingSource n m) = 0 :=
  seamMatchingTransitionMatrix_pow_card_zero_of_no_cycle seamMatchingStep_no_cycle
    G H hG hH R

/-- The normalized full matching matrix times its constructed finite inverse is one. -/
theorem seamMatchingMatrix_mul_inverse
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingMatrix G H hG hH R * seamMatchingMatrixInverse G H hG hH R = 1 :=
  seamMatchingMatrix_mul_inverse_of_no_cycle seamMatchingStep_no_cycle G H hG hH R

/-- The same finite formula is a left inverse of the actual normalized full matching matrix. -/
theorem seamMatchingMatrix_inverse_mul
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamMatchingMatrixInverse G H hG hH R * seamMatchingMatrix G H hG hH R = 1 :=
  seamMatchingMatrix_inverse_mul_of_no_cycle seamMatchingStep_no_cycle G H hG hH R

/-- Invertibility is a consequence of the full rectangle matching, with no matrix hypothesis. -/
theorem isUnit_seamMatchingMatrix
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] : IsUnit (seamMatchingMatrix G H hG hH R) := by
  exact ⟨⟨seamMatchingMatrix G H hG hH R, seamMatchingMatrixInverse G H hG hH R,
    seamMatchingMatrix_mul_inverse G H hG hH R,
    seamMatchingMatrix_inverse_mul G H hG hH R⟩, rfl⟩

end OnLeConjecture.KnotFloer.GridFull
