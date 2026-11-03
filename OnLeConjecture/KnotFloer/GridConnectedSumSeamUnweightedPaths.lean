/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSpecialization
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamEntryExit
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod

/-!
# The finite unweighted paths in the seam Schur coefficient

Internal steps retain actual empty rectangles. The predecessor rank bounds
their length. Specialization at U=1 counts these finite choices over F₂,
independently of every marking permutation.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
open scoped BigOperators
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable

/-- An internal edge includes its actual nonmatching empty rectangle. -/
abbrev SeamInternalRectangle (x y : SeamMatchingSource n m) :=
  {r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val //
    x ≠ y ∧ r.IsEmpty}

private theorem card_emptyRectangles {k : ℕ} (x y : GridState k) :
    Fintype.card {r : GridRectangleBetween x y // r.IsEmpty} = (emptyRectangles x y).card := by
  classical
  exact Fintype.card_of_subtype _ fun r => mem_emptyRectangles r

theorem card_seamInternalRectangle (x y : SeamMatchingSource n m) :
    Fintype.card (SeamInternalRectangle x y) =
      if x = y then 0 else (emptyRectangles x.val.val (seamComplementPartner y.val).val).card := by
  classical
  by_cases h : x = y
  · subst y
    simp only [SeamInternalRectangle, Fintype.card_subtype, ne_eq, not_true_eq_false,
      false_and, Finset.filter_false, Finset.card_empty, ite_true]
  · rw [if_neg h, ← card_emptyRectangles]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight fun r => by simp [h]

/-- The unweighted internal matrix depends only on the state rectangles. -/
def seamUnweightedTransition :
    Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (ZMod 2) :=
  fun y x => Fintype.card (SeamInternalRectangle x y)

/-- A path of fixed length consists of the chosen empty rectangles, not just their endpoints. -/
def SeamInternalPath : ℕ → SeamMatchingSource n m → SeamMatchingSource n m → Type
  | 0, x, y => {_u : Unit // x = y}
  | k + 1, x, y => Σ z : SeamMatchingSource n m,
      SeamInternalRectangle x z × SeamInternalPath k z y

instance seamInternalPathFintype (k : ℕ) (x y : SeamMatchingSource n m) :
    Fintype (SeamInternalPath k x y) := by
  classical
  induction k generalizing x y with
  | zero => exact inferInstanceAs (Fintype {_u : Unit // x = y})
  | succ k ih =>
    letI (a b : SeamMatchingSource n m) : Fintype (SeamInternalPath k a b) := ih a b
    exact inferInstanceAs (Fintype (Σ z : SeamMatchingSource n m,
      SeamInternalRectangle x z × SeamInternalPath k z y))

theorem seamInternalPath_rank {k : ℕ} {x y : SeamMatchingSource n m}
    (p : SeamInternalPath k x y) : seamMatchingRank x + k ≤ seamMatchingRank y := by
  induction k generalizing x y with
  | zero =>
    have h : x = y := p.property
    subst y
    omega
  | succ k ih =>
    obtain ⟨z, r, p⟩ := p
    have hr := seamMatchingRank_step_lt (show SeamMatchingStep x z from
      ⟨r.property.1, r.val, r.property.2⟩)
    have hp := ih p
    omega

/-- No actual internal rectangle path reaches the finite number of matching pairs. -/
theorem seamInternalPath_length_lt {k : ℕ} {x y : SeamMatchingSource n m}
    (p : SeamInternalPath k x y) : k < Fintype.card (SeamMatchingSource n m) := by
  have hp := seamInternalPath_rank p
  have hy := seamMatchingRank_lt_card y
  omega

/-- Matrix powers count all chosen internal rectangles, with their parity retained. -/
theorem seamInternalPath_card (k : ℕ) (x y : SeamMatchingSource n m) :
    (Fintype.card (SeamInternalPath k x y) : ZMod 2) =
      (seamUnweightedTransition (n := n) (m := m) ^ k) y x := by
  classical
  induction k generalizing x y with
  | zero =>
    change (Fintype.card {_u : Unit // x = y} : ZMod 2) = (1 : Matrix _ _ (ZMod 2)) y x
    rw [Fintype.card_subtype]
    by_cases h : x = y
    · subst y
      simp
    · simp [h, Ne.symm h]
  | succ k ih =>
    change (Fintype.card (Σ z : SeamMatchingSource n m,
      SeamInternalRectangle x z × SeamInternalPath k z y) : ZMod 2) = _
    rw [Fintype.card_sigma, Nat.cast_sum, pow_succ, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Fintype.card_prod, Nat.cast_mul, ih]
    exact mul_comm _ _

theorem seamMatchingTransition_evalOne
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : SeamMatchingSource n m) :
    laurentEvalOne (seamMatchingTransitionMatrix G H hG hH (ZMod 2) y x) =
      seamUnweightedTransition y x := by
  classical
  rw [seamUnweightedTransition, card_seamInternalRectangle]
  by_cases h : x = y
  · subst y
    simp only [seamMatchingTransitionMatrix_diag, map_zero, ite_true, Nat.cast_zero]
  · rw [seamMatchingTransitionMatrix_offDiag G H hG hH (ZMod 2) x y h,
      if_neg h]
    change laurentEvalOne (LaurentPolynomial.T _ * laurentCoefficient _ _ _ _) = _
    rw [map_mul, laurentEvalOne_T, one_mul, laurentEvalOne_coefficient]

/-- The finite unweighted inverse is a sum of internal path matrices. -/
def seamUnweightedInverse :
    Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (ZMod 2) :=
  ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m)), seamUnweightedTransition ^ k

theorem seamMatchingMatrixInverse_evalOne
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (x y : SeamMatchingSource n m) :
    laurentEvalOne (seamMatchingMatrixInverse G H hG hH (ZMod 2) y x) =
      seamUnweightedInverse y x := by
  classical
  let φ : Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (LaurentPolynomial (ZMod 2)) →+*
      Matrix (SeamMatchingSource n m) (SeamMatchingSource n m) (ZMod 2) :=
    (laurentEvalOne (R := ZMod 2)).mapMatrix
  have ht : φ (seamMatchingTransitionMatrix G H hG hH (ZMod 2)) =
      seamUnweightedTransition := by
    ext y x
    exact seamMatchingTransition_evalOne G H hG hH x y
  have hn : -(seamUnweightedTransition (n := n) (m := m)) = seamUnweightedTransition := by
    ext y x
    exact CharTwo.neg_eq _
  have hm : φ (seamMatchingMatrixInverse G H hG hH (ZMod 2)) = seamUnweightedInverse := by
    simp only [seamMatchingMatrixInverse, seamUnweightedInverse, map_sum, map_pow, map_neg, ht, hn]
  exact congrArg (fun A => A y x) hm

/-- A correction path chooses its entry, every internal rectangle, and its exit. -/
abbrev SeamCorrectionPath (k : ℕ) (p q : SeamRetainedIndex n m) :=
  Σ x : SeamMatchingSource n m, Σ y : SeamMatchingSource n m,
    {r : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val //
      r.IsEmpty} ×
    SeamInternalPath k x y ×
    {r : GridRectangleBetween y.val.val (seamState q.1 q.2) // r.IsEmpty}

instance seamCorrectionPathFintype (k : ℕ) (p q : SeamRetainedIndex n m) :
    Fintype (SeamCorrectionPath k p q) := inferInstance

theorem seamCorrectionPath_card (k : ℕ) (p q : SeamRetainedIndex n m) :
    (Fintype.card (SeamCorrectionPath k p q) : ZMod 2) =
      ∑ x : SeamMatchingSource n m, ∑ y : SeamMatchingSource n m,
        ((emptyRectangles (seamState p.1 p.2) (seamComplementPartner x.val).val).card : ZMod 2) *
        (seamUnweightedTransition ^ k) y x *
        ((emptyRectangles y.val.val (seamState q.1 q.2)).card : ZMod 2) := by
  simp only [SeamCorrectionPath, Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum,
    Nat.cast_mul, card_emptyRectangles, seamInternalPath_card, mul_assoc]

/-- Direct rectangles and all bounded correction paths are the Schur contributions. -/
abbrev SeamTransferPath (p q : SeamRetainedIndex n m) :=
  {r : GridRectangleBetween (seamState p.1 p.2) (seamState q.1 q.2) // r.IsEmpty} ⊕
    Σ k : Fin (Fintype.card (SeamMatchingSource n m)), SeamCorrectionPath k.val p q

instance seamTransferPathFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamTransferPath p q) := inferInstance

/-- The tensor contributions are factor rectangles with the other factor fixed. -/
abbrev SeamFactorRectanglePath (p q : SeamRetainedIndex n m) :=
  ({r : GridRectangleBetween p.1 q.1 // r.IsEmpty} × {_u : Unit // p.2 = q.2}) ⊕
    ({_u : Unit // p.1 = q.1} × {r : GridRectangleBetween p.2 q.2 // r.IsEmpty})

instance seamFactorRectanglePathFintype (p q : SeamRetainedIndex n m) :
    Fintype (SeamFactorRectanglePath p q) := inferInstance

theorem seamFactorRectanglePath_card (p q : SeamRetainedIndex n m) :
    (Fintype.card (SeamFactorRectanglePath p q) : ZMod 2) =
      (if p.2 = q.2 then ((emptyRectangles p.1 q.1).card : ZMod 2) else 0) +
        if p.1 = q.1 then ((emptyRectangles p.2 q.2).card : ZMod 2) else 0 := by
  classical
  simp only [SeamFactorRectanglePath, Fintype.card_sum, Fintype.card_prod]
  rw [card_emptyRectangles, card_emptyRectangles]
  simp only [Fintype.card_subtype]
  by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;> simp [h₁, h₂]

theorem seamTransferPath_card (p q : SeamRetainedIndex n m) :
    (Fintype.card (SeamTransferPath p q) : ZMod 2) =
      ((emptyRectangles (seamState p.1 p.2) (seamState q.1 q.2)).card : ZMod 2) +
        ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m)),
          (Fintype.card (SeamCorrectionPath k p q) : ZMod 2) := by
  rw [Fintype.card_sum, Nat.cast_add, card_emptyRectangles, Fintype.card_sigma,
    Nat.cast_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun k => (Fintype.card (SeamCorrectionPath k p q) : ZMod 2)) _

/-- The actual specialized Schur coefficient is the parity of these concrete finite paths. -/
theorem seamRetainedDifferential_evalOne_eq_pathCard
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (p q : SeamRetainedIndex n m) :
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2) (Pi.single p 1) q) =
      (Fintype.card (SeamTransferPath p q) : ZMod 2) := by
  classical
  rw [seamRetainedDifferential_single_apply_eq_schur, map_sub, seamTransferPath_card]
  simp only [map_sum, map_mul, laurentEvalOne_coefficient, seamMatchingMatrixInverse_evalOne,
    laurentEvalOne_T, one_mul, sub_eq_add_neg, CharTwo.neg_eq]
  congr 1
  have hinv (x y : SeamMatchingSource n m) : seamUnweightedInverse y x =
      ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m)),
        (seamUnweightedTransition ^ k) y x := by
    simp only [seamUnweightedInverse, Matrix.sum_apply]
  simp only [hinv, Finset.sum_mul, Finset.mul_sum, seamCorrectionPath_card]
  calc
    _ = ∑ x : SeamMatchingSource n m,
        ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m)),
          ∑ y : SeamMatchingSource n m,
            ((emptyRectangles x.val.val (seamState q.1 q.2)).card : ZMod 2) *
              (seamUnweightedTransition ^ k) x y *
              ((emptyRectangles (seamState p.1 p.2) (seamComplementPartner y.val).val).card :
                ZMod 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ k ∈ Finset.range (Fintype.card (SeamMatchingSource n m)),
          ∑ x : SeamMatchingSource n m, ∑ y : SeamMatchingSource n m,
            ((emptyRectangles x.val.val (seamState q.1 q.2)).card : ZMod 2) *
              (seamUnweightedTransition ^ k) x y *
              ((emptyRectangles (seamState p.1 p.2) (seamComplementPartner y.val).val).card :
                ZMod 2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring

end OnLeConjecture.KnotFloer.GridFull
