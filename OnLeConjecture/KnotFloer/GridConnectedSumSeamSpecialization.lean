/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTransferred
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamGrading
public import OnLeConjecture.KnotFloer.GridLaurentHomogeneousSpecialization

/-!
# Reducing the prepared seam differential comparison to U = 1

The actual retained Schur coefficients have a proved single Maslov degree.
For a prepared factor, that degree agrees with the tensor coefficient.
Consequently the remaining coefficient identity is exactly its finite
specialization at U = 1. The specialized identity is not assumed proved.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem coefficient_degree {k : ℕ} (G : GridDiagram k) (R : Type*)
    [CommRing R] (x y : GridState k) {j : ℤ}
    (hj : j ∈ (laurentCoefficient G R x y).coeff.support) :
    2 * j = G.maslovOℤ y - G.maslovOℤ x + 1 := by
  obtain ⟨r, hr, rfl⟩ := exists_rectangle_of_mem_support_laurentCoefficient G R hj
  have hd := laurentMaslovDegree_add_card_OColumns G r ((mem_emptyRectangles r).mp hr) 0
  simp only [zero_add, laurentMaslovDegree, mul_zero, sub_zero] at hd
  omega

private theorem normalized_entry_degree
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (w : GridState (n + m + 1))
    (y : SeamMatchingSource n m) {j : ℤ}
    (hj : j ∈ (LaurentPolynomial.T (-(seamComplementOCount G H y.val : ℤ)) *
      laurentCoefficient (connectedSumSeamGrid G H hG hH) R w
        (seamComplementPartner y.val).val).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ y.val.val -
      (connectedSumSeamGrid G H hG hH).maslovOℤ w := by
  have hs := AddMonoidAlgebra.support_coeff_single_mul_subset
    (laurentCoefficient (connectedSumSeamGrid G H hG hH) R w
      (seamComplementPartner y.val).val) (1 : R)
      (-(seamComplementOCount G H y.val : ℤ)) hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
  have hd := coefficient_degree (connectedSumSeamGrid G H hG hH) R _ _ hk
  have hm := connectedSumSeamGrid_complement_maslov G H hG hH y.val y.property
  omega

/-- Every actual Schur coefficient has the differential's required Maslov degree. -/
theorem seamRetainedDifferential_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) {j : ℤ}
    (hj : j ∈ (seamRetainedDifferential G H hG hH R (Pi.single p 1) q).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState q.1 q.2) -
      (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState p.1 p.2) + 1 := by
  classical
  rw [seamRetainedDifferential_single_apply_eq_schur, AddMonoidAlgebra.coeff_sub] at hj
  rcases Finset.mem_union.mp (Finsupp.support_sub hj) with hDirect | hCorrection
  · exact coefficient_degree _ R _ _ hDirect
  · rw [AddMonoidAlgebra.coeff_sum] at hCorrection
    obtain ⟨x, hx, hjx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hCorrection)
    obtain ⟨a, hExit, b, hb, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hjx)
    rw [AddMonoidAlgebra.coeff_sum] at hb
    obtain ⟨y, hy, hby⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hb)
    obtain ⟨c, hInverse, d, hEntry, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hby)
    have h₁ := coefficient_degree (connectedSumSeamGrid G H hG hH) R _ _ hExit
    have h₂ := seamMatchingMatrixInverse_support_maslov G H hG hH R y x hInverse
    have h₃ := normalized_entry_degree G H hG hH R _ y hEntry
    omega

/-- The literal full factor-tensor coefficient in the pair-state basis. -/
def seamTensorCoefficient
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) : LaurentPolynomial R :=
  (if p.2 = q.2 then laurentCoefficient G R p.1 q.1 else 0) +
    if p.1 = q.1 then laurentCoefficient H R p.2 q.2 else 0

/-- Odd differential degree excludes every retained diagonal entry. -/
theorem seamRetainedDifferential_self_eq_zero
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (p : SeamRetainedIndex n m) :
    seamRetainedDifferential G H hG hH R (Pi.single p 1) p = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  change (seamRetainedDifferential G H hG hH R (Pi.single p 1) p).coeff j = 0
  by_contra h
  have hd := seamRetainedDifferential_support_maslov G H hG hH R p p
    (Finsupp.mem_support_iff.mpr h)
  omega

theorem seamTensorCoefficient_evalOne
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) :
    laurentEvalOne (seamTensorCoefficient G H R p q) =
      (if p.2 = q.2 then ((emptyRectangles p.1 q.1).card : R) else 0) +
        if p.1 = q.1 then ((emptyRectangles p.2 q.2).card : R) else 0 := by
  classical
  simp only [seamTensorCoefficient, map_add]
  split_ifs <;> simp only [laurentEvalOne_coefficient, map_zero]

theorem seamTensorCoefficient_support_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) {j : ℤ}
    (hj : j ∈ (seamTensorCoefficient G H R p q).coeff.support) :
    2 * j = (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState q.1 q.2) -
      (connectedSumSeamGrid G H hG hH).maslovOℤ (seamState p.1 p.2) + 1 := by
  classical
  rw [connectedSumSeamGrid_maslovO_of_last_O G H hG hH hO,
    connectedSumSeamGrid_maslovO_of_last_O G H hG hH hO]
  rw [seamTensorCoefficient, AddMonoidAlgebra.coeff_add] at hj
  rcases Finset.mem_union.mp (Finsupp.support_add hj) with h | h
  · split_ifs at h with he
    · have hd := coefficient_degree G R _ _ h
      rw [he]
      omega
    · simp at h
  · split_ifs at h with he
    · have hd := coefficient_degree H R _ _ h
      rw [he]
      omega
    · simp at h

/-- The remaining prepared-seam coefficient identity is exactly its finite U=1 identity. -/
theorem seamRetainedDifferential_eq_tensor_iff_evalOne
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) :
    seamRetainedDifferential G H hG hH R (Pi.single p 1) q = seamTensorCoefficient G H R p q ↔
      laurentEvalOne (seamRetainedDifferential G H hG hH R (Pi.single p 1) q) =
        (if p.2 = q.2 then ((emptyRectangles p.1 q.1).card : R) else 0) +
          if p.1 = q.1 then ((emptyRectangles p.2 q.2).card : R) else 0 := by
  rw [← seamTensorCoefficient_evalOne G H R p q]
  constructor
  · intro h
    exact congrArg laurentEvalOne h
  · intro h
    apply eq_of_laurentEvalOne_eq_of_homogeneous _ _
      ((connectedSumSeamGrid G H hG hH).maslovOℤ (seamState q.1 q.2))
      ((connectedSumSeamGrid G H hG hH).maslovOℤ (seamState p.1 p.2) - 1)
    · intro j hj
      have hd := seamRetainedDifferential_support_maslov G H hG hH R p q hj
      omega
    · intro j hj
      have hd := seamTensorCoefficient_support_maslov G H hG hH hO R p q hj
      omega
    · exact h

end OnLeConjecture.KnotFloer.GridFull
