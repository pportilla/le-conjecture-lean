/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPreparedFiltration
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamGrading

/-!
# Maslov grading of the prepared seam cancellation

The constructed inverse raises Maslov degree by one. Consequently the
corrected inclusion and projection preserve degree, and the transferred
differential lowers degree by one. Its identification with the balanced
tensor differential is a separate assertion.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
variable {n m : ℕ}

/-- The inverse matching block raises the target-state Maslov degree by one. -/
theorem seamFullMatchingBlockEquiv_symm_degree_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) {d : ℤ}
    (hc : ∀ y j, j ∈ (c y).coeff.support →
      laurentMaslovDegree (connectedSumSeamGrid G H hG hH) j
        (seamComplementPartner y.val).val = d)
    (x : SeamMatchingSource n m) (k : ℤ)
    (hk : k ∈ ((seamFullMatchingBlockEquiv G H hG hH R).symm c x).coeff.support) :
    laurentMaslovDegree (connectedSumSeamGrid G H hG hH) k x.val.val = d + 1 := by
  classical
  rw [seamFullMatchingBlockEquiv_symm_apply_of_last_O G H hG hH hO,
    AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨y, hy, hky⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hky)
  have hI := seamMatchingMatrixInverse_support_maslov G H hG hH R y x ha
  have hM := connectedSumSeamGrid_complement_maslov G H hG hH y.val y.property
  rw [seamComplementOCount_eq_zero_of_last_O G H hO y.val] at hM
  have hh := hc y b hb
  simp only [laurentMaslovDegree] at hh ⊢
  omega

/-- The actual contraction homotopy raises Maslov degree by one. -/
theorem seamFullContraction_homotopy_mem_maslov_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {d : ℤ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d) :
    (seamFullContraction G H hG hH R).homotopy c ∈
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R (d + 1) := by
  rw [seamFullContraction_homotopy_apply]
  intro w k hk
  obtain ⟨a, rfl⟩ := seamThreeState_surjective w
  rcases a with p | x
  · change k ∈ ((seamCoordinateEquiv R).symm _ (seamState p.1 p.2)).coeff.support at hk
    rw [seamCoordinateEquiv_symm_retained] at hk
    simp at hk
  · rcases x with x | y
    · change k ∈ ((seamCoordinateEquiv R).symm _ x.val.val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_source] at hk
      exact seamFullMatchingBlockEquiv_symm_degree_of_last_O G H hG hH hO R _
        (fun y j hj => hc (seamComplementPartner y.val).val j hj) x k hk
    · change k ∈ ((seamCoordinateEquiv R).symm _
        (seamComplementPartner y.val).val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_target] at hk
      simp at hk

/-- The homogeneous retained coefficients, with the actual seam-state Maslov degree. -/
def seamRetainedMaslovPiece
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (d : ℤ) : Submodule R (SeamRetainedCoordinates R n m) :=
  (laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d).comap
    ((seamRetainedInclusion R).restrictScalars R)

/-- Reading pair-state coefficients preserves their Maslov degree. -/
theorem seamRetainedProjection_mem_maslov
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] {d : ℤ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d) :
    seamRetainedProjection R c ∈ seamRetainedMaslovPiece G H hG hH R d := by
  intro w k hk
  obtain ⟨a, rfl⟩ := seamThreeState_surjective w
  rcases a with p | x
  · change k ∈ ((seamCoordinateEquiv R).symm _ (seamState p.1 p.2)).coeff.support at hk
    rw [seamCoordinateEquiv_symm_retained] at hk
    exact hc (seamState p.1 p.2) k hk
  · rcases x with x | y
    · change k ∈ ((seamCoordinateEquiv R).symm _ x.val.val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_source] at hk
      simp [FiniteBlockCancellation.retainedInclusion] at hk
    · change k ∈ ((seamCoordinateEquiv R).symm _
        (seamComplementPartner y.val).val).coeff.support at hk
      rw [seamCoordinateEquiv_symm_target] at hk
      simp [FiniteBlockCancellation.retainedInclusion] at hk

/-- The corrected inclusion preserves Maslov degree on prepared seams. -/
theorem seamFullContraction_incl_mem_maslov_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {d : ℤ} {c : SeamRetainedCoordinates R n m}
    (hc : c ∈ seamRetainedMaslovPiece G H hG hH R d) :
    (seamFullContraction G H hG hH R).incl c ∈
      laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d := by
  rw [seamFullContraction_incl_apply]
  change seamRetainedInclusion R c ∈ laurentMaslovPiece _ R d at hc
  apply Submodule.sub_mem _ hc
  simpa only [sub_add_cancel] using
    seamFullContraction_homotopy_mem_maslov_of_last_O G H hG hH hO R
      (laurentDifferential_mem_maslovPiece _ hc)

/-- The corrected projection preserves Maslov degree on prepared seams. -/
theorem seamFullContraction_proj_mem_maslov_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {d : ℤ} {c : LaurentChain R (n + m + 1)}
    (hc : c ∈ laurentMaslovPiece (connectedSumSeamGrid G H hG hH) R d) :
    (seamFullContraction G H hG hH R).proj c ∈
      seamRetainedMaslovPiece G H hG hH R d := by
  rw [seamFullContraction_proj_apply]
  apply seamRetainedProjection_mem_maslov G H hG hH R
  apply Submodule.sub_mem _ hc
  simpa only [add_sub_cancel_right] using laurentDifferential_mem_maslovPiece _
    (seamFullContraction_homotopy_mem_maslov_of_last_O G H hG hH hO R hc)

/-- The actual retained differential lowers Maslov degree by one. -/
theorem seamRetainedDifferential_mem_maslov_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] [CharP R 2] {d : ℤ} {c : SeamRetainedCoordinates R n m}
    (hc : c ∈ seamRetainedMaslovPiece G H hG hH R d) :
    seamRetainedDifferential G H hG hH R c ∈
      seamRetainedMaslovPiece G H hG hH R (d - 1) := by
  have hi := seamFullContraction_incl_mem_maslov_of_last_O G H hG hH hO R hc
  have hp := seamFullContraction_proj_mem_maslov_of_last_O G H hG hH hO R
    (laurentDifferential_mem_maslovPiece _ hi)
  rw [(seamFullContraction G H hG hH R).proj_dM_apply,
    (seamFullContraction G H hG hH R).proj_incl_apply] at hp
  exact hp

/-- The retained homogeneous condition is exactly the sum of factor degrees in the prepared case. -/
theorem mem_seamRetainedMaslovPiece_iff_of_last_O
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
    (R : Type*) [CommRing R] (d : ℤ) (c : SeamRetainedCoordinates R n m) :
    c ∈ seamRetainedMaslovPiece G H hG hH R d ↔
      ∀ p k, k ∈ (c p).coeff.support → G.maslovOℤ p.1 + H.maslovOℤ p.2 - 2 * k = d := by
  constructor
  · intro hc p k hk
    have hh := hc (seamState p.1 p.2) k
    change k ∈ ((seamCoordinateEquiv R).symm (c, (0, 0))
      (seamState p.1 p.2)).coeff.support → _ at hh
    rw [seamCoordinateEquiv_symm_retained] at hh
    simpa only [laurentMaslovDegree, Set.mem_singleton_iff,
      connectedSumSeamGrid_maslovO_of_last_O G H hG hH hO] using hh hk
  · intro hc w k hk
    obtain ⟨a, rfl⟩ := seamThreeState_surjective w
    rcases a with p | x
    · change k ∈ ((seamCoordinateEquiv R).symm (c, (0, 0)) (seamState p.1 p.2)).coeff.support at hk
      rw [seamCoordinateEquiv_symm_retained] at hk
      change laurentMaslovDegree _ k (seamState p.1 p.2) = d
      simpa only [laurentMaslovDegree, Set.mem_singleton_iff,
      connectedSumSeamGrid_maslovO_of_last_O G H hG hH hO] using hc p k hk
    · rcases x with x | y
      · change k ∈ ((seamCoordinateEquiv R).symm (c, (0, 0)) x.val.val).coeff.support at hk
        rw [seamCoordinateEquiv_symm_source] at hk
        simp at hk
      · change k ∈ ((seamCoordinateEquiv R).symm (c, (0, 0))
          (seamComplementPartner y.val).val).coeff.support at hk
        rw [seamCoordinateEquiv_symm_target] at hk
        simp at hk

end OnLeConjecture.KnotFloer.GridFull
