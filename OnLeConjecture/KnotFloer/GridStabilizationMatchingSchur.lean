/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingProjection
public import OnLeConjecture.KnotFloer.GridStabilizationXPartner

/-!
# Finite matching formula for the actual transferred diagonal

The internal matching matrix is `1+T`, where `T` is the proved locally
nilpotent full transition operator. The actual second projection on matching
targets is `E (1+T)⁻¹`. Consequently its transferred diagonal is the direct
center term plus `E (1+T)⁻¹ F`. No identification with the old differential
is assumed. The remaining rectangle calculation can be applied to this formula.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- The inverse of the proved invertible full internal matching matrix. -/
def stabilizationMatchingInverse : Module.End (LaurentPolynomial R)
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  ↑((isUnit_one_add_stabilizationMatchingTransition G s R).unit⁻¹)

theorem stabilizationMatchingInternal_comp_inverse :
    (1 + stabilizationMatchingTransition G s R) ∘ₗ stabilizationMatchingInverse G s R =
      LinearMap.id :=
  (isUnit_one_add_stabilizationMatchingTransition G s R).mul_val_inv

theorem stabilizationMatchingInverse_comp_internal :
    stabilizationMatchingInverse G s R ∘ₗ (1 + stabilizationMatchingTransition G s R) =
      LinearMap.id :=
  (isUnit_one_add_stabilizationMatchingTransition G s R).val_inv_mul

/-- Restoring the removed unit diagonal recovers the full internal differential matrix. -/
theorem one_add_stabilizationMatchingTransition_eq :
    1 + stabilizationMatchingTransition G s R =
      stabilizationMatchingTargetProjection G s R ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
          stabilizationMatchingSourceInclusion G s R := by
  rw [stabilizationMatchingTransition]
  change LinearMap.id + (_ - LinearMap.id) = _
  abel

/-- Full differential paths entering a noncritical matching target from a center state. -/
def stabilizationMatchingEntry :
    LaurentChain R n →ₗ[LaurentPolynomial R]
      (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  stabilizationMatchingTargetProjection G s R ∘ₗ
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
      laurentStabilizationCenterInclusion G s R

/-- Full differential paths leaving a noncritical source for a center state. -/
def stabilizationMatchingExit :
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R n :=
  laurentStabilizationCenterProjection G s R ∘ₗ
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
      stabilizationMatchingSourceInclusion G s R

/-- The direct full center-to-center contribution. -/
def stabilizationMatchingDirect : Module.End (LaurentPolynomial R) (LaurentChain R n) :=
  laurentStabilizationCenterProjection G s R ∘ₗ
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
      laurentStabilizationCenterInclusion G s R

variable [CharP R 2]

/-- The full projection kills the differential of every noncritical matching source. -/
theorem stabilizationSecondProjection_d_matchingSource :
    stabilizationSecondProjection G s R ∘ₗ
        laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
          stabilizationMatchingSourceInclusion G s R = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    stabilizationMatchingSourceInclusion_single, LinearMap.zero_apply]
  change ((fullStabilizationTransferredRetraction G s R).proj
    (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
      (single x.val 1))).2 = 0
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply (single x.val 1)
  rw [fullStabilizationTransferredRetraction_proj_noncritical_source G s R x.val
    x.property.1 x.property.2, map_zero] at h
  exact congrArg Prod.snd h

/-- The actual projection on matching targets solves the finite internal matching equation. -/
theorem stabilizationMatchingSecondProjection_comp_internal :
    stabilizationMatchingSecondProjection G s R ∘ₗ
        (1 + stabilizationMatchingTransition G s R) = stabilizationMatchingExit G s R := by
  have h := stabilizationSecondProjection_d_matchingSource G s R
  rw [stabilizationSecondProjection_decomposition, LinearMap.add_comp] at h
  simp only [LinearMap.comp_assoc] at h
  rw [← one_add_stabilizationMatchingTransition_eq] at h
  change stabilizationMatchingExit G s R +
    stabilizationMatchingSecondProjection G s R ∘ₗ
      (1 + stabilizationMatchingTransition G s R) = 0 at h
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro y
  have hh := congrArg (fun f => f x y) h
  change stabilizationMatchingExit G s R x y +
    (stabilizationMatchingSecondProjection G s R ∘ₗ
      (1 + stabilizationMatchingTransition G s R)) x y = 0 at hh
  exact (CharTwo.add_eq_zero.mp hh).symm

/-- The second projection is the exit matrix followed by the finite internal inverse. -/
theorem stabilizationMatchingSecondProjection_eq_exit_inverse :
    stabilizationMatchingSecondProjection G s R =
      stabilizationMatchingExit G s R ∘ₗ stabilizationMatchingInverse G s R := by
  have h := congrArg (fun f => f ∘ₗ stabilizationMatchingInverse G s R)
    (stabilizationMatchingSecondProjection_comp_internal G s R)
  simpa only [LinearMap.comp_assoc, stabilizationMatchingInternal_comp_inverse,
    LinearMap.comp_id] using h

/-- The actual transferred center diagonal is the direct term plus the finite matching paths. -/
theorem stabilizationTransferredDifferential_snd_schur (c : LaurentChain R n) :
    (stabilizationTransferredDifferential G s R (0, c)).2 =
      stabilizationMatchingDirect G s R c +
        stabilizationMatchingExit G s R
          (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R c)) := by
  rw [stabilizationTransferredDifferential_second]
  change stabilizationSecondProjection G s R
    (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
      (laurentStabilizationCenterInclusion G s R c)) = _
  rw [stabilizationSecondProjection_decomposition, LinearMap.add_apply, LinearMap.comp_apply,
    stabilizationMatchingSecondProjection_eq_exit_inverse, LinearMap.comp_apply]
  rfl

/-- The common diagonal has the same explicit finite path formula. -/
theorem stabilizationTransferredDifferential_fst_schur (c : LaurentChain R n) :
    (stabilizationTransferredDifferential G s R (c, 0)).1 =
      stabilizationMatchingDirect G s R c +
        stabilizationMatchingExit G s R
          (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R c)) := by
  rw [stabilizationTransferredDifferential_diagonal_eq]
  exact stabilizationTransferredDifferential_snd_schur G s R c

end OnLeConjecture.KnotFloer.GridFull
