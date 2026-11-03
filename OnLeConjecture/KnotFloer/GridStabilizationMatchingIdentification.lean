/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingTruncation
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingDirectCoefficient
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingTwoCoefficient
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingThreeCoefficient
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingPartition

/-!
# Identification of the full stabilization transferred differential

The matching paths with two or more internal transitions vanish. The remaining
three kinds of paths are in weight-preserving bijection with a partition of the
old empty rectangles. Thus the differential obtained from the explicit special
contraction is exactly the full old Laurent differential on each of its two summands.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- Every coefficient of the transferred diagonal is the full old rectangle count. -/
theorem stabilizationTransferredDifferential_fst_single_apply_eq
    (x y : GridState n) :
    (stabilizationTransferredDifferential G s R (single x 1, 0)).1 y =
      laurentCoefficient G R x y := by
  classical
  rw [stabilizationTransferredDifferential_fst_short, Finsupp.add_apply, Finsupp.add_apply,
    stabilizationMatchingDirect_single_apply_eq_sum,
    stabilizationMatchingExit_entry_single_apply_eq_sum,
    stabilizationMatchingExit_transition_entry_single_apply_eq_sum,
    laurentCoefficient_eq_sum_stabilizationStandardWeight G s,
    sum_stabilizationStandardWeight_partition]
  rfl

/-- The first transferred diagonal is the original full Laurent differential. -/
theorem stabilizationTransferredDifferential_fst_eq_laurentDifferential :
    LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
      stabilizationTransferredDifferential G s R ∘ₗ
        LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) =
      laurentDifferential G R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro y
  change (stabilizationTransferredDifferential G s R (single x 1, 0)).1 y =
    laurentDifferential G R (single x 1) y
  rw [laurentDifferential_single, laurentOnGenerator_apply]
  exact stabilizationTransferredDifferential_fst_single_apply_eq G s R x y

/-- The actual transferred differential is the full old differential on both summands. -/
theorem stabilizationTransferredDifferential_eq_old_double :
    stabilizationTransferredDifferential G s R =
      (laurentDifferential G R).prodMap (laurentDifferential G R) := by
  rw [stabilizationTransferredDifferential_eq_repeated_diagonal,
    stabilizationTransferredDifferential_fst_eq_laurentDifferential]

/-- The two components of the transferred differential are the old full differentials. -/
theorem stabilizationTransferredDifferential_apply_eq_old_double
    (c : LaurentChain R n × LaurentChain R n) :
    stabilizationTransferredDifferential G s R c =
      (laurentDifferential G R c.1, laurentDifferential G R c.2) := by
  rw [stabilizationTransferredDifferential_eq_old_double]
  rfl

end OnLeConjecture.KnotFloer.GridFull
