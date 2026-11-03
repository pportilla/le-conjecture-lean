/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingSchur
public import OnLeConjecture.KnotFloer.FiniteMatchingInverse
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingLongPathVanishing

/-!
# The remaining algebra after higher matching paths vanish

The concrete rectangle argument excludes every path with at least two internal
transitions. The actual transferred diagonal is therefore the sum of the direct,
two-rectangle, and three-rectangle contributions. No global bound on the
nilpotence exponent is needed.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The precise higher-path identity suffices to truncate the actual full diagonal. -/
theorem stabilizationTransferredDifferential_fst_short_of_higher_paths
    (hpaths : ∀ k : ℕ, stabilizationMatchingExit G s R ∘ₗ
        (stabilizationMatchingTransition G s R ^ (k + 2)) ∘ₗ
          stabilizationMatchingEntry G s R = 0)
    (c : LaurentChain R n) :
    (stabilizationTransferredDifferential G s R (c, 0)).1 =
      stabilizationMatchingDirect G s R c +
          stabilizationMatchingExit G s R (stabilizationMatchingEntry G s R c) +
        stabilizationMatchingExit G s R
          (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R c)) := by
  have hkill (k : ℕ) : stabilizationMatchingExit G s R
      ((stabilizationMatchingTransition G s R ^ (k + 2))
        (stabilizationMatchingEntry G s R c)) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f => f c) (hpaths k)
  have h := matchingInverse_apply_truncate_two (stabilizationMatchingTransition G s R)
    (isUnit_one_add_stabilizationMatchingTransition G s R).unit
    (isUnit_one_add_stabilizationMatchingTransition G s R).unit_spec
    (stabilizationMatchingExit G s R) (stabilizationMatchingEntry G s R c)
    (stabilizationMatchingTransition_locallyNilpotent G s R _) hkill
  change stabilizationMatchingExit G s R
      (stabilizationMatchingInverse G s R (stabilizationMatchingEntry G s R c)) =
    stabilizationMatchingExit G s R (stabilizationMatchingEntry G s R c) -
      stabilizationMatchingExit G s R
        (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R c)) at h
  rw [stabilizationTransferredDifferential_fst_schur, h]
  apply Finsupp.ext
  intro x
  simp only [Finsupp.add_apply, Finsupp.sub_apply, CharTwo.sub_eq_add, add_assoc]

/-- The proved long-path exclusion truncates the actual full transferred diagonal. -/
theorem stabilizationTransferredDifferential_fst_short (c : LaurentChain R n) :
    (stabilizationTransferredDifferential G s R (c, 0)).1 =
      stabilizationMatchingDirect G s R c +
          stabilizationMatchingExit G s R (stabilizationMatchingEntry G s R c) +
        stabilizationMatchingExit G s R
          (stabilizationMatchingTransition G s R (stabilizationMatchingEntry G s R c)) :=
  stabilizationTransferredDifferential_fst_short_of_higher_paths G s R
    (stabilizationMatchingExit_power_entry_eq_zero G s R) c

end OnLeConjecture.KnotFloer.GridFull
