/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationTransferredFilteredComparison

/-!
# The center column of the full stabilization comparison

The constructed full projection is exactly the second-copy inclusion on center chains.
The homotopy has no center output and kills center input. These identities specify a
column of the comparison without an arbitrary choice of homology equivalence.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The partially blocked homotopy kills every center chain. -/
theorem localStabilizationRetraction_homotopy_centerInclusion (c : LaurentChain R n) :
    (localStabilizationRetraction G s R).homotopy
      (laurentStabilizationCenterInclusion G s R c) = 0 := by
  rw [localStabilizationRetraction_homotopy, laurentOffCenterProjection_centerInclusion,
    map_zero, map_zero, neg_zero]

/-- The partially blocked homotopy has no center output. -/
theorem centerProjection_localStabilizationRetraction_homotopy (c : LaurentChain R (n + 1)) :
    laurentStabilizationCenterProjection G s R
      ((localStabilizationRetraction G s R).homotopy c) = 0 := by
  rw [localStabilizationRetraction_homotopy, map_neg,
    laurentStabilizationCenterProjection_offCenterInclusion, neg_zero]

/-- Restoring the X crossings preserves the vanishing on center input. -/
theorem fullStabilizationTransferredRetraction_homotopy_centerInclusion (c : LaurentChain R n) :
    (fullStabilizationTransferredRetraction G s R).homotopy
      (laurentStabilizationCenterInclusion G s R c) = 0 := by
  rw [fullStabilizationTransferredRetraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    localStabilizationRetraction_homotopy_centerInclusion, map_zero, map_zero, sub_self]

/-- Restoring the X crossings preserves the vanishing of center output. -/
theorem centerProjection_fullStabilizationTransferredRetraction_homotopy
    (c : LaurentChain R (n + 1)) :
    laurentStabilizationCenterProjection G s R
      ((fullStabilizationTransferredRetraction G s R).homotopy c) = 0 := by
  rw [fullStabilizationTransferredRetraction_homotopy, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
    centerProjection_localStabilizationRetraction_homotopy,
    centerProjection_localStabilizationRetraction_homotopy, sub_self]

/-- On center chains the full comparison is the identity into its shifted second copy. -/
theorem fullStabilizationTransferredRetraction_proj_centerInclusion (c : LaurentChain R n) :
    (fullStabilizationTransferredRetraction G s R).proj
      (laurentStabilizationCenterInclusion G s R c) = (0, c) := by
  rw [fullStabilizationTransferredRetraction_proj, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    localStabilizationRetraction_homotopy_centerInclusion, map_zero, map_zero, sub_zero,
    localStabilizationRetraction_proj, laurentOffCenterProjection_centerInclusion, map_zero]
  exact congrArg (fun z : LaurentChain R n => ((0 : LaurentChain R n), z))
    (LinearMap.congr_fun (laurentStabilizationCenterProjection_comp_inclusion G s R) c)

/-- The full corrected center inclusion is determined by the actual full differential. -/
theorem fullStabilizationTransferredRetraction_incl_second (c : LaurentChain R n) :
    (fullStabilizationTransferredRetraction G s R).incl (0, c) =
      laurentStabilizationCenterInclusion G s R c -
        (fullStabilizationTransferredRetraction G s R).homotopy
          (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
            (laurentStabilizationCenterInclusion G s R c)) := by
  have h := (fullStabilizationTransferredRetraction G s R).incl_proj_apply
    (laurentStabilizationCenterInclusion G s R c)
  rw [fullStabilizationTransferredRetraction_proj_centerInclusion,
    fullStabilizationTransferredRetraction_homotopy_centerInclusion, map_zero, sub_zero] at h
  exact h

/-- The second target column is the projection of the differential of a center chain. -/
theorem stabilizationTransferredDifferential_second (c : LaurentChain R n) :
    stabilizationTransferredDifferential G s R (0, c) =
      (fullStabilizationTransferredRetraction G s R).proj
        (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
          (laurentStabilizationCenterInclusion G s R c)) := by
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    (laurentStabilizationCenterInclusion G s R c)
  rw [fullStabilizationTransferredRetraction_proj_centerInclusion] at h
  exact h.symm

/-- The full projection satisfies its specified finite perturbation recursion. -/
theorem fullStabilizationTransferredRetraction_proj_recursion (c : LaurentChain R (n + 1)) :
    (fullStabilizationTransferredRetraction G s R).proj c +
      (fullStabilizationTransferredRetraction G s R).proj
        (laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
          R {s.castSucc, s.succ} ((localStabilizationRetraction G s R).homotopy c)) =
        (localStabilizationRetraction G s R).proj c := by
  have h := LinearMap.congr_fun (LinearSpecialContraction.perturb_proj_comp_one_add_mul
    (localStabilizationRetraction G s R)
    (laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ})
    (laurentXCrossing_perturbation (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ}) (isUnit_one_add_stabilizationXCrossing_homotopy G s R)) c
  simpa only [fullStabilizationTransferredRetraction,
    LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply, map_add] using h

end OnLeConjecture.KnotFloer.GridFull
