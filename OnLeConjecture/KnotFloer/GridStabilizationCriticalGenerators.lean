/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationSourceRectangle

/-!
# The two explicit generator sets for the transferred stabilization differential

The center states and their row-matching partners map to the two standard copies of
the old grid generators. Both are killed by the full homotopy. Thus both columns of
the transferred differential are obtained by applying the full differential and then
the specified projection to these explicit states.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The off-center matching partner of a center generator. -/
def stabilizationPartnerState (x : GridState n) : G.StabilizeXOffCenterState s :=
  ⟨(x.insertPoint s.succ (G.X s).succ).swapRows (G.X s).castSucc (G.X s).succ, by
    simp only [GridState.swapRows_apply, GridState.insertPoint_apply_newColumn,
      Equiv.swap_apply_right]
    exact Fin.castSucc_lt_succ.ne⟩

/-- Matching the explicit partner recovers the center generator. -/
theorem stabilizationPartnerState_matching (x : GridState n) :
    G.stabilizeXMatching s (.inl (stabilizationPartnerState G s x)) = .inr x := by
  apply (G.stabilizeXConeStateEquiv s).injective
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching,
    GridDiagram.stabilizeXConeStateEquiv_apply_inl,
    GridDiagram.stabilizeXConeStateEquiv_apply_inr]
  exact GridState.swapRows_swapRows _ _ _

/-- Every explicit partner is a source of the row matching. -/
theorem stabilizationPartnerState_is_matching_source (x : GridState n) :
    G.StabilizeXMatchingSource s (.inl (stabilizationPartnerState G s x)) := by
  have h := G.stabilizeXMatchingSource_stabilizeXMatching_iff s
    (.inl (stabilizationPartnerState G s x))
  rw [stabilizationPartnerState_matching] at h
  exact Classical.not_not.mp ((not_congr h).mp (G.not_stabilizeXMatchingSource_inr s x))

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The partner states are sent to the first standard copy by the full projection. -/
theorem fullStabilizationTransferredRetraction_proj_partner_single (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).proj
      (single (stabilizationPartnerState G s x).val 1) = (single x 1, 0) := by
  classical
  apply Prod.ext
  · apply Finsupp.ext
    intro y
    rw [fullStabilizationTransferredRetraction_proj_source_coefficient_eq G s R _
      (stabilizationPartnerState_is_matching_source G s x),
      stabilizationPartnerState_matching]
    simp only [Sum.inr.injEq, Finsupp.single_apply]
  · simpa only using congrArg Prod.snd
      (fullStabilizationTransferredRetraction_proj_single_of_matching_source G s R _
        (stabilizationPartnerState_is_matching_source G s x))

/-- The full homotopy kills each partner generator. -/
theorem fullStabilizationTransferredRetraction_homotopy_partner_single (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).homotopy
      (single (stabilizationPartnerState G s x).val 1) = 0 :=
  fullStabilizationTransferredRetraction_homotopy_single_of_matching_source G s R _
    (stabilizationPartnerState_is_matching_source G s x)

/-- The corrected first inclusion column is specified by the full differential of a partner. -/
theorem fullStabilizationTransferredRetraction_incl_first_single (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).incl (single x 1, 0) =
      single (stabilizationPartnerState G s x).val 1 -
        (fullStabilizationTransferredRetraction G s R).homotopy
          (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
            (single (stabilizationPartnerState G s x).val 1)) := by
  have h := (fullStabilizationTransferredRetraction G s R).incl_proj_apply
    (single (stabilizationPartnerState G s x).val 1)
  rw [fullStabilizationTransferredRetraction_proj_partner_single,
    fullStabilizationTransferredRetraction_homotopy_partner_single, map_zero, sub_zero] at h
  exact h

/-- The first transferred column is projection of the full differential on the explicit partner. -/
theorem stabilizationTransferredDifferential_first_single (x : GridState n) :
    stabilizationTransferredDifferential G s R (single x 1, 0) =
      (fullStabilizationTransferredRetraction G s R).proj
        (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R
          (single (stabilizationPartnerState G s x).val 1)) := by
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    (single (stabilizationPartnerState G s x).val 1)
  rw [fullStabilizationTransferredRetraction_proj_partner_single] at h
  exact h.symm

end OnLeConjecture.KnotFloer.GridFull
