/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Stabilization.Comparison
public import OnLeConjecture.KnotFloer.MatchingContraction

/-!
# An explicit contraction of the reduced stabilization comparison cone

The reduced cone uses the fully blocked off-center and center differentials and the
zero-O coefficient of the designated X-square comparison map. Its reverse row matching,
normalized by a finite geometric inverse, gives a special contraction onto zero.
Every matching and support hypothesis is supplied by the checked grid geometry.

This is the reduced comparison cone. Identifying the differential transferred by perturbation
with the full stabilized Laurent differential is a further step.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The reduced stabilization comparison cone has a constructed special contraction onto zero. -/
noncomputable def reducedStabilizationContraction :
    LinearSpecialContraction (G.stabilizeXReducedCone s R) (0 : Module.End R PUnit.{1}) :=
  MatchingContraction.ofMatching (G.stabilizeXReducedCone s R)
    (G.stabilizeXReducedCone_comp_self s R)
    (G.stabilizeXConeWeight s) (Finite.wellFounded_of_trans_of_irrefl _)
    (G.stabilizeXMatching s) (G.StabilizeXMatchingSource s)
    (G.stabilizeXMatching_involutive s) (G.stabilizeXConeWeight_stabilizeXMatching s)
    (fun i => by rw [G.stabilizeXMatchingSource_stabilizeXMatching_iff, not_not])
    (fun i hi => by
      rw [G.stabilizeXReducedCone_single_apply_stabilizeXMatching s R i hi]
      exact isUnit_one)
    (G.stabilizeXConeWeight_lt_or_of_mem_support s R)

/-- The contraction's homotopy is an explicit inverse-normalized reverse row matching. -/
noncomputable def reducedStabilizationHomotopy :
    Module.End R (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :=
  (reducedStabilizationContraction G s R).homotopy

/-- The constructed homotopy contracts the exact reduced cone differential. -/
theorem reducedStabilizationHomotopy_contracts :
    G.stabilizeXReducedCone s R ∘ₗ reducedStabilizationHomotopy G s R +
      reducedStabilizationHomotopy G s R ∘ₗ G.stabilizeXReducedCone s R = LinearMap.id := by
  have h := (reducedStabilizationContraction G s R).dM_comp_homotopy_add_homotopy_comp_dM
  simpa only [reducedStabilizationHomotopy, reducedStabilizationContraction,
    MatchingContraction.ofMatching, MatchingContraction.toZero, LinearMap.zero_comp,
    sub_zero] using h

/-- The normalized homotopy has the square-zero side condition needed by HPL. -/
theorem reducedStabilizationHomotopy_comp_self :
    reducedStabilizationHomotopy G s R ∘ₗ reducedStabilizationHomotopy G s R = 0 :=
  (reducedStabilizationContraction G s R).homotopy_comp_homotopy

end OnLeConjecture.KnotFloer.GridFull
