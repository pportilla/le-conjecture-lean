/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationPartialFiltration

/-!
# The transferred differential for full Laurent stabilization

Restoring the two new X crossings gives a special contraction of the full stabilized
Laurent complex onto two copies of the old state module with an explicit transferred
differential. No identification of that differential with a standard stabilization
factor is asserted in this module.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The finite perturbation operator restoring the two new X crossings. -/
noncomputable def stabilizationXSeries :
    Module.End (LaurentPolynomial R) (LaurentChain R (n + 1)) :=
  (localStabilizationRetraction G s R).perturbationSeries
    (laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ})

/-- The transferred differential on the two old state modules. -/
noncomputable def stabilizationTransferredDifferential :
    Module.End (LaurentPolynomial R) (LaurentChain R n × LaurentChain R n) :=
  (localStabilizationRetraction G s R).perturbedDifferential
    (laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ})

/-- The transferred differential is the blocked differential plus its specified correction. -/
theorem stabilizationTransferredDifferential_eq :
    stabilizationTransferredDifferential G s R =
      (laurentXBlockedDifferential G R {s}).prodMap (laurentXBlockedDifferential G R {s}) +
        (localStabilizationRetraction G s R).proj ∘ₗ stabilizationXSeries G s R ∘ₗ
          (localStabilizationRetraction G s R).incl :=
  LinearSpecialContraction.perturbedDifferential_def _ _

/-- The actual full stabilized differential retracts to the explicit transferred differential. -/
noncomputable def fullStabilizationTransferredRetraction :
    LinearSpecialContraction
      (laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R)
      (stabilizationTransferredDifferential G s R) := by
  let c := (localStabilizationRetraction G s R).perturb
    (laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ})
    (laurentXCrossing_perturbation (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ}) (isUnit_one_add_stabilizationXCrossing_homotopy G s R)
  exact {
    incl := c.incl
    proj := c.proj
    homotopy := c.homotopy
    dM_comp_incl := by
      simpa only [laurentXBlocked_add_crossing, stabilizationTransferredDifferential]
        using c.dM_comp_incl
    proj_comp_dM := by
      simpa only [laurentXBlocked_add_crossing, stabilizationTransferredDifferential]
        using c.proj_comp_dM
    proj_comp_incl := c.proj_comp_incl
    dM_comp_homotopy_add_homotopy_comp_dM := by
      simpa only [laurentXBlocked_add_crossing] using c.dM_comp_homotopy_add_homotopy_comp_dM
    homotopy_comp_incl := c.homotopy_comp_incl
    proj_comp_homotopy := c.proj_comp_homotopy
    homotopy_comp_homotopy := c.homotopy_comp_homotopy }

/-- The explicitly transferred differential squares to zero. -/
theorem stabilizationTransferredDifferential_comp_self :
    stabilizationTransferredDifferential G s R ∘ₗ stabilizationTransferredDifferential G s R = 0 :=
  (fullStabilizationTransferredRetraction G s R).dN_comp_dN_eq_zero
    (laurentDifferential_comp_self_eq_zero (G.stabilizeX s.castSucc (G.X s).castSucc s) R)

/-- The full comparison inclusion is the finite correction of the partially blocked inclusion. -/
theorem fullStabilizationTransferredRetraction_incl :
    (fullStabilizationTransferredRetraction G s R).incl =
      (localStabilizationRetraction G s R).incl -
        (localStabilizationRetraction G s R).homotopy ∘ₗ stabilizationXSeries G s R ∘ₗ
          (localStabilizationRetraction G s R).incl := by
  unfold fullStabilizationTransferredRetraction
  exact LinearSpecialContraction.perturb_incl (localStabilizationRetraction G s R) _ _ _

/-- The full comparison projection is the finite correction of the partially blocked projection. -/
theorem fullStabilizationTransferredRetraction_proj :
    (fullStabilizationTransferredRetraction G s R).proj =
      (localStabilizationRetraction G s R).proj -
        (localStabilizationRetraction G s R).proj ∘ₗ stabilizationXSeries G s R ∘ₗ
          (localStabilizationRetraction G s R).homotopy := by
  unfold fullStabilizationTransferredRetraction
  exact LinearSpecialContraction.perturb_proj (localStabilizationRetraction G s R) _ _ _

/-- The full comparison homotopy is the finite correction of the constructed homotopy. -/
theorem fullStabilizationTransferredRetraction_homotopy :
    (fullStabilizationTransferredRetraction G s R).homotopy =
      (localStabilizationRetraction G s R).homotopy -
        (localStabilizationRetraction G s R).homotopy ∘ₗ stabilizationXSeries G s R ∘ₗ
          (localStabilizationRetraction G s R).homotopy := by
  unfold fullStabilizationTransferredRetraction
  exact LinearSpecialContraction.perturb_homotopy (localStabilizationRetraction G s R) _ _ _

end OnLeConjecture.KnotFloer.GridFull
