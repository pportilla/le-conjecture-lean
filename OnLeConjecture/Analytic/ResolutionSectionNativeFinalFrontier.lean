/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeFrontier
public import OnLeConjecture.KnotFloer.GridExteriorScissorFrontier
public import OnLeConjecture.Analytic.LevelPointSmoothCluster

/-!
# The final frontier of the native route

This module combines the frontier theorems of the native route with the reduction
`scissorCleanupStatement_of_endpointCleanup` of the scissor cleanup statement to the endpoint
cleanup, and with the local braids at the smooth critical points
(`LevelProjectionSetup.pointClusterData_of_smoothCritical`) and at the singular points
(`LevelProjectionSetup.pointClusterData_of_singular`). Lê's conjecture then follows from two statements, both proved later in the chain
(see `LeConjectureNative.lean`):

* `LevelSetupStatement`, the construction of a projection setup of a level with its root
  family and connectedness;
* `ScissorEndpointCleanupStatement`, the grid moves from the scissor endpoint grid to the tower
  of four-mark blocks over the iterated seam grid.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotTheory

/-- **Lê's conjecture from the setup construction, the smooth critical local braids and the
endpoint cleanup.** -/
theorem leConjecture_of_final_frontier (hS : LevelSetupStatement)
    (hSmooth : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
        ∀ {c : ℂ} {x : Source 2}, c ∈ P.critical → x ∈ P.levelFibre c →
          ¬ Function.Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) →
            (∀ j, x ≠ L.point j) → Nonempty (P.PointClusterData c x))
    (hendpoint : ScissorEndpointCleanupStatement) : LeConjecture :=
  leConjecture_of_levelSetup_smooth_frontier hS hSmooth
    (scissorCleanupStatement_of_endpointCleanup hendpoint)

/-- **Lê's conjecture from the setup construction and the endpoint cleanup.** -/
theorem leConjecture_of_setup_endpoint (hS : LevelSetupStatement)
    (hendpoint : ScissorEndpointCleanupStatement) : LeConjecture :=
  leConjecture_of_final_frontier hS (fun P hP => P.pointClusterData_of_smoothCritical hP)
    hendpoint

end OnLeConjecture.Analytic
