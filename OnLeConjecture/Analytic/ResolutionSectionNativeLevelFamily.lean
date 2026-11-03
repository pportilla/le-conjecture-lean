/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeFinalFrontier
public import OnLeConjecture.Analytic.LevelSetupConstruction
public import OnLeConjecture.KnotFloer.GridEndpointCleanupAssembly

/-!
# The root families of the levels and the event factorization

This module assembles the proved inputs of Section 3 of the proof of Statement E:

* `levelSetupStatement`: the projection setup of a level, its root family and its
  connectedness;
* `LevelProjectionSetup.outerHolds_of_admissible`: the outer braid;
* `LevelProjectionSetup.pointClusterData_of_smoothCritical` and
  `LevelProjectionSetup.pointClusterData_of_singular`: the local braids at the critical points.

They give `levelRootFamilyStatement` and the finite event factorization
`eventFactorizationStatement`. Lê's conjecture then follows from the single statement
`ScissorEndpointCleanupStatement` (`leConjecture_of_endpointCleanup`), and hence, by
`scissorEndpointCleanupStatement_of_markedFactorCleanup`, from the per-factor marked inverse
cancellation of Section 8 (`leConjecture_of_markedFactorCleanup`).
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotTheory

/-- The projection setup statement of the levels holds. -/
theorem levelProjectionSetupStatement : LevelProjectionSetupStatement :=
  levelProjectionSetupStatement_of_levelSetup levelSetupStatement
    (fun _ _ _ _ _ P hP => P.outerHolds_of_admissible hP)
    (fun _ _ _ _ _ => criticalHolds_of_pointClusterStatement
      (pointClusterStatement_of_cases (fun P hP => P.pointClusterData_of_smoothCritical hP)
        (fun P hP j => P.pointClusterData_of_singular hP j)) _ _ _ _ _)

/-- **Root families of the levels.** -/
theorem levelRootFamilyStatement : LevelRootFamilyStatement :=
  levelRootFamilyStatement_of_setup levelProjectionSetupStatement

/-- **Finite event factorization** (Lemma `finiteProjectionEventFactorization` of the proof of
Statement E). -/
theorem eventFactorizationStatement : EventFactorizationStatement :=
  eventFactorizationStatement_of_rootFamily levelRootFamilyStatement

/-- **Lê's conjecture from the scissor endpoint cleanup.** -/
theorem leConjecture_of_endpointCleanup (hendpoint : ScissorEndpointCleanupStatement) :
    LeConjecture :=
  leConjecture_of_rootFamily_frontier levelRootFamilyStatement
    (scissorCleanupStatement_of_endpointCleanup hendpoint)

/-- **Lê's conjecture from the marked inverse cancellation of Section 8.** -/
theorem leConjecture_of_markedFactorCleanup (hmarked : MarkedFactorCleanupStatement) :
    LeConjecture :=
  leConjecture_of_endpointCleanup (scissorEndpointCleanupStatement_of_markedFactorCleanup hmarked)

end OnLeConjecture.Analytic
