/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeRemaining
public import OnLeConjecture.Analytic.ExteriorNativeMapReduction
public import OnLeConjecture.Analytic.BraidMonodromyEventFactorization
public import OnLeConjecture.KnotTheory.SignedWordGridMoves
public import OnLeConjecture.Analytic.BraidMonodromyRootFactorization
public import OnLeConjecture.Analytic.LevelRootTransitive
public import OnLeConjecture.Analytic.LevelSetupInterface
public import OnLeConjecture.Analytic.LevelOuterBraid
public import OnLeConjecture.Analytic.LevelRootRegularCluster
public import OnLeConjecture.Analytic.LevelPointSingular

/-!
# The frontier of the native route

This module combines `leConjecture_of_remaining_inputs` with the reduction
`exteriorNativeMapStatement_of_reductions` of the exterior statement and with the signed
word-grid relations `SignedGrid.signedWordGridRelations` (Section 7 of the proof of
Statement E). Lê's conjecture then follows from two statements, both proved later in the chain
(see `LeConjectureNative.lean`):

* the closed-braid level factorization `LevelBraidFactorizationStatement`, the analytic part
  of Section 3 of the proof of Statement E (its word-level part is
  `eventFactorizationStatement_of_levelBraidFactorization`);
* the scissor and cleanup statement of Sections 4–6 and 8–11 of that proof.

The variant `leConjecture_of_rootFamily_frontier` replaces the first statement by the
geometric root-family statement `LevelRootFamilyStatement`, through
`eventFactorizationStatement_of_rootFamily`. The variant `leConjecture_of_levelSetup_frontier`
replaces it further by the construction of a projection setup of a level
(`LevelSetupStatement`) and the outer-braid and critical-value fields of such a setup, through
`levelRootFamilyStatement_of_setup` and `levelProjectionSetupStatement_of_levelSetup`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotTheory

/-- **Lê's conjecture from the level factorization and the scissor cleanup.** -/
theorem leConjecture_of_frontier
    (hlevel : LevelBraidFactorizationStatement)
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_remaining_inputs
    (exteriorNativeMapStatement_of_reductions
      (eventFactorizationStatement_of_levelBraidFactorization hlevel)
      SignedGrid.signedWordGridRelations hscissor)

/-- **Lê's conjecture from the root families of the levels and the scissor cleanup.** -/
theorem leConjecture_of_rootFamily_frontier (hroot : LevelRootFamilyStatement)
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_remaining_inputs
    (exteriorNativeMapStatement_of_reductions (eventFactorizationStatement_of_rootFamily hroot)
      SignedGrid.signedWordGridRelations hscissor)

/-- **Lê's conjecture from the projection setup of the levels and the scissor cleanup.** -/
theorem leConjecture_of_levelSetup_frontier (hS : LevelSetupStatement)
    (hB : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi)
      (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L), P.OuterAdmissible →
        P.OuterHolds)
    (hC : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi)
      (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L), P.SetupProperties →
        P.CriticalHolds)
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_rootFamily_frontier
    (levelRootFamilyStatement_of_setup (levelProjectionSetupStatement_of_levelSetup hS hB hC))
    hscissor

/-- **Lê's conjecture from the setup construction, the critical-value field and the scissor
cleanup.** The outer-braid field is discharged by
`LevelProjectionSetup.outerHolds_of_admissible`. -/
theorem leConjecture_of_levelSetup_critical_frontier (hS : LevelSetupStatement)
    (hC : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi)
      (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L), P.SetupProperties →
        P.CriticalHolds)
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_levelSetup_frontier hS (fun _ _ _ _ _ P hP => P.outerHolds_of_admissible hP) hC
    hscissor

/-- **Lê's conjecture from the setup construction, the two critical local cases and the scissor
cleanup.** The critical-value field is assembled by `pointClusterStatement_of_cases` and
`criticalHolds_of_pointClusterStatement` from the local braids at smooth critical points
(`hSmooth`) and at singular points (`hSingular`). -/
theorem leConjecture_of_levelSetup_cases_frontier (hS : LevelSetupStatement)
    (hSmooth : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
        ∀ {c : ℂ} {x : Source 2}, c ∈ P.critical → x ∈ P.levelFibre c →
          ¬ Function.Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) →
            (∀ j, x ≠ L.point j) → Nonempty (P.PointClusterData c x))
    (hSingular : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
        ∀ j : Fin L.points.card,
          Nonempty (P.PointClusterData (P.baseCoord (A.H (L.point j))) (L.point j)))
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_levelSetup_critical_frontier hS
    (fun _ _ _ _ _ => criticalHolds_of_pointClusterStatement
      (pointClusterStatement_of_cases hSmooth hSingular) _ _ _ _ _)
    hscissor

/-- **Lê's conjecture from the setup construction, the smooth critical local case and the scissor
cleanup.** The singular local case is `LevelProjectionSetup.pointClusterData_of_singular`. -/
theorem leConjecture_of_levelSetup_smooth_frontier (hS : LevelSetupStatement)
    (hSmooth : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
        ∀ {c : ℂ} {x : Source 2}, c ∈ P.critical → x ∈ P.levelFibre c →
          ¬ Function.Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) →
            (∀ j, x ≠ L.point j) → Nonempty (P.PointClusterData c x))
    (hscissor : ScissorCleanupStatement) : LeConjecture :=
  leConjecture_of_levelSetup_cases_frontier hS hSmooth
    (fun P hP j => P.pointClusterData_of_singular hP j) hscissor

end OnLeConjecture.Analytic
