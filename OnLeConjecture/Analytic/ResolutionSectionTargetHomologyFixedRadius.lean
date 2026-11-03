/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetBoundaryCritical

/-! # Milnor homology at a retained source cutoff

The alternating inclusion argument is stated at the chosen source radius,
retaining the analyticity and injectivity needed to compare source cutoffs.
The assembly theorem in the following module discharges its collar inputs.
-/

@[expose] public noncomputable section

open Filter Set Metric Function CategoryTheory
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The proved two-collar comparison retains the prescribed source radius.
Both homotopy equivalences must have the literal inclusions as forward maps. -/
theorem targetSectionCut_homology_at_radius (A : ResolutionSectionAssembly g hd hi)
    {R εT : ℝ} (hR : 0 < R) (hεT : 0 < εT)
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R))
    (hinj : InjOn A.H (closedBall (0 : Source 2) R))
    (htarget : ∀ ε₂, 0 < ε₂ → ε₂ ≤ εT → ∀ ε₁, 0 < ε₁ → ε₁ ≤ ε₂ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s‖ < δ →
        ∃ e : ContinuousMap.HomotopyEquiv (targetSectionCut A.H R ε₁ s)
          (targetSectionCut A.H R ε₂ s), ∀ z, (e.toFun z : CollarPlane) = z) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
          HasCurveRatHomology ↥(targetSectionCut A.H R ε s)
            (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) : ℤ)) ∧
          Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε s) 0) = 1 ∧
          Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε s) 1) =
            Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) ∧
          IsCompact (targetSectionCut A.H R ε s) ∧
          IsPathConnected (targetSectionCut A.H R ε s) ∧
          ∃ γ : ℕ, 2 * γ + PlaneCurve.irreducibleBranchCount A.sourceEquation =
              Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε s) 1) + 1 ∧
            γ + PlaneCurve.irreducibleBranchCount A.sourceEquation =
              PlaneCurve.deltaInvariant A.sourceEquation + 1 := by
  let V : Source 2 → ℂ := fun x => A.H x 0
  have hV : AnalyticAt ℂ V 0 := (analyticAt_pi_iff.mp A.H_analytic) 0
  have hV0 : V 0 = 0 := by simp [V, A.H_zero]
  have heq : ofFunction V hV = A.sourceEquation := by
    rw [← A.sourceEquation_component]
    apply Subtype.ext
    exact (MapGerm.component_ofFunction A.H A.H_analytic 0).symm
  have hsq : Squarefree (ofFunction V hV) := heq ▸ A.sourceEquation_squarefree
  obtain ⟨εM, hεM, hmilnor⟩ := exists_milnorFibre_topology V hV hV0 hsq
  obtain ⟨εC, hεC, hsource⟩ := exists_milnorFibre_collar V hV hV0 hsq
  obtain ⟨b, hb, hbsmall, hBT⟩ := exists_milnorFibre_subset_targetSectionCut A.H
    A.H_analytic.continuousAt A.H_zero hR hεT (lt_min hεM hεC)
  have hbM : b ≤ εM := hbsmall.le.trans (min_le_left _ _)
  have hbC : b ≤ εC := hbsmall.le.trans (min_le_right _ _)
  have hball : ∀ z : CollarPlane, ‖z‖ < b →
      (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 R := by
    intro z hz
    exact (hBT (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0) ⟨hz.le, rfl⟩).1.1
  obtain ⟨εsmall, hεsmall, hTB⟩ := exists_targetSectionCut_subset_milnorFibre A.H
    A.H_zero hb ha.continuousOn hinj hball
  refine ⟨min εsmall εT, lt_min hεsmall hεT, ?_⟩
  intro ε hε hεbound
  have hεsmall' : ε ≤ εsmall := hεbound.trans (min_le_left _ _)
  have hεT' : ε ≤ εT := hεbound.trans (min_le_right _ _)
  obtain ⟨a, ha', hab, hAT⟩ := exists_milnorFibre_subset_targetSectionCut A.H
    A.H_analytic.continuousAt A.H_zero hR hε hb
  obtain ⟨δS, hδS, hS⟩ := hsource b hb hbC a ha' hab
  obtain ⟨δT, hδT, hT⟩ := htarget εT hεT le_rfl ε hε hεT'
  obtain ⟨δM, hδM, hM⟩ := hmilnor b hb hbM
  refine ⟨min δS (min δT δM), lt_min hδS (lt_min hδT hδM), ?_⟩
  intro s hs0 hs
  have hsS : ‖s‖ < δS := hs.trans_le (min_le_left _ _)
  have hsT : ‖s‖ < δT := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsM : ‖s‖ < δM := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨eS, heS⟩ := hS s hsS
  obtain ⟨eT, heT⟩ := hT s hsT
  have hAB : milnorFibre V a s ⊆ targetSectionCut A.H R ε s := hAT s
  have hBC : targetSectionCut A.H R ε s ⊆ milnorFibre V b s := hTB ε hε.le hεsmall' s
  have hCD : milnorFibre V b s ⊆ targetSectionCut A.H R εT s := hBT s
  let f₁ : C(↥(milnorFibre V a s), ↥(targetSectionCut A.H R ε s)) :=
    ⟨Set.inclusion hAB, continuous_inclusion hAB⟩
  let f₂ : C(↥(targetSectionCut A.H R ε s), ↥(milnorFibre V b s)) :=
    ⟨Set.inclusion hBC, continuous_inclusion hBC⟩
  let f₃ : C(↥(milnorFibre V b s), ↥(targetSectionCut A.H R εT s)) :=
    ⟨Set.inclusion hCD, continuous_inclusion hCD⟩
  have he₁ : eS.toFun = f₂.comp f₁ := by
    exact ContinuousMap.ext fun z => Subtype.ext (heS z)
  have he₂ : eT.toFun = f₃.comp f₂ := by
    exact ContinuousMap.ext fun z => Subtype.ext (heT z)
  have hiso : ∀ n, IsIso (ratHMap f₂ n) := fun n =>
    isIso_ratHMap_of_sandwich f₁ f₂ f₃ eS he₁ eT he₂ n
  let eH : ∀ n, ratH ↥(targetSectionCut A.H R ε s) n ≅ ratH ↥(milnorFibre V b s) n :=
    fun n => @asIso _ _ _ _ (ratHMap f₂ n) (hiso n)
  obtain ⟨_, _, _, _, _, _, _, _, hcurve, hzero, hone, _, γ, hg₁, _, hg₂⟩ := hM s hs0 hsM
  have hc : HasCurveRatHomology ↥(targetSectionCut A.H R ε s)
      (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) : ℤ)) := by
    rw [← heq]
    exact hcurve.of_iso eH
  have hzero' : Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε s) 0) = 1 :=
    (finrank_eq_of_iso (eH 0)).trans hzero
  have hone' : Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε s) 1) =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) := by
    rw [finrank_eq_of_iso (eH 1), hone, heq]
  have hpc : PathConnectedSpace ↥(targetSectionCut A.H R ε s) :=
    pathConnectedSpace_of_finrank_ratH_zero hc.finite₀ hzero'
  refine ⟨hc, hzero', hone', isCompact_targetSectionCut A.H s ha.continuousOn,
    isPathConnected_iff_pathConnectedSpace.mpr hpc, γ, ?_, ?_⟩
  · rw [← heq, finrank_eq_of_iso (eH 1)]
    exact hg₁
  · simpa only [heq] using hg₂


end ResolutionSectionAssembly

end OnLeConjecture.Analytic
