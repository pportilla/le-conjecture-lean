/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetHomologyFixedRadius

/-! # One target cut with homology, oriented charts, and interior critical points

Compact confinement makes cuts with two source cutoffs literally equal.
This permits the Milnor homology comparison and the uniform target-annulus
estimate to be used for the same nearby section. All its critical points
are then strictly inside half the chosen target radius.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

/-- Confinement makes the two source-cutoff versions of the target cut
literally equal. The norm bound is the same Euclidean target bound. -/
theorem targetSectionCut_eq_of_confinement (H : Source 2 → Source 3)
    {R r ε : ℝ} (hrR : r ≤ R) (hε : 0 ≤ ε)
    (hconf : ∀ x ∈ closedBall (0 : Source 2) R,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε → x ∈ closedBall 0 r)
    (s : ℂ) : targetSectionCut H R ε s = targetSectionCut H r ε s := by
  ext z
  rw [mem_targetSectionCut_iff hε, mem_targetSectionCut_iff hε]
  constructor
  · intro hz
    exact ⟨⟨hconf _ hz.1.1 hz.2, hz.1.2⟩, hz.2⟩
  · intro hz
    exact ⟨⟨closedBall_subset_closedBall hrR hz.1.1, hz.1.2⟩, hz.2⟩

/-- The corresponding literal target boundaries are equal under the same
confinement hypothesis. -/
theorem targetSectionBoundary_eq_of_confinement (H : Source 2 → Source 3)
    {R r ε : ℝ} (hrR : r ≤ R)
    (hconf : ∀ x ∈ closedBall (0 : Source 2) R,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε → x ∈ closedBall 0 r)
    (s : ℂ) : targetSectionBoundary H R ε s = targetSectionBoundary H r ε s := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨hconf _ hz.1.1 hz.2.le, hz.1.2⟩, hz.2⟩
  · intro hz
    exact ⟨⟨closedBall_subset_closedBall hrR hz.1.1, hz.1.2⟩, hz.2⟩

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- One actual nearby section retains the Milnor homology, the oriented
outer boundary charts, and the whole finite critical list inside the inner
target cut. Every analytic, confinement and transversivity input is derived
from the assembly. -/
theorem exists_common_targetSectionLevel (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
      InjOn A.H (closedBall (0 : Source 2) R) ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A,
        L.radius = R ∧ ‖L.parameter‖ < ε / 2 ∧
        HasCurveRatHomology ↥(targetSectionCut A.H R ε L.parameter)
          (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) : ℤ)) ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 0) = 1 ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 1) =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) ∧
        IsCompact (targetSectionCut A.H R ε L.parameter) ∧
        IsPathConnected (targetSectionCut A.H R ε L.parameter) ∧
        (∃ γ : ℕ, 2 * γ + irreducibleBranchCount A.sourceEquation =
            Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 1) + 1 ∧
          γ + irreducibleBranchCount A.sourceEquation = deltaInvariant A.sourceEquation + 1) ∧
        (∀ x ∈ closedBall (0 : Source 2) R,
          ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε → x ∈ ball 0 (R / 2)) ∧
        (∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = L.parameter →
          ε / 2 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ →
          Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x)) ∧
        (∀ z ∈ targetSectionBoundary A.H R ε L.parameter,
          Nonempty (SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
            (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
            ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z)) ∧
        ∀ x ∈ L.points,
          ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ < ε / 2 := by
  obtain ⟨B, εT, hB, hBA, hεT, haB, hinjB, _, hcollar⟩ := A.exists_targetSectionCut_collars
  obtain ⟨εH, hεH, hhomology⟩ :=
    A.targetSectionCut_homology_at_radius hB hεT haB hinjB hcollar
  have hsquare : Squarefree (ofFunction (fun x => A.H x 0)
      ((analyticAt_pi_iff.mp A.H_analytic) 0)) := by
    have heq : ofFunction (fun x => A.H x 0) ((analyticAt_pi_iff.mp A.H_analytic) 0) =
        A.sourceEquation := by
      rw [← A.sourceEquation_component]
      apply Subtype.ext
      exact (MapGerm.component_ofFunction A.H A.H_analytic 0).symm
    rw [heq]
    exact A.sourceEquation_squarefree
  obtain ⟨R, hR, hRBhalf, ha, hsub⟩ :=
    exists_uniform_planeMapTargetRadialPair_submersion A.H A.H_analytic A.H_zero
      (closedBall 0 B) (closedBall_mem_nhds _ hB) hinjB hsquare (B / 2) (half_pos hB)
  have hRB : R < B := hRBhalf.trans_lt (half_lt_self hB)
  have hRA : R < A.radius := hRB.trans hBA
  have hinj : InjOn A.H (closedBall (0 : Source 2) R) :=
    hinjB.mono (closedBall_subset_closedBall hRB.le)
  obtain ⟨εC, hεC, hconf⟩ := exists_euclidean_target_cut_confinement A.H A.H_zero
    (half_pos hR) ((half_lt_self hR).trans hRB) haB.continuousOn hinjB
  have hQc : ContinuousOn (fun x => ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖)
      (closedBall (0 : Source 2) R) :=
    ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn ha.continuousOn).norm
  obtain ⟨xM, _, hM⟩ := (isCompact_closedBall (0 : Source 2) R).exists_isMaxOn
    ⟨0, mem_closedBall_self hR.le⟩ hQc
  let M := ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H xM)‖
  refine ⟨R, min εH εC, hR, hRA, lt_min hεH hεC, ha, hinj, ?_⟩
  intro ε hε hε₀
  have hεH' : ε ≤ εH := hε₀.trans (min_le_left _ _)
  have hεC' : ε ≤ εC := hε₀.trans (min_le_right _ _)
  obtain ⟨δH, hδH, hH⟩ := hhomology ε hε hεH'
  obtain ⟨δR, hδR, hRsub⟩ := hsub (ε / 2) M (half_pos hε)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < min δH (min δR (ε / 2)) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hδH (lt_min hδR (half_pos hε)))] with s hs
    exact mem_ball_zero_iff.mp hs
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := self_mem_nhdsWithin
  obtain ⟨s, ⟨hlevel, hsbound⟩, hs0⟩ :=
    (((A.levels R hR hRA.le).and hsmall).filter_mono nhdsWithin_le_nhds |>.and hne).exists
  have hsH : ‖s‖ < δH := hsbound.trans_le (min_le_left _ _)
  have hsR : ‖s‖ < δR := hsbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsε : ‖s‖ < ε / 2 := hsbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩ := hlevel hs0
  let L : ResolutionSectionLevel A :=
    ⟨R, hR, hRA.le, s, hs0, Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩
  have hconfR : ∀ x ∈ closedBall (0 : Source 2) R,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε → x ∈ ball 0 (R / 2) :=
    fun x hx hxε => hconf x (closedBall_subset_closedBall hRB.le hx) (hxε.trans hεC')
  have heq : targetSectionCut A.H B ε s = targetSectionCut A.H R ε s :=
    targetSectionCut_eq_of_confinement A.H hRB.le hε.le
      (fun x hx hxε => ball_subset_closedBall
        (ball_subset_ball (half_lt_self hR).le (hconf x hx (hxε.trans hεC')))) s
  obtain ⟨hc, hzero, hone, hcompact, hpath, hgenus⟩ := hH s hs0 hsH
  rw [heq] at hc hzero hone hcompact hpath hgenus
  have hsubR : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = s →
      ε / 2 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ →
      Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x) := by
    intro x hx hxs hxε
    exact hRsub x hx hxε (hM hx) (by rw [hxs]; exact hsR)
  refine ⟨L, rfl, hsε, hc, hzero, hone, hcompact, hpath, hgenus, hconfR, hsubR, ?_, ?_⟩
  · intro z hz
    apply nonempty_targetSectionBoundaryChart A.H ha hz
      (ball_subset_ball (half_lt_self hR).le (hconfR _ hz.1.1 hz.2.le))
    exact hsubR _ hz.1.1 hz.1.2 (by rw [hz.2]; exact (half_lt_self hε).le)
  · intro x hx
    have hxp := (L.points_iff x).mp hx
    change x ∈ ball 0 R ∧ A.H x 0 = s ∧ ¬ Injective (fderiv ℂ A.H x) at hxp
    by_contra hn
    have hlarge : ε / 2 ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ := le_of_not_gt hn
    let z : CollarPlane := (EuclideanSpace.equiv (Fin 2) ℂ).symm x
    have hze : (EuclideanSpace.equiv (Fin 2) ℂ) z = x :=
      (EuclideanSpace.equiv (Fin 2) ℂ).apply_symm_apply x
    have hzb : z ∈ targetSectionBoundary A.H R
        ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ s := by
      change (_ ∈ closedBall 0 R ∧ _ = s) ∧ _ = _
      rw [hze]
      exact ⟨⟨ball_subset_closedBall hxp.1, hxp.2.1⟩, rfl⟩
    obtain ⟨C⟩ := nonempty_targetSectionBoundaryChart A.H ha hzb
      (hze.symm ▸ hxp.1) (hze.symm ▸ hsubR x (ball_subset_closedBall hxp.1) hxp.2.1 hlarge)
    have hf : fderiv ℂ (fun y => A.H y 0) ((EuclideanSpace.equiv (Fin 2) ℂ) z) ≠ 0 := by
      rw [hze]
      exact (hregular x hxp.1 hxp.2.1).1
    have hinj' := injective_fderiv_of_targetSectionBoundaryChart A.H ha hzb hf C
    rw [hze] at hinj'
    exact hxp.2.2 hinj'

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
