/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetCollar
public import OnLeConjecture.Analytic.PlaneMilnorFibreGenus

/-! # Comparing the target cut with the source Milnor fibre

Both families of cuts are cofinal. Their proved inclusion collars give the
two homotopy equivalences in an alternating four-term sandwich. This
identifies the rational homology of the target cut with that of a source
Milnor fibre without asserting that a single sandwich is sufficient.
-/

@[expose] public noncomputable section

open Filter Set Metric Function CategoryTheory
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology OnLeConjecture.PlaneCurve

/-- Continuity at the origin puts a sufficiently small Euclidean source
ball inside any prescribed positive target cutoff and source domain. -/
theorem exists_milnorFibre_subset_targetSectionCut (H : Source 2 → Source 3)
    (hH : ContinuousAt H 0) (hH0 : H 0 = 0) {R ε b : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ ∀ s : ℂ,
      milnorFibre (fun x => H x 0) a s ⊆ targetSectionCut H R ε s := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun z => (EuclideanSpace.equiv (Fin 3) ℂ).symm (H (e z))
  have hQ : ContinuousAt Q 0 :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.continuousAt.comp
      (hH.comp_of_eq e.continuous.continuousAt (map_zero _))
  have hQ0 : Q 0 = 0 := by simp [Q, map_zero, hH0]
  have hnear : ∀ᶠ z in 𝓝 (0 : CollarPlane), e z ∈ ball 0 R ∧ Q z ∈ ball 0 ε := by
    have he := e.continuous.continuousAt.tendsto (x := 0)
    rw [map_zero] at he
    have hq := hQ.tendsto
    rw [hQ0] at hq
    exact (he.eventually (ball_mem_nhds _ hR)).and (hq.eventually (ball_mem_nhds _ hε))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let a := min (r / 2) (b / 2)
  have ha : 0 < a := lt_min (half_pos hr) (half_pos hb)
  refine ⟨a, ha, (min_le_right _ _).trans_lt (half_lt_self hb), ?_⟩
  intro s z hz
  have hzr : z ∈ ball (0 : CollarPlane) r :=
    mem_ball_zero_iff.mpr (hz.1.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr)))
  have hzq := hrsub hzr
  exact (mem_targetSectionCut_iff hε.le).mpr
    ⟨⟨ball_subset_closedBall hzq.1, hz.2⟩, (mem_ball_zero_iff.mp hzq.2).le⟩

/-- Compact unique-fibre shrinking confines every sufficiently small target
cut to a prescribed Euclidean source ball. The source coordinate norm is
not identified with the Euclidean norm. -/
theorem exists_targetSectionCut_subset_milnorFibre (H : Source 2 → Source 3)
    (hH0 : H 0 = 0) {R b : ℝ} (hb : 0 < b)
    (hH : ContinuousOn H (closedBall (0 : Source 2) R))
    (hinj : InjOn H (closedBall (0 : Source 2) R))
    (hball : ∀ z : CollarPlane, ‖z‖ < b →
      (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ s : ℂ,
      targetSectionCut H R ε s ⊆ milnorFibre (fun x => H x 0) b s := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let S : Set CollarPlane := e ⁻¹' closedBall 0 R
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun z => (EuclideanSpace.equiv (Fin 3) ℂ).symm (H (e z))
  have hS : IsCompact S := e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 R)
  have hQ : ContinuousOn Q S :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
      (hH.comp e.continuous.continuousOn (fun _ hz => hz))
  have hQinj : InjOn Q S := by
    intro x hx y hy hxy
    exact e.injective (hinj hx hy ((EuclideanSpace.equiv (Fin 3) ℂ).symm.injective hxy))
  have hQ0 : Q 0 = 0 := by simp [Q, map_zero, hH0]
  have h0S : (0 : CollarPlane) ∈ S := hball 0 (by simpa using hb)
  have hsmall := eventually_mem_image_iff_of_compact_unique_fibre hS hQ
    (ball_mem_nhds (0 : CollarPlane) hb)
    (fun z hz => hball z (mem_ball_zero_iff.mp hz))
    (fun z hz hz0 => hQinj hz h0S (hz0.trans hQ0.symm))
  obtain ⟨ε, hε, hεsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro η hη hηε s z hz
  have hzz := (mem_targetSectionCut_iff hη).mp hz
  have hQz : Q z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) ε :=
    mem_ball_zero_iff.mpr (hzz.2.trans_lt (hηε.trans_lt (half_lt_self hε)))
  obtain ⟨y, hy, hyz⟩ := (hεsmall hQz).mpr ⟨z, hzz.1.1, rfl⟩
  have hyS : y ∈ S := hball y (mem_ball_zero_iff.mp hy)
  have hyz' : y = z := hQinj hyS hzz.1.1 hyz
  exact ⟨(mem_ball_zero_iff.mp (hyz' ▸ hy)).le, hzz.1.2⟩

/-- The literal target cut is compact in its fixed closed source domain. -/
theorem isCompact_targetSectionCut (H : Source 2 → Source 3) {R ε : ℝ} (s : ℂ)
    (hH : ContinuousOn H (closedBall (0 : Source 2) R)) :
    IsCompact (targetSectionCut H R ε s) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let S : Set CollarPlane := e ⁻¹' closedBall 0 R
  have hS : IsCompact S := e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 R)
  have hHe : ContinuousOn (fun z => H (e z)) S :=
    hH.comp e.continuous.continuousOn (fun _ hz => hz)
  have hpair : ContinuousOn (fun z =>
      (H (e z) 0, planeMapTargetRadiusSq H (e z))) S :=
    ((continuous_apply 0).comp_continuousOn hHe).prodMk
      (((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn hHe).norm.pow 2)
  have heq : targetSectionCut H R ε s = S ∩
      (fun z => (H (e z) 0, planeMapTargetRadiusSq H (e z))) ⁻¹' ({s} ×ˢ Iic (ε ^ 2)) := by
    ext z
    simp only [targetSectionCut, S, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      mem_prod, mem_singleton_iff, mem_Iic]
    tauto
  rw [heq]
  exact hS.of_isClosed_subset
    (hpair.preimage_isClosed_of_isClosed hS.isClosed (isClosed_singleton.prod isClosed_Iic))
    inter_subset_left

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The rational homology and numerical genus relations of a source Milnor
fibre transfer to the literal target cut through two inclusion collars.
The genus is recorded numerically, without asserting a target-boundary
manifold or an identification of its boundary components. -/
theorem exists_targetSectionCut_homology (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
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
  obtain ⟨R, εT, hR, hRA, hεT, ha, hinj, _, htarget⟩ := A.exists_targetSectionCut_collars
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
  refine ⟨R, min εsmall εT, hR, hRA, lt_min hεsmall hεT, ?_⟩
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

/-- The nearby level can be selected from the assembly's critical-section
construction while retaining the proved homology of its target cut. -/
theorem exists_level_with_targetSectionCut_homology (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A,
        L.radius = R ∧ ‖L.parameter‖ < ε ∧
        HasCurveRatHomology ↥(targetSectionCut A.H R ε L.parameter)
          (1 - (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) : ℤ)) ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 0) = 1 ∧
        Module.finrank ℚ (ratH ↥(targetSectionCut A.H R ε L.parameter) 1) =
          Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal A.sourceEquation) ∧
        IsCompact (targetSectionCut A.H R ε L.parameter) ∧
        IsPathConnected (targetSectionCut A.H R ε L.parameter) := by
  obtain ⟨R, ε₀, hR, hRA, hε₀, hhom⟩ := A.exists_targetSectionCut_homology
  refine ⟨R, ε₀, hR, hRA, hε₀, ?_⟩
  intro ε hε hεε₀
  obtain ⟨δ, hδ, hδhom⟩ := hhom ε hε hεε₀
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < min δ ε := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hδ hε)] with s hs
    exact mem_ball_zero_iff.mp hs
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := self_mem_nhdsWithin
  obtain ⟨s, ⟨hlevel, hbound⟩, hs0⟩ :=
    (((A.levels R hR hRA.le).and hsmall).filter_mono nhdsWithin_le_nhds |>.and hne).exists
  obtain ⟨Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩ := hlevel hs0
  let L : ResolutionSectionLevel A :=
    ⟨R, hR, hRA.le, s, hs0, Z, hZ, hcard, hHinj, hemb, hregular, hsingular, hsum⟩
  obtain ⟨hc, hzero, hone, hcompact, hpath, _⟩ := hδhom s hs0 (hbound.trans_le (min_le_left _ _))
  exact ⟨L, rfl, hbound.trans_le (min_le_right _ _), hc, hzero, hone, hcompact, hpath⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
