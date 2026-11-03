/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetCollarFlow

/-! # Inclusion equivalences for Euclidean target cuts

Source coordinates are converted explicitly to a Euclidean plane. The
closed source domain remains a preimage of its original coordinate ball.
The cutoff radius is the Euclidean norm of the three target coordinates.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A target cut in Euclidean source coordinates, retaining its original
closed source domain as a separate condition. -/
def targetSectionCut (H : Source 2 → Source 3) (R ε : ℝ) (s : ℂ) : Set CollarPlane :=
  {z | ((EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 R ∧
    H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0 = s) ∧
    planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) z) ≤ ε ^ 2}

theorem mem_targetSectionCut_iff {H : Source 2 → Source 3} {R ε : ℝ} {s : ℂ}
    {z : CollarPlane} (hε : 0 ≤ ε) : z ∈ targetSectionCut H R ε s ↔
    ((EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 R ∧
      H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0 = s) ∧
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
      (H ((EuclideanSpace.equiv (Fin 2) ℂ) z))‖ ≤ ε := by
  exact and_congr_right fun _ => pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero

/-- Joint submersivity and confinement in the original source ball give
the literal target-cut inclusion a homotopy inverse. -/
theorem targetSectionCut_collar_of_transverse (H : Source 2 → Source 3)
    {R ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁ε₂ : ε₁ ≤ ε₂)
    (ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R)) (s : ℂ)
    (hconf : ∀ x ∈ closedBall (0 : Source 2) R,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε₂ → x ∈ ball 0 R)
    (hsub : ∀ x ∈ closedBall (0 : Source 2) R, H x 0 = s →
      ε₁ ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ →
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε₂ →
      Surjective (fderiv ℝ (planeMapTargetRadialPair H) x)) :
    ∃ e : ContinuousMap.HomotopyEquiv (targetSectionCut H R ε₁ s)
      (targetSectionCut H R ε₂ s), ∀ z, (e.toFun z : CollarPlane) = z := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let f : CollarPlane → ℂ := fun z => H (e z) 0
  let ρ : CollarPlane → ℝ := fun z => planeMapTargetRadiusSq H (e z)
  let S : Set CollarPlane := e ⁻¹' closedBall 0 R
  let U : Set CollarPlane := e ⁻¹' ball 0 R
  have hS : IsCompact S := e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 R)
  have hU : IsOpen U := isOpen_ball.preimage e.continuous
  have hUS : U ⊆ S := fun _ hz => ball_subset_closedBall hz
  have hfa : AnalyticOnNhd ℂ f S := fun z hz =>
    ((analyticAt_pi_iff.mp (ha (e z) hz)) 0).comp (e.analyticAt z)
  have hρa : ∀ z ∈ S, ContDiffAt ℝ ∞ ρ z := fun z hz =>
    (contDiffAt_planeMapTargetRadiusSq (ha (e z) hz)).comp z
      (e.contDiff.contDiffAt.restrict_scalars ℝ)
  refine sectionRadius_collar_of_transverse f ρ S U hS hU hUS hfa.continuousOn
    (fun z hz => (hρa z hz).continuousAt.continuousWithinAt)
    (hfa.mono hUS) (fun z hz => hρa z (hUS hz))
    (pow_le_pow_left₀ hε₁ hε₁ε₂ 2) s ?_ ?_
  · intro z hz _ _ hz₂
    exact hconf (e z) hz
      ((pow_le_pow_iff_left₀ (norm_nonneg _) (hε₁.trans hε₁ε₂) two_ne_zero).mp hz₂)
  · intro z hz hzs hz₁ hz₂
    have hh := ha (e z) hz
    have hd : fderiv ℝ (fun z => (f z, ρ z)) z =
        (fderiv ℝ (planeMapTargetRadialPair H) (e z)).comp
          (e.toContinuousLinearMap.restrictScalars ℝ) :=
      (((contDiffAt_planeMapTargetRadialPair hh).differentiableAt (by simp)).hasFDerivAt.comp z
        (e.hasFDerivAt.restrictScalars ℝ)).fderiv
    rw [hd]
    exact (hsub (e z) hz hzs
      ((pow_le_pow_iff_left₀ hε₁ (norm_nonneg _) two_ne_zero).mp hz₁)
      ((pow_le_pow_iff_left₀ (norm_nonneg _) (hε₁.trans hε₁ε₂) two_ne_zero).mp hz₂)).comp
        e.surjective

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The assembled map admits target collars at every sufficiently small
pair of radii and all sufficiently small section levels. No transversivity
or collar hypothesis is added to the assembly. -/
theorem exists_targetSectionCut_collars (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
      InjOn A.H (closedBall (0 : Source 2) R) ∧
      (∀ x ∈ closedBall (0 : Source 2) R,
        ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ ≤ ε₀ → x ∈ ball 0 (R / 2)) ∧
      ∀ ε₂, 0 < ε₂ → ε₂ ≤ ε₀ → ∀ ε₁, 0 < ε₁ → ε₁ ≤ ε₂ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s‖ < δ →
          ∃ e : ContinuousMap.HomotopyEquiv (targetSectionCut A.H R ε₁ s)
            (targetSectionCut A.H R ε₂ s), ∀ z, (e.toFun z : CollarPlane) = z := by
  obtain ⟨L, hL⟩ := A.exists_level_at_radius A.radius A.radius_pos le_rfl
  have hinjA : InjOn A.H (ball (0 : Source 2) A.radius) := by simpa only [hL] using L.injective
  have hsquare : Squarefree (ofFunction (fun x => A.H x 0)
      ((analyticAt_pi_iff.mp A.H_analytic) 0)) := by
    have heq : ofFunction (fun x => A.H x 0) ((analyticAt_pi_iff.mp A.H_analytic) 0) =
        A.sourceEquation := by
      rw [← A.sourceEquation_component]
      apply Subtype.ext
      exact (MapGerm.component_ofFunction A.H A.H_analytic 0).symm
    rw [heq]
    exact A.sourceEquation_squarefree
  obtain ⟨B, hB, hBA, haB, hsubB⟩ :=
    exists_uniform_planeMapTargetRadialPair_submersion A.H A.H_analytic A.H_zero
      (ball 0 A.radius) (ball_mem_nhds _ A.radius_pos) hinjA hsquare A.radius A.radius_pos
  let R := B / 2
  have hR : 0 < R := half_pos hB
  have hRB : R < B := half_lt_self hB
  have hRA : R < A.radius := hRB.trans_le hBA
  have ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) :=
    haB.mono (closedBall_subset_closedBall hRB.le)
  have hinj : InjOn A.H (closedBall (0 : Source 2) R) :=
    hinjA.mono (closedBall_subset_ball hRA)
  obtain ⟨ε₀, hε₀, hconf⟩ := exists_euclidean_target_cut_confinement A.H A.H_zero
    (half_pos hR) (half_lt_self hR) ha.continuousOn hinj
  refine ⟨R, ε₀, hR, hRA, hε₀, ha, hinj, hconf, ?_⟩
  intro ε₂ _ hε₂ ε₁ hε₁ hε₁ε₂
  obtain ⟨δ, hδ, hsub⟩ := hsubB ε₁ ε₂ hε₁
  refine ⟨δ, hδ, fun s hs => targetSectionCut_collar_of_transverse A.H hε₁.le hε₁ε₂ ha s
    (fun x hx hxe => ball_subset_ball (half_lt_self hR).le (hconf x hx (hxe.trans hε₂))) ?_⟩
  intro x hx hxs hx₁ hx₂
  exact hsub x (closedBall_subset_closedBall hRB.le hx) hx₁ hx₂ (by rw [hxs]; exact hs)

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
