/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionCoordinateDiskLocal

/-! # The inward coordinate and orientation at a removed source disk

The exterior lies on the increasing-coordinate-radius side. Its inward
radius function is therefore the negative squared coordinate norm. The
oriented boundary tangent has strictly negative angular sign in this
same holomorphic coordinate.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic
namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

/-- The decreasing radius function whose sublevel is outside the disk. -/
def holeRadius (D : PlaneLevelCoordinateDisk f s z) (w : CollarPlane) : ℝ :=
  -‖D.coordinate (w - z)‖ ^ 2

theorem contDiff_holeRadius (D : PlaneLevelCoordinateDisk f s z) :
    ContDiff ℝ ω D.holeRadius :=
  (((D.coordinate.restrictScalars ℝ).contDiff.comp
    (contDiff_id.sub contDiff_const)).norm_sq (𝕜 := ℂ)).neg

theorem fderiv_holeRadius (D : PlaneLevelCoordinateDisk f s z) (w v : CollarPlane) :
    fderiv ℝ D.holeRadius w v =
      -2 * (conj (D.coordinate (w - z)) * D.coordinate v).re := by
  have hq : HasFDerivAt (fun y => D.coordinate (y - z))
      (D.coordinate.restrictScalars ℝ) w := by
    simpa using (D.coordinate.hasFDerivAt (x := w)).restrictScalars ℝ
  have hd : HasFDerivAt D.holeRadius
      (-(2 • (innerSL ℝ (D.coordinate (w - z))).comp (D.coordinate.restrictScalars ℝ))) w := by
    convert hq.norm_sq.neg using 1 <;> rfl
  rw [hd.fderiv]
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.coe_restrictScalars', nsmul_eq_mul, Nat.cast_ofNat]
  rw [Complex.inner]
  simp only [mul_comm (D.coordinate v) (conj (D.coordinate (w - z)))]
  ring

/-- Joint submersivity follows from the retained holomorphic coordinate,
without an additional boundary-transversivity assumption. -/
theorem holeRadius_pair_surjective (D : PlaneLevelCoordinateDisk f s z) {u : ℂ}
    (hu : u ∈ D.W) (hu0 : u ≠ 0) (hf : AnalyticAt ℂ f (D.ψ u))
    (hfn : fderiv ℂ f (D.ψ u) ≠ 0) :
    Surjective (fderiv ℝ (fun w => (f w, D.holeRadius w)) (D.ψ u)) := by
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective_euclidean _
    (D.coordinate_prod_fderiv_injective hu hf.differentiableAt hfn)
  have hs : Surjective (fderiv ℝ f (D.ψ u)) := by
    intro c
    obtain ⟨v, hv⟩ := e.surjective (0, c)
    refine ⟨v, ?_⟩
    rw [hf.differentiableAt.fderiv_restrictScalars ℝ]
    have h := congrArg Prod.snd hv
    rwa [← ContinuousLinearEquiv.coe_coe, he] at h
  have hk : fderiv ℝ f (D.ψ u) (fderiv ℂ D.ψ u u) = 0 := by
    rw [hf.differentiableAt.fderiv_restrictScalars ℝ]
    exact D.level_fderiv hu hf.differentiableAt u
  have hr : fderiv ℝ D.holeRadius (D.ψ u) (fderiv ℂ D.ψ u u) ≠ 0 := by
    rw [D.fderiv_holeRadius, D.left_inverse _ hu, D.coordinate_fderiv hu]
    have hp : 0 < (conj u * u).re := by
      simpa [Complex.mul_re, Complex.normSq_apply] using Complex.normSq_pos.mpr hu0
    nlinarith
  rw [((hf.differentiableAt.restrictScalars ℝ).hasFDerivAt.prodMk
    (D.contDiff_holeRadius.differentiable (by simp) (D.ψ u)).hasFDerivAt).fderiv]
  exact DifferentialTopology.surjective_prod_of_surjective_of_nonzero_on_ker _ _ hs _ hk hr

/-- The real-axis tangent of an oriented upper-half-plane chart has the
clockwise angular sign appropriate to the exterior of the source disk. -/
theorem holeRadius_chart_tangent (D : PlaneLevelCoordinateDisk f s z)
    {O : Set CollarPlane} {w : CollarPlane}
    (C : SectionRadiusBoundaryChart f D.holeRadius O w)
    (hf : DifferentiableAt ℂ f w) :
    fderiv ℂ f w (fderiv ℝ C.φ 0 1) = 0 ∧
      (conj (D.coordinate (w - z)) * D.coordinate (fderiv ℝ C.φ 0 1)).re = 0 ∧
      (conj (D.coordinate (w - z)) * D.coordinate (fderiv ℝ C.φ 0 1)).im < 0 := by
  obtain ⟨hk, hu, hv⟩ := C.tangent_properties hf
    (D.contDiff_holeRadius.differentiable (by simp) w)
  rw [D.fderiv_holeRadius] at hu hv
  have hre : (conj (D.coordinate (w - z)) * D.coordinate (fderiv ℝ C.φ 0 1)).re = 0 := by
    linarith
  obtain ⟨c, hc, hci⟩ := C.oriented 0 C.zero_mem
  rw [hci, map_smul, smul_eq_mul, ← mul_assoc,
    mul_comm (conj (D.coordinate (w - z))) c, mul_assoc, Complex.mul_re,
    hre, mul_zero, zero_sub] at hv
  exact ⟨hk 1, hre, by nlinarith⟩

end PlaneLevelCoordinateDisk
end OnLeConjecture.Analytic
