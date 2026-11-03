/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetConfinement
public import OnLeConjecture.Analytic.PlaneMilnorFibreCollar

/-! # A collar field for a general radius on a plane section

The two real components of the radius differential on the complex kernel
line determine a field tangent to the equation and decreasing the radius
at unit speed. Joint submersivity proves that its denominator is nonzero.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

abbrev CollarPlane := EuclideanSpace ℂ (Fin 2)

def sectionRadiusDerivative (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (z : CollarPlane) : ℝ := fderiv ℝ ρ z (euclideanKernelVector f z)

def sectionRadiusImagDerivative (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (z : CollarPlane) : ℝ := fderiv ℝ ρ z (Complex.I • euclideanKernelVector f z)

def sectionRadiusDenominator (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (z : CollarPlane) : ℝ :=
  sectionRadiusDerivative f ρ z ^ 2 + sectionRadiusImagDerivative f ρ z ^ 2

def sectionRadiusField (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (z : CollarPlane) : CollarPlane :=
  -(sectionRadiusDenominator f ρ z)⁻¹ •
    (sectionRadiusDerivative f ρ z • euclideanKernelVector f z +
      sectionRadiusImagDerivative f ρ z • (Complex.I • euclideanKernelVector f z))

/-- The explicit complex kernel vector spans every kernel vector when the
complex differential is nonzero. -/
theorem exists_smul_euclideanKernelVector {f : CollarPlane → ℂ} {z v : CollarPlane}
    (hL : fderiv ℂ f z ≠ 0) (hv : fderiv ℂ f z v = 0) :
    ∃ c : ℂ, v = c • euclideanKernelVector f z := by
  let a := fderiv ℂ f z (EuclideanSpace.single 0 1)
  let b := fderiv ℂ f z (EuclideanSpace.single 1 1)
  have hcoord (w : CollarPlane) : fderiv ℂ f z w = w 0 * a + w 1 * b := by
    have hw : w = w 0 • EuclideanSpace.single 0 1 + w 1 • EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hw]
    simp [a, b]
  have hv' : v 0 * a + v 1 * b = 0 := (hcoord v).symm.trans hv
  have hK0 : (euclideanKernelVector f z) 0 = -b := by simp [euclideanKernelVector, b]
  have hK1 : (euclideanKernelVector f z) 1 = a := by simp [euclideanKernelVector, a]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hL
      ext w
      simp [hcoord, ha, hb]
    refine ⟨-(v 0 / b), ?_⟩
    have hv1 : v 1 = 0 := (mul_eq_zero.mp (by simpa [ha] using hv')).resolve_right hb
    ext i
    fin_cases i
    · change v 0 = -(v 0 / b) * (euclideanKernelVector f z) 0
      rw [hK0]
      field_simp
    · change v 1 = -(v 0 / b) * (euclideanKernelVector f z) 1
      rw [hK1, ha, mul_zero, hv1]
  · refine ⟨v 1 / a, ?_⟩
    ext i
    fin_cases i
    · change v 0 = v 1 / a * (euclideanKernelVector f z) 0
      rw [hK0]
      field_simp
      linear_combination hv'
    · change v 1 = v 1 / a * (euclideanKernelVector f z) 1
      rw [hK1, div_mul_cancel₀ _ ha]

/-- Joint submersivity supplies a nonzero real derivative along the complex
kernel line, so the sum of squares in the collar field cannot vanish. -/
theorem sectionRadiusDenominator_ne_zero {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hf : DifferentiableAt ℂ f z) (hρ : DifferentiableAt ℝ ρ z)
    (hs : Surjective (fderiv ℝ (fun z => (f z, ρ z)) z)) :
    sectionRadiusDenominator f ρ z ≠ 0 := by
  rw [((hf.hasFDerivAt.restrictScalars ℝ).prodMk hρ.hasFDerivAt).fderiv] at hs
  obtain ⟨u, hu⟩ := hs (1, 0)
  obtain ⟨v, hv⟩ := hs (0, 1)
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_restrictScalars',
    Prod.mk.injEq] at hu hv
  have hL : fderiv ℂ f z ≠ 0 := by
    intro h
    simpa [h] using hu.1
  obtain ⟨c, rfl⟩ := exists_smul_euclideanKernelVector hL hv.1
  intro hd
  have ha : sectionRadiusDerivative f ρ z = 0 := by
    have h := sq_nonneg (sectionRadiusImagDerivative f ρ z)
    dsimp [sectionRadiusDenominator] at hd
    nlinarith [sq_nonneg (sectionRadiusDerivative f ρ z)]
  have hb : sectionRadiusImagDerivative f ρ z = 0 := by
    dsimp [sectionRadiusDenominator] at hd
    rw [ha] at hd
    nlinarith [sq_nonneg (sectionRadiusImagDerivative f ρ z)]
  have hc : c • euclideanKernelVector f z =
      c.re • euclideanKernelVector f z + c.im • (Complex.I • euclideanKernelVector f z) := by
    have he : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    calc
      c • _ = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • _ := congrArg (fun q : ℂ => q • _) he
      _ = _ := by simp only [add_smul, mul_smul, ← Complex.coe_smul]
  have hv2 := hv.2
  rw [hc, map_add, map_smul, map_smul] at hv2
  change c.re * sectionRadiusDerivative f ρ z +
    c.im * sectionRadiusImagDerivative f ρ z = 1 at hv2
  simp [ha, hb] at hv2

theorem fderiv_sectionRadiusField (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (z : CollarPlane) : fderiv ℂ f z (sectionRadiusField f ρ z) = 0 := by
  simp [sectionRadiusField, fderiv_euclideanKernelVector]

theorem radius_fderiv_sectionRadiusField {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hz : sectionRadiusDenominator f ρ z ≠ 0) :
    fderiv ℝ ρ z (sectionRadiusField f ρ z) = -1 := by
  simp only [sectionRadiusField, map_smul, map_add, smul_eq_mul]
  change -(sectionRadiusDenominator f ρ z)⁻¹ *
    (sectionRadiusDerivative f ρ z * sectionRadiusDerivative f ρ z +
      sectionRadiusImagDerivative f ρ z * sectionRadiusImagDerivative f ρ z) = -1
  rw [← sq, ← sq, ← sectionRadiusDenominator, neg_mul, inv_mul_cancel₀ hz]

theorem contDiffAt_sectionRadiusDerivative {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hf : AnalyticAt ℂ f z) (hρ : ContDiffAt ℝ ∞ ρ z) :
    ContDiffAt ℝ ∞ (sectionRadiusDerivative f ρ) z := by
  exact (hρ.fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_euclideanKernelVector hf)

theorem contDiffAt_sectionRadiusImagDerivative {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hf : AnalyticAt ℂ f z) (hρ : ContDiffAt ℝ ∞ ρ z) :
    ContDiffAt ℝ ∞ (sectionRadiusImagDerivative f ρ) z := by
  exact (hρ.fderiv_right (m := ∞) (by simp)).clm_apply
    ((contDiffAt_const (c := Complex.I)).smul (contDiffAt_euclideanKernelVector hf))

theorem contDiffAt_sectionRadiusDenominator {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hf : AnalyticAt ℂ f z) (hρ : ContDiffAt ℝ ∞ ρ z) :
    ContDiffAt ℝ ∞ (sectionRadiusDenominator f ρ) z :=
  ((contDiffAt_sectionRadiusDerivative hf hρ).pow 2).add
    ((contDiffAt_sectionRadiusImagDerivative hf hρ).pow 2)

theorem contDiffAt_sectionRadiusField {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ}
    {z : CollarPlane} (hf : AnalyticAt ℂ f z) (hρ : ContDiffAt ℝ ∞ ρ z)
    (hz : sectionRadiusDenominator f ρ z ≠ 0) :
    ContDiffAt ℝ ∞ (sectionRadiusField f ρ) z :=
  ((contDiffAt_sectionRadiusDenominator hf hρ).inv hz).neg.smul
    (((contDiffAt_sectionRadiusDerivative hf hρ).smul (contDiffAt_euclideanKernelVector hf)).add
      ((contDiffAt_sectionRadiusImagDerivative hf hρ).smul
        ((contDiffAt_const (c := Complex.I)).smul (contDiffAt_euclideanKernelVector hf))))

/-- A smooth cutoff of the explicit field is supported in the prescribed
open domain and retains unit radius speed on the compact transverse set. -/
theorem exists_sectionRadius_cutoff (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    {K U : Set CollarPlane} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hρ : ∀ z ∈ U, ContDiffAt ℝ ∞ ρ z)
    (hsub : ∀ z ∈ K, Surjective (fderiv ℝ (fun z => (f z, ρ z)) z)) :
    ∃ χ : CollarPlane → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ (∀ z ∈ K, χ z = 1) ∧
      (∀ z ∈ tsupport χ, sectionRadiusDenominator f ρ z ≠ 0) ∧
      ContDiff ℝ ∞ (fun z => χ z • sectionRadiusField f ρ z) ∧
      HasCompactSupport (fun z => χ z • sectionRadiusField f ρ z) ∧
      (∀ z, fderiv ℂ f z (χ z • sectionRadiusField f ρ z) = 0) ∧
      (∀ z, fderiv ℝ ρ z (χ z • sectionRadiusField f ρ z) = -χ z) := by
  let W := U ∩ sectionRadiusDenominator f ρ ⁻¹' {0}ᶜ
  have hW : IsOpen W := by
    refine ContinuousOn.isOpen_inter_preimage ?_ hU isOpen_compl_singleton
    intro z hz
    exact (contDiffAt_sectionRadiusDenominator (hf z hz) (hρ z hz)).continuousAt.continuousWithinAt
  have hKW : K ⊆ W := fun z hz => ⟨hKU hz,
    sectionRadiusDenominator_ne_zero (hf z (hKU hz)).differentiableAt
      ((hρ z (hKU hz)).differentiableAt (by simp)) (hsub z hz)⟩
  obtain ⟨χ, hχ, hc, hχW, hχ01, hχK⟩ := exists_contDiff_cutoff hK hW hKW
  refine ⟨χ, hχ, hc, fun z hz => (hχW hz).1, hχ01, hχK,
    fun z hz => (hχW hz).2, ?_, hc.smul_right, ?_, ?_⟩
  · exact contDiff_smul_of_tsupport hχ fun z hz =>
      contDiffAt_sectionRadiusField (hf z (hχW hz).1) (hρ z (hχW hz).1) (hχW hz).2
  · intro z
    simp [fderiv_sectionRadiusField]
  · intro z
    by_cases hz : χ z = 0
    · simp [hz]
    · rw [map_smul, radius_fderiv_sectionRadiusField (hχW (subset_tsupport _ hz)).2]
      simp

end OnLeConjecture.Analytic
