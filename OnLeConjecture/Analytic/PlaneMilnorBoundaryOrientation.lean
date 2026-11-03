/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCharts
public import OnLeConjecture.Analytic.PlaneMilnorFibreBoundary
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Positive tangents of Milnor fibre boundary charts

The complex orientation and the outward-normal-first boundary convention
select the real-coordinate tangent in a chart whose model is the upper
half-plane. Its Hermitian pairing with position has positive imaginary
part. The proof uses the actual chart map into the Milnor ball, not an
assumed sign for its derivative.
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

/-- A vector in the complex level tangent plane is determined by its Hermitian
pairing with position whenever the radial kernel pairing is nonzero. -/
theorem eq_zero_of_euclidean_kernel_inner_eq_zero
    {f : EuclideanSpace ℂ (Fin 2) → ℂ} {z v : EuclideanSpace ℂ (Fin 2)}
    (hz : euclideanKernelPairing f z ≠ 0)
    (hv : fderiv ℂ f z v = 0) (hi : inner ℂ z v = 0) : v = 0 := by
  set a := fderiv ℂ f z (EuclideanSpace.single 0 1)
  set b := fderiv ℂ f z (EuclideanSpace.single 1 1)
  have hL : fderiv ℂ f z v = v 0 * a + v 1 * b := by
    have he : v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [he]
    simp only [map_add, map_smul, smul_eq_mul, a, b]
  have hi' : conj (z 0) * v 0 + conj (z 1) * v 1 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hi
  have hz' : -b * conj (z 0) + a * conj (z 1) ≠ 0 := by
    simpa [euclideanKernelPairing, euclideanKernelVector, inner_add_right, inner_smul_right,
      EuclideanSpace.inner_single_right, a, b] using hz
  rw [hL] at hv
  have h0 : (-b * conj (z 0) + a * conj (z 1)) * v 0 = 0 := by
    linear_combination conj (z 1) * hv - b * hi'
  have h1 : (-b * conj (z 0) + a * conj (z 1)) * v 1 = 0 := by
    linear_combination a * hi' - conj (z 0) * hv
  have hv0 := (mul_eq_zero.mp h0).resolve_left hz'
  have hv1 := (mul_eq_zero.mp h1).resolve_left hz'
  ext i
  fin_cases i <;> simp [hv0, hv1]

/-- Multiplication by `-i` turns the normalized inward radial field into a
positive boundary tangent. -/
def euclideanBoundaryTangent (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  -Complex.I • euclideanRadialField f z

theorem fderiv_euclideanBoundaryTangent (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) :
    fderiv ℂ f z (euclideanBoundaryTangent f z) = 0 := by
  simp [euclideanBoundaryTangent, fderiv_euclideanRadialField]

/-- The normalization fixes the boundary tangent's Hermitian pairing exactly. -/
theorem inner_euclideanBoundaryTangent {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hz : euclideanKernelPairing f z ≠ 0) :
    inner ℂ z (euclideanBoundaryTangent f z) = Complex.I / 2 := by
  rw [euclideanBoundaryTangent, euclideanRadialField, inner_smul_right, inner_smul_right,
    ← euclideanKernelPairing]
  field_simp

/-- Every level-and-sphere tangent is the specified real multiple of the
normalized boundary tangent. -/
theorem eq_real_smul_euclideanBoundaryTangent
    {f : EuclideanSpace ℂ (Fin 2) → ℂ} {z v : EuclideanSpace ℂ (Fin 2)}
    (hz : euclideanKernelPairing f z ≠ 0)
    (hv : fderiv ℂ f z v = 0) (hi : (inner ℂ z v).re = 0) :
    v = (2 * (inner ℂ z v).im : ℝ) • euclideanBoundaryTangent f z := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  apply sub_eq_zero.mp
  apply eq_zero_of_euclidean_kernel_inner_eq_zero hz
  · simp only [map_sub, map_smul, hv, fderiv_euclideanBoundaryTangent,
      smul_zero, sub_self]
  · rw [inner_sub_right, inner_smul_right]
    rw [inner_euclideanBoundaryTangent hz]
    apply Complex.ext <;> simp [hi]
    ring

/-- Every vector pointing into the upper half-plane belongs to its positive tangent cone. -/
theorem mem_posTangentConeAt_complex_upperHalfPlane {v : ℂ} (hv : 0 ≤ v.im) :
    v ∈ posTangentConeAt {t : ℂ | 0 ≤ t.im} 0 := by
  apply mem_posTangentConeAt_of_frequently_mem
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 ≤ (0 + t • v).im
  simpa using mul_nonneg (le_of_lt ht) hv

namespace MilnorFibreChart

/-- A chart centered on the boundary has the upper-half-plane model. -/
theorem boundaryChart_of_mem_boundary {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (C : MilnorFibreChart H ε s z)
    (hz : z ∈ milnorFibreBoundary H ε s) : C.boundaryChart = true := by
  have h := (C.boundary_iff 0 C.zero_mem).mp (C.φ_zero.symm ▸ hz)
  exact h.1

/-- The real-coordinate tangent of an actual Milnor boundary chart has positive
imaginary Hermitian pairing with position. -/
theorem boundary_tangent_properties {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (C : MilnorFibreChart H ε s z)
    (hz : z ∈ milnorFibreBoundary H ε s)
    (han : AnalyticAt ℂ (euclideanEquation H) z)
    (hrad : Surjective (fderiv ℝ (radialPair H) z)) :
    fderiv ℂ (euclideanEquation H) z (fderiv ℝ C.φ 0 1) = 0 ∧
      (inner ℂ z (fderiv ℝ C.φ 0 1)).re = 0 ∧
      0 < (inner ℂ z (fderiv ℝ C.φ 0 1)).im := by
  have hb := C.boundaryChart_of_mem_boundary hz
  have hmodel : C.model = C.W ∩ {t : ℂ | 0 ≤ t.im} := by
    rw [C.model_eq, hb]
    rfl
  have h0W : (0 : ℂ) ∈ C.W := by
    have h := C.zero_mem
    rw [hmodel] at h
    exact h.1
  have hφ : DifferentiableAt ℝ C.φ 0 :=
    (C.smooth.contDiffAt (C.isOpen_W.mem_nhds h0W)).differentiableAt (by simp)
  have hn : HasFDerivAt (fun t => ‖C.φ t‖ ^ 2)
      (2 • (innerSL ℝ z).comp (fderiv ℝ C.φ 0)) 0 := by
    simpa only [C.φ_zero] using hφ.hasFDerivAt.norm_sq
  have hmax : IsLocalMaxOn (fun t => ‖C.φ t‖ ^ 2) {t : ℂ | 0 ≤ t.im} 0 := by
    filter_upwards [nhdsWithin_le_nhds (C.isOpen_W.mem_nhds h0W),
      self_mem_nhdsWithin] with t htW ht
    have htM : t ∈ C.model := hmodel ▸ ⟨htW, ht⟩
    have hnorm := (C.mapsTo htM).1
    change ‖C.φ t‖ ^ 2 ≤ ‖C.φ 0‖ ^ 2
    rw [C.φ_zero, hz.1]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have huRe : (inner ℂ z (fderiv ℝ C.φ 0 1)).re = 0 := by
    have h := hmax.hasFDerivWithinAt_eq_zero hn.hasFDerivWithinAt
      (mem_posTangentConeAt_complex_upperHalfPlane (v := 1) (by simp))
      (mem_posTangentConeAt_complex_upperHalfPlane (v := -1) (by simp))
    simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
      real_inner_euclidean, nsmul_eq_mul, Nat.cast_ofNat] at h
    linarith
  have hvRe : (inner ℂ z (fderiv ℝ C.φ 0 Complex.I)).re ≤ 0 := by
    have h := hmax.hasFDerivWithinAt_nonpos hn.hasFDerivWithinAt
      (mem_posTangentConeAt_complex_upperHalfPlane (v := Complex.I) (by simp))
    simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
      real_inner_euclidean, nsmul_eq_mul, Nat.cast_ofNat] at h
    linarith
  have hreal : ∀ᶠ t : ℝ in 𝓝 0, euclideanEquation H (C.φ (t : ℂ)) = s := by
    have hW := Complex.continuous_ofReal.continuousAt.preimage_mem_nhds
      (C.isOpen_W.mem_nhds h0W)
    filter_upwards [hW] with t ht
    exact (C.mapsTo (hmodel ▸ ⟨ht, by simp⟩)).2
  have hE : HasFDerivAt (euclideanEquation H)
      ((fderiv ℂ (euclideanEquation H) z).restrictScalars ℝ) (C.φ 0) := by
    rw [C.φ_zero]
    exact han.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hcomp : HasDerivAt (fun t : ℝ => euclideanEquation H (C.φ (t : ℂ)))
      (fderiv ℂ (euclideanEquation H) z (fderiv ℝ C.φ 0 1)) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.ofRealCLM_apply,
      Complex.ofReal_zero, Complex.ofReal_one] using
      (hE.comp 0 hφ.hasFDerivAt).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ))
        0 Complex.ofRealCLM.hasDerivAt
  have hzero : HasDerivAt (fun t : ℝ => euclideanEquation H (C.φ (t : ℂ))) 0 0 :=
    (hasDerivAt_const 0 s).congr_of_eventuallyEq hreal
  have huKer : fderiv ℂ (euclideanEquation H) z (fderiv ℝ C.φ 0 1) = 0 := by
    exact hcomp.unique hzero
  have huNe : fderiv ℝ C.φ 0 1 ≠ 0 := by
    intro hu
    have h := (C.immersion 0 h0W) (hu.trans (map_zero _).symm)
    exact one_ne_zero h
  have hiNe : inner ℂ z (fderiv ℝ C.φ 0 1) ≠ 0 := by
    intro hi
    exact huNe (eq_zero_of_euclidean_kernel_inner_eq_zero
      (euclideanKernelPairing_ne_zero han.differentiableAt hrad) huKer hi)
  obtain ⟨c, hc, hcφ⟩ := C.oriented 0 h0W
  rw [hcφ, inner_smul_right, Complex.mul_re, huRe, mul_zero, zero_sub] at hvRe
  have him : 0 ≤ (inner ℂ z (fderiv ℝ C.φ 0 1)).im := by
    nlinarith
  refine ⟨huKer, huRe, lt_of_le_of_ne him ?_⟩
  intro h
  apply hiNe
  exact Complex.ext huRe h.symm

/-- The real-coordinate tangent of a Milnor boundary chart has the positive sign. -/
theorem boundary_tangent_im_pos {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (C : MilnorFibreChart H ε s z)
    (hz : z ∈ milnorFibreBoundary H ε s)
    (han : AnalyticAt ℂ (euclideanEquation H) z)
    (hrad : Surjective (fderiv ℝ (radialPair H) z)) :
    0 < (inner ℂ z (fderiv ℝ C.φ 0 1)).im :=
  (C.boundary_tangent_properties hz han hrad).2.2

/-- The chart's boundary tangent is a positive real multiple of the vector
obtained by rotating the inward radial field through `-i`. -/
theorem boundary_tangent_eq_pos_smul {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (C : MilnorFibreChart H ε s z)
    (hz : z ∈ milnorFibreBoundary H ε s)
    (han : AnalyticAt ℂ (euclideanEquation H) z)
    (hrad : Surjective (fderiv ℝ (radialPair H) z)) :
    ∃ a : ℝ, 0 < a ∧ fderiv ℝ C.φ 0 1 =
      a • euclideanBoundaryTangent (euclideanEquation H) z := by
  obtain ⟨hker, hre, him⟩ := C.boundary_tangent_properties hz han hrad
  exact ⟨2 * (inner ℂ z (fderiv ℝ C.φ 0 1)).im, by positivity,
    eq_real_smul_euclideanBoundaryTangent
      (euclideanKernelPairing_ne_zero han.differentiableAt hrad) hker hre⟩

end MilnorFibreChart
end OnLeConjecture.Analytic
