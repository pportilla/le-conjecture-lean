/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetBoundarySection

/-! # Separation of the target boundary from critical section points

The positive boundary tangent has nonzero target differential. Since the
complex level tangent is one dimensional, the full map is an immersion
there. The assembly's exact critical-point enumeration therefore places
all enumerated critical points away from this outer boundary.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A nonzero image of one tangent in the complex kernel line forces
injectivity of a map whose first component is the level equation. -/
theorem injective_of_nonzero_on_euclidean_level_tangent
    {f : CollarPlane → ℂ} {z : CollarPlane}
    (Q : CollarPlane →L[ℂ] EuclideanSpace ℂ (Fin 3))
    (hfirst : ∀ v, (Q v) 0 = fderiv ℂ f z v)
    (hf : fderiv ℂ f z ≠ 0) {u : CollarPlane}
    (hu : fderiv ℂ f z u = 0) (hQu : Q u ≠ 0) : Injective Q := by
  obtain ⟨c, hc⟩ := exists_smul_euclideanKernelVector hf hu
  have hQK : Q (euclideanKernelVector f z) ≠ 0 := by
    intro hzero
    apply hQu
    rw [hc, map_smul, hzero, smul_zero]
  apply (injective_iff_map_eq_zero Q).mpr
  intro v hv
  have hfv : fderiv ℂ f z v = 0 := by rw [← hfirst, hv]; rfl
  obtain ⟨a, ha⟩ := exists_smul_euclideanKernelVector hf hfv
  have hz : a • Q (euclideanKernelVector f z) = 0 := by rw [← map_smul, ← ha, hv]
  have ha0 : a = 0 := (smul_eq_zero.mp hz).resolve_right hQK
  rw [ha, ha0, zero_smul]

/-- A chart on the target boundary proves injectivity of the full target
differential, once the source equation differential is nonzero. -/
theorem injective_fderiv_of_targetSectionBoundaryChart (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R))
    (hz : z ∈ targetSectionBoundary H R ε s)
    (hf : fderiv ℂ (fun x => H x 0) ((EuclideanSpace.equiv (Fin 2) ℂ) z) ≠ 0)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) :
    Injective (fderiv ℂ H ((EuclideanSpace.equiv (Fin 2) ℂ) z)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let q := (EuclideanSpace.equiv (Fin 3) ℂ).symm
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) := fun w => q (H (e w))
  let f := euclideanEquation (fun x => H x 0)
  have hH : AnalyticAt ℂ H (e z) := ha (e z) hz.1.1
  have hHe : AnalyticAt ℂ (fun w => H (e w)) z := hH.comp (e.analyticAt z)
  have hQ : AnalyticAt ℂ Q z := (q.analyticAt _).comp hHe
  have hdQ : fderiv ℂ Q z = q.toContinuousLinearMap.comp
      ((fderiv ℂ H (e z)).comp e.toContinuousLinearMap) :=
    (q.hasFDerivAt.comp z (hH.differentiableAt.hasFDerivAt.comp z e.hasFDerivAt)).fderiv
  have hdf : fderiv ℂ f z =
      (fderiv ℂ (fun x => H x 0) (e z)).comp e.toContinuousLinearMap :=
    (((analyticAt_pi_iff.mp hH) 0).differentiableAt.hasFDerivAt.comp z e.hasFDerivAt).fderiv
  have hfn : fderiv ℂ f z ≠ 0 := by
    intro hn
    apply hf
    ext v
    have he := DFunLike.congr_fun hn (e.symm v)
    simpa only [hdf, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he
  have hfirst : ∀ v, (fderiv ℂ Q z v) 0 = fderiv ℂ f z v := by
    have hd₀ : fderiv ℂ f z = (EuclideanSpace.proj 0).comp (fderiv ℂ Q z) :=
      ((show EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ from EuclideanSpace.proj 0).hasFDerivAt.comp z
        hQ.differentiableAt.hasFDerivAt).fderiv
    intro v
    rw [hd₀]
    rfl
  obtain ⟨hker, _, hpos⟩ := targetSectionBoundaryChart_tangent H ha hz C
  have hQu : fderiv ℂ Q z (fderiv ℝ C.φ 0 1) ≠ 0 := by
    intro hzero
    change 0 < (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).im at hpos
    simp only [hzero, inner_zero_right, Complex.zero_im, lt_self_iff_false] at hpos
  have hinj := injective_of_nonzero_on_euclidean_level_tangent (fderiv ℂ Q z) hfirst hfn hker hQu
  intro v w hvw
  have he : e.symm v = e.symm w := hinj (by
    rw [hdQ]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using congrArg q hvw)
  exact e.symm.injective he

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- An actual outer boundary chart is disjoint from the complete finite
critical-point list of the SAME nearby section. -/
theorem not_mem_points_of_targetSectionBoundaryChart (L : ResolutionSectionLevel A)
    {ε : ℝ} {z : CollarPlane}
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hz : z ∈ targetSectionBoundary A.H L.radius ε L.parameter)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
      (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 L.radius) z) :
    (EuclideanSpace.equiv (Fin 2) ℂ) z ∉ L.points := by
  have hinside : (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius := by
    have h := C.mapsTo C.zero_mem
    rwa [C.φ_zero] at h
  have hf := (L.regular _ hinside hz.1.2).1
  have hi := injective_fderiv_of_targetSectionBoundaryChart A.H ha hz hf C
  intro hm
  exact ((L.points_iff _).mp hm).2.2 hi

end ResolutionSectionLevel

end OnLeConjecture.Analytic
