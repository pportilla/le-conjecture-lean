/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetBoundaryOrientation

/-! # The target boundary inside its affine plane section

Removing the constant first coordinate changes the sphere radius from
`epsilon` to `sqrt (epsilon^2 - norm(s)^2)`. The positive boundary tangent
has exactly the same Hermitian pairing in those two section coordinates.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The last two target coordinates, with both Euclidean identifications explicit. -/
def euclideanTargetTail : EuclideanSpace ℂ (Fin 3) →L[ℂ] CollarPlane :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap.comp
    ((hyperplaneTail 2).comp (EuclideanSpace.equiv (Fin 3) ℂ).toContinuousLinearMap)

@[simp] theorem euclideanTargetTail_apply (q : EuclideanSpace ℂ (Fin 3)) (i : Fin 2) :
    euclideanTargetTail q i = q i.succ := by
  rfl

theorem euclideanTargetTail_norm_sq (q : EuclideanSpace ℂ (Fin 3)) :
    ‖q‖ ^ 2 = ‖q 0‖ ^ 2 + ‖euclideanTargetTail q‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, euclideanTargetTail_apply]

theorem euclideanTargetTail_inner (q v : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ q v = conj (q 0) * v 0 + inner ℂ (euclideanTargetTail q) (euclideanTargetTail v) := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, euclideanTargetTail_apply, mul_comm]

/-- The assembled section map, expressed in Euclidean source and target coordinates. -/
def euclideanSectionMap (H : Source 2 → Source 3) (z : CollarPlane) : CollarPlane :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm
    (hyperplaneTail 2 (H ((EuclideanSpace.equiv (Fin 2) ℂ) z)))

theorem euclideanSectionMap_eq_tail (H : Source 2 → Source 3) (z : CollarPlane) :
    euclideanSectionMap H z = euclideanTargetTail
      ((EuclideanSpace.equiv (Fin 3) ℂ).symm (H ((EuclideanSpace.equiv (Fin 2) ℂ) z))) := by
  rfl

/-- The literal target boundary lies on the exact sphere in the affine section. -/
theorem targetSectionBoundary_section_norm (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane} (hz : z ∈ targetSectionBoundary H R ε s) :
    ‖euclideanSectionMap H z‖ = Real.sqrt (ε ^ 2 - ‖s‖ ^ 2) := by
  have he := euclideanTargetTail_norm_sq
    ((EuclideanSpace.equiv (Fin 3) ℂ).symm (H ((EuclideanSpace.equiv (Fin 2) ℂ) z)))
  rw [hz.2, ← euclideanSectionMap_eq_tail] at he
  change ε ^ 2 = ‖H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0‖ ^ 2 +
    ‖euclideanSectionMap H z‖ ^ 2 at he
  rw [hz.1.2] at he
  have he' : ε ^ 2 - ‖s‖ ^ 2 = ‖euclideanSectionMap H z‖ ^ 2 := by linarith
  rw [he', Real.sqrt_sq (norm_nonneg _)]

/-- The target-section boundary tangent preserves the positive sign when
the constant first coordinate is removed. -/
theorem targetSectionBoundaryChart_section_tangent (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R))
    (hz : z ∈ targetSectionBoundary H R ε s)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) :
    (inner ℂ (euclideanSectionMap H z)
      (fderiv ℂ (euclideanSectionMap H) z (fderiv ℝ C.φ 0 1))).re = 0 ∧
    0 < (inner ℂ (euclideanSectionMap H z)
      (fderiv ℂ (euclideanSectionMap H) z (fderiv ℝ C.φ 0 1))).im := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
    fun w => (EuclideanSpace.equiv (Fin 3) ℂ).symm (H (e w))
  have hHe : AnalyticAt ℂ (fun w => H (e w)) z := (ha (e z) hz.1.1).comp (e.analyticAt z)
  have hQ : AnalyticAt ℂ Q z :=
    ((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp hHe
  have hd : fderiv ℂ (euclideanSectionMap H) z = euclideanTargetTail.comp (fderiv ℂ Q z) :=
    (euclideanTargetTail.hasFDerivAt.comp z hQ.differentiableAt.hasFDerivAt).fderiv
  have hd₀ : fderiv ℂ (euclideanEquation (fun x => H x 0)) z =
      (EuclideanSpace.proj 0).comp (fderiv ℂ Q z) :=
    ((show EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ from EuclideanSpace.proj 0).hasFDerivAt.comp z
      hQ.differentiableAt.hasFDerivAt).fderiv
  obtain ⟨hker, hre, him⟩ := targetSectionBoundaryChart_tangent H ha hz C
  have hzero : (fderiv ℂ Q z (fderiv ℝ C.φ 0 1)) 0 = 0 := by
    rw [hd₀] at hker
    exact hker
  have heq : inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1)) =
      inner ℂ (euclideanSectionMap H z)
        (fderiv ℂ (euclideanSectionMap H) z (fderiv ℝ C.φ 0 1)) := by
    rw [euclideanTargetTail_inner, hzero, mul_zero, zero_add, hd]
    rfl
  exact ⟨heq ▸ hre, heq ▸ him⟩

/-- The actual section-sphere radius is positive under the retained level bound. -/
theorem section_sphere_radius_pos {ε : ℝ} {s : ℂ} (hε : 0 < ε) (hs : ‖s‖ < ε) :
    0 < Real.sqrt (ε ^ 2 - ‖s‖ ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg s]

end OnLeConjecture.Analytic
