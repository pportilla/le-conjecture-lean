/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchClosedBraid
public import OnLeConjecture.Analytic.PlaneBranchMixedLevels
public import OnLeConjecture.DifferentialTopology.ComplexSolidTorus

/-! # The solid-torus coordinates of a power-normalized branch circle

The complementary coordinate is divided by `r^a`. With this scaling, the
solid-torus image is exactly the radial normalization of the analytic branch
on the parameter circle of radius `r`.
-/

@[expose] public noncomputable section

open Set Metric Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

open DifferentialTopology

/-- The solid-torus map with its circle coordinate placed in position `i`. -/
def planeSolidTorusMap (i : Fin 2) (p : Circle × ℂ) : EuclideanSpace ℂ (Fin 2) :=
  complexSolidTorusScale p.2 • (EuclideanSpace.equiv (Fin 2) ℂ).symm
    (fun j => if j = i then (p.1 : ℂ) else p.2)

theorem planeSolidTorusMap_apply (i j : Fin 2) (p : Circle × ℂ) :
    planeSolidTorusMap i p j =
      complexSolidTorusMap p (if j = i then 0 else 1) := by
  by_cases h : j = i <;> simp [planeSolidTorusMap, h]

/-- The coordinate permutation placing coordinate zero in position `i`. -/
def planeSolidTorusCoordinateEquiv (i : Fin 2) :
    EuclideanSpace ℂ (Fin 2) ≃L[ℝ] EuclideanSpace ℂ (Fin 2) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap 0 i)).toContinuousLinearEquiv
    |>.restrictScalars ℝ

theorem planeSolidTorusMap_eq_coordinateEquiv (i : Fin 2) :
    planeSolidTorusMap i = planeSolidTorusCoordinateEquiv i ∘ complexSolidTorusMap := by
  funext p
  ext j
  rw [planeSolidTorusMap_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeSolidTorusCoordinateEquiv, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft']

/-- The selected-coordinate version is the same smooth embedding with permuted coordinates. -/
theorem planeSolidTorusMap_isSmoothEmbedding (i : Fin 2) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
      (planeSolidTorusMap i) := by
  rw [planeSolidTorusMap_eq_coordinateEquiv]
  let e := planeSolidTorusCoordinateEquiv i
  have he : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ e := e.contDiff.contMDiff
  apply (he.comp complexSolidTorusMap_contMDiff).isSmoothEmbedding_of_injective_mfderiv
    (by simp) _ (e.toHomeomorph.isEmbedding.comp complexSolidTorusMap_isEmbedding)
  intro p
  rw [mfderiv_comp p (he.mdifferentiableAt (by simp))
    (complexSolidTorusMap_contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv,
    e.fderiv]
  exact e.injective.comp (complexSolidTorusMap_mfderiv_injective p)

@[simp] theorem planeSolidTorusMap_selected (i : Fin 2) (p : Circle × ℂ) :
    planeSolidTorusMap i p i = complexSolidTorusScale p.2 • (p.1 : ℂ) := by
  simp [planeSolidTorusMap]

@[simp] theorem planeSolidTorusMap_other (i : Fin 2) (p : Circle × ℂ) :
    planeSolidTorusMap i p i.rev = complexSolidTorusScale p.2 • p.2 := by
  fin_cases i <;> simp [planeSolidTorusMap]

theorem planeSolidTorusMap_selected_norm (i : Fin 2) (p : Circle × ℂ) :
    ‖planeSolidTorusMap i p i‖ = complexSolidTorusScale p.2 := by
  rw [planeSolidTorusMap_selected, norm_smul, Real.norm_eq_abs,
    abs_of_pos (complexSolidTorusScale_pos p.2), Circle.norm_coe, mul_one]

theorem planeSolidTorusMap_selected_ne_zero (i : Fin 2) (p : Circle × ℂ) :
    planeSolidTorusMap i p i ≠ 0 := by
  apply norm_pos_iff.mp
  rw [planeSolidTorusMap_selected_norm]
  exact complexSolidTorusScale_pos p.2

/-- Both cylinder coordinates are recovered on the complement of the selected axis. -/
theorem planeSolidTorusMap_recovery (i : Fin 2) (p : Circle × ℂ) :
    (‖planeSolidTorusMap i p i‖⁻¹ • planeSolidTorusMap i p i,
      ‖planeSolidTorusMap i p i‖⁻¹ • planeSolidTorusMap i p i.rev) =
        ((p.1 : ℂ), p.2) := by
  rw [planeSolidTorusMap_selected_norm, planeSolidTorusMap_selected,
    planeSolidTorusMap_other]
  simp only [smul_smul, inv_mul_cancel₀ (complexSolidTorusScale_pos p.2).ne', one_smul]

theorem planeSolidTorusMap_eq_radialNormalization (i : Fin 2) (p : Circle × ℂ) :
    planeSolidTorusMap i p = planeRadialNormalization
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm
        (fun j => if j = i then (p.1 : ℂ) else p.2)) := by
  have hn : ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm
      (fun j => if j = i then (p.1 : ℂ) else p.2)‖ =
      Real.sqrt (1 + ‖p.2‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    fin_cases i <;> simp [Circle.norm_coe, add_comm]
  simp only [planeSolidTorusMap, planeRadialNormalization, hn, complexSolidTorusScale]

theorem planeSolidTorusMap_norm (i : Fin 2) (p : Circle × ℂ) :
    ‖planeSolidTorusMap i p‖ = 1 := by
  rw [planeSolidTorusMap_eq_radialNormalization]
  apply norm_planeRadialNormalization
  intro h
  have hi := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z i) h
  simp at hi

/-- Positive real rescaling does not change radial normalization. -/
theorem planeRadialNormalization_pos_smul (y : EuclideanSpace ℂ (Fin 2))
    {c : ℝ} (hc : 0 < c) :
    planeRadialNormalization (c • y) = planeRadialNormalization y := by
  simp only [planeRadialNormalization, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
    mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- The scaled cylinder circle whose sphere image is the normalized analytic circle. -/
def curvePowerSolidTorusCircle (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) :
    Circle → Circle × ℂ := fun u =>
  (u ^ a, F ((r : ℂ) * u) i.rev / (r : ℂ) ^ a)

theorem curvePowerSolidTorusCircle_projection
    (F : ℂ → Source 2) (i : Fin 2) (a : ℕ) (r : ℝ) :
    Prod.fst ∘ curvePowerSolidTorusCircle F i a r = fun u => u ^ a := rfl

/-- The solid-torus formula agrees pointwise with the branch endpoint used by the isotopy. -/
theorem curvePowerSolidTorusCircle_map
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) (u : Circle) :
    planeSolidTorusMap i (curvePowerSolidTorusCircle F i a r u) =
      planeRadialNormalization
        ((EuclideanSpace.equiv (Fin 2) ℂ).symm (F (r • (u : ℂ)))) := by
  have hmem : (r : ℂ) * (u : ℂ) ∈ ball 0 R := by
    simpa [mem_ball, dist_zero_right, norm_mul, Circle.norm_coe,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrR
  have hrpow : (r : ℂ) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne')
  let v : EuclideanSpace ℂ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℂ).symm (fun j =>
      if j = i then (u : ℂ) ^ a else F ((r : ℂ) * u) i.rev / (r : ℂ) ^ a)
  have hv : (EuclideanSpace.equiv (Fin 2) ℂ).symm (F (r • (u : ℂ))) =
      (r ^ a : ℝ) • v := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [v, Complex.real_smul, hp _ hmem, mul_pow]
    · have hj : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
      change F (r • (u : ℂ)) j = (r ^ a : ℝ) •
        (if j = i then _ else F ((r : ℂ) * u) i.rev / (r : ℂ) ^ a)
      rw [if_neg hji, hj]
      simp [Complex.real_smul, mul_div_cancel₀ _ hrpow]
  rw [hv, planeRadialNormalization_pos_smul _ (pow_pos hr a),
    planeSolidTorusMap_eq_radialNormalization]
  rfl

theorem curvePowerSolidTorusCircle_range
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    Set.range (planeSolidTorusMap i ∘ curvePowerSolidTorusCircle F i a r) =
      Set.range (fun u : Circle => planeRadialNormalization
        ((EuclideanSpace.equiv (Fin 2) ℂ).symm (F (r • (u : ℂ))))) := by
  congr 1
  funext u
  exact curvePowerSolidTorusCircle_map hr hrR hp u

theorem curvePowerSolidTorusCircle_recovery
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) (u : Circle) :
    let y := planeRadialNormalization
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm (F (r • (u : ℂ))))
    (‖y i‖⁻¹ • y i, ‖y i‖⁻¹ • y i.rev) =
      ((u : ℂ) ^ a, F ((r : ℂ) * u) i.rev / (r : ℂ) ^ a) := by
  dsimp only
  rw [← curvePowerSolidTorusCircle_map hr hrR hp u]
  exact planeSolidTorusMap_recovery i (curvePowerSolidTorusCircle F i a r u)

set_option backward.isDefEq.respectTransparency false in
theorem curvePowerSolidTorusCircle_contMDiff
    {F : ℂ → Source 2} (i : Fin 2) (a : ℕ) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hF : AnalyticOnNhd ℂ F (ball 0 R)) :
    ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (curvePowerSolidTorusCircle F i a r) := by
  have hc := curvePowerCylinderCircle_contMDiff i a hr hrR hF
  have hs := (show ContDiff ℝ ∞ (fun z : ℂ => z * ((r : ℂ) ^ a)⁻¹) from
    contDiff_id.mul contDiff_const).contMDiff.comp (contMDiff_snd.comp hc)
  unfold curvePowerSolidTorusCircle
  simp only [div_eq_mul_inv]
  exact (contMDiff_pow a).prodMk hs

theorem curvePowerSolidTorusCircle_isClosedEmbedding
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) (hi : InjOn F (ball 0 R))
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    Topology.IsClosedEmbedding (curvePowerSolidTorusCircle F i a r) := by
  apply (curvePowerSolidTorusCircle_contMDiff i a hr hrR hF).continuous.isClosedEmbedding
  intro u v huv
  apply (curvePowerCylinderCircle_isClosedEmbedding hr hrR hF.continuousOn hi hp).injective
  apply Prod.ext
  · simpa only [curvePowerSolidTorusCircle, curvePowerCylinderCircle] using
      congrArg Prod.fst huv
  · have he := congrArg Prod.snd huv
    exact (div_left_inj' (pow_ne_zero a (show (r : ℂ) ≠ 0 by
      exact_mod_cast hr.ne'))).mp he

/-- The scaled cylinder circle is a native smooth embedding. -/
theorem curvePowerSolidTorusCircle_isSmoothEmbedding
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R)) (hi : InjOn F (ball 0 R))
    (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞
      (curvePowerSolidTorusCircle F i a r) := by
  have hc := curvePowerSolidTorusCircle_contMDiff i a hr hrR hF
  apply hc.isSmoothEmbedding_of_injective_mfderiv (by simp) _
    (curvePowerSolidTorusCircle_isClosedEmbedding hr hrR hF hi hp).isEmbedding
  intro u
  have hp' : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℂ => (p.1 : ℂ)) := contMDiff_coe_sphere.comp contMDiff_fst
  have hchain := mfderiv_comp u (hp'.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  intro v w hvw
  apply circle_pow_coe_mfderiv_injective ha u
  change mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      ((fun p : Circle × ℂ => (p.1 : ℂ)) ∘ curvePowerSolidTorusCircle F i a r) u v =
    mfderiv (𝓡 1) 𝓘(ℝ, ℂ)
      ((fun p : Circle × ℂ => (p.1 : ℂ)) ∘ curvePowerSolidTorusCircle F i a r) u w
  rw [hchain]
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg _ hvw

theorem curvePowerSolidTorusCircle_covering
    (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a) (r : ℝ) :
    IsCoveringMap (Prod.fst ∘ curvePowerSolidTorusCircle F i a r) ∧
      ∀ v : Circle,
        Nat.card {u : Circle // (curvePowerSolidTorusCircle F i a r u).1 = v} = a :=
  ⟨circle_pow_isCoveringMap ha, circle_pow_fiber_card ha⟩

end OnLeConjecture.Analytic
