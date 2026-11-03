/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ENoninvariantRotation
public import OnLeConjecture.DThree.ECNineProjective
public import OnLeConjecture.DThree.HomogenizedResidueRotationNoninjectivity
public import OnLeConjecture.DThree.OrdinaryOrderExpansion

/-!
# Persistence of an E rotation line collision

A noninvariant homogeneous third form can have a zero on the rotation line
before the remaining C9 case occurs. The first two equations are transverse
along this line. The third difference is a nonzero polynomial in the affine
chart. Multiple zero persistence therefore turns the homogeneous collision
into collisions of every analytic perturbation with higher ordinary order.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The affine chart polynomial of the rotation difference. -/
@[expose]
noncomputable def eRotationLinePolynomial
    (omega : ℂ) (R : Form ℂ) : ℂ[X] :=
  MvPolynomial.aeval ![X, 1] (eRotationDifference omega R)

theorem eRotationLinePolynomial_eval
    (omega : ℂ) (R : Form ℂ) (z : ℂ) :
    (eRotationLinePolynomial omega R).eval z =
      MvPolynomial.eval ![z, 1] (eRotationDifference omega R) := by
  rw [eRotationLinePolynomial, MvPolynomial.aeval_def,
    MvPolynomial.polynomial_eval_eval₂]
  have hcomp :
      (Polynomial.evalRingHom z).comp (algebraMap ℂ (ℂ[X])) =
        RingHom.id ℂ := by
    ext c
    simp
  rw [hcomp, MvPolynomial.eval₂_id]
  congr
  funext i
  fin_cases i
  all_goals simp

/-- Dehomogenization in the second coordinate chart detects every nonzero
homogeneous binary form. -/
theorem eRotationLinePolynomial_ne_zero
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N)
    (hdifference : eRotationDifference omega R ≠ 0) :
    eRotationLinePolynomial omega R ≠ 0 := by
  let F := eRotationDifference omega R
  have hF : F.IsHomogeneous N :=
    eRotationDifference_isHomogeneous omega hR
  have hrecover :
      (eRotationLinePolynomial omega R).homogenize N = F := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hF
    rfl
  intro hzero
  apply hdifference
  calc
    eRotationDifference omega R = F := rfl
    _ = (eRotationLinePolynomial omega R).homogenize N := hrecover.symm
    _ = 0 := by
      rw [hzero]
      simp

/-- A projective rotation collision in the chart `t ≠ 0` produces a root
of the affine rotation difference. -/
theorem ERotationLineCollisionCertificate.chart_root
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (data : ERotationLineCollisionCertificate omega R)
    (hR : R.IsHomogeneous N) :
    (eRotationLinePolynomial omega R).IsRoot (data.x / data.t) := by
  have hF : (eRotationDifference omega R).IsHomogeneous N :=
    eRotationDifference_isHomogeneous omega hR
  have hzero :
      MvPolynomial.eval ![data.x, data.t]
        (eRotationDifference omega R) = 0 := by
    change MvPolynomial.eval ![data.x, data.t]
      (R - eRotateForm omega R) = 0
    rw [map_sub, eRotateForm_eval]
    exact sub_eq_zero.mpr data.thirdValues_eq
  have hscale := eHomogeneousForm_eval_scale hF data.t
    (data.x / data.t) 1
  have hx : data.t * (data.x / data.t) = data.x := by
    exact mul_div_cancel₀ data.x data.t_ne_zero
  rw [hx, mul_one, hzero] at hscale
  have hpower : data.t ^ N ≠ 0 := pow_ne_zero N data.t_ne_zero
  have hchart :
      MvPolynomial.eval ![data.x / data.t, 1]
        (eRotationDifference omega R) = 0 := by
    exact (mul_eq_zero.mp hscale.symm).resolve_left hpower
  change (eRotationLinePolynomial omega R).eval (data.x / data.t) = 0
  rw [eRotationLinePolynomial_eval]
  exact hchart

/-- Rescale the affine rotation difference so that it is represented by the
standard restricted difference with exponent one. -/
@[expose]
noncomputable def eRotationLineNormalizedPolynomial
    (omega : ℂ) (R : Form ℂ) : ℂ[X] :=
  C ((1 - omega)⁻¹) * eRotationLinePolynomial omega R

theorem eRotationLineNormalizedPolynomial_ne_zero
    {omega : ℂ} {R : Form ℂ}
    (homega : omega ≠ 1)
    (hdifference : eRotationLinePolynomial omega R ≠ 0) :
    eRotationLineNormalizedPolynomial omega R ≠ 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (inv_ne_zero (sub_ne_zero.mpr homega.symm))
  · exact hdifference

theorem eRotationLineNormalizedPolynomial_isRoot
    {omega : ℂ} {R : Form ℂ} {z : ℂ}
    (hz : (eRotationLinePolynomial omega R).IsRoot z) :
    (eRotationLineNormalizedPolynomial omega R).IsRoot z := by
  change (C ((1 - omega)⁻¹) *
    eRotationLinePolynomial omega R).eval z = 0
  rw [eval_mul, eval_C, hz, mul_zero]

theorem rotationRestrictedDifference_normalizedRotationLine
    {omega : ℂ} {R : Form ℂ} (homega : omega ≠ 1) :
    rotationRestrictedDifference omega 1
        (eRotationLineNormalizedPolynomial omega R) =
      eRotationLinePolynomial omega R := by
  rw [rotationRestrictedDifference_eq,
    eRotationLineNormalizedPolynomial]
  simp only [pow_one]
  have hscalar : (1 - omega) * (1 - omega)⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_ne_zero.mpr homega.symm)
  calc
    C (1 - omega) *
        (C (1 - omega)⁻¹ * eRotationLinePolynomial omega R) =
      C ((1 - omega) * (1 - omega)⁻¹) *
        eRotationLinePolynomial omega R := by rw [map_mul, mul_assoc]
    _ = eRotationLinePolynomial omega R := by rw [hscalar, map_one, one_mul]

/-- The determinant of the point derivative for the ordinary E rotation
line. -/
theorem det_eOrdinaryRotationPointDerivative
    (x omega : ℂ) (homegaCube : omega ^ 3 = 1) :
    (eResidueRotationPointDerivative 1 x omega).det =
      -(36 * omega ^ 2) := by
  simp [eResidueRotationPointDerivative,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    eResidueRotationPointJacobian, Matrix.det_fin_two, homegaCube]
  ring

/-- The derivative of the first two equations is invertible on a nonzero
ordinary rotation line. -/
@[expose]
noncomputable def eOrdinaryRotationPointDerivativeEquiv
    (x omega : ℂ) (homegaCube : omega ^ 3 = 1) (homegaZero : omega ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (eResidueRotationPointDerivative 1 x omega).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_eOrdinaryRotationPointDerivative x omega homegaCube]
    exact neg_ne_zero.mpr <| mul_ne_zero (by norm_num)
      (pow_ne_zero 2 homegaZero)

/-- The explicit ordinary rotation branch solves the first two E equations. -/
theorem e_explicitOrdinaryRotationPlaneBranch_eq_zero
    (x omega : ℂ) (homegaCube : omega ^ 3 = 1) (lambda : ℂ) :
    eResidueRotationPlaneDifference 1 x
      (lambda, explicitRotationPlaneBranch x omega lambda) = 0 := by
  funext i
  fin_cases i
  all_goals
    simp [eResidueRotationPlaneDifference, explicitRotationPlaneBranch,
      homegaCube]

/-- Near an ordinary rotation pair, the first two E equations consist of the
explicit rotation branch. -/
theorem eventually_eOrdinaryRotationPlaneDifference_eq_zero_iff_explicitBranch
    (x omega : ℂ) (homegaCube : omega ^ 3 = 1) (homegaZero : omega ≠ 0) :
    ∀ᶠ s in nhds (0, ![x, omega]),
      eResidueRotationPlaneDifference 1 x s = 0 ↔
        explicitRotationPlaneBranch x omega s.1 = s.2 := by
  let Phi := eResidueRotationPlaneDifference 1 x
  let base : ℂ × (Fin 2 → ℂ) := (0, ![x, omega])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base :=
    (analyticAt_eResidueRotationPlaneDifference 1 x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq : Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
        eResidueRotationPointDerivative 1 x omega := by
      simpa [Phi, Phi', base] using
        fderiv_eResidueRotationPlaneDifference_point 1 x omega
    rw [heq]
    simpa [eOrdinaryRotationPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := eOrdinaryRotationPointDerivativeEquiv
          x omega homegaCube homegaZero))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base, explicitRotationPlaneBranch] using
      e_explicitOrdinaryRotationPlaneBranch_eq_zero x omega homegaCube 0
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards
      [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda ↦ (lambda, explicitRotationPlaneBranch x omega lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using
      tendsto_id.prodMk_nhds (tendsto_explicitRotationPlaneBranch x omega)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = explicitRotationPlaneBranch x omega lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocal'
    exact hlocal'.mp <| by
      simpa [Phi] using
        e_explicitOrdinaryRotationPlaneBranch_eq_zero
          x omega homegaCube lambda
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = explicitRotationPlaneBranch x omega s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst] with s hlocal' hpsi'
  rw [hlocal', hpsi']

/-- The ordinary E initial map used in the rotation line branch. -/
@[expose]
noncomputable def eOrdinaryInitialMap
    (R : Form ℂ) : ℂ × ℂ → Fin 3 → ℂ :=
  weightedPolynomialMap (eInvariantPolynomialMap R)

/-- At radial parameter zero, the first two divided differences are the
ordinary rotation plane equations. -/
theorem eOrdinaryRotationPlanePart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation (eOrdinaryInitialMap R) remainder)
        x ((0, lambda), v) =
      eResidueRotationPlaneDifference 1 x (lambda, v) := by
  funext i
  fin_cases i
  all_goals
    simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint, eOrdinaryInitialMap,
      weightedPolynomialMap, eInvariantPolynomialMap, cubicForm, quarticForm,
      formX, formT, eResidueRotationPlaneDifference]

/-- On the explicit branch, the third divided difference is the affine
rotation polynomial. -/
theorem eOrdinaryRotationThirdPart_zero
    (omega : ℂ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) :
    rotationThirdPart
        (weightedRescaledPerturbation (eOrdinaryInitialMap R) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x omega lambda) =
      (eRotationLinePolynomial omega R).eval (x + lambda) := by
  rw [rotationThirdPart, rotationReparametrization,
    weightedRescaledPerturbation_zero,
    eRotationLinePolynomial_eval]
  simp only [weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, rotationAffinePoint,
    explicitRotationPlaneBranch, eOrdinaryInitialMap,
    eInvariantPolynomialMap,
    Fin.isValue]
  change MvPolynomial.eval ![x + lambda, 1] R -
      MvPolynomial.eval ![x + lambda, omega] R =
    MvPolynomial.eval ![x + lambda, 1]
      (R - eRotateForm omega R)
  rw [map_sub, eRotateForm_eval]
  simp

/-- An ordinary rotation line collision persists under every analytic radial
perturbation. -/
theorem eventually_exists_eOrdinaryRotationZero_mem_nhds
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (data : ERotationLineCollisionCertificate omega R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (data.x / data.t, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (data.x / data.t, omega)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![data.x / data.t, data.x / data.t, omega])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation (eOrdinaryInitialMap R) remainder
            (tau, q) = 0 := by
  let z := data.x / data.t
  let p := eRotationLineNormalizedPolynomial omega R
  let Phi := weightedRescaledPerturbation (eOrdinaryInitialMap R) remainder
  have homegaCube : omega ^ 3 = 1 := homega.pow_eq_one
  have homegaOne : omega ≠ 1 := homega.ne_one (by norm_num)
  have homegaZero : omega ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : 3 ≠ 0)] at homegaCube
    exact zero_ne_one homegaCube
  have hpBase : eRotationLinePolynomial omega R ≠ 0 :=
    eRotationLinePolynomial_ne_zero hR data.rotationDifference_ne_zero
  have hp : p ≠ 0 :=
    eRotationLineNormalizedPolynomial_ne_zero homegaOne hpBase
  have hx : p.IsRoot z :=
    eRotationLineNormalizedPolynomial_isRoot (data.chart_root hR)
  have hPhi : AnalyticAt ℂ Phi (0, ![z, z, omega]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) _
    · simpa [z, residueFirstChartPoint] using hfirst
    · simpa [z, residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_explicitThird
    Phi (eResidueRotationPlaneDifference 1 z)
      (eOrdinaryRotationPointDerivativeEquiv
        z omega homegaCube homegaZero)
      z omega 1 p hPhi
  · exact eOrdinaryRotationPlanePart_zero R remainder z
  · simpa [eOrdinaryRotationPointDerivativeEquiv] using
      hasStrictFDerivAt_eResidueRotationPlaneDifference_point
        1 z omega
  · simpa [explicitRotationPlaneBranch] using
      e_explicitOrdinaryRotationPlaneBranch_eq_zero
        z omega homegaCube 0
  · exact
      eventually_eOrdinaryRotationPlaneDifference_eq_zero_iff_explicitBranch
        z omega homegaCube homegaZero
  · intro lambda
    calc
      rotationThirdPart Phi z
          ((0, lambda), explicitRotationPlaneBranch z omega lambda) =
        (eRotationLinePolynomial omega R).eval (z + lambda) :=
          eOrdinaryRotationThirdPart_zero omega R remainder z lambda
      _ = (rotationRestrictedDifference omega 1 p).eval (z + lambda) := by
        rw [rotationRestrictedDifference_normalizedRotationLine homegaOne]
      _ = residueRotationThirdDifference 1 p z
          (lambda, explicitRotationPlaneBranch z omega lambda) := by
        rw [residueRotationThirdDifference]
        exact (explicitRotationThirdDifference_eq
          1 p z omega lambda).symm
  · simpa using homegaOne
  · exact hp
  · exact hx
  · simpa [z] using hU

/-- Ordinary correction terms above the three initial degrees make a
rotation line collision incompatible with local injectivity. -/
theorem eRotationLineMaximalIdealTails_not_hasInjectiveRepresentative
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (data : ERotationLineCollisionCertificate omega R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eInvariantPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (eInvariantDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasOrdinaryRadialExpansionAt_of_mem_maximalIdeal_pow
      (eInvariantDegrees N) (eInvariantPolynomialMap R)
      (eInvariantPolynomialMap_isWeightedHomogeneous R N hR)
      representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedRotationZeros
    1 (eInvariantDegrees N) (eOrdinaryInitialMap R)
      representative remainder (data.x / data.t) omega
      (by norm_num) (homega.ne_one (by norm_num))
  · exact hexpansion (data.x / data.t, 1)
  · exact hexpansion (data.x / data.t, omega)
  · intro U hU
    exact eventually_exists_eOrdinaryRotationZero_mem_nhds
      homega hR data remainder
        (hexpansion (data.x / data.t, 1)).remainder_analyticAt
        (hexpansion (data.x / data.t, omega)).remainder_analyticAt U hU

end OnLeConjecture.DThree
