/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNoninvariantReflection
public import OnLeConjecture.DThree.ERotationLineNoninjectivity

/-!
# Persistence of an H reflection line collision

The first two H equations are transverse along the reflection line. The third
difference is a nonzero polynomial in the affine chart. Multiple zero
persistence therefore produces collisions for every analytic perturbation
whose correction terms have larger ordinary order.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A projective H reflection collision gives a root of the affine reflection
difference. -/
theorem HReflectionLineCollisionCertificate.chart_root
    {R : Form ℂ} {N : ℕ}
    (data : HReflectionLineCollisionCertificate R)
    (hR : R.IsHomogeneous N) :
    (eRotationLinePolynomial (-1) R).IsRoot (data.x / data.t) := by
  have hF : (eRotationDifference (-1) R).IsHomogeneous N :=
    eRotationDifference_isHomogeneous (-1) hR
  have hzero :
      MvPolynomial.eval ![data.x, data.t]
        (eRotationDifference (-1) R) = 0 := by
    change MvPolynomial.eval ![data.x, data.t]
      (R - eRotateForm (-1) R) = 0
    rw [map_sub, eRotateForm_eval]
    norm_num
    exact sub_eq_zero.mpr data.thirdValues_eq
  have hscale := eHomogeneousForm_eval_scale hF data.t
    (data.x / data.t) 1
  have hx : data.t * (data.x / data.t) = data.x :=
    mul_div_cancel₀ data.x data.t_ne_zero
  rw [hx, mul_one, hzero] at hscale
  have hpower : data.t ^ N ≠ 0 := pow_ne_zero N data.t_ne_zero
  have hchart :
      MvPolynomial.eval ![data.x / data.t, 1]
        (eRotationDifference (-1) R) = 0 := by
    exact (mul_eq_zero.mp hscale.symm).resolve_left hpower
  change (eRotationLinePolynomial (-1) R).eval (data.x / data.t) = 0
  rw [eRotationLinePolynomial_eval]
  exact hchart

/-- The determinant of the H point derivative at an ordinary reflection
pair. -/
theorem det_hOrdinaryReflectionPointJacobian
    (x omega : ℂ) (homegaSquare : omega ^ 2 = 1) :
    Matrix.det (hResidueRotationPointJacobian 1 x omega) =
      24 * omega := by
  have homegaCube : omega ^ 3 = omega := by
    calc
      omega ^ 3 = omega ^ 2 * omega := by ring
      _ = omega := by rw [homegaSquare, one_mul]
  simp [hResidueRotationPointJacobian, Matrix.det_fin_two,
    homegaSquare, homegaCube]
  ring

theorem det_hOrdinaryReflectionPointDerivative
    (x omega : ℂ) (homegaSquare : omega ^ 2 = 1) :
    (hResidueRotationPointDerivative 1 x omega).det = 24 * omega := by
  simpa [hResidueRotationPointDerivative,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin'] using
    det_hOrdinaryReflectionPointJacobian x omega homegaSquare

/-- The point derivative at an ordinary H reflection pair is invertible. -/
@[expose]
noncomputable def hOrdinaryReflectionPointDerivativeEquiv
    (x omega : ℂ) (homegaSquare : omega ^ 2 = 1)
    (homegaZero : omega ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (hResidueRotationPointDerivative 1 x omega).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_hOrdinaryReflectionPointDerivative x omega homegaSquare]
    exact mul_ne_zero (by norm_num) homegaZero

/-- The explicit ordinary reflection branch solves the first two H
equations. -/
theorem h_explicitOrdinaryReflectionPlaneBranch_eq_zero
    (x omega : ℂ) (homegaSquare : omega ^ 2 = 1) (lambda : ℂ) :
    hResidueRotationPlaneDifference 1 x
      (lambda, explicitRotationPlaneBranch x omega lambda) = 0 := by
  have homegaFourth : omega ^ 4 = 1 := by
    calc
      omega ^ 4 = (omega ^ 2) ^ 2 := by ring
      _ = 1 := by rw [homegaSquare, one_pow]
  funext i
  fin_cases i
  all_goals
    simp [hResidueRotationPlaneDifference, explicitRotationPlaneBranch,
      homegaSquare, homegaFourth]

/-- Near an ordinary reflection pair, the first two H equations consist of
the explicit reflection branch. -/
theorem eventually_hOrdinaryReflectionPlaneDifference_eq_zero_iff_explicitBranch
    (x omega : ℂ) (homegaSquare : omega ^ 2 = 1)
    (homegaZero : omega ≠ 0) :
    ∀ᶠ s in nhds (0, ![x, omega]),
      hResidueRotationPlaneDifference 1 x s = 0 ↔
        explicitRotationPlaneBranch x omega s.1 = s.2 := by
  let Phi := hResidueRotationPlaneDifference 1 x
  let base : ℂ × (Fin 2 → ℂ) := (0, ![x, omega])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base :=
    (analyticAt_hResidueRotationPlaneDifference 1 x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq :
        Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
          hResidueRotationPointDerivative 1 x omega := by
      simpa [Phi, Phi', base] using
        fderiv_hResidueRotationPlaneDifference_point 1 x omega
    rw [heq]
    simpa [hOrdinaryReflectionPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := hOrdinaryReflectionPointDerivativeEquiv
          x omega homegaSquare homegaZero))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base, explicitRotationPlaneBranch] using
      h_explicitOrdinaryReflectionPlaneBranch_eq_zero
        x omega homegaSquare 0
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards
      [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda => (lambda, explicitRotationPlaneBranch x omega lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using
      tendsto_id.prodMk_nhds
        (tendsto_explicitRotationPlaneBranch x omega)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = explicitRotationPlaneBranch x omega lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocal'
    exact hlocal'.mp <| by
      simpa [Phi] using
        h_explicitOrdinaryReflectionPlaneBranch_eq_zero
          x omega homegaSquare lambda
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) => s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) => s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = explicitRotationPlaneBranch x omega s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst] with s hlocal' hpsi'
  rw [hlocal', hpsi']

/-- The ordinary H polynomial map. -/
@[expose]
noncomputable def hOrdinaryPolynomialMap
    (R : Form ℂ) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![cubicForm 3 0, quarticForm 1 0 4 0 2, R]

/-- The ordinary degrees of the H polynomial map. -/
@[expose]
noncomputable def hOrdinaryDegrees (N : ℕ) : Fin 3 → ℕ :=
  ![3, 4, N]

/-- The ordinary H polynomial map is homogeneous in its three prescribed
degrees. -/
theorem hOrdinaryPolynomialMap_isWeightedHomogeneous
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N) (i : Fin 3) :
    (hOrdinaryPolynomialMap R i).IsWeightedHomogeneous
      ![1, 1] (hOrdinaryDegrees N i) := by
  have hx : (formX : Form ℂ).IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [formX] using
      MvPolynomial.isWeightedHomogeneous_X ℂ ![1, 1] (0 : Fin 2)
  have ht : (formT : Form ℂ).IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [formT] using
      MvPolynomial.isWeightedHomogeneous_X ℂ ![1, 1] (1 : Fin 2)
  fin_cases i
  · change (cubicForm 3 0 : Form ℂ).IsWeightedHomogeneous ![1, 1] 3
    have h1 := hx.pow 3
    have h2 := (hx.C_mul (3 : ℂ)).mul (ht.pow 2)
    have h3 := (ht.pow 3).C_mul (0 : ℂ)
    simpa [cubicForm, nsmul_eq_mul] using (h1.add h2).add h3
  · change (quarticForm 1 0 4 0 2 : Form ℂ).IsWeightedHomogeneous
      ![1, 1] 4
    have h4 := (hx.pow 4).C_mul (1 : ℂ)
    have h31 := ((hx.pow 3).C_mul (0 : ℂ)).mul ht
    have h22 := ((hx.pow 2).C_mul (4 : ℂ)).mul (ht.pow 2)
    have h13 := (hx.C_mul (0 : ℂ)).mul (ht.pow 3)
    have h04 := (ht.pow 4).C_mul (2 : ℂ)
    simpa [quarticForm, nsmul_eq_mul] using
      (((h4.add h31).add h22).add h13).add h04
  · change R.IsWeightedHomogeneous ![1, 1] N
    change R.IsWeightedHomogeneous 1 N at hR
    have hw : (![1, 1] : Fin 2 → ℕ) = 1 := by
      funext j
      fin_cases j
      all_goals rfl
    rwa [hw]

/-- The ordinary H map evaluated as a function. -/
@[expose]
noncomputable def hOrdinaryInitialMap
    (R : Form ℂ) : ℂ × ℂ → Fin 3 → ℂ :=
  weightedPolynomialMap (hOrdinaryPolynomialMap R)

/-- At radial parameter zero, the first two divided differences are the H
reflection plane equations. -/
theorem hOrdinaryReflectionPlanePart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation (hOrdinaryInitialMap R) remainder)
        x ((0, lambda), v) =
      hResidueRotationPlaneDifference 1 x (lambda, v) := by
  funext i
  fin_cases i
  all_goals
    simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint, hOrdinaryInitialMap,
      weightedPolynomialMap, hOrdinaryPolynomialMap, cubicForm, quarticForm,
      formX, formT, hResidueRotationPlaneDifference]

/-- On the explicit branch, the third divided difference is the affine
reflection polynomial. -/
theorem hOrdinaryReflectionThirdPart_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) :
    rotationThirdPart
        (weightedRescaledPerturbation (hOrdinaryInitialMap R) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x (-1) lambda) =
      (eRotationLinePolynomial (-1) R).eval (x + lambda) := by
  rw [rotationThirdPart, rotationReparametrization,
    weightedRescaledPerturbation_zero, eRotationLinePolynomial_eval]
  simp only [weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, rotationAffinePoint,
    explicitRotationPlaneBranch, hOrdinaryInitialMap,
    hOrdinaryPolynomialMap, Fin.isValue]
  change MvPolynomial.eval ![x + lambda, 1] R -
      MvPolynomial.eval ![x + lambda, -1] R =
    MvPolynomial.eval ![x + lambda, 1]
      (R - eRotateForm (-1) R)
  rw [map_sub, eRotateForm_eval]
  norm_num

/-- An ordinary H reflection line collision persists under every analytic
radial perturbation. -/
theorem eventually_exists_hOrdinaryReflectionZero_mem_nhds
    {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N)
    (data : HReflectionLineCollisionCertificate R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (data.x / data.t, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (data.x / data.t, -1)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![data.x / data.t, data.x / data.t, -1])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation (hOrdinaryInitialMap R) remainder
            (tau, q) = 0 := by
  let z := data.x / data.t
  let p := eRotationLineNormalizedPolynomial (-1) R
  let Phi := weightedRescaledPerturbation (hOrdinaryInitialMap R) remainder
  have homegaSquare : (-1 : ℂ) ^ 2 = 1 := by norm_num
  have homegaOne : (-1 : ℂ) ≠ 1 := by norm_num
  have homegaZero : (-1 : ℂ) ≠ 0 := by norm_num
  have hpBase : eRotationLinePolynomial (-1) R ≠ 0 :=
    eRotationLinePolynomial_ne_zero hR data.reflectionDifference_ne_zero
  have hp : p ≠ 0 :=
    eRotationLineNormalizedPolynomial_ne_zero homegaOne hpBase
  have hx : p.IsRoot z :=
    eRotationLineNormalizedPolynomial_isRoot (data.chart_root hR)
  have hPhi : AnalyticAt ℂ Phi (0, ![z, z, -1]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (hOrdinaryPolynomialMap R) _
    · simpa [z, residueFirstChartPoint] using hfirst
    · simpa [z, residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_explicitThird
    Phi (hResidueRotationPlaneDifference 1 z)
      (hOrdinaryReflectionPointDerivativeEquiv
        z (-1) homegaSquare homegaZero)
      z (-1) 1 p hPhi
  · exact hOrdinaryReflectionPlanePart_zero R remainder z
  · simpa [hOrdinaryReflectionPointDerivativeEquiv] using
      hasStrictFDerivAt_hResidueRotationPlaneDifference_point 1 z (-1)
  · simpa [explicitRotationPlaneBranch] using
      h_explicitOrdinaryReflectionPlaneBranch_eq_zero
        z (-1) homegaSquare 0
  · exact
      eventually_hOrdinaryReflectionPlaneDifference_eq_zero_iff_explicitBranch
        z (-1) homegaSquare homegaZero
  · intro lambda
    calc
      rotationThirdPart Phi z
          ((0, lambda), explicitRotationPlaneBranch z (-1) lambda) =
        (eRotationLinePolynomial (-1) R).eval (z + lambda) :=
          hOrdinaryReflectionThirdPart_zero R remainder z lambda
      _ = (rotationRestrictedDifference (-1) 1 p).eval (z + lambda) := by
        rw [rotationRestrictedDifference_normalizedRotationLine homegaOne]
      _ = residueRotationThirdDifference 1 p z
          (lambda, explicitRotationPlaneBranch z (-1) lambda) := by
        rw [residueRotationThirdDifference]
        exact (explicitRotationThirdDifference_eq
          1 p z (-1) lambda).symm
  · norm_num
  · exact hp
  · exact hx
  · simpa [z] using hU

/-- Ordinary correction terms above the initial degrees make an H reflection
line collision incompatible with local injectivity. -/
theorem hReflectionLineMaximalIdealTails_not_hasInjectiveRepresentative
    {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N)
    (data : HReflectionLineCollisionCertificate R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasOrdinaryRadialExpansionAt_of_mem_maximalIdeal_pow
      (hOrdinaryDegrees N) (hOrdinaryPolynomialMap R)
      (hOrdinaryPolynomialMap_isWeightedHomogeneous R N hR)
      representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedRotationZeros
    1 (hOrdinaryDegrees N) (hOrdinaryInitialMap R)
      representative remainder (data.x / data.t) (-1)
      (by norm_num) (by norm_num)
  · exact hexpansion (data.x / data.t, 1)
  · exact hexpansion (data.x / data.t, -1)
  · intro U hU
    exact eventually_exists_hOrdinaryReflectionZero_mem_nhds
      hR data remainder
        (hexpansion (data.x / data.t, 1)).remainder_analyticAt
        (hexpansion (data.x / data.t, -1)).remainder_analyticAt U hU

end OnLeConjecture.DThree
