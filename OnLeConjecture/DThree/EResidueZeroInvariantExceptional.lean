/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroInvariantRegular
public import OnLeConjecture.DThree.EInvariantExceptionalNoninjectivity

/-!
# Exceptional invariant E collisions after a power substitution

In the exceptional chart, the second coordinate of the second point
vanishes. The weighted coordinate itself is used as the branch parameter.
Its `a`th power is the parameter in the ordinary exceptional equations.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The exceptional ordinary plane equations after replacing their
parameter by its `a`th power. -/
@[expose]
noncomputable def eInvariantExceptionalPlaneDifferencePower
    (a : ℕ) (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  eInvariantExceptionalPlaneDifference z (q.1 ^ a, q.2)

theorem analyticAt_eInvariantExceptionalPlaneDifferencePower
    (a : ℕ) (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eInvariantExceptionalPlaneDifferencePower a z) q := by
  have hlift : AnalyticAt ℂ
      (fun value : ℂ × (Fin 2 → ℂ) ↦ (value.1 ^ a, value.2)) q :=
    (analyticAt_fst.pow a).prod analyticAt_snd
  exact AnalyticAt.fun_comp
    (x := q) (g := eInvariantExceptionalPlaneDifference z)
      (f := fun value : ℂ × (Fin 2 → ℂ) ↦
        (value.1 ^ a, value.2))
      (analyticAt_eInvariantExceptionalPlaneDifference z
        (q.1 ^ a, q.2)) hlift

/-- The derivative in the point variables at parameter zero is unchanged
by the power substitution. -/
theorem
    hasStrictFDerivAt_eInvariantExceptionalPlaneDifferencePower_point
    (a : ℕ) (ha : 0 < a) (z s : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ eInvariantExceptionalPlaneDifferencePower a z (0, v))
      (eInvariantExceptionalPointDerivative z s) ![0, s] := by
  have heq :
      (fun v ↦ eInvariantExceptionalPlaneDifferencePower a z (0, v)) =
        fun v ↦ eInvariantExceptionalPlaneDifference z (0, v) := by
    funext v
    simp [eInvariantExceptionalPlaneDifferencePower, zero_pow ha.ne']
  rw [heq]
  exact hasStrictFDerivAt_eInvariantExceptionalPlaneDifference_point z s

/-- At radial parameter zero, the first two weighted differences are the
powered exceptional plane equations. -/
theorem eInvariantExceptionalPlanePart_eResidueZero_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z g : ℂ) (v : Fin 2 → ℂ) :
    eInvariantExceptionalPlanePart
        (weightedRescaledPerturbation
          (eResidueZeroInitialMap a R) remainder)
        z ((0, g), v) =
      eInvariantExceptionalPlaneDifferencePower a z (g, v) := by
  funext i
  fin_cases i
  · simp [eInvariantExceptionalPlanePart,
      eInvariantExceptionalReparametrization,
      eInvariantExceptionalAffinePoint,
      eInvariantExceptionalPlaneDifferencePower,
      eInvariantExceptionalPlaneDifference, eInvariantPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      eResidueZeroInitialMap, eResidueZeroPolynomialMap,
      weightedPolynomialMap, eInvariantPolynomialMap,
      weightedPowerSubstitutionForm, cubicForm, formX, formT]
    all_goals ring_nf
  · simp [eInvariantExceptionalPlanePart,
      eInvariantExceptionalReparametrization,
      eInvariantExceptionalAffinePoint,
      eInvariantExceptionalPlaneDifferencePower,
      eInvariantExceptionalPlaneDifference, eInvariantPlaneDifference,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      eResidueZeroInitialMap, eResidueZeroPolynomialMap,
      weightedPolynomialMap, eInvariantPolynomialMap,
      weightedPowerSubstitutionForm, quarticForm, formX, formT]
    all_goals ring_nf

/-- The third weighted special fibre coordinate is the ordinary third
difference with powered exceptional parameter. -/
theorem eInvariantExceptionalThirdPart_eResidueZero_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z g : ℂ) (v : Fin 2 → ℂ) :
    eInvariantExceptionalThirdPart
        (weightedRescaledPerturbation
          (eResidueZeroInitialMap a R) remainder)
        z ((0, g), v) =
      weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 1 * (z + v 0), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 1, g ^ a) 2 := by
  rw [eInvariantExceptionalThirdPart,
    eInvariantExceptionalReparametrization,
    eInvariantExceptionalAffinePoint, weightedRescaledPerturbation_zero]
  change
    MvPolynomial.eval ![v 1 * (z + v 0), 1]
          (weightedPowerSubstitutionForm a R) -
        MvPolynomial.eval ![v 1, g]
          (weightedPowerSubstitutionForm a R) =
      MvPolynomial.eval ![v 1 * (z + v 0), 1] R -
        MvPolynomial.eval ![v 1, g ^ a] R
  have hfirst := eval_weightedPowerSubstitutionForm
    a R (v 1 * (z + v 0), 1)
  have hsecond := eval_weightedPowerSubstitutionForm a R (v 1, g)
  simpa using congrArg₂ (· - ·) hfirst hsecond

/-- An analytic perturbation of the powered exceptional equations has a
full zero in every neighborhood of the initial direction. -/
theorem
    eventually_exists_eInvariantExceptionalPowerZero_mem_nhds_of_analyticPerturbation
    (a : ℕ) (ha : 0 < a)
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (z s : ℂ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0)
    (hPhi : AnalyticAt ℂ Phi (0, ![s * z, s, 0]))
    (hspecialPlane : ∀ g v,
      eInvariantExceptionalPlanePart Phi z ((0, g), v) =
        eInvariantExceptionalPlaneDifferencePower a z (g, v))
    (hspecialThird : ∀ g v,
      eInvariantExceptionalThirdPart Phi z ((0, g), v) =
        weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 1 * (z + v 0), 1) 2 -
          weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 1, g ^ a) 2)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![s * z, s, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![0, s]
  let plane := eInvariantExceptionalPlanePart Phi z
  let third := eInvariantExceptionalThirdPart Phi z
  have hreparamBase :
      eInvariantExceptionalReparametrization z
          (((0, 0) : ℂ × ℂ), q) =
        (0, ![s * z, s, 0]) := by
    ext i
    all_goals simp [eInvariantExceptionalReparametrization,
      eInvariantExceptionalAffinePoint, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_eInvariantExceptionalPlanePart
    simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_eInvariantExceptionalThirdPart
    simpa [hreparamBase] using hPhi
  let pointEquiv :=
    eInvariantExceptionalPointDerivativeEquiv z s hzOne hs hW
  have hmodelDerivative :
      HasStrictFDerivAt
        (fun v ↦ eInvariantExceptionalPlaneDifferencePower a z (0, v))
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, eInvariantExceptionalPointDerivativeEquiv] using
      hasStrictFDerivAt_eInvariantExceptionalPlaneDifferencePower_point
        a ha z s
  have hpointEq :
      fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) =
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) := by
    have hcomposition := hplane.hasStrictFDerivAt.comp q
      ((hasStrictFDerivAt_const (𝕜 := ℂ) ((0, 0) : ℂ × ℂ) q).prodMk
        (hasStrictFDerivAt_id q))
    have hinr :
        (0 : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ)).prod
            (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
          ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ) := by
      ext v
      all_goals rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun v ↦ plane (((0, 0) : ℂ × ℂ), v)) =
          fun v ↦ eInvariantExceptionalPlaneDifferencePower a z (0, v) := by
      funext v
      exact hspecialPlane 0 v
    rw [hfixed] at hcomposition
    exact hcomposition.hasFDerivAt.unique hmodelDerivative.hasFDerivAt
  have hpoint :
      (fderiv ℂ plane (((0, 0) : ℂ × ℂ), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) (Fin 2 → ℂ)).IsInvertible := by
    rw [hpointEq]
    exact ContinuousLinearMap.isInvertible_equiv
  have hplaneZero : plane (((0, 0) : ℂ × ℂ), q) = 0 := by
    dsimp only [plane, q]
    rw [hspecialPlane]
    rw [eInvariantExceptionalPlaneDifferencePower,
      eInvariantExceptionalPlaneDifference]
    have hbase := eInvariantPlaneDifference_base_eq_zero z s 0 hs (by
      simp [hW])
    simpa [zero_pow ha.ne'] using hbase
  let branch := analyticImplicitBranch
    plane (((0, 0), q)) hplane hpoint
  have hbranch : AnalyticAt ℂ branch (0, 0) :=
    analyticAt_analyticImplicitBranch
      plane (((0, 0), q)) hplane hpoint
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base
      plane (((0, 0), q)) hplane hpoint
  have hparameter : Tendsto
      (fun g : ℂ ↦ ((0, g) : ℂ × ℂ))
      (nhds 0) (nhds (0, 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hbranchSpecial : Tendsto (fun g ↦ branch (0, g))
      (nhds 0) (nhds q) := by
    have htendsto := hbranch.continuousAt.tendsto.comp hparameter
    rw [hbranchBase] at htendsto
    simpa [Function.comp_def] using htendsto
  have hplaneBranch : ∀ᶠ parameter in nhds (0, 0),
      plane (parameter, branch parameter) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane (((0, 0), q)) hplane hpoint] with parameter hparameterAt
    simpa [hplaneZero] using hparameterAt
  have hplaneBranchSpecial : ∀ᶠ g in nhds 0,
      eInvariantExceptionalPlaneDifferencePower a z
        (g, branch (0, g)) = 0 := by
    filter_upwards [hparameter.eventually hplaneBranch] with g hg
    rw [← hspecialPlane g (branch (0, g))]
    exact hg
  have hsNe : s ≠ 0 := eInvariant_chart_s_ne_zero hs
  have hbranchScale : Tendsto
      (fun g ↦ branch (0, g) 1) (nhds 0) (nhds s) := by
    simpa [q] using tendsto_pi_nhds.mp hbranchSpecial 1
  have hbranchScaleNe : ∀ᶠ g in nhds 0,
      branch (0, g) 1 ≠ 0 :=
    hbranchScale.eventually_ne hsNe
  have hbranchLambda : Tendsto
      (fun g ↦ branch (0, g) 0) (nhds 0) (nhds 0) := by
    simpa [q] using tendsto_pi_nhds.mp hbranchSpecial 0
  have hdirection : Tendsto
      (fun g ↦ z + branch (0, g) 0) (nhds 0) (nhds z) := by
    simpa using tendsto_const_nhds.add hbranchLambda
  have hdirectionNe : ∀ᶠ g in nhds 0,
      z + branch (0, g) 0 ≠ 1 :=
    hdirection.eventually_ne hzOne
  have hresidual : ∀ᶠ g in nhds 0,
      branch (0, g) 1 ^ 3 *
          eResidualW (z + branch (0, g) 0) 1 = 1 ∧
        (g ^ a) ^ 3 = branch (0, g) 1 ^ 3 *
          eResidualW 1 (z + branch (0, g) 0) := by
    filter_upwards [hplaneBranchSpecial, hbranchScaleNe,
      hdirectionNe] with g hplaneAt hscaleAt hdirectionAt
    exact eInvariantExceptionalPlaneDifference_zero_residual_coordinates
      z (g ^ a) (branch (0, g)) hscaleAt hdirectionAt hplaneAt
  have hembed : AnalyticAt ℂ
      (fun g : ℂ ↦ ((0, g) : ℂ × ℂ)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hbranchAlong : AnalyticAt ℂ
      (fun g ↦ branch (0, g)) 0 :=
    hbranch.fun_comp hembed
  have hbranchCoordinateAnalytic (i : Fin 2) : AnalyticAt ℂ
      (fun g ↦ branch (0, g) i) 0 :=
    AnalyticAt.fun_comp
      (g := fun value : Fin 2 → ℂ ↦ value i)
      (f := fun g ↦ branch (0, g))
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
        (branch (0, 0))) hbranchAlong
  have hresidualQuotientAnalytic : AnalyticAt ℂ
      (fun g ↦ eInvariantExceptionalResidualQuotient z
        (branch (0, g) 0)) 0 := by
    have hargument : AnalyticAt ℂ
        (fun g ↦ z + branch (0, g) 0) 0 :=
      analyticAt_const.add (hbranchCoordinateAnalytic 0)
    have hsum : AnalyticAt ℂ (fun g ↦
        (z + branch (0, g) 0) ^ 2 +
          (z + branch (0, g) 0) * z + z ^ 2 +
          (z + branch (0, g) 0) + z + 1) 0 :=
      ((((hargument.pow 2).add (hargument.mul analyticAt_const)).add
        analyticAt_const).add hargument).add analyticAt_const
        |>.add analyticAt_const
    convert hsum.const_smul (c := (12 : ℂ)⁻¹) using 1
    funext g
    simp [eInvariantExceptionalResidualQuotient, div_eq_mul_inv,
      Pi.smul_apply, smul_eq_mul]
    ring
  let denominator : ℂ → ℂ := fun g ↦
    branch (0, g) 1 ^ 3 *
      eInvariantExceptionalResidualQuotient z (branch (0, g) 0)
  have hdenominator : AnalyticAt ℂ denominator 0 := by
    exact (hbranchCoordinateAnalytic 1).pow 3
      |>.mul hresidualQuotientAnalytic
  have hdenominatorZero : denominator 0 ≠ 0 := by
    rw [show denominator 0 = s ^ 3 *
        eInvariantExceptionalResidualQuotient z 0 by
      simp [denominator, hbranchBase, q]]
    exact mul_ne_zero (pow_ne_zero 3 hsNe)
      (eInvariantExceptionalResidualQuotient_zero_ne z s hs)
  have hdenominatorNe : ∀ᶠ g in nhds 0, denominator g ≠ 0 :=
    hdenominator.continuousAt.eventually_ne hdenominatorZero
  let lambdaUnit : ℂ → ℂ := fun g ↦ (denominator g)⁻¹
  have hlambdaUnit : AnalyticAt ℂ lambdaUnit 0 :=
    hdenominator.inv hdenominatorZero
  have hlambdaUnitZero : lambdaUnit 0 ≠ 0 :=
    inv_ne_zero hdenominatorZero
  have hlambdaFactor : ∀ᶠ g in nhds 0,
      branch (0, g) 0 = g ^ (3 * a) * lambdaUnit g := by
    filter_upwards [hresidual, hdenominatorNe]
      with g hresidualAt hdenominatorAt
    have hsecond := hresidualAt.2
    rw [eResidualW_one_add_factorization
      z (branch (0, g) 0) hW] at hsecond
    have hproduct :
        branch (0, g) 0 * denominator g = (g ^ a) ^ 3 := by
      calc
        branch (0, g) 0 * denominator g =
            branch (0, g) 1 ^ 3 *
              (branch (0, g) 0 *
                eInvariantExceptionalResidualQuotient z
                  (branch (0, g) 0)) := by
          simp only [denominator]
          ring
        _ = (g ^ a) ^ 3 := hsecond.symm
    change branch (0, g) 0 = g ^ (3 * a) * (denominator g)⁻¹
    calc
      branch (0, g) 0 =
          (branch (0, g) 0 * denominator g) * (denominator g)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hdenominatorAt, mul_one]
      _ = (g ^ a) ^ 3 * (denominator g)⁻¹ := by rw [hproduct]
      _ = g ^ (3 * a) * (denominator g)⁻¹ := by
        rw [← pow_mul]
        congr 2
        omega
  let p := ePairDehomogenize (eThetaPolynomial ℂ c)
  obtain ⟨hm, quotient, hfactorization, hquotient⟩ :=
    exists_polynomial_local_factorization hp hzRoot
  let unit : ℂ → ℂ := fun g ↦
    branch (0, g) 1 ^ (n + 1) *
      (z + branch (0, g) 0 - 1) *
      lambdaUnit g ^ p.rootMultiplicity z *
      quotient.eval (z + branch (0, g) 0)
  have hquotientAnalytic : AnalyticAt ℂ
      (fun g ↦ quotient.eval (z + branch (0, g) 0)) 0 := by
    have hargument : AnalyticAt ℂ
        (fun g ↦ z + branch (0, g) 0) 0 :=
      analyticAt_const.add (hbranchCoordinateAnalytic 0)
    simpa [aeval_def] using hargument.aeval_polynomial quotient
  have hunit : AnalyticAt ℂ unit 0 := by
    exact ((((hbranchCoordinateAnalytic 1).pow (n + 1)).mul
      ((analyticAt_const.add (hbranchCoordinateAnalytic 0)).sub
        analyticAt_const)).mul
          (hlambdaUnit.pow (p.rootMultiplicity z))).mul hquotientAnalytic
  have hunitZero : unit 0 ≠ 0 := by
    rw [show unit 0 = s ^ (n + 1) * (z - 1) *
        lambdaUnit 0 ^ p.rootMultiplicity z * quotient.eval z by
      simp [unit, hbranchBase, q]]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero (n + 1) hsNe)
          (sub_ne_zero.mpr hzOne))
        (pow_ne_zero (p.rootMultiplicity z) hlambdaUnitZero)) hquotient
  have hfactor : ∀ᶠ g in nhds 0,
      third ((0, g), branch (0, g)) =
        g ^ ((3 * a) * p.rootMultiplicity z) * unit g := by
    filter_upwards [hplaneBranchSpecial, hbranchScaleNe,
      hdirectionNe, hlambdaFactor] with
      g hplaneAt hscaleAt hdirectionAt hlambdaAt
    change eInvariantExceptionalThirdPart Phi z
        ((0, g), branch (0, g)) =
      g ^ ((3 * a) * p.rootMultiplicity z) * unit g
    rw [hspecialThird]
    rw [eInvariantExceptionalThirdDifference_factorization_of_plane_zero
      Rzero R c n hdescent hdecomposition hhomogeneous z (g ^ a)
        (branch (0, g)) hscaleAt hdirectionAt hplaneAt]
    rw [polynomial_eval_add_factorization hfactorization]
    rw [hlambdaAt, mul_pow, ← pow_mul]
    simp only [unit, p]
    rw [hlambdaAt]
    ring
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    eInvariantExceptionalReparametrization z ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have htendsto :=
      (analyticAt_eInvariantExceptionalReparametrization z
        (((0, 0) : ℂ × ℂ), q)).continuousAt
    have htendsto' : Tendsto (eInvariantExceptionalReparametrization z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, ![s * z, s, 0])) := by
      change Tendsto (eInvariantExceptionalReparametrization z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (eInvariantExceptionalReparametrization z
          (((0, 0), q)))) at htendsto
      rw [hreparamBase] at htendsto
      exact htendsto
    exact htendsto'.eventually hU
  have hzero :=
    eventually_exists_fullZero_of_analyticElimination_mem_nhds
      plane third q hplane hpoint hplaneZero hthird
        ((3 * a) * p.rootMultiplicity z) unit
          (Nat.mul_pos (by omega) hm)
          hunit hunitZero hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨g, hmem, hplaneAt, hthirdAt⟩ := htau
  let point := eInvariantExceptionalAffinePoint z g (branch (tau, g))
  refine ⟨point, hmem, ?_⟩
  funext i
  fin_cases i
  · exact congrFun hplaneAt 0
  · exact congrFun hplaneAt 1
  · exact hthirdAt

/-- The rescaled perturbation of a substituted exceptional invariant map
has a zero in every neighborhood of its initial collision. -/
theorem eventually_exists_eResidueZeroInvariantExceptionalZero_mem_nhds
    (a : ℕ) (ha : 0 < a)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (z s : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (s * z, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (s, 0)))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![s * z, s, 0])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  let Phi := weightedRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![s * z, s, 0]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) ![s * z, s, 0]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply
    eventually_exists_eInvariantExceptionalPowerZero_mem_nhds_of_analyticPerturbation
      a ha Phi Rzero R c n z s hdescent hdecomposition hhomogeneous hp
        hzRoot hzOne hs hW hPhi
  · exact eInvariantExceptionalPlanePart_eResidueZero_zero
      a R remainder z
  · exact eInvariantExceptionalThirdPart_eResidueZero_zero
      a R remainder z
  · exact hU

/-- Weighted tails exclude an injective representative at an exceptional
invariant residual root after every positive power substitution. -/
theorem
    eInvariantExceptionalResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a : ℕ) (ha : 0 < a)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ) (z : ℂ)
    (hR : R.IsHomogeneous N)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hThetaHomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hw : eResidualW z 1 ≠ 0)
    (hW : eResidualW 1 z = 0)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨s, _, hs, _⟩ :=
    exists_eInvariantRegularChartCoordinates z hw
  have hsNe : s ≠ 0 := eInvariant_chart_s_ne_zero hs
  have hdistinct : s * z ≠ s := by
    intro hequal
    apply hzOne
    apply mul_left_cancel₀ hsNe
    simpa using hequal
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (eResidueZeroDegrees a N) (eResidueZeroPolynomialMap a R)
        (eResidueZeroPolynomialMap_isWeightedHomogeneous a N R hR)
          representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_first
    a (eResidueZeroDegrees a N) (eResidueZeroInitialMap a R)
      representative remainder (s * z) s 0 ha hdistinct
  · simpa [eResidueZeroInitialMap] using hexpansion (s * z, 1)
  · simpa [eResidueZeroInitialMap] using hexpansion (s, 0)
  · intro U hU
    exact eventually_exists_eResidueZeroInvariantExceptionalZero_mem_nhds
      a ha Rzero R c n z s remainder
        (hexpansion (s * z, 1)).remainder_analyticAt
        (hexpansion (s, 0)).remainder_analyticAt
        hdescent hdecomposition hThetaHomogeneous hp hzRoot hzOne
          hs hW U hU

end OnLeConjecture.DThree
