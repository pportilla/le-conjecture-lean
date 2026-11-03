/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultipleZeroElimination
public import OnLeConjecture.DThree.EInvariantRegularChart
public import OnLeConjecture.DThree.ResidueRotationNoninjectivity

/-!
# Persistence of a regular invariant E collision

This file treats residual roots for which both cube coordinates are nonzero.
The first two equations are eliminated in the regular affine chart.  The
remaining equation has the root multiplicity of the dehomogenized residual
factor.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A point of the three dimensional fibre chart determined by a residual
direction and the two point variables. -/
@[expose]
noncomputable def eInvariantAffinePoint
    (z lambda : ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![v 0 * (z + lambda), v 0, v 1]

/-- Reparametrization by the perturbation parameter, residual direction,
and point variables. -/
@[expose]
noncomputable def eInvariantReparametrization
    (z : ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × (Fin 3 → ℂ) :=
  (q.1.1, eInvariantAffinePoint z q.1.2 q.2)

/-- The first two coordinates after residual reparametrization. -/
@[expose]
noncomputable def eInvariantPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (eInvariantReparametrization z q) 0,
    Phi (eInvariantReparametrization z q) 1]

/-- The third coordinate after residual reparametrization. -/
@[expose]
noncomputable def eInvariantThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (eInvariantReparametrization z q) 2

theorem analyticAt_eInvariantReparametrization
    (z : ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eInvariantReparametrization z) q := by
  have hparameter : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.1) q :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlambda : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.2) q :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2 i) q := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp
        (analyticAt_snd : AnalyticAt ℂ
          (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.2) q)
  have hpoint : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        eInvariantAffinePoint z q.1.2 q.2) q := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · change AnalyticAt ℂ (fun q ↦ q.2 0 * (z + q.1.2)) q
      exact (hcoordinate 0).mul (analyticAt_const.add hlambda)
    · exact hcoordinate 0
    · exact hcoordinate 1
  exact hparameter.prod hpoint

theorem analyticAt_eInvariantPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi (eInvariantReparametrization z q)) :
    AnalyticAt ℂ (eInvariantPlanePart Phi z) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (eInvariantReparametrization z u)) q :=
    hPhi.fun_comp (analyticAt_eInvariantReparametrization z q)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (eInvariantReparametrization z u)) 0) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 0)
        (f := fun u ↦ Phi (eInvariantReparametrization z u))
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
          (Phi (eInvariantReparametrization z q))) hfull
    simpa [eInvariantPlanePart] using hcoordinate
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (eInvariantReparametrization z u)) 1) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 1)
        (f := fun u ↦ Phi (eInvariantReparametrization z u))
        ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
          (Phi (eInvariantReparametrization z q))) hfull
    simpa [eInvariantPlanePart] using hcoordinate

theorem analyticAt_eInvariantThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi (eInvariantReparametrization z q)) :
    AnalyticAt ℂ (eInvariantThirdPart Phi z) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (eInvariantReparametrization z u)) q :=
    hPhi.fun_comp (analyticAt_eInvariantReparametrization z q)
  have hcoordinate : AnalyticAt ℂ
      (fun u ↦ (Phi (eInvariantReparametrization z u)) 2) q :=
    AnalyticAt.fun_comp
      (g := fun value : Fin 3 → ℂ ↦ value 2)
      (f := fun u ↦ Phi (eInvariantReparametrization z u))
      ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
        (Phi (eInvariantReparametrization z q))) hfull
  change AnalyticAt ℂ
    (fun u ↦ Phi (eInvariantReparametrization z u) 2) q
  exact hcoordinate

/-- Homogeneous evaluation in the affine chart. -/
theorem ePairPointEval_scaled_dehomogenize
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (s u : ℂ) (hs : s ≠ 0) :
    ePairPointEval ℂ (s * u) s theta =
      s ^ n * (ePairDehomogenize theta).eval u := by
  have hdegree := ePairDehomogenize_natDegree_le hhomogeneous
  calc
    ePairPointEval ℂ (s * u) s theta =
        MvPolynomial.eval ![s * u, s] (eIteratedToForm theta) :=
      ePairPointEval_eq_eval_iteratedToForm theta (s * u) s
    _ = MvPolynomial.eval ![s * u, s]
        ((ePairDehomogenize theta).homogenize n) := by
      rw [ePair_homogenize_dehomogenize hhomogeneous]
    _ = (ePairDehomogenize theta).eval ((s * u) / s) * s ^ n :=
      Polynomial.eval_homogenize hdegree ![s * u, s] (by simpa using hs)
    _ = s ^ n * (ePairDehomogenize theta).eval u := by
      rw [mul_div_cancel_left₀ u hs]
      ring

/-- The first two special fibre coordinates in the residual chart are the
explicit plane difference. -/
theorem eInvariantPlanePart_weightedRescaledPerturbation_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z lambda : ℂ) (v : Fin 2 → ℂ) :
    eInvariantPlanePart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        z ((0, lambda), v) =
      eInvariantPlaneDifference z (lambda, v) := by
  funext i
  fin_cases i <;>
    simp [eInvariantPlanePart, eInvariantReparametrization,
      eInvariantAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, weightedPolynomialMap,
      eInvariantPolynomialMap, eInvariantPlaneDifference, cubicForm,
      quarticForm, formX, formT] <;>
    ring

/-- The third special fibre coordinate is the third initial difference. -/
theorem eInvariantThirdPart_weightedRescaledPerturbation_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z lambda : ℂ) (v : Fin 2 → ℂ) :
    eInvariantThirdPart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        z ((0, lambda), v) =
      weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0 * (z + lambda), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0, v 1) 2 := by
  simp [eInvariantThirdPart, eInvariantReparametrization,
    eInvariantAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint]

/-- On the plane fibre, the third difference factors through the
dehomogenized residual polynomial. -/
theorem eInvariantThirdDifference_factorization_of_plane_zero
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (z lambda : ℂ) (v : Fin 2 → ℂ)
    (hs : v 0 ≠ 0) (hdirection : z + lambda ≠ 1)
    (hplane : eInvariantPlaneDifference z (lambda, v) = 0) :
    weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0 * (z + lambda), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0, v 1) 2 =
      (v 0) ^ (n + 1) * (z + lambda - 1) *
        (ePairDehomogenize (eThetaPolynomial ℂ c)).eval
          (z + lambda) := by
  let u := z + lambda
  let x := v 0 * u
  let X := v 0
  have hx : x ≠ X := by
    intro heq
    apply hdirection
    apply mul_left_cancel₀ hs
    simpa [x, X, u] using heq
  have hP : eP x (1 ^ 3) = eP X ((v 1) ^ 3) := by
    have hcomponent := congrFun hplane 0
    have hcomponent' :
        v 0 ^ 3 * ((z + lambda) ^ 3 - 1) +
          3 * (1 - v 1 ^ 3) = 0 := by
      simpa [eInvariantPlaneDifference] using hcomponent
    rw [eP, eP]
    dsimp only [x, X, u]
    norm_num
    linear_combination hcomponent'
  have hQ : eQ x (1 ^ 3) = eQ X ((v 1) ^ 3) := by
    have hcomponent := congrFun hplane 1
    have hcomponent' :
        v 0 ^ 4 * ((z + lambda) ^ 4 - 1) +
          4 * v 0 * (z + lambda - v 1 ^ 3) = 0 := by
      simpa [eInvariantPlaneDifference] using hcomponent
    rw [eQ, eQ]
    dsimp only [x, X, u]
    norm_num
    linear_combination hcomponent'
  obtain ⟨hfirstResidual, hsecondResidual⟩ :=
    (e_fibre_iff_residual hx).mp ⟨hP, hQ⟩
  rw [eInvariantPolynomialMap_third Rzero R hdescent,
    eInvariantPolynomialMap_third Rzero R hdescent]
  rw [hfirstResidual, hsecondResidual]
  rw [eSourcePointEval_residual_difference Rzero c hdecomposition x X]
  rw [ePairPointEval_scaled_dehomogenize hhomogeneous
    (v 0) u hs]
  dsimp only [x, X, u]
  ring

/-- A root of a nonzero polynomial has its root multiplicity factorization
with a nonvanishing quotient. -/
theorem exists_polynomial_local_factorization
    {p : ℂ[X]} {z : ℂ} (hp : p ≠ 0) (hz : p.IsRoot z) :
    0 < p.rootMultiplicity z ∧
      ∃ quotient : ℂ[X],
        p = (X - C z) ^ p.rootMultiplicity z * quotient ∧
        quotient.eval z ≠ 0 := by
  have hm : 0 < p.rootMultiplicity z :=
    (rootMultiplicity_pos hp).2 hz
  let quotient := p /ₘ (X - C z) ^ p.rootMultiplicity z
  exact ⟨hm, quotient,
    (pow_mul_divByMonic_rootMultiplicity_eq p z).symm,
    eval_divByMonic_pow_rootMultiplicity_ne_zero z hp⟩

/-- Evaluation of the local polynomial factorization after translation by
the selected root. -/
theorem polynomial_eval_add_factorization
    {p quotient : ℂ[X]} {z : ℂ}
    (hfactor : p = (X - C z) ^ p.rootMultiplicity z * quotient)
    (lambda : ℂ) :
    p.eval (z + lambda) =
      lambda ^ p.rootMultiplicity z * quotient.eval (z + lambda) := by
  have heval := congrArg (fun polynomial : ℂ[X] ↦
    polynomial.eval (z + lambda)) hfactor
  rw [eval_mul, eval_pow] at heval
  simpa using heval

/-- A perturbation of a regular invariant residual collision has a full
zero in every neighborhood of the initial projective direction. -/
theorem eventually_exists_eInvariantRegularZero_mem_nhds_of_analyticPerturbation
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (z s g : ℂ)
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
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0)
    (hPhi : AnalyticAt ℂ Phi (0, ![s * z, s, g]))
    (hspecialPlane : ∀ lambda v,
      eInvariantPlanePart Phi z ((0, lambda), v) =
        eInvariantPlaneDifference z (lambda, v))
    (hspecialThird : ∀ lambda v,
      eInvariantThirdPart Phi z ((0, lambda), v) =
        weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 0 * (z + lambda), 1) 2 -
          weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 0, v 1) 2)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![s * z, s, g])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let q : Fin 2 → ℂ := ![s, g]
  let plane := eInvariantPlanePart Phi z
  let third := eInvariantThirdPart Phi z
  have hreparamBase :
      eInvariantReparametrization z (((0, 0) : ℂ × ℂ), q) =
        (0, ![s * z, s, g]) := by
    ext i <;> simp [eInvariantReparametrization,
      eInvariantAffinePoint, q]
  have hplane : AnalyticAt ℂ plane (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_eInvariantPlanePart
    simpa [hreparamBase] using hPhi
  have hthird : AnalyticAt ℂ third (((0, 0) : ℂ × ℂ), q) := by
    apply analyticAt_eInvariantThirdPart
    simpa [hreparamBase] using hPhi
  let pointEquiv :=
    eInvariantPlanePointDerivativeEquiv z s g hs hg hW hzOne
  have hmodelDerivative :
      HasStrictFDerivAt
        (fun v ↦ eInvariantPlaneDifference z (0, v))
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, eInvariantPlanePointDerivativeEquiv] using
      hasStrictFDerivAt_eInvariantPlaneDifference_point z s g
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
      ext v <;> rfl
    rw [hinr] at hcomposition
    have hfixed :
        (fun v ↦ plane (((0, 0) : ℂ × ℂ), v)) =
          fun v ↦ eInvariantPlaneDifference z (0, v) := by
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
    exact eInvariantPlaneDifference_base_eq_zero z s g hs hg
  let branch := analyticImplicitBranch
    plane (((0, 0), q)) hplane hpoint
  have hbranch : AnalyticAt ℂ branch (0, 0) :=
    analyticAt_analyticImplicitBranch
      plane (((0, 0), q)) hplane hpoint
  have hbranchBase : branch (0, 0) = q :=
    analyticImplicitBranch_apply_base
      plane (((0, 0), q)) hplane hpoint
  have hparameter : Tendsto
      (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ))
      (nhds 0) (nhds (0, 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hbranchSpecial : Tendsto (fun lambda ↦ branch (0, lambda))
      (nhds 0) (nhds q) := by
    have ht := hbranch.continuousAt.tendsto.comp hparameter
    rw [hbranchBase] at ht
    simpa [Function.comp_def] using ht
  have hplaneBranch : ∀ᶠ parameter in nhds (0, 0),
      plane (parameter, branch parameter) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane (((0, 0), q)) hplane hpoint] with parameter hparameter'
    simpa [hplaneZero] using hparameter'
  have hplaneBranchSpecial : ∀ᶠ lambda in nhds 0,
      eInvariantPlaneDifference z (lambda, branch (0, lambda)) = 0 := by
    filter_upwards [hparameter.eventually hplaneBranch] with lambda hlambda
    rw [← hspecialPlane lambda (branch (0, lambda))]
    exact hlambda
  have hsNe : s ≠ 0 := eInvariant_chart_s_ne_zero hs
  have hbranchFirst : Tendsto
      (fun lambda ↦ branch (0, lambda) 0) (nhds 0) (nhds s) := by
    simpa [q] using tendsto_pi_nhds.mp hbranchSpecial 0
  have hbranchFirstNe : ∀ᶠ lambda in nhds 0,
      branch (0, lambda) 0 ≠ 0 :=
    hbranchFirst.eventually_ne hsNe
  have hdirection : Tendsto (fun lambda : ℂ ↦ z + lambda)
      (nhds 0) (nhds z) := by
    have hzConstant : Tendsto (fun _ : ℂ ↦ z) (nhds 0) (nhds z) :=
      tendsto_const_nhds
    simpa [id] using hzConstant.add tendsto_id
  have hdirectionNe : ∀ᶠ lambda in nhds 0,
      z + lambda ≠ 1 := hdirection.eventually_ne hzOne
  let p := ePairDehomogenize (eThetaPolynomial ℂ c)
  obtain ⟨hm, quotient, hfactorization, hquotient⟩ :=
    exists_polynomial_local_factorization hp hzRoot
  let unit : ℂ → ℂ := fun lambda ↦
    branch (0, lambda) 0 ^ (n + 1) * (z + lambda - 1) *
      quotient.eval (z + lambda)
  have hbranchCoordinateAnalytic : AnalyticAt ℂ
      (fun lambda ↦ branch (0, lambda) 0) 0 := by
    have hembed : AnalyticAt ℂ
        (fun lambda : ℂ ↦ ((0, lambda) : ℂ × ℂ)) 0 :=
      analyticAt_const.prod analyticAt_id
    have hbranchAlong : AnalyticAt ℂ
        (fun lambda ↦ branch (0, lambda)) 0 :=
      hbranch.fun_comp hembed
    have hprojection : AnalyticAt ℂ
        (fun lambda ↦ branch (0, lambda) 0) 0 :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 2 → ℂ ↦ value 0)
        (f := fun lambda ↦ branch (0, lambda))
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt
          (branch (0, 0))) hbranchAlong
    exact hprojection
  have hquotientAnalytic : AnalyticAt ℂ
      (fun lambda ↦ quotient.eval (z + lambda)) 0 := by
    have hargument : AnalyticAt ℂ (fun lambda : ℂ ↦ z + lambda) 0 :=
      analyticAt_const.add analyticAt_id
    simpa [aeval_def] using hargument.aeval_polynomial quotient
  have hunit : AnalyticAt ℂ unit 0 := by
    exact ((hbranchCoordinateAnalytic.pow (n + 1)).mul
      ((analyticAt_const.add analyticAt_id).sub analyticAt_const)).mul
        hquotientAnalytic
  have hunitZero : unit 0 ≠ 0 := by
    rw [show unit 0 = s ^ (n + 1) * (z - 1) * quotient.eval z by
      simp [unit, hbranchBase, q]]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero (n + 1) hsNe)
        (sub_ne_zero.mpr hzOne)) hquotient
  have hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda), branch (0, lambda)) =
        lambda ^ p.rootMultiplicity z * unit lambda := by
    filter_upwards [hplaneBranchSpecial, hbranchFirstNe,
      hdirectionNe] with lambda hplaneAt hfirstNe hdirectionAt
    change eInvariantThirdPart Phi z
        ((0, lambda), branch (0, lambda)) =
      lambda ^ p.rootMultiplicity z * unit lambda
    rw [hspecialThird]
    rw [eInvariantThirdDifference_factorization_of_plane_zero
      Rzero R c n hdescent hdecomposition hhomogeneous z lambda
        (branch (0, lambda)) hfirstNe hdirectionAt hplaneAt]
    rw [polynomial_eval_add_factorization hfactorization]
    simp only [unit, p]
    ring
  let V : Set (((ℂ × ℂ) × (Fin 2 → ℂ))) :=
    eInvariantReparametrization z ⁻¹' U
  have hV : V ∈ nhds (((0, 0) : ℂ × ℂ), q) := by
    have ht :=
      (analyticAt_eInvariantReparametrization z
        (((0, 0) : ℂ × ℂ), q)).continuousAt
    have ht' : Tendsto (eInvariantReparametrization z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (0, ![s * z, s, g])) := by
      change Tendsto (eInvariantReparametrization z)
        (nhds (((0, 0) : ℂ × ℂ), q))
        (nhds (eInvariantReparametrization z (((0, 0), q)))) at ht
      rw [hreparamBase] at ht
      exact ht
    exact ht'.eventually hU
  have hzero :=
    eventually_exists_fullZero_of_analyticElimination_mem_nhds
      plane third q hplane hpoint hplaneZero hthird
        (p.rootMultiplicity z) unit hm hunit hunitZero hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨lambda, hmem, hplaneAt, hthirdAt⟩ := htau
  let point := eInvariantAffinePoint z lambda (branch (tau, lambda))
  refine ⟨point, ?_, ?_⟩
  · exact hmem
  · funext i
    fin_cases i
    · exact congrFun hplaneAt 0
    · exact congrFun hplaneAt 1
    · exact hthirdAt

theorem analyticAt_weightedPolynomialMap
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ) (point : ℂ × ℂ) :
    AnalyticAt ℂ (weightedPolynomialMap P) point := by
  rw [analyticAt_pi_iff]
  intro i
  have hcoordinate (j : Fin 2) : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z j) point := by
    exact (((ContinuousLinearMap.proj (R := ℂ) j).comp
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap)
        |>.analyticAt point)
  change AnalyticAt ℂ
    (fun z : ℂ × ℂ ↦ MvPolynomial.eval
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) (P i)) point
  simpa [MvPolynomial.aeval_def] using
    AnalyticAt.aeval_mvPolynomial hcoordinate (P i)

theorem analyticAt_weightedInitialDifference_weightedPolynomialMap
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference (weightedPolynomialMap P)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ weightedPolynomialMap P (residueFirstChartPoint q)) -
      fun q ↦ weightedPolynomialMap P (residueSecondChartPoint q)) q
  exact
    (analyticAt_weightedPolynomialMap P (residueFirstChartPoint q)).fun_comp
      (analyticAt_residueFirstChartPoint q) |>.sub
        ((analyticAt_weightedPolynomialMap P (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

/-- The rescaled perturbation of a regular invariant initial map has a zero
in every neighborhood of its initial collision. -/
theorem eventually_exists_eWeightedInvariantRegularZero_mem_nhds
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (z s g : ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (s * z, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (s, g)))
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
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![s * z, s, g])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (weightedPolynomialMap (eInvariantPolynomialMap R))
              remainder (tau, point) = 0 := by
  let initialMap := weightedPolynomialMap (eInvariantPolynomialMap R)
  let Phi := weightedRescaledPerturbation initialMap remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![s * z, s, g]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) ![s * z, s, g]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply eventually_exists_eInvariantRegularZero_mem_nhds_of_analyticPerturbation
    Phi Rzero R c n z s g hdescent hdecomposition hhomogeneous hp
      hzRoot hzOne hs hg hW hPhi
  · exact eInvariantPlanePart_weightedRescaledPerturbation_zero
      R remainder z
  · exact eInvariantThirdPart_weightedRescaledPerturbation_zero
      R remainder z
  · exact hU

end OnLeConjecture.DThree
