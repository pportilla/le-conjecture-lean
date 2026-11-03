/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SimpleZeroPersistence
public import OnLeConjecture.DTwo.ResidualWeightedHomogeneity
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Transversality and multiplicity for the residual collision

The first two equations determine the branch
`(X, Y) = (-(x + lambda), eta)` near the certified collision.  The third
difference on this branch is twice the prepared odd polynomial.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- The first two initial differences with first point `(x + lambda, 1)`
and second point `(X, Y)`. -/
@[expose]
noncomputable def residualRotationPlaneDifference
    (k L : ℕ) (c T x : ℂ)
    (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![1 - s.2 1 ^ k,
    -c * ((x + s.1) ^ 2 + T - (s.2 0 ^ 2 + T * s.2 1 ^ L))]

/-- The derivative in `(X, Y)` of the first two equations at the certified
point. -/
@[expose]
noncomputable def residualRotationPointJacobian
    (k L : ℕ) (c T x eta : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -(k : ℂ) * eta ^ (k - 1);
    -2 * c * x, c * T * (L : ℂ) * eta ^ (L - 1)]

/-- The continuous linear map represented by the point Jacobian. -/
@[expose]
noncomputable def residualRotationPointDerivative
    (k L : ℕ) (c T x eta : ℂ) :
    (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (residualRotationPointJacobian k L c T x eta)).toContinuousLinearMap

theorem analyticAt_residualRotationPlaneDifference
    (k L : ℕ) (c T x : ℂ) (s : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (residualRotationPlaneDifference k L c T x) s := by
  have hlambda : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1) s := analyticAt_fst
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun s : ℂ × (Fin 2 → ℂ) ↦ s.2 i) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt s.2).comp analyticAt_snd
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) ↦
      1 - s.2 1 ^ k) s
    exact analyticAt_const.sub ((hcoordinate 1).pow k)
  · change AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) ↦
      -c * ((x + s.1) ^ 2 + T -
        (s.2 0 ^ 2 + T * s.2 1 ^ L))) s
    fun_prop (disch := assumption)

theorem hasStrictFDerivAt_residualRotationPlaneDifference_point
    (k L : ℕ) (c T x eta : ℂ) :
    HasStrictFDerivAt
      (fun q ↦ residualRotationPlaneDifference k L c T x (0, q))
      (residualRotationPointDerivative k L c T x eta) ![-x, eta] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [residualRotationPlaneDifference]
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) (1 : ℂ) ![-x, eta]).sub
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![-x, eta]).pow k)
      using 1
    · rfl
    · ext v
      simp [residualRotationPointDerivative,
        residualRotationPointJacobian, Matrix.toLin'_apply, dotProduct,
        Fin.sum_univ_succ, mul_comm]
  · convert
      ((hasStrictFDerivAt_const (𝕜 := ℂ) (x ^ 2 + T) ![-x, eta]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2)
          ![-x, eta]).pow 2).add
            (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2)
              ![-x, eta]).pow L).const_mul T))).const_mul (-c)
      using 1
    · rfl
    · funext y
      simp
    · ext v
      simp [residualRotationPointDerivative,
        residualRotationPointJacobian, Matrix.toLin'_apply, dotProduct,
        Fin.sum_univ_succ]
      ring

/-- The determinant is the negative product of the two derivatives already
stored in the collision certificate. -/
theorem det_residualRotationPointJacobian
    (k L : ℕ) (c T x eta : ℂ) :
    Matrix.det (residualRotationPointJacobian k L c T x eta) =
      -((firstInitialDifference k).derivative.eval eta *
        (secondInitialDifference c x).derivative.eval (-x)) := by
  rw [firstInitialDifference_derivative_eval,
    secondInitialDifference_derivative_eval]
  simp [residualRotationPointJacobian, Matrix.det_fin_two]

theorem det_residualRotationPointDerivative
    (k L : ℕ) (c T x eta : ℂ) :
    (residualRotationPointDerivative k L c T x eta).det =
      -((firstInitialDifference k).derivative.eval eta *
        (secondInitialDifference c x).derivative.eval (-x)) := by
  simpa [residualRotationPointDerivative,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin'] using
      det_residualRotationPointJacobian k L c T x eta

/-- The two derivative conditions in a collision certificate give the
point derivative equivalence. -/
@[expose]
noncomputable def InitialCollisionCertificate.residualRotationPointDerivativeEquiv
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (certificate : InitialCollisionCertificate k L N c T Psi) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (residualRotationPointDerivative k L c T certificate.x certificate.eta
    ).toContinuousLinearEquivOfDetNeZero <| by
      rw [det_residualRotationPointDerivative]
      exact neg_ne_zero.mpr <| mul_ne_zero
        certificate.first_derivative_ne_zero
        certificate.second_derivative_ne_zero

/-- The explicit branch of the first two equations through the certified
collision. -/
@[expose]
noncomputable def residualExplicitPlaneBranch
    (x eta lambda : ℂ) : Fin 2 → ℂ :=
  ![-(x + lambda), eta]

theorem tendsto_residualExplicitPlaneBranch (x eta : ℂ) :
    Tendsto (residualExplicitPlaneBranch x eta) (nhds 0)
      (nhds ![-x, eta]) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · change Tendsto (fun lambda : ℂ ↦ -(x + lambda)) (nhds 0) (nhds (-x))
    have hx : Tendsto (fun _ : ℂ ↦ x) (nhds 0) (nhds x) :=
      tendsto_const_nhds
    have hlambda : Tendsto (fun lambda : ℂ ↦ lambda) (nhds 0) (nhds 0) :=
      tendsto_id
    simpa using (hx.add hlambda).neg
  · exact tendsto_const_nhds

theorem residualExplicitPlaneBranch_eq_zero
    (k L : ℕ) (c T x eta lambda : ℂ)
    (hetaK : eta ^ k = 1) (hetaL : eta ^ L = 1) :
    residualRotationPlaneDifference k L c T x
      (lambda, residualExplicitPlaneBranch x eta lambda) = 0 := by
  funext i
  fin_cases i
  · change 1 - eta ^ k = 0
    rw [hetaK]
    ring
  · change -c * ((x + lambda) ^ 2 + T -
        ((-(x + lambda)) ^ 2 + T * eta ^ L)) = 0
    rw [hetaL]
    ring

theorem InitialCollisionCertificate.residualRotationPlaneDifference_zero
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (certificate : InitialCollisionCertificate k L N c T Psi) :
    residualRotationPlaneDifference k L c T certificate.x
      (0, ![-certificate.x, certificate.eta]) = 0 := by
  simpa [residualExplicitPlaneBranch] using
    residualExplicitPlaneBranch_eq_zero k L c T certificate.x
      certificate.eta 0 certificate.eta_pow_k certificate.eta_pow_L

/-- Near the certified collision, the first two equations define exactly
the explicit branch. -/
theorem eventually_residualRotationPlaneDifference_eq_zero_iff_explicitBranch
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (certificate : InitialCollisionCertificate k L N c T Psi) :
    ∀ᶠ s in nhds (0, ![-certificate.x, certificate.eta]),
      residualRotationPlaneDifference k L c T certificate.x s = 0 ↔
        residualExplicitPlaneBranch certificate.x certificate.eta s.1 = s.2 := by
  let Phi := residualRotationPlaneDifference k L c T certificate.x
  let base : ℂ × (Fin 2 → ℂ) :=
    (0, ![-certificate.x, certificate.eta])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base :=
    (analyticAt_residualRotationPlaneDifference
      k L c T certificate.x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq :
        Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
          residualRotationPointDerivative k L c T
            certificate.x certificate.eta := by
      have hcomposition := hPhi.comp ![-certificate.x, certificate.eta]
        ((hasStrictFDerivAt_const (𝕜 := ℂ) (0 : ℂ)
          ![-certificate.x, certificate.eta]).prodMk
            (hasStrictFDerivAt_id ![-certificate.x, certificate.eta]))
      have hinr :
          (0 : (Fin 2 → ℂ) →L[ℂ] ℂ).prod
              (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
            ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) := by
        ext v <;> rfl
      rw [hinr] at hcomposition
      exact hcomposition.hasFDerivAt.unique
        (hasStrictFDerivAt_residualRotationPlaneDifference_point
          k L c T certificate.x certificate.eta).hasFDerivAt
    rw [heq]
    simpa [InitialCollisionCertificate.residualRotationPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := certificate.residualRotationPointDerivativeEquiv))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base] using certificate.residualRotationPlaneDifference_zero
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards
      [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda ↦
        (lambda, residualExplicitPlaneBranch certificate.x
          certificate.eta lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using tendsto_id.prodMk_nhds
      (tendsto_residualExplicitPlaneBranch certificate.x certificate.eta)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = residualExplicitPlaneBranch certificate.x
        certificate.eta lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocal'
    exact hlocal'.mp <| by
      simpa [Phi] using residualExplicitPlaneBranch_eq_zero
        k L c T certificate.x certificate.eta lambda
          certificate.eta_pow_k certificate.eta_pow_L
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = residualExplicitPlaneBranch certificate.x
        certificate.eta s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst] with s hlocal' hpsi'
  rw [hlocal', hpsi']

/-- The third initial difference after the same reparametrization. -/
@[expose]
noncomputable def residualRotationThirdDifference
    {N : ℕ} (L : ℕ) (T x : ℂ) (Psi : PreparedOddFamily N)
    (s : ℂ × (Fin 2 → ℂ)) : ℂ :=
  (Psi.polynomial T).eval (x + s.1) -
    (Psi.polynomial (T * s.2 1 ^ L)).eval (s.2 0)

/-- On the explicit plane branch, the third difference is twice the
prepared odd polynomial. -/
theorem residualRotationThirdDifference_explicitBranch
    {N : ℕ} (L : ℕ) (T x eta lambda : ℂ)
    (Psi : PreparedOddFamily N) (hetaL : eta ^ L = 1) :
    residualRotationThirdDifference L T x Psi
        (lambda, residualExplicitPlaneBranch x eta lambda) =
      2 * (Psi.polynomial T).eval (x + lambda) := by
  rw [residualRotationThirdDifference]
  simp only [residualExplicitPlaneBranch, Matrix.cons_val_zero,
    Matrix.cons_val_one, hetaL, mul_one]
  rw [Psi.eval_neg]
  ring

/-- The restricted third difference has the positive root multiplicity of
the prepared polynomial. -/
theorem exists_residualRotationThirdDifference_factorization
    {N : ℕ} {L : ℕ} {T x eta : ℂ} {Psi : PreparedOddFamily N}
    (hetaL : eta ^ L = 1)
    (hp : Psi.polynomial T ≠ 0) (hx : (Psi.polynomial T).IsRoot x) :
    0 < (Psi.polynomial T).rootMultiplicity x ∧
      ∃ quotient : ℂ[X], quotient.eval x ≠ 0 ∧
        ∀ lambda : ℂ,
          residualRotationThirdDifference L T x Psi
              (lambda, residualExplicitPlaneBranch x eta lambda) =
            lambda ^ (Psi.polynomial T).rootMultiplicity x *
              quotient.eval (x + lambda) := by
  let p := Psi.polynomial T
  let m := p.rootMultiplicity x
  let baseQuotient := p /ₘ (X - C x) ^ m
  let quotient := C 2 * baseQuotient
  have hm : 0 < m := (rootMultiplicity_pos hp).2 hx
  have hdecomposition : p = (X - C x) ^ m * baseQuotient := by
    simpa [p, m, baseQuotient] using
      (pow_mul_divByMonic_rootMultiplicity_eq p x).symm
  have hbaseQuotient : baseQuotient.eval x ≠ 0 := by
    simpa [p, m, baseQuotient] using
      eval_divByMonic_pow_rootMultiplicity_ne_zero x hp
  have hquotient : quotient.eval x ≠ 0 := by
    simp only [quotient, eval_mul, eval_C]
    exact mul_ne_zero (by norm_num) hbaseQuotient
  refine ⟨hm, quotient, hquotient, ?_⟩
  intro lambda
  rw [residualRotationThirdDifference_explicitBranch L T x eta lambda
    Psi hetaL]
  have heval := congrArg (fun q : ℂ[X] ↦ q.eval (x + lambda)) hdecomposition
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at heval
  rw [heval]
  simp only [quotient, eval_mul, eval_C]
  ring

end OnLeConjecture.DTwo
