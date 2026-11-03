/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SimpleZeroPersistence
public import OnLeConjecture.DThree.ResidueRotationMultiplicity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Transversality along a residual rotation component

The first two coordinate differences have an invertible derivative in the
second source point along a rotation component. The implicit function
theorem therefore gives a local solution branch for the first two equations.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The first two `E` differences with first point `(x + lambda, 1)` and
second point `(X, Y)`. -/
@[expose]
noncomputable def eResidueRotationPlaneDifference
    (a : ℕ) (x : ℂ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![(x + s.1) ^ 3 + 3 - (s.2 0 ^ 3 + 3 * s.2 1 ^ (3 * a)),
    (x + s.1) ^ 4 + 4 * (x + s.1) -
      (s.2 0 ^ 4 + 4 * s.2 0 * s.2 1 ^ (3 * a))]

/-- The first two `H` differences with first point `(x + lambda, 1)` and
second point `(X, Y)`. -/
@[expose]
noncomputable def hResidueRotationPlaneDifference
    (a : ℕ) (x : ℂ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![(x + s.1) ^ 3 + 3 * (x + s.1) -
      (s.2 0 ^ 3 + 3 * s.2 0 * s.2 1 ^ (2 * a)),
    (x + s.1) ^ 4 + 4 * (x + s.1) ^ 2 + 2 -
      (s.2 0 ^ 4 + 4 * s.2 0 ^ 2 * s.2 1 ^ (2 * a) +
        2 * s.2 1 ^ (4 * a))]

/-- The point derivative of the `E` plane difference at `(0, (x, zeta))`. -/
@[expose]
noncomputable def eResidueRotationPointJacobian
    (a : ℕ) (x zeta : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(3 * x ^ 2), -(3 * (3 * a : ℕ) * zeta ^ (3 * a - 1));
    -(4 * x ^ 3 + 4 * zeta ^ (3 * a)),
      -(4 * x * (3 * a : ℕ) * zeta ^ (3 * a - 1))]

/-- The point derivative of the `H` plane difference at `(0, (x, zeta))`. -/
@[expose]
noncomputable def hResidueRotationPointJacobian
    (a : ℕ) (x zeta : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(3 * x ^ 2 + 3 * zeta ^ (2 * a)),
      -(3 * x * (2 * a : ℕ) * zeta ^ (2 * a - 1));
    -(4 * x ^ 3 + 8 * x * zeta ^ (2 * a)),
      -(4 * x ^ 2 * (2 * a : ℕ) * zeta ^ (2 * a - 1) +
        2 * (4 * a : ℕ) * zeta ^ (4 * a - 1))]

/-- The continuous linear map represented by the `E` point Jacobian. -/
@[expose]
noncomputable def eResidueRotationPointDerivative
    (a : ℕ) (x zeta : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eResidueRotationPointJacobian a x zeta)).toContinuousLinearMap

/-- The continuous linear map represented by the `H` point Jacobian. -/
@[expose]
noncomputable def hResidueRotationPointDerivative
    (a : ℕ) (x zeta : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (hResidueRotationPointJacobian a x zeta)).toContinuousLinearMap

theorem analyticAt_eResidueRotationPlaneDifference
    (a : ℕ) (x : ℂ) (s : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eResidueRotationPlaneDifference a x) s := by
  have hlambda : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.1) s :=
    analyticAt_fst
  have hzero : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2 0) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt s.2).comp
        (analyticAt_snd : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2) s)
  have hone : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2 1) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt s.2).comp
        (analyticAt_snd : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2) s)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun t =>
      (x + t.1) ^ 3 + 3 - (t.2 0 ^ 3 + 3 * t.2 1 ^ (3 * a))) s
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ (fun t =>
      (x + t.1) ^ 4 + 4 * (x + t.1) -
        (t.2 0 ^ 4 + 4 * t.2 0 * t.2 1 ^ (3 * a))) s
    fun_prop (disch := assumption)

theorem analyticAt_hResidueRotationPlaneDifference
    (a : ℕ) (x : ℂ) (s : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (hResidueRotationPlaneDifference a x) s := by
  have hlambda : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.1) s :=
    analyticAt_fst
  have hzero : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2 0) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt s.2).comp
        (analyticAt_snd : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2) s)
  have hone : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2 1) s := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt s.2).comp
        (analyticAt_snd : AnalyticAt ℂ (fun s : ℂ × (Fin 2 → ℂ) => s.2) s)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun t =>
      (x + t.1) ^ 3 + 3 * (x + t.1) -
        (t.2 0 ^ 3 + 3 * t.2 0 * t.2 1 ^ (2 * a))) s
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ (fun t =>
      (x + t.1) ^ 4 + 4 * (x + t.1) ^ 2 + 2 -
        (t.2 0 ^ 4 + 4 * t.2 0 ^ 2 * t.2 1 ^ (2 * a) +
          2 * t.2 1 ^ (4 * a))) s
    fun_prop (disch := assumption)

theorem hasStrictFDerivAt_eResidueRotationPlaneDifference_point
    (a : ℕ) (x zeta : ℂ) :
    HasStrictFDerivAt (fun q => eResidueRotationPlaneDifference a x (0, q))
      (eResidueRotationPointDerivative a x zeta) ![x, zeta] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eResidueRotationPlaneDifference]
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) (x ^ 3 + 3) ![x, zeta]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).pow 3).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, zeta]).pow
            (3 * a)).const_mul (3 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [eResidueRotationPointDerivative, eResidueRotationPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) (x ^ 4 + 4 * x) ![x, zeta]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).pow 4).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, zeta]).pow
              (3 * a))).const_mul (4 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [eResidueRotationPointDerivative, eResidueRotationPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem hasStrictFDerivAt_hResidueRotationPlaneDifference_point
    (a : ℕ) (x zeta : ℂ) :
    HasStrictFDerivAt (fun q => hResidueRotationPlaneDifference a x (0, q))
      (hResidueRotationPointDerivative a x zeta) ![x, zeta] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [hResidueRotationPlaneDifference]
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) (x ^ 3 + 3 * x) ![x, zeta]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).pow 3).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, zeta]).pow
              (2 * a))).const_mul (3 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [hResidueRotationPointDerivative, hResidueRotationPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) (x ^ 4 + 4 * x ^ 2 + 2) ![x, zeta]).sub
        ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).pow 4).add
          ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, zeta]).pow 2).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, zeta]).pow
              (2 * a))).const_mul (4 : ℂ))).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, zeta]).pow
            (4 * a)).const_mul (2 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [hResidueRotationPointDerivative, hResidueRotationPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring

/-- The determinant of the `E` point derivative along a rotation component. -/
theorem det_eResidueRotationPointJacobian
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ a = 1) :
    Matrix.det (eResidueRotationPointJacobian a x zeta) =
      -(36 * (a : ℂ) * zeta ^ (3 * a - 1)) := by
  have hzetaThreeA : zeta ^ (3 * a) = 1 := by
    calc
      zeta ^ (3 * a) = zeta ^ (a * 3) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  simp [eResidueRotationPointJacobian, Matrix.det_fin_two, hzetaThreeA]
  ring

/-- The determinant of the `H` point derivative along a rotation component. -/
theorem det_hResidueRotationPointJacobian
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    Matrix.det (hResidueRotationPointJacobian a x zeta) =
      24 * (a : ℂ) * zeta ^ (2 * a - 1) := by
  have hzetaTwoA : zeta ^ (2 * a) = 1 := by
    calc
      zeta ^ (2 * a) = zeta ^ (a * 2) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  have hexponent : 4 * a - 1 = (2 * a - 1) + 2 * a := by omega
  have hzetaShift : zeta ^ (4 * a - 1) = zeta ^ (2 * a - 1) := by
    rw [hexponent, pow_add, hzetaTwoA, mul_one]
  simp [hResidueRotationPointJacobian, Matrix.det_fin_two,
    hzetaTwoA, hzetaShift]
  ring

theorem det_eResidueRotationPointDerivative
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ a = 1) :
    (eResidueRotationPointDerivative a x zeta).det =
      -(36 * (a : ℂ) * zeta ^ (3 * a - 1)) := by
  simpa [eResidueRotationPointDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using
    det_eResidueRotationPointJacobian a x zeta hzeta

theorem det_hResidueRotationPointDerivative
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    (hResidueRotationPointDerivative a x zeta).det =
      24 * (a : ℂ) * zeta ^ (2 * a - 1) := by
  simpa [hResidueRotationPointDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using
    det_hResidueRotationPointJacobian a x zeta ha hzeta

theorem zeta_ne_zero_of_pow_eq_one
    {a : ℕ} {zeta : ℂ} (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    zeta ≠ 0 := by
  intro hzetaZero
  rw [hzetaZero, zero_pow ha.ne'] at hzeta
  exact zero_ne_one hzeta

/-- The `E` point derivative is invertible along every rotation
component. -/
@[expose]
noncomputable def eResidueRotationPointDerivativeEquiv
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (eResidueRotationPointDerivative a x zeta).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_eResidueRotationPointDerivative a x zeta hzeta]
    exact neg_ne_zero.mpr <| mul_ne_zero
      (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha.ne'))
      (pow_ne_zero _ (zeta_ne_zero_of_pow_eq_one ha hzeta))

/-- The `H` point derivative is invertible along every rotation
component. -/
@[expose]
noncomputable def hResidueRotationPointDerivativeEquiv
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (hResidueRotationPointDerivative a x zeta).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_hResidueRotationPointDerivative a x zeta ha hzeta]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha.ne'))
      (pow_ne_zero _ (zeta_ne_zero_of_pow_eq_one ha hzeta))

theorem fderiv_eResidueRotationPlaneDifference_point
    (a : ℕ) (x zeta : ℂ) :
    fderiv ℂ (eResidueRotationPlaneDifference a x) (0, ![x, zeta]) ∘L
        ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
      eResidueRotationPointDerivative a x zeta := by
  have hjoint :=
    (analyticAt_eResidueRotationPlaneDifference a x (0, ![x, zeta])).hasStrictFDerivAt
  have hcomposition := hjoint.comp ![x, zeta]
    ((hasStrictFDerivAt_const (𝕜 := ℂ) (0 : ℂ) ![x, zeta]).prodMk
      (hasStrictFDerivAt_id ![x, zeta]))
  have hinr :
      (0 : (Fin 2 → ℂ) →L[ℂ] ℂ).prod
          (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
        ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) := by
    ext q <;> rfl
  rw [hinr] at hcomposition
  exact hcomposition.hasFDerivAt.unique
    (hasStrictFDerivAt_eResidueRotationPlaneDifference_point a x zeta).hasFDerivAt

theorem fderiv_hResidueRotationPlaneDifference_point
    (a : ℕ) (x zeta : ℂ) :
    fderiv ℂ (hResidueRotationPlaneDifference a x) (0, ![x, zeta]) ∘L
        ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
      hResidueRotationPointDerivative a x zeta := by
  have hjoint :=
    (analyticAt_hResidueRotationPlaneDifference a x (0, ![x, zeta])).hasStrictFDerivAt
  have hcomposition := hjoint.comp ![x, zeta]
    ((hasStrictFDerivAt_const (𝕜 := ℂ) (0 : ℂ) ![x, zeta]).prodMk
      (hasStrictFDerivAt_id ![x, zeta]))
  have hinr :
      (0 : (Fin 2 → ℂ) →L[ℂ] ℂ).prod
          (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)) =
        ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) := by
    ext q <;> rfl
  rw [hinr] at hcomposition
  exact hcomposition.hasFDerivAt.unique
    (hasStrictFDerivAt_hResidueRotationPlaneDifference_point a x zeta).hasFDerivAt

/-- The first two `E` fibre equations have a local solution branch
through a rotation pair. -/
theorem exists_eResidueRotationPlaneBranch
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    ∃ branch : ℂ → (Fin 2 → ℂ),
      branch 0 = ![x, zeta] ∧
      Tendsto branch (nhds 0) (nhds ![x, zeta]) ∧
      ∀ᶠ lambda in nhds 0,
        eResidueRotationPlaneDifference a x (lambda, branch lambda) = 0 := by
  have hzetaThreeA : zeta ^ (3 * a) = 1 := by
    calc
      zeta ^ (3 * a) = zeta ^ (a * 3) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  have hzero :
      eResidueRotationPlaneDifference a x (0, ![x, zeta]) = 0 := by
    funext i
    fin_cases i <;>
      simp [eResidueRotationPlaneDifference, hzetaThreeA]
  exact OnLeConjecture.Analytic.exists_simpleZeroBranch_of_pointDerivativeEquiv
    (eResidueRotationPlaneDifference a x) ![x, zeta]
    (fderiv ℂ (eResidueRotationPlaneDifference a x) (0, ![x, zeta]))
    (eResidueRotationPointDerivativeEquiv a x zeta ha hzeta)
    hzero
    (analyticAt_eResidueRotationPlaneDifference a x (0, ![x, zeta])).hasStrictFDerivAt
    (by
      simpa [eResidueRotationPointDerivativeEquiv] using
        fderiv_eResidueRotationPlaneDifference_point a x zeta)

/-- The first two `H` fibre equations have a local solution branch
through a rotation pair. -/
theorem exists_hResidueRotationPlaneBranch
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    ∃ branch : ℂ → (Fin 2 → ℂ),
      branch 0 = ![x, zeta] ∧
      Tendsto branch (nhds 0) (nhds ![x, zeta]) ∧
      ∀ᶠ lambda in nhds 0,
        hResidueRotationPlaneDifference a x (lambda, branch lambda) = 0 := by
  have hzetaTwoA : zeta ^ (2 * a) = 1 := by
    calc
      zeta ^ (2 * a) = zeta ^ (a * 2) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  have hzetaFourA : zeta ^ (4 * a) = 1 := by
    calc
      zeta ^ (4 * a) = zeta ^ (a * 4) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 4 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  have hzero :
      hResidueRotationPlaneDifference a x (0, ![x, zeta]) = 0 := by
    funext i
    fin_cases i <;>
      simp [hResidueRotationPlaneDifference, hzetaTwoA, hzetaFourA]
  exact OnLeConjecture.Analytic.exists_simpleZeroBranch_of_pointDerivativeEquiv
    (hResidueRotationPlaneDifference a x) ![x, zeta]
    (fderiv ℂ (hResidueRotationPlaneDifference a x) (0, ![x, zeta]))
    (hResidueRotationPointDerivativeEquiv a x zeta ha hzeta)
    hzero
    (analyticAt_hResidueRotationPlaneDifference a x (0, ![x, zeta])).hasStrictFDerivAt
    (by
      simpa [hResidueRotationPointDerivativeEquiv] using
        fderiv_hResidueRotationPlaneDifference_point a x zeta)

/-- A rotation branch remains off the diagonal when its rotation is
nontrivial. -/
theorem eventually_rotationPlaneBranch_second_ne_one
    {branch : ℂ → (Fin 2 → ℂ)} {x zeta : ℂ}
    (hbranch : Tendsto branch (nhds 0) (nhds ![x, zeta]))
    (hzeta : zeta ≠ 1) :
    ∀ᶠ lambda in nhds 0, branch lambda 1 ≠ 1 := by
  have htendsto : Tendsto (fun lambda => branch lambda 1) (nhds 0) (nhds zeta) := by
    simpa using (tendsto_pi_nhds.mp hbranch 1)
  exact htendsto.eventually_ne hzeta

/-- The explicit rotation branch through `(x, zeta)`. -/
@[expose]
noncomputable def explicitRotationPlaneBranch
    (x zeta lambda : ℂ) : Fin 2 → ℂ :=
  ![x + lambda, zeta]

theorem tendsto_explicitRotationPlaneBranch (x zeta : ℂ) :
    Tendsto (explicitRotationPlaneBranch x zeta) (nhds 0)
      (nhds ![x, zeta]) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · change Tendsto (fun lambda : ℂ => x + lambda) (nhds 0) (nhds x)
    have hxconst : Tendsto (fun _ : ℂ => x) (nhds 0) (nhds x) :=
      tendsto_const_nhds
    have hid : Tendsto (fun lambda : ℂ => lambda) (nhds 0) (nhds 0) :=
      tendsto_id
    simpa only [add_zero] using hxconst.add hid
  · change Tendsto (fun _ : ℂ => zeta) (nhds 0) (nhds zeta)
    exact tendsto_const_nhds

/-- The explicit rotation branch solves the first two `E` fibre equations. -/
theorem e_explicitRotationPlaneBranch_eq_zero
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ a = 1) (lambda : ℂ) :
    eResidueRotationPlaneDifference a x
      (lambda, explicitRotationPlaneBranch x zeta lambda) = 0 := by
  have hzetaThreeA : zeta ^ (3 * a) = 1 := by
    calc
      zeta ^ (3 * a) = zeta ^ (a * 3) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  funext i
  fin_cases i <;>
    simp [eResidueRotationPlaneDifference, explicitRotationPlaneBranch,
      hzetaThreeA]

/-- The explicit rotation branch solves the first two `H` fibre equations. -/
theorem h_explicitRotationPlaneBranch_eq_zero
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ a = 1) (lambda : ℂ) :
    hResidueRotationPlaneDifference a x
      (lambda, explicitRotationPlaneBranch x zeta lambda) = 0 := by
  have hzetaTwoA : zeta ^ (2 * a) = 1 := by
    calc
      zeta ^ (2 * a) = zeta ^ (a * 2) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  have hzetaFourA : zeta ^ (4 * a) = 1 := by
    calc
      zeta ^ (4 * a) = zeta ^ (a * 4) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 4 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, one_pow]
  funext i
  fin_cases i <;>
    simp [hResidueRotationPlaneDifference, explicitRotationPlaneBranch,
      hzetaTwoA, hzetaFourA]

/-- Near a rotation pair, the `E` plane fibre consists exactly of the
explicit rotation branch. -/
theorem eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      eResidueRotationPlaneDifference a x s = 0 ↔
        explicitRotationPlaneBranch x zeta s.1 = s.2 := by
  let Phi := eResidueRotationPlaneDifference a x
  let base : ℂ × (Fin 2 → ℂ) := (0, ![x, zeta])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base := by
    exact (analyticAt_eResidueRotationPlaneDifference a x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq : Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
        eResidueRotationPointDerivative a x zeta := by
      simpa [Phi, Phi', base] using
        fderiv_eResidueRotationPlaneDifference_point a x zeta
    rw [heq]
    simpa [eResidueRotationPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := eResidueRotationPointDerivativeEquiv a x zeta ha hzeta))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base, explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero a x zeta hzeta 0
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda => (lambda, explicitRotationPlaneBranch x zeta lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using
      tendsto_id.prodMk_nhds (tendsto_explicitRotationPlaneBranch x zeta)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = explicitRotationPlaneBranch x zeta lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocal'
    exact hlocal'.mp <| by
      simpa [Phi] using
        e_explicitRotationPlaneBranch_eq_zero a x zeta hzeta lambda
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) => s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) => s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = explicitRotationPlaneBranch x zeta s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst] with s hlocal' hpsi'
  rw [hlocal', hpsi']

/-- Near a rotation pair, the `H` plane fibre consists exactly of the
explicit rotation branch. -/
theorem eventually_hResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a) (hzeta : zeta ^ a = 1) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      hResidueRotationPlaneDifference a x s = 0 ↔
        explicitRotationPlaneBranch x zeta s.1 = s.2 := by
  let Phi := hResidueRotationPlaneDifference a x
  let base : ℂ × (Fin 2 → ℂ) := (0, ![x, zeta])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base := by
    exact (analyticAt_hResidueRotationPlaneDifference a x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq : Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
        hResidueRotationPointDerivative a x zeta := by
      simpa [Phi, Phi', base] using
        fderiv_hResidueRotationPlaneDifference_point a x zeta
    rw [heq]
    simpa [hResidueRotationPointDerivativeEquiv] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := hResidueRotationPointDerivativeEquiv a x zeta ha hzeta))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base, explicitRotationPlaneBranch] using
      h_explicitRotationPlaneBranch_eq_zero a x zeta hzeta 0
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda => (lambda, explicitRotationPlaneBranch x zeta lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using
      tendsto_id.prodMk_nhds (tendsto_explicitRotationPlaneBranch x zeta)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = explicitRotationPlaneBranch x zeta lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocal'
    exact hlocal'.mp <| by
      simpa [Phi] using
        h_explicitRotationPlaneBranch_eq_zero a x zeta hzeta lambda
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) => s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) => s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = explicitRotationPlaneBranch x zeta s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst] with s hlocal' hpsi'
  rw [hlocal', hpsi']

/-- The third difference on the explicit rotation branch is the restricted
polynomial difference. -/
theorem explicitRotationThirdDifference_eq
    (r : ℕ) (p : ℂ[X]) (x zeta lambda : ℂ) :
    p.eval (x + lambda) -
        (explicitRotationPlaneBranch x zeta lambda 1) ^ r *
          p.eval (explicitRotationPlaneBranch x zeta lambda 0) =
      (rotationRestrictedDifference zeta r p).eval (x + lambda) := by
  simp [explicitRotationPlaneBranch, rotationRestrictedDifference_eq]
  ring

/-- The third coordinate difference with first point `(x + lambda, 1)`. -/
@[expose]
noncomputable def residueRotationThirdDifference
    (r : ℕ) (p : ℂ[X]) (x : ℂ)
    (s : ℂ × (Fin 2 → ℂ)) : ℂ :=
  p.eval (x + s.1) - s.2 1 ^ r * p.eval (s.2 0)

/-- The third difference on the explicit branch has the same positive local
multiplicity as the dehomogenized third form. -/
theorem exists_explicitRotationThirdDifference_factorization
    {r : ℕ} {p : ℂ[X]} {x zeta : ℂ}
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    0 < p.rootMultiplicity x ∧
      ∃ quotient : ℂ[X], quotient.eval x ≠ 0 ∧
        ∀ lambda : ℂ,
          p.eval (x + lambda) -
              (explicitRotationPlaneBranch x zeta lambda 1) ^ r *
                p.eval (explicitRotationPlaneBranch x zeta lambda 0) =
            lambda ^ p.rootMultiplicity x * quotient.eval (x + lambda) := by
  obtain ⟨hpositive, quotient, hfactorization, hquotient⟩ :=
    exists_rotationRestrictedDifference_factorization_with_sourceMultiplicity
      hzeta hp hx
  refine ⟨hpositive, quotient, hquotient, ?_⟩
  intro lambda
  rw [explicitRotationThirdDifference_eq, hfactorization, eval_mul, eval_pow]
  simp

/-- An isolated root of the third form makes the full rotation fibre system
isolated once the plane fibre is the explicit rotation branch. -/
theorem eventually_rotationPlaneAndThird_eq_base
    (planeDifference : ℂ × (Fin 2 → ℂ) → (Fin 2 → ℂ))
    {r : ℕ} {p : ℂ[X]} {x zeta : ℂ}
    (hplane : ∀ᶠ s in nhds (0, ![x, zeta]),
      planeDifference s = 0 ↔
        explicitRotationPlaneBranch x zeta s.1 = s.2)
    (hzeta : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      (planeDifference s = 0 ∧
        residueRotationThirdDifference r p x s = 0) ↔
      s = (0, ![x, zeta]) := by
  obtain ⟨hpositive, quotient, hquotient, hfactorization⟩ :=
    exists_explicitRotationThirdDifference_factorization hzeta hp hx
  have hcontinuous : ContinuousAt
      (fun lambda : ℂ => quotient.eval (x + lambda)) 0 := by
    have heval : Continuous (fun z : ℂ => quotient.eval z) := by
      change Continuous (fun z : ℂ => quotient.eval₂ (RingHom.id ℂ) z)
      exact quotient.continuous_eval₂ (RingHom.id ℂ)
    exact heval.continuousAt.comp (by fun_prop)
  have hquotientEventually : ∀ᶠ lambda in nhds 0,
      quotient.eval (x + lambda) ≠ 0 := by
    exact hcontinuous.eventually_ne <| by simpa using hquotient
  have hfst : Tendsto
      (fun s : ℂ × (Fin 2 → ℂ) => s.1)
      (nhds (0, ![x, zeta])) (nhds 0) :=
    continuousAt_fst.tendsto
  have hquotientAtFirst : ∀ᶠ s in nhds (0, ![x, zeta]),
      quotient.eval (x + s.1) ≠ 0 :=
    hfst.eventually hquotientEventually
  filter_upwards [hplane, hquotientAtFirst] with s hplane' hquotient'
  constructor
  · rintro ⟨hplaneZero, hthirdZero⟩
    have hbranch := hplane'.mp hplaneZero
    have hthirdExplicit :
        p.eval (x + s.1) -
            (explicitRotationPlaneBranch x zeta s.1 1) ^ r *
              p.eval (explicitRotationPlaneBranch x zeta s.1 0) = 0 := by
      simpa [residueRotationThirdDifference, hbranch] using hthirdZero
    rw [hfactorization s.1] at hthirdExplicit
    have hlambda : s.1 = 0 := by
      rcases mul_eq_zero.mp hthirdExplicit with hpower | hquotientZero
      · exact (pow_eq_zero_iff hpositive.ne').mp hpower
      · exact False.elim (hquotient' hquotientZero)
    apply Prod.ext
    · exact hlambda
    · rw [← hbranch, hlambda]
      simp [explicitRotationPlaneBranch]
  · intro hs
    subst s
    constructor
    · apply hplane'.mpr
      simp [explicitRotationPlaneBranch]
    · have hxeval : p.eval x = 0 := hx
      simp [residueRotationThirdDifference, hxeval]

/-- The full `E` rotation fibre system has an isolated zero at the chosen
rotation pair. -/
theorem eventually_eResidueRotation_full_eq_base
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      (eResidueRotationPlaneDifference a x s = 0 ∧
        residueRotationThirdDifference r p x s = 0) ↔
      s = (0, ![x, zeta]) :=
  eventually_rotationPlaneAndThird_eq_base
    (eResidueRotationPlaneDifference a x)
    (eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA)
    hzetaR hp hx

/-- The full `H` rotation fibre system has an isolated zero at the chosen
rotation pair. -/
theorem eventually_hResidueRotation_full_eq_base
    (a r : ℕ) (p : ℂ[X]) (x zeta : ℂ)
    (ha : 0 < a) (hzetaA : zeta ^ a = 1)
    (hzetaR : zeta ^ r ≠ 1) (hp : p ≠ 0) (hx : p.IsRoot x) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      (hResidueRotationPlaneDifference a x s = 0 ∧
        residueRotationThirdDifference r p x s = 0) ↔
      s = (0, ![x, zeta]) :=
  eventually_rotationPlaneAndThird_eq_base
    (hResidueRotationPlaneDifference a x)
    (eventually_hResidueRotationPlaneDifference_eq_zero_iff_explicitBranch
      a x zeta ha hzetaA)
    hzetaR hp hx

end OnLeConjecture.DThree
