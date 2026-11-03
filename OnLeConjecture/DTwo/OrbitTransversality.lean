/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitFiniteChart
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Transversality of the quadratic orbit collision

At least one of the two second source coordinates is nonzero.  The first two
orbit equations can therefore be solved for the source point containing that
coordinate.  This file records the two reparametrizations and computes the
two point derivatives.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.DThree

/-- A pair represented by its two coordinates. -/
@[expose]
def orbitPointOfFinTwo (q : Fin 2 → ℂ) : ℂ × ℂ :=
  (q 0, q 1)

/-- The two coordinates of a source point as a function on `Fin 2`. -/
@[expose]
def orbitFinTwoOfPoint (p : ℂ × ℂ) : Fin 2 → ℂ :=
  ![p.1, p.2]

/-- The first two orbit coordinates of a source point. -/
@[expose]
def orbitPlaneMap (q : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![orbitPhi (q 0) (q 1), orbitPsi (q 0) (q 1)]

/-- The derivative of the first two orbit coordinates at `(x, y)`. -/
@[expose]
noncomputable def orbitPointJacobian
    (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2 * x, -2 * y;
    6 * x ^ 2 - 3 * y ^ 2, -6 * x * y]

/-- The continuous linear map represented by the orbit point Jacobian. -/
@[expose]
noncomputable def orbitPointDerivative
    (x y : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (orbitPointJacobian x y)).toContinuousLinearMap

/-- The derivative when the variable source point is subtracted. -/
@[expose]
noncomputable def orbitNegativePointJacobian
    (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-2 * x, 2 * y;
    -(6 * x ^ 2 - 3 * y ^ 2), 6 * x * y]

/-- The continuous linear derivative when the variable point is
subtracted. -/
@[expose]
noncomputable def orbitNegativePointDerivative
    (x y : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (orbitNegativePointJacobian x y)).toContinuousLinearMap

theorem orbitPointDerivative_apply (x y : ℂ) (v : Fin 2 → ℂ) :
    orbitPointDerivative x y v =
      ![2 * x * v 0 - 2 * y * v 1,
        (6 * x ^ 2 - 3 * y ^ 2) * v 0 - 6 * x * y * v 1] := by
  funext i
  fin_cases i <;>
    simp [orbitPointDerivative, orbitPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem orbitNegativePointDerivative_eq_neg (x y : ℂ) :
    orbitNegativePointDerivative x y = -orbitPointDerivative x y := by
  ext v i
  fin_cases i <;>
    simp [orbitNegativePointDerivative, orbitNegativePointJacobian,
      orbitPointDerivative, orbitPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem analyticAt_orbitPlaneMap (q : Fin 2 → ℂ) :
    AnalyticAt ℂ orbitPlaneMap q := by
  rw [analyticAt_pi_iff]
  have hcoordinate (i : Fin 2) :
      AnalyticAt ℂ (fun p : Fin 2 → ℂ ↦ p i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun p : Fin 2 → ℂ ↦
      orbitPhi (p 0) (p 1)) q
    simp only [orbitPhi]
    exact ((hcoordinate 0).pow 2).sub ((hcoordinate 1).pow 2)
  · change AnalyticAt ℂ (fun p : Fin 2 → ℂ ↦
      orbitPsi (p 0) (p 1)) q
    simp only [orbitPsi]
    exact (analyticAt_const.mul ((hcoordinate 0).pow 3)).sub
      ((analyticAt_const.mul (hcoordinate 0)).mul ((hcoordinate 1).pow 2))

theorem hasStrictFDerivAt_orbitPlaneMap (x y : ℂ) :
    HasStrictFDerivAt orbitPlaneMap
      (orbitPointDerivative x y) ![x, y] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [orbitPlaneMap, orbitPhi, orbitPsi]
  · convert
      ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, y]).pow 2).sub
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, y]).pow 2)
      using 1
    · funext q
      simp
    · ext v
      simp [orbitPointDerivative_apply]
  · convert
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2)
          ![x, y]).pow 3).const_mul 2).sub
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2)
          ![x, y]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2)
              ![x, y]).pow 2) |>.const_mul 3)
      using 1
    · funext q
      simp
      ring
    · ext v
      simp [orbitPointDerivative_apply]
      ring

theorem det_orbitPointJacobian (x y : ℂ) :
    Matrix.det (orbitPointJacobian x y) = -6 * y ^ 3 := by
  simp [orbitPointJacobian, Matrix.det_fin_two]
  ring

theorem det_orbitPointDerivative (x y : ℂ) :
    (orbitPointDerivative x y).det = -6 * y ^ 3 := by
  simpa [orbitPointDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using det_orbitPointJacobian x y

theorem det_orbitNegativePointDerivative (x y : ℂ) :
    (orbitNegativePointDerivative x y).det = -6 * y ^ 3 := by
  simp [orbitNegativePointDerivative, orbitNegativePointJacobian,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two]
  ring

/-- An invertible orbit point derivative at a point with nonzero second
coordinate. -/
@[expose]
noncomputable def orbitPointDerivativeEquiv
    (x y : ℂ) (hy : y ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (orbitPointDerivative x y).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_orbitPointDerivative]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)

/-- An invertible negative orbit point derivative at a point with nonzero
second coordinate. -/
@[expose]
noncomputable def orbitNegativePointDerivativeEquiv
    (x y : ℂ) (hy : y ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (orbitNegativePointDerivative x y).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_orbitNegativePointDerivative]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)

/-- The varying second point chart. -/
@[expose]
noncomputable def orbitSecondVariablePair
    (delta z : ℂ) (q : Fin 2 → ℂ) : (ℂ × ℂ) × (ℂ × ℂ) :=
  (orbitFiniteChartFirstPoint delta z, orbitPointOfFinTwo q)

/-- The varying first point chart. -/
@[expose]
noncomputable def orbitFirstVariablePair
    (delta z : ℂ) (q : Fin 2 → ℂ) : (ℂ × ℂ) × (ℂ × ℂ) :=
  (orbitPointOfFinTwo q, orbitFiniteChartSecondPoint delta z)

/-- The special fibre plane equations when the second source point is
variable. -/
@[expose]
noncomputable def orbitSecondVariablePlaneDifference
    (delta z : ℂ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  orbitPlaneMap
      (orbitFinTwoOfPoint (orbitFiniteChartFirstPoint delta (z + s.1))) -
    orbitPlaneMap s.2

/-- The special fibre plane equations when the first source point is
variable. -/
@[expose]
noncomputable def orbitFirstVariablePlaneDifference
    (delta z : ℂ) (s : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  orbitPlaneMap s.2 -
    orbitPlaneMap
      (orbitFinTwoOfPoint (orbitFiniteChartSecondPoint delta (z + s.1)))

/-- The explicit branch of the special fibre in the varying second point
chart. -/
@[expose]
noncomputable def orbitSecondVariableExplicitBranch
    (delta z lambda : ℂ) : Fin 2 → ℂ :=
  orbitFinTwoOfPoint (orbitFiniteChartSecondPoint delta (z + lambda))

/-- The explicit branch of the special fibre in the varying first point
chart. -/
@[expose]
noncomputable def orbitFirstVariableExplicitBranch
    (delta z lambda : ℂ) : Fin 2 → ℂ :=
  orbitFinTwoOfPoint (orbitFiniteChartFirstPoint delta (z + lambda))

theorem analyticAt_orbitSecondVariableExplicitBranch
    (delta z : ℂ) :
    AnalyticAt ℂ (orbitSecondVariableExplicitBranch delta z) 0 := by
  have hpoint : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        orbitFiniteChartSecondPoint delta (z + lambda)) 0 := by
    simp only [orbitFiniteChartSecondPoint, orbitConicT_eval,
      orbitConicZeta_eval, orbitConicRhoValue_eq,
      orbitConicAlphaValue_eq, orbitConicBetaValue_eq]
    fun_prop
  have houter : AnalyticAt ℂ
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
      (orbitFiniteChartSecondPoint delta z) :=
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap
      |>.analyticAt _
  have hvalue : orbitFiniteChartSecondPoint delta (z + 0) =
      orbitFiniteChartSecondPoint delta z := by simp
  have hlinear := houter.comp_of_eq hpoint hvalue
  have heq :
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm ∘
        fun lambda : ℂ ↦ orbitFiniteChartSecondPoint delta (z + lambda)) =
        orbitSecondVariableExplicitBranch delta z := by
    funext lambda
    apply (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).injective
    simp [orbitSecondVariableExplicitBranch, orbitFinTwoOfPoint]
  rw [← heq]
  exact hlinear

theorem analyticAt_orbitFirstVariableExplicitBranch
    (delta z : ℂ) :
    AnalyticAt ℂ (orbitFirstVariableExplicitBranch delta z) 0 := by
  have hpoint : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        orbitFiniteChartFirstPoint delta (z + lambda)) 0 := by
    simp only [orbitFiniteChartFirstPoint, orbitConicS_eval,
      orbitConicLambda_eval, orbitConicRhoValue_eq,
      orbitConicAlphaValue_eq, orbitConicBetaValue_eq]
    fun_prop
  have houter : AnalyticAt ℂ
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
      (orbitFiniteChartFirstPoint delta z) :=
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.toContinuousLinearMap
      |>.analyticAt _
  have hvalue : orbitFiniteChartFirstPoint delta (z + 0) =
      orbitFiniteChartFirstPoint delta z := by simp
  have hlinear := houter.comp_of_eq hpoint hvalue
  have heq :
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm ∘
        fun lambda : ℂ ↦ orbitFiniteChartFirstPoint delta (z + lambda)) =
        orbitFirstVariableExplicitBranch delta z := by
    funext lambda
    apply (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).injective
    simp [orbitFirstVariableExplicitBranch, orbitFinTwoOfPoint]
  rw [← heq]
  exact hlinear

theorem hasStrictFDerivAt_orbitSecondVariablePlaneDifference_point
    (delta z : ℂ) :
    HasStrictFDerivAt
      (fun q ↦ orbitSecondVariablePlaneDifference delta z (0, q))
      (orbitNegativePointDerivative
        (orbitFiniteChartSecondPoint delta z).1
        (orbitFiniteChartSecondPoint delta z).2)
      (orbitSecondVariableExplicitBranch delta z 0) := by
  let fixed := orbitPlaneMap
    (orbitFinTwoOfPoint (orbitFiniteChartFirstPoint delta z))
  have hconst : HasStrictFDerivAt (fun _ : Fin 2 → ℂ ↦ fixed)
      (0 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
      (orbitSecondVariableExplicitBranch delta z 0) :=
    hasStrictFDerivAt_const _ _
  have hvariable := hasStrictFDerivAt_orbitPlaneMap
    (orbitFiniteChartSecondPoint delta z).1
    (orbitFiniteChartSecondPoint delta z).2
  have hbase :
      ![(orbitFiniteChartSecondPoint delta z).1,
        (orbitFiniteChartSecondPoint delta z).2] =
        orbitSecondVariableExplicitBranch delta z 0 := by
    funext i
    fin_cases i <;>
      simp [orbitSecondVariableExplicitBranch, orbitFinTwoOfPoint]
  rw [hbase] at hvariable
  have hfunction :
      (fun q ↦ orbitSecondVariablePlaneDifference delta z (0, q)) =
        (fun _ : Fin 2 → ℂ ↦ fixed) - orbitPlaneMap := by
    funext q
    simp [fixed, orbitSecondVariablePlaneDifference]
  rw [hfunction, orbitNegativePointDerivative_eq_neg]
  simpa only [zero_sub] using hconst.sub hvariable

theorem hasStrictFDerivAt_orbitFirstVariablePlaneDifference_point
    (delta z : ℂ) :
    HasStrictFDerivAt
      (fun q ↦ orbitFirstVariablePlaneDifference delta z (0, q))
      (orbitPointDerivative
        (orbitFiniteChartFirstPoint delta z).1
        (orbitFiniteChartFirstPoint delta z).2)
      (orbitFirstVariableExplicitBranch delta z 0) := by
  let fixed := orbitPlaneMap
    (orbitFinTwoOfPoint (orbitFiniteChartSecondPoint delta z))
  have hconst : HasStrictFDerivAt (fun _ : Fin 2 → ℂ ↦ fixed)
      (0 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ))
      (orbitFirstVariableExplicitBranch delta z 0) :=
    hasStrictFDerivAt_const _ _
  have hvariable := hasStrictFDerivAt_orbitPlaneMap
    (orbitFiniteChartFirstPoint delta z).1
    (orbitFiniteChartFirstPoint delta z).2
  have hbase :
      ![(orbitFiniteChartFirstPoint delta z).1,
        (orbitFiniteChartFirstPoint delta z).2] =
        orbitFirstVariableExplicitBranch delta z 0 := by
    funext i
    fin_cases i <;>
      simp [orbitFirstVariableExplicitBranch, orbitFinTwoOfPoint]
  rw [hbase] at hvariable
  have hfunction :
      (fun q ↦ orbitFirstVariablePlaneDifference delta z (0, q)) =
        orbitPlaneMap - (fun _ : Fin 2 → ℂ ↦ fixed) := by
    funext q
    simp [fixed, orbitFirstVariablePlaneDifference]
  rw [hfunction]
  simpa only [sub_zero] using hvariable.sub hconst

theorem orbitSecondVariablePlaneDifference_explicitBranch_zero
    {delta : ℂ} (hdelta : delta ^ 2 = 3) (R : OrbitSourceForm)
    (z lambda : ℂ) :
    orbitSecondVariablePlaneDifference delta z
      (lambda, orbitSecondVariableExplicitBranch delta z lambda) = 0 := by
  have hpair := orbitPairInitialDifference_finiteChart hdelta R (z + lambda)
  funext i
  fin_cases i
  · simpa [orbitSecondVariablePlaneDifference,
      orbitSecondVariableExplicitBranch, orbitPlaneMap,
      orbitFinTwoOfPoint, orbitPairInitialDifference,
      orbitFiniteChartPair,
      weightedPolynomialMap_orbitInitialPolynomialMap] using congrFun hpair 0
  · simpa [orbitSecondVariablePlaneDifference,
      orbitSecondVariableExplicitBranch, orbitPlaneMap,
      orbitFinTwoOfPoint, orbitPairInitialDifference,
      orbitFiniteChartPair,
      weightedPolynomialMap_orbitInitialPolynomialMap] using congrFun hpair 1

theorem orbitFirstVariablePlaneDifference_explicitBranch_zero
    {delta : ℂ} (hdelta : delta ^ 2 = 3) (R : OrbitSourceForm)
    (z lambda : ℂ) :
    orbitFirstVariablePlaneDifference delta z
      (lambda, orbitFirstVariableExplicitBranch delta z lambda) = 0 := by
  have hpair := orbitPairInitialDifference_finiteChart hdelta R (z + lambda)
  funext i
  fin_cases i
  · simpa [orbitFirstVariablePlaneDifference,
      orbitFirstVariableExplicitBranch, orbitPlaneMap,
      orbitFinTwoOfPoint, orbitPairInitialDifference,
      orbitFiniteChartPair,
      weightedPolynomialMap_orbitInitialPolynomialMap] using congrFun hpair 0
  · simpa [orbitFirstVariablePlaneDifference,
      orbitFirstVariableExplicitBranch, orbitPlaneMap,
      orbitFinTwoOfPoint, orbitPairInitialDifference,
      orbitFiniteChartPair,
      weightedPolynomialMap_orbitInitialPolynomialMap] using congrFun hpair 1

/-- Reparametrization used when the second point has nonzero second
coordinate. -/
@[expose]
noncomputable def orbitSecondVariableReparametrization
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (s.1.1, orbitSecondVariablePair delta (z + s.1.2) s.2)

/-- Reparametrization used when the first point has nonzero second
coordinate. -/
@[expose]
noncomputable def orbitFirstVariableReparametrization
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) :=
  (s.1.1, orbitFirstVariablePair delta (z + s.1.2) s.2)

theorem analyticAt_orbitSecondVariableReparametrization
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (orbitSecondVariableReparametrization delta z) s := by
  have htau : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.1) s :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlambda : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.2) s :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hq (i : Fin 2) : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.2 i) s :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt s.2
      |>.fun_comp analyticAt_snd
  have hfirst : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        orbitFiniteChartFirstPoint delta (z + t.1.2)) s := by
    simp only [orbitFiniteChartFirstPoint, orbitConicS_eval,
      orbitConicLambda_eval]
    simp only [orbitConicRhoValue_eq, orbitConicAlphaValue_eq,
      orbitConicBetaValue_eq]
    have hargument : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ z + t.1.2) s :=
      analyticAt_const.add hlambda
    have hone : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ (1 : ℂ)) s :=
      analyticAt_const
    have htwo : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ (2 : ℂ)) s :=
      analyticAt_const
    have hdelta : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ delta) s :=
      analyticAt_const
    have halpha : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          (z + t.1.2) ^ 2 - 1 ^ 2) s :=
      (hargument.pow 2).sub (hone.pow 2)
    have hbeta : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          2 * (z + t.1.2) * 1) s :=
      (htwo.mul hargument).mul hone
    have hrho : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          delta * ((z + t.1.2) ^ 2 + 1 ^ 2)) s :=
      hdelta.mul ((hargument.pow 2).add (hone.pow 2))
    exact
      (((halpha.pow 2).add (htwo.mul (hbeta.pow 2))).neg).prod
        (hrho.mul hbeta)
  have hsecond : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        orbitPointOfFinTwo t.2) s := by
    exact (hq 0).prod (hq 1)
  exact htau.prod (hfirst.prod hsecond)

theorem analyticAt_orbitFirstVariableReparametrization
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (orbitFirstVariableReparametrization delta z) s := by
  have htau : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.1) s :=
    analyticAt_fst.fun_comp analyticAt_fst
  have hlambda : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.1.2) s :=
    analyticAt_snd.fun_comp analyticAt_fst
  have hq (i : Fin 2) : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ t.2 i) s :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt s.2
      |>.fun_comp analyticAt_snd
  have hfirst : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        orbitPointOfFinTwo t.2) s := by
    exact (hq 0).prod (hq 1)
  have hsecond : AnalyticAt ℂ
      (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
        orbitFiniteChartSecondPoint delta (z + t.1.2)) s := by
    simp only [orbitFiniteChartSecondPoint, orbitConicT_eval,
      orbitConicZeta_eval]
    simp only [orbitConicRhoValue_eq, orbitConicAlphaValue_eq,
      orbitConicBetaValue_eq]
    have hargument : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ z + t.1.2) s :=
      analyticAt_const.add hlambda
    have hone : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ (1 : ℂ)) s :=
      analyticAt_const
    have htwo : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ (2 : ℂ)) s :=
      analyticAt_const
    have hdelta : AnalyticAt ℂ
        (fun _ : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ delta) s :=
      analyticAt_const
    have halpha : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          (z + t.1.2) ^ 2 - 1 ^ 2) s :=
      (hargument.pow 2).sub (hone.pow 2)
    have hbeta : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          2 * (z + t.1.2) * 1) s :=
      (htwo.mul hargument).mul hone
    have hrho : AnalyticAt ℂ
        (fun t : (ℂ × ℂ) × (Fin 2 → ℂ) ↦
          delta * ((z + t.1.2) ^ 2 + 1 ^ 2)) s :=
      hdelta.mul ((hargument.pow 2).add (hone.pow 2))
    exact
      ((htwo.mul (halpha.pow 2)).add (hbeta.pow 2)).prod
        (hrho.mul halpha)
  exact htau.prod (hfirst.prod hsecond)

/-- The first two equations in the varying second point chart. -/
@[expose]
noncomputable def orbitSecondVariablePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (orbitSecondVariableReparametrization delta z s) 0,
    Phi (orbitSecondVariableReparametrization delta z s) 1]

/-- The third equation in the varying second point chart. -/
@[expose]
noncomputable def orbitSecondVariableThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (orbitSecondVariableReparametrization delta z s) 2

/-- The first two equations in the varying first point chart. -/
@[expose]
noncomputable def orbitFirstVariablePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (orbitFirstVariableReparametrization delta z s) 0,
    Phi (orbitFirstVariableReparametrization delta z s) 1]

/-- The third equation in the varying first point chart. -/
@[expose]
noncomputable def orbitFirstVariableThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ)
    (s : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (orbitFirstVariableReparametrization delta z s) 2

theorem analyticAt_orbitSecondVariablePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (orbitSecondVariableReparametrization delta z s)) :
    AnalyticAt ℂ (orbitSecondVariablePlanePart Phi delta z) s := by
  have hfull := hPhi.fun_comp
    (analyticAt_orbitSecondVariableReparametrization delta z s)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt _
      |>.fun_comp hfull
  · exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt _
      |>.fun_comp hfull

theorem analyticAt_orbitSecondVariableThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (orbitSecondVariableReparametrization delta z s)) :
    AnalyticAt ℂ (orbitSecondVariableThirdPart Phi delta z) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt _
    |>.fun_comp
      (hPhi.fun_comp
        (analyticAt_orbitSecondVariableReparametrization delta z s))

theorem analyticAt_orbitFirstVariablePlanePart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (orbitFirstVariableReparametrization delta z s)) :
    AnalyticAt ℂ (orbitFirstVariablePlanePart Phi delta z) s := by
  have hfull := hPhi.fun_comp
    (analyticAt_orbitFirstVariableReparametrization delta z s)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt _
      |>.fun_comp hfull
  · exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt _
      |>.fun_comp hfull

theorem analyticAt_orbitFirstVariableThirdPart
    (Phi : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Fin 3 → ℂ)
    (delta z : ℂ) (s : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (orbitFirstVariableReparametrization delta z s)) :
    AnalyticAt ℂ (orbitFirstVariableThirdPart Phi delta z) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt _
    |>.fun_comp
      (hPhi.fun_comp
        (analyticAt_orbitFirstVariableReparametrization delta z s))

end OnLeConjecture.DTwo
