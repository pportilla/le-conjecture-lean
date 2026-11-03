/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantRegularPersistence

/-!
# Persistence at an exceptional invariant E root

This file treats a residual root for which the normalized first cube
coordinate is nonzero and the second cube coordinate is zero.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A point in the exceptional chart.  The second cube coordinate is the
parameter, while the direction displacement and scale are point variables. -/
@[expose]
noncomputable def eInvariantExceptionalAffinePoint
    (z g : ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![v 1 * (z + v 0), v 1, g]

@[expose]
noncomputable def eInvariantExceptionalReparametrization
    (z : ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    ℂ × (Fin 3 → ℂ) :=
  (q.1.1, eInvariantExceptionalAffinePoint z q.1.2 q.2)

@[expose]
noncomputable def eInvariantExceptionalPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![Phi (eInvariantExceptionalReparametrization z q) 0,
    Phi (eInvariantExceptionalReparametrization z q) 1]

@[expose]
noncomputable def eInvariantExceptionalThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ)) : ℂ :=
  Phi (eInvariantExceptionalReparametrization z q) 2

theorem analyticAt_eInvariantExceptionalReparametrization
    (z : ℂ) (q : (ℂ × ℂ) × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eInvariantExceptionalReparametrization z) q := by
  have houterFirst : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × (Fin 2 → ℂ) ↦ q.1.1) q :=
    analyticAt_fst.fun_comp analyticAt_fst
  have houterSecond : AnalyticAt ℂ
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
        eInvariantExceptionalAffinePoint z q.1.2 q.2) q := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact (hcoordinate 1).mul
        (analyticAt_const.add (hcoordinate 0))
    · exact hcoordinate 1
    · exact houterSecond
  exact houterFirst.prod hpoint

theorem analyticAt_eInvariantExceptionalPlanePart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (eInvariantExceptionalReparametrization z q)) :
    AnalyticAt ℂ (eInvariantExceptionalPlanePart Phi z) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (eInvariantExceptionalReparametrization z u)) q :=
    hPhi.fun_comp (analyticAt_eInvariantExceptionalReparametrization z q)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (eInvariantExceptionalReparametrization z u)) 0) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 0)
        (f := fun u ↦ Phi (eInvariantExceptionalReparametrization z u))
        ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt
          (Phi (eInvariantExceptionalReparametrization z q))) hfull
    simpa [eInvariantExceptionalPlanePart] using hcoordinate
  · have hcoordinate : AnalyticAt ℂ
        (fun u ↦ (Phi (eInvariantExceptionalReparametrization z u)) 1) q :=
      AnalyticAt.fun_comp
        (g := fun value : Fin 3 → ℂ ↦ value 1)
        (f := fun u ↦ Phi (eInvariantExceptionalReparametrization z u))
        ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt
          (Phi (eInvariantExceptionalReparametrization z q))) hfull
    simpa [eInvariantExceptionalPlanePart] using hcoordinate

theorem analyticAt_eInvariantExceptionalThirdPart
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ) (z : ℂ)
    (q : (ℂ × ℂ) × (Fin 2 → ℂ))
    (hPhi : AnalyticAt ℂ Phi
      (eInvariantExceptionalReparametrization z q)) :
    AnalyticAt ℂ (eInvariantExceptionalThirdPart Phi z) q := by
  have hfull : AnalyticAt ℂ
      (fun u ↦ Phi (eInvariantExceptionalReparametrization z u)) q :=
    hPhi.fun_comp (analyticAt_eInvariantExceptionalReparametrization z q)
  have hcoordinate : AnalyticAt ℂ
      (fun u ↦ (Phi (eInvariantExceptionalReparametrization z u)) 2) q :=
    AnalyticAt.fun_comp
    (g := fun value : Fin 3 → ℂ ↦ value 2)
    (f := fun u ↦ Phi (eInvariantExceptionalReparametrization z u))
    ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt
      (Phi (eInvariantExceptionalReparametrization z q))) hfull
  change AnalyticAt ℂ
    (fun u ↦ Phi (eInvariantExceptionalReparametrization z u) 2) q
  exact hcoordinate

/-- The first two special fibre equations with the zero cube coordinate as
parameter and the direction and scale as point variables. -/
@[expose]
noncomputable def eInvariantExceptionalPlaneDifference
    (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  eInvariantPlaneDifference z (q.2 0, ![q.2 1, q.1])

theorem eInvariantExceptionalPlanePart_weightedRescaledPerturbation_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z g : ℂ) (v : Fin 2 → ℂ) :
    eInvariantExceptionalPlanePart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        z ((0, g), v) =
      eInvariantExceptionalPlaneDifference z (g, v) := by
  funext i
  fin_cases i
  all_goals simp [eInvariantExceptionalPlanePart,
    eInvariantExceptionalReparametrization,
    eInvariantExceptionalAffinePoint,
    eInvariantExceptionalPlaneDifference, eInvariantPlaneDifference,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    weightedPolynomialMap, eInvariantPolynomialMap, cubicForm,
    quarticForm, formX, formT]
  all_goals ring

theorem eInvariantExceptionalThirdPart_weightedRescaledPerturbation_zero
    (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z g : ℂ) (v : Fin 2 → ℂ) :
    eInvariantExceptionalThirdPart
        (weightedRescaledPerturbation
          (weightedPolynomialMap (eInvariantPolynomialMap R)) remainder)
        z ((0, g), v) =
      weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 1 * (z + v 0), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 1, g) 2 := by
  simp [eInvariantExceptionalThirdPart,
    eInvariantExceptionalReparametrization,
    eInvariantExceptionalAffinePoint, weightedRescaledPerturbation_zero,
    weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint]

theorem eResidualW_common_scale (s x X : ℂ) :
    eResidualW (s * x) (s * X) = s ^ 3 * eResidualW x X := by
  simp only [eResidualW]
  field_simp

/-- A zero of the two exceptional plane equations satisfies the two residual
coordinate identities. -/
theorem eInvariantExceptionalPlaneDifference_zero_residual_coordinates
    (z g : ℂ) (v : Fin 2 → ℂ)
    (hscale : v 1 ≠ 0) (hdirection : z + v 0 ≠ 1)
    (hplane : eInvariantExceptionalPlaneDifference z (g, v) = 0) :
    v 1 ^ 3 * eResidualW (z + v 0) 1 = 1 ∧
      g ^ 3 = v 1 ^ 3 * eResidualW 1 (z + v 0) := by
  let u := z + v 0
  let x := v 1 * u
  let X := v 1
  have hx : x ≠ X := by
    intro hequal
    apply hdirection
    apply mul_left_cancel₀ hscale
    simpa [x, X, u] using hequal
  have hP : eP x (1 ^ 3) = eP X (g ^ 3) := by
    have hcomponent := congrFun hplane 0
    have hcomponent' :
        v 1 ^ 3 * ((z + v 0) ^ 3 - 1) + 3 * (1 - g ^ 3) = 0 := by
      simpa [eInvariantExceptionalPlaneDifference,
        eInvariantPlaneDifference] using hcomponent
    rw [eP, eP]
    dsimp only [x, X, u]
    norm_num
    linear_combination hcomponent'
  have hQ : eQ x (1 ^ 3) = eQ X (g ^ 3) := by
    have hcomponent := congrFun hplane 1
    have hcomponent' :
        v 1 ^ 4 * ((z + v 0) ^ 4 - 1) +
          4 * v 1 * (z + v 0 - g ^ 3) = 0 := by
      simpa [eInvariantExceptionalPlaneDifference,
        eInvariantPlaneDifference] using hcomponent
    rw [eQ, eQ]
    dsimp only [x, X, u]
    norm_num
    linear_combination hcomponent'
  obtain ⟨hfirst, hsecond⟩ :=
    (e_fibre_iff_residual hx).mp ⟨hP, hQ⟩
  constructor
  · calc
      v 1 ^ 3 * eResidualW (z + v 0) 1 =
          eResidualW (v 1 * (z + v 0)) (v 1 * 1) := by
            rw [eResidualW_common_scale]
      _ = 1 := by simpa [x, X, u] using hfirst.symm
  · calc
      g ^ 3 = eResidualW X x := hsecond
      _ = v 1 ^ 3 * eResidualW 1 (z + v 0) := by
        simpa [x, X, u] using eResidualW_common_scale (v 1) 1 (z + v 0)

/-- The quotient obtained by factoring the exceptional residual coordinate
at the selected root. -/
@[expose]
noncomputable def eInvariantExceptionalResidualQuotient
    (z lambda : ℂ) : ℂ :=
  ((z + lambda) ^ 2 + (z + lambda) * z + z ^ 2 +
    (z + lambda) + z + 1) / 12

theorem eResidualW_one_add_factorization
    (z lambda : ℂ) (hW : eResidualW 1 z = 0) :
    eResidualW 1 (z + lambda) =
      lambda * eInvariantExceptionalResidualQuotient z lambda := by
  simp only [eResidualW] at hW ⊢
  field_simp at hW ⊢
  dsimp only [eInvariantExceptionalResidualQuotient]
  field_simp
  linear_combination hW

theorem eInvariantExceptionalResidualQuotient_zero_ne
    (z s : ℂ) (hs : s ^ 3 * eResidualW z 1 = 1) :
    eInvariantExceptionalResidualQuotient z 0 ≠ 0 := by
  intro hquotient
  have hw : eResidualW z 1 = 0 := by
    calc
      eResidualW z 1 =
          -(z - 1) * eInvariantExceptionalResidualQuotient z 0 := by
            simp [eResidualW, eInvariantExceptionalResidualQuotient]
            ring
      _ = 0 := by rw [hquotient, mul_zero]
  rw [hw, mul_zero] at hs
  exact zero_ne_one hs

/-- The third exceptional special fibre coordinate has the same residual
factorization as in the regular chart. -/
theorem
    eInvariantExceptionalThirdDifference_factorization_of_plane_zero
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (z g : ℂ) (v : Fin 2 → ℂ)
    (hscale : v 1 ≠ 0) (hdirection : z + v 0 ≠ 1)
    (hplane : eInvariantExceptionalPlaneDifference z (g, v) = 0) :
    weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 1 * (z + v 0), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R) (v 1, g) 2 =
      v 1 ^ (n + 1) * (z + v 0 - 1) *
        (ePairDehomogenize (eThetaPolynomial ℂ c)).eval
          (z + v 0) := by
  simpa [eInvariantExceptionalPlaneDifference] using
    eInvariantThirdDifference_factorization_of_plane_zero
      Rzero R c n hdescent hdecomposition hhomogeneous z (v 0)
        ![v 1, g] hscale hdirection hplane

/-- The derivative in the direction and scale variables at the exceptional
point. -/
@[expose]
noncomputable def eInvariantExceptionalPointJacobian
    (z s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 * s ^ 3 * z ^ 2, 3 * s ^ 2 * (z ^ 3 - 1);
    4 * s ^ 4 * z ^ 3 + 4 * s,
      4 * s ^ 3 * (z ^ 4 - 1) + 4 * z]

@[expose]
noncomputable def eInvariantExceptionalPointDerivative
    (z s : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eInvariantExceptionalPointJacobian z s))
    |>.toContinuousLinearMap

theorem analyticAt_eInvariantExceptionalPlaneDifference
    (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eInvariantExceptionalPlaneDifference z) q := by
  have hparameter : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ q.1) q := analyticAt_fst
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ q.2 i) q := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp
        (analyticAt_snd : AnalyticAt ℂ
          (fun q : ℂ × (Fin 2 → ℂ) ↦ q.2) q)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      q.2 1 ^ 3 * ((z + q.2 0) ^ 3 - 1) + 3 * (1 - q.1 ^ 3)) q
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      q.2 1 ^ 4 * ((z + q.2 0) ^ 4 - 1) +
        4 * q.2 1 * (z + q.2 0 - q.1 ^ 3)) q
    fun_prop (disch := assumption)

theorem hasStrictFDerivAt_eInvariantExceptionalPlaneDifference_point
    (z s : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ eInvariantExceptionalPlaneDifference z (0, v))
      (eInvariantExceptionalPointDerivative z s) ![0, s] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eInvariantExceptionalPlaneDifference,
    eInvariantPlaneDifference]
  · convert
      ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![0, s]).pow 3)
        |>.mul
          ((((hasStrictFDerivAt_const (𝕜 := ℂ) z ![0, s]).add
            (hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![0, s]))
            |>.pow 3).sub
              (hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![0, s])))
        |>.add (hasStrictFDerivAt_const (𝕜 := ℂ) 3 ![0, s]))
      using 1
    · funext v
      simp
    · ext v
      simp [eInvariantExceptionalPointDerivative,
        eInvariantExceptionalPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring
  · convert
      ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![0, s]).pow 4)
        |>.mul
          ((((hasStrictFDerivAt_const (𝕜 := ℂ) z ![0, s]).add
            (hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![0, s]))
            |>.pow 4).sub
              (hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![0, s])))
        |>.add
          (((hasStrictFDerivAt_const (𝕜 := ℂ) z ![0, s]).add
            (hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![0, s]))
            |>.mul (hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![0, s])
            |>.const_mul (4 : ℂ)))
      using 1
    · funext v
      simp
      ring
    · ext v
      simp [eInvariantExceptionalPointDerivative,
        eInvariantExceptionalPointJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring

theorem det_eInvariantExceptionalPointJacobian (z s : ℂ) :
    Matrix.det (eInvariantExceptionalPointJacobian z s) =
      12 * s ^ 3 * (s ^ 3 * z ^ 3 - s ^ 3 * z ^ 2 + 1) := by
  simp [eInvariantExceptionalPointJacobian, Matrix.det_fin_two]
  ring

theorem det_eInvariantExceptionalPointDerivative (z s : ℂ) :
    (eInvariantExceptionalPointDerivative z s).det =
      12 * s ^ 3 * (s ^ 3 * z ^ 3 - s ^ 3 * z ^ 2 + 1) := by
  calc
    (eInvariantExceptionalPointDerivative z s).det =
        Matrix.det (eInvariantExceptionalPointJacobian z s) := by
      simp [eInvariantExceptionalPointDerivative,
        LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
    _ = _ := det_eInvariantExceptionalPointJacobian z s

theorem eInvariant_exceptional_inner_ne_zero
    (z s : ℂ)
    (hz : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0) :
    s ^ 3 * z ^ 3 - s ^ 3 * z ^ 2 + 1 ≠ 0 := by
  intro hinner
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hquadratic : (3 : ℂ) + 2 * z + z ^ 2 = 0 := by
    have hequation := e_residual_second_equation z (1 : ℂ)
    rw [hW] at hequation
    exact (mul_eq_zero.mp (by simpa using hequation)).resolve_left hsub
  have hscale :
      s ^ 3 * (1 + z + z ^ 2 - 3 * z ^ 3) = 12 := by
    have hscale' := hs
    rw [eResidualW] at hscale'
    field_simp at hscale'
    calc
      s ^ 3 * (1 + z + z ^ 2 - 3 * z ^ 3) =
          s ^ 3 * (1 + z + z ^ 2 - z ^ 3 * 3) := by ring
      _ = 12 := hscale'
  have hcubic : z ^ 3 - z - 6 = 0 := by
    linear_combination (z - 2) * hquadratic
  have hinnerReduced : 3 * s ^ 3 * (z + 3) + 1 = 0 := by
    linear_combination
      hinner + s ^ 3 * hquadratic - s ^ 3 * hcubic
  have hscaleReduced : s ^ 3 * (z + 5) + 3 = 0 := by
    linear_combination
      (-1 / 4) * hscale + (s ^ 3 / 4) * hquadratic -
        (3 * s ^ 3 / 4) * hcubic
  have hsValue : 3 * s ^ 3 + 4 = 0 := by
    linear_combination
      (-1 / 2) * hinnerReduced + (3 / 2) * hscaleReduced
  have hzValue : 4 * z + 11 = 0 := by
    linear_combination
      (z + 5) * hsValue - 3 * hscaleReduced
  have hfalse : (81 : ℂ) = 0 := by
    linear_combination 16 * hquadratic - (4 * z - 3) * hzValue
  norm_num at hfalse

/-- The derivative in the direction and scale variables is invertible at an
exceptional residual point. -/
@[expose]
noncomputable def eInvariantExceptionalPointDerivativeEquiv
    (z s : ℂ)
    (hz : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hW : eResidualW 1 z = 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (eInvariantExceptionalPointDerivative z s)
    |>.toContinuousLinearEquivOfDetNeZero <| by
      rw [det_eInvariantExceptionalPointDerivative]
      exact mul_ne_zero
        (mul_ne_zero (by norm_num)
          (pow_ne_zero 3 (eInvariant_chart_s_ne_zero hs)))
        (eInvariant_exceptional_inner_ne_zero z s hz hs hW)

/-- A perturbation of an exceptional invariant residual collision has a full
zero in every neighborhood of the initial direction. -/
theorem eventually_exists_eInvariantExceptionalZero_mem_nhds_of_analyticPerturbation
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
        eInvariantExceptionalPlaneDifference z (g, v))
    (hspecialThird : ∀ g v,
      eInvariantExceptionalThirdPart Phi z ((0, g), v) =
        weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 1 * (z + v 0), 1) 2 -
          weightedPolynomialMap (eInvariantPolynomialMap R)
            (v 1, g) 2)
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
    ext i <;> simp [eInvariantExceptionalReparametrization,
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
        (fun v ↦ eInvariantExceptionalPlaneDifference z (0, v))
        (pointEquiv : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) q := by
    simpa [pointEquiv, q, eInvariantExceptionalPointDerivativeEquiv] using
      hasStrictFDerivAt_eInvariantExceptionalPlaneDifference_point z s
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
          fun v ↦ eInvariantExceptionalPlaneDifference z (0, v) := by
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
    change eInvariantPlaneDifference z (0, ![s, 0]) = 0
    apply eInvariantPlaneDifference_base_eq_zero z s 0 hs
    simp [hW]
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
        plane (((0, 0), q)) hplane hpoint] with parameter hparameter'
    simpa [hplaneZero] using hparameter'
  have hplaneBranchSpecial : ∀ᶠ g in nhds 0,
      eInvariantExceptionalPlaneDifference z (g, branch (0, g)) = 0 := by
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
        g ^ 3 = branch (0, g) 1 ^ 3 *
          eResidualW 1 (z + branch (0, g) 0) := by
    filter_upwards [hplaneBranchSpecial, hbranchScaleNe,
      hdirectionNe] with g hplaneAt hscaleAt hdirectionAt
    exact eInvariantExceptionalPlaneDifference_zero_residual_coordinates
      z g (branch (0, g)) hscaleAt hdirectionAt hplaneAt
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
  have hlambdaUnitZero : lambdaUnit 0 ≠ 0 := by
    exact inv_ne_zero hdenominatorZero
  have hlambdaFactor : ∀ᶠ g in nhds 0,
      branch (0, g) 0 = g ^ 3 * lambdaUnit g := by
    filter_upwards [hresidual, hdenominatorNe] with g hresidualAt hdenominatorAt
    have hsecond := hresidualAt.2
    rw [eResidualW_one_add_factorization z (branch (0, g) 0) hW]
      at hsecond
    have hproduct : branch (0, g) 0 * denominator g = g ^ 3 := by
      calc
        branch (0, g) 0 * denominator g =
            branch (0, g) 1 ^ 3 *
              (branch (0, g) 0 *
                eInvariantExceptionalResidualQuotient z
                  (branch (0, g) 0)) := by
            simp only [denominator]
            ring
        _ = g ^ 3 := hsecond.symm
    change branch (0, g) 0 = g ^ 3 * (denominator g)⁻¹
    calc
      branch (0, g) 0 =
          (branch (0, g) 0 * denominator g) * (denominator g)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hdenominatorAt, mul_one]
      _ = g ^ 3 * (denominator g)⁻¹ := by rw [hproduct]
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
        g ^ (3 * p.rootMultiplicity z) * unit g := by
    filter_upwards [hplaneBranchSpecial, hbranchScaleNe,
      hdirectionNe, hlambdaFactor] with
      g hplaneAt hscaleAt hdirectionAt hlambdaAt
    change eInvariantExceptionalThirdPart Phi z
        ((0, g), branch (0, g)) =
      g ^ (3 * p.rootMultiplicity z) * unit g
    rw [hspecialThird]
    rw [eInvariantExceptionalThirdDifference_factorization_of_plane_zero
      Rzero R c n hdescent hdecomposition hhomogeneous z g
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
        (3 * p.rootMultiplicity z) unit (Nat.mul_pos (by norm_num) hm)
          hunit hunitZero hfactor V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨g, hmem, hplaneAt, hthirdAt⟩ := htau
  let point := eInvariantExceptionalAffinePoint z g (branch (tau, g))
  refine ⟨point, ?_, ?_⟩
  · exact hmem
  · funext i
    fin_cases i
    · exact congrFun hplaneAt 0
    · exact congrFun hplaneAt 1
    · exact hthirdAt

/-- The rescaled perturbation of an exceptional invariant initial map has a
zero in every neighborhood of its initial collision. -/
theorem eventually_exists_eWeightedInvariantExceptionalZero_mem_nhds
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
            (weightedPolynomialMap (eInvariantPolynomialMap R))
              remainder (tau, point) = 0 := by
  let initialMap := weightedPolynomialMap (eInvariantPolynomialMap R)
  let Phi := weightedRescaledPerturbation initialMap remainder
  have hPhi : AnalyticAt ℂ Phi (0, ![s * z, s, 0]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eInvariantPolynomialMap R) ![s * z, s, 0]
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  apply
    eventually_exists_eInvariantExceptionalZero_mem_nhds_of_analyticPerturbation
      Phi Rzero R c n z s hdescent hdecomposition hhomogeneous hp
        hzRoot hzOne hs hW hPhi
  · exact eInvariantExceptionalPlanePart_weightedRescaledPerturbation_zero
      R remainder z
  · exact eInvariantExceptionalThirdPart_weightedRescaledPerturbation_zero
      R remainder z
  · exact hU

end OnLeConjecture.DThree
