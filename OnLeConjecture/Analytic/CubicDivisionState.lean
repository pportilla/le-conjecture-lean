/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BanachAlgebraTaylorExtension

/-!
# A finite state model for cubic division

Multiplication by the first coordinate modulo a monic cubic, together with
the accumulated quotient, is represented by a four dimensional linear
operator. Powers of this operator simultaneously record the quotient and
the remainder of every monomial.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators

namespace Germ

/-- The quotient coordinate followed by the three remainder coordinates. -/
abbrev CubicDivisionState := Fin 4 → ℂ

/-- Continuous endomorphisms of the cubic division state space. -/
abbrev CubicDivisionEndomorphism :=
  Germ.CubicDivisionState →L[ℂ] Germ.CubicDivisionState

/-- The initial state represents the constant monomial one. -/
@[expose] noncomputable def cubicDivisionInitialState :
    Germ.CubicDivisionState :=
  fun i ↦ if i = 1 then 1 else 0

@[simp]
theorem cubicDivisionInitialState_apply_zero :
    Germ.cubicDivisionInitialState 0 = 0 := by
  simp [Germ.cubicDivisionInitialState]

@[simp]
theorem cubicDivisionInitialState_apply_one :
    Germ.cubicDivisionInitialState 1 = 1 := by
  simp [Germ.cubicDivisionInitialState]

@[simp]
theorem cubicDivisionInitialState_apply_two :
    Germ.cubicDivisionInitialState 2 = 0 := by
  simp [Germ.cubicDivisionInitialState]

@[simp]
theorem cubicDivisionInitialState_apply_three :
    Germ.cubicDivisionInitialState 3 = 0 := by
  simp [Germ.cubicDivisionInitialState]

/-- The monic cubic used by the state division. -/
@[expose] noncomputable def cubicDivisionPolynomialValue
    (x a₂ a₁ a₀ : ℂ) : ℂ :=
  x ^ 3 + a₂ * x ^ 2 + a₁ * x + a₀

/-- Multiplication by `x` on quotient and remainder states for the monic
cubic `x³ + a₂x² + a₁x + a₀`. -/
@[expose] noncomputable def cubicDivisionOperator
    (x a₂ a₁ a₀ : ℂ) : Germ.CubicDivisionEndomorphism :=
  ContinuousLinearMap.pi fun i ↦
    Fin.cases
      (x • ContinuousLinearMap.proj (R := ℂ) (0 : Fin 4) +
        ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4))
      (fun j ↦ Fin.cases
        ((-a₀) • ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4))
        (fun k ↦ Fin.cases
          (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 4) +
            (-a₁) • ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4))
          (fun _ ↦
            ContinuousLinearMap.proj (R := ℂ) (2 : Fin 4) +
              (-a₂) •
                ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4)) k) j) i

@[simp]
theorem cubicDivisionOperator_apply_zero
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionOperator x a₂ a₁ a₀ s 0 =
      x * s 0 + s 3 := by
  simp [Germ.cubicDivisionOperator]

@[simp]
theorem cubicDivisionOperator_apply_one
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionOperator x a₂ a₁ a₀ s 1 =
      -a₀ * s 3 := by
  change ((-a₀) •
      ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4)) s = _
  simp

@[simp]
theorem cubicDivisionOperator_apply_two
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionOperator x a₂ a₁ a₀ s 2 =
      s 1 - a₁ * s 3 := by
  change ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 4) +
      (-a₁) • ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4) :
        Germ.CubicDivisionState →L[ℂ] ℂ)) s = _
  simp
  ring

@[simp]
theorem cubicDivisionOperator_apply_three
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionOperator x a₂ a₁ a₀ s 3 =
      s 2 - a₂ * s 3 := by
  change ((ContinuousLinearMap.proj (R := ℂ) (2 : Fin 4) +
      (-a₂) • ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4) :
        Germ.CubicDivisionState →L[ℂ] ℂ)) s = _
  simp
  ring

/-- The parameter dependent part of the division operator is linear. -/
@[expose] noncomputable def cubicDivisionOperatorLinearMap :
    Source 4 →ₗ[ℂ] Germ.CubicDivisionEndomorphism where
  toFun z := Germ.cubicDivisionOperator (z 0) (z 1) (z 2) (z 3) -
    Germ.cubicDivisionOperator 0 0 0 0
  map_add' z w := by
    ext s i
    fin_cases i <;>
      simp [Germ.cubicDivisionOperator_apply_zero,
        Germ.cubicDivisionOperator_apply_one,
        Germ.cubicDivisionOperator_apply_two,
        Germ.cubicDivisionOperator_apply_three] <;>
      ring
  map_smul' c z := by
    ext s i
    fin_cases i <;>
      simp [Germ.cubicDivisionOperator_apply_zero,
        Germ.cubicDivisionOperator_apply_one,
        Germ.cubicDivisionOperator_apply_two,
        Germ.cubicDivisionOperator_apply_three] <;>
      ring

/-- The continuous version of the linear parameter dependence. -/
@[expose] noncomputable def cubicDivisionOperatorContinuousLinearMap :
    Source 4 →L[ℂ] Germ.CubicDivisionEndomorphism :=
  LinearMap.toContinuousLinearMap
    Germ.cubicDivisionOperatorLinearMap

/-- Affine linear expression for the division operator. -/
theorem cubicDivisionOperator_eq_base_add_linear (z : Source 4) :
    Germ.cubicDivisionOperator (z 0) (z 1) (z 2) (z 3) =
      Germ.cubicDivisionOperator 0 0 0 0 +
        Germ.cubicDivisionOperatorContinuousLinearMap z := by
  change _ = _ +
    (Germ.cubicDivisionOperator (z 0) (z 1) (z 2) (z 3) -
      Germ.cubicDivisionOperator 0 0 0 0)
  abel

/-- The division operator depends analytically on the polynomial and
evaluation parameters. -/
theorem analyticAt_cubicDivisionOperator (z : Source 4) :
    AnalyticAt ℂ
      (fun w : Source 4 ↦
        Germ.cubicDivisionOperator (w 0) (w 1) (w 2) (w 3)) z := by
  have hlinear :=
    Germ.cubicDivisionOperatorContinuousLinearMap.analyticAt z
  have hsum : AnalyticAt ℂ
      (fun w : Source 4 ↦ Germ.cubicDivisionOperator 0 0 0 0 +
        Germ.cubicDivisionOperatorContinuousLinearMap w) z :=
    analyticAt_const.add hlinear
  convert hsum using 1
  funext w
  exact Germ.cubicDivisionOperator_eq_base_add_linear w

/-- Evaluation of a state as quotient times divisor plus remainder. -/
@[expose] noncomputable def cubicDivisionStateEvaluation
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) : ℂ :=
  Germ.cubicDivisionPolynomialValue x a₂ a₁ a₀ * s 0 +
    s 1 + x * s 2 + x ^ 2 * s 3

/-- Applying the division operator multiplies the represented expression by
the first coordinate. -/
theorem cubicDivisionStateEvaluation_operator
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀
        (Germ.cubicDivisionOperator x a₂ a₁ a₀ s) =
      x * Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀ s := by
  simp only [Germ.cubicDivisionStateEvaluation,
    Germ.cubicDivisionOperator_apply_zero,
    Germ.cubicDivisionOperator_apply_one,
    Germ.cubicDivisionOperator_apply_two,
    Germ.cubicDivisionOperator_apply_three,
    Germ.cubicDivisionPolynomialValue]
  ring

/-- The state obtained after `n` multiplication steps. -/
@[expose] noncomputable def cubicDivisionMonomialState
    (x a₂ a₁ a₀ : ℂ) : ℕ → Germ.CubicDivisionState
  | 0 => Germ.cubicDivisionInitialState
  | n + 1 => Germ.cubicDivisionOperator x a₂ a₁ a₀
      (Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n)

/-- Every monomial is represented by its cubic division state. -/
theorem cubicDivisionStateEvaluation_monomialState
    (x a₂ a₁ a₀ : ℂ) (n : ℕ) :
    Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀
        (Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n) =
      x ^ n := by
  induction n with
  | zero =>
      simp [Germ.cubicDivisionMonomialState,
        Germ.cubicDivisionStateEvaluation,
        Germ.cubicDivisionPolynomialValue]
  | succ n ih =>
      rw [Germ.cubicDivisionMonomialState,
        Germ.cubicDivisionStateEvaluation_operator, ih, pow_succ']

/-- Recursive states agree with powers of the division operator. -/
theorem cubicDivisionMonomialState_eq_pow_apply
    (x a₂ a₁ a₀ : ℂ) (n : ℕ) :
    Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n =
      ((Germ.cubicDivisionOperator x a₂ a₁ a₀) ^ n)
        Germ.cubicDivisionInitialState := by
  induction n with
  | zero => simp [Germ.cubicDivisionMonomialState]
  | succ n ih =>
      rw [Germ.cubicDivisionMonomialState, ih, pow_succ']
      rw [mul_apply_eq_comp]

/-- The remainder coordinates of a monomial division state do not depend on
the point at which the quotient is evaluated. -/
theorem cubicDivisionMonomialState_remainder_independent
    (x z a₂ a₁ a₀ : ℂ) (n : ℕ) (i : Fin 3) :
    Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n i.succ =
      Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n i.succ := by
  induction n generalizing i with
  | zero =>
      fin_cases i <;> simp [Germ.cubicDivisionMonomialState]
  | succ n ih =>
      fin_cases i
      · change Germ.cubicDivisionOperator x a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n) 1 =
          Germ.cubicDivisionOperator z a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n) 1
        have h3 : Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n 3 =
            Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n 3 := by
          simpa using ih (2 : Fin 3)
        rw [Germ.cubicDivisionOperator_apply_one,
          Germ.cubicDivisionOperator_apply_one, h3]
      · change Germ.cubicDivisionOperator x a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n) 2 =
          Germ.cubicDivisionOperator z a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n) 2
        have h1 : Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n 1 =
            Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n 1 := by
          simpa using ih (0 : Fin 3)
        have h3 : Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n 3 =
            Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n 3 := by
          simpa using ih (2 : Fin 3)
        rw [Germ.cubicDivisionOperator_apply_two,
          Germ.cubicDivisionOperator_apply_two, h1, h3]
      · change Germ.cubicDivisionOperator x a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n) 3 =
          Germ.cubicDivisionOperator z a₂ a₁ a₀
            (Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n) 3
        have h2 : Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n 2 =
            Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n 2 := by
          simpa using ih (1 : Fin 3)
        have h3 : Germ.cubicDivisionMonomialState x a₂ a₁ a₀ n 3 =
            Germ.cubicDivisionMonomialState z a₂ a₁ a₀ n 3 := by
          simpa using ih (2 : Fin 3)
        rw [Germ.cubicDivisionOperator_apply_three,
          Germ.cubicDivisionOperator_apply_three, h2, h3]

/-- The scalar identity operator raised to a power acts by the corresponding
scalar power. -/
theorem scalar_identity_pow_apply
    (y : ℂ) (n : ℕ) (s : Germ.CubicDivisionState) :
    ((y • (1 : Germ.CubicDivisionEndomorphism)) ^ n) s = y ^ n • s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      simp only [smul_apply, one_apply_eq_self, smul_smul]
      rw [pow_succ']
      rw [mul_comm]

/-- The algebra monomial in the division operator and a scalar identity
acts on the initial state by the corresponding scalar multiple of the
monomial division state. -/
theorem algebraHomogeneousMonomial_divisionOperator_apply
    (d : ℕ) (i : Fin (d + 1)) (x y a₂ a₁ a₀ : ℂ) :
    Germ.algebraHomogeneousMonomial d i
        (fun _ : Fin d ↦
          (Germ.cubicDivisionOperator x a₂ a₁ a₀,
            y • (1 : Germ.CubicDivisionEndomorphism)))
        Germ.cubicDivisionInitialState =
      y ^ (d - i.1) •
        Germ.cubicDivisionMonomialState x a₂ a₁ a₀ i.1 := by
  rw [Germ.algebraHomogeneousMonomial_apply_diagonal,
    mul_apply_eq_comp,
    Germ.scalar_identity_pow_apply,
    map_smul,
    Germ.cubicDivisionMonomialState_eq_pow_apply]

/-- State evaluation as a continuous linear functional. -/
@[expose] noncomputable def cubicDivisionStateEvaluationLinear
    (x a₂ a₁ a₀ : ℂ) : Germ.CubicDivisionState →L[ℂ] ℂ :=
  Germ.cubicDivisionPolynomialValue x a₂ a₁ a₀ •
      ContinuousLinearMap.proj (R := ℂ) (0 : Fin 4) +
    ContinuousLinearMap.proj (R := ℂ) (1 : Fin 4) +
    x • ContinuousLinearMap.proj (R := ℂ) (2 : Fin 4) +
    x ^ 2 • ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4)

@[simp]
theorem cubicDivisionStateEvaluationLinear_apply
    (x a₂ a₁ a₀ : ℂ) (s : Germ.CubicDivisionState) :
    Germ.cubicDivisionStateEvaluationLinear x a₂ a₁ a₀ s =
      Germ.cubicDivisionStateEvaluation x a₂ a₁ a₀ s := by
  simp [Germ.cubicDivisionStateEvaluationLinear,
    Germ.cubicDivisionStateEvaluation]

/-- Applying state evaluation to one homogeneous extended coefficient
recovers the corresponding scalar homogeneous coefficient. -/
theorem cubicDivisionStateEvaluation_banachAlgebraExtensionSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (x y a₂ a₁ a₀ : ℂ) :
    Germ.cubicDivisionStateEvaluationLinear x a₂ a₁ a₀
        (Germ.banachAlgebraExtensionSeries p d
          (fun _ : Fin d ↦
            (Germ.cubicDivisionOperator x a₂ a₁ a₀,
              y • (1 : Germ.CubicDivisionEndomorphism)))
          Germ.cubicDivisionInitialState) =
      p d (fun _ : Fin d ↦ Germ.planePoint x y) := by
  rw [Germ.homogeneous_apply_planePoint_grouped]
  simp only [Germ.banachAlgebraExtensionSeries, sum_apply, smul_apply]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [Germ.algebraHomogeneousMonomial_divisionOperator_apply]
  simp_rw [map_smul]
  simp_rw [Germ.cubicDivisionStateEvaluationLinear_apply,
    Germ.cubicDivisionStateEvaluation_monomialState]
  simp only [smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ Germ.mixedCoefficient p d i *
      (y ^ (d - i) * x ^ i)) (d + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Germ

end OnLeConjecture.Analytic
