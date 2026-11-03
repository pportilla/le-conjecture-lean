/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BanachAlgebraTaylorExtension

/-!
# Finite state division by a monic polynomial

For every positive degree, multiplication by the first coordinate modulo a
monic polynomial is represented by an endomorphism of a finite dimensional
state space. The first state coordinate records the quotient evaluated at a
chosen point. The remaining coordinates record the polynomial remainder.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators

namespace Germ

/-- A quotient coordinate followed by the coefficients of a remainder of
degree at most `d`. The corresponding monic divisor has degree `d + 1`. -/
abbrev GeneralDivisionState (d : ℕ) :=
  ℂ × (Fin (d + 1) → ℂ)

/-- Continuous endomorphisms of the general division state space. -/
abbrev GeneralDivisionEndomorphism (d : ℕ) :=
  Germ.GeneralDivisionState d →L[ℂ] Germ.GeneralDivisionState d

/-- The monic divisor with coefficient vector ordered by increasing powers. -/
@[expose] noncomputable def generalDivisionPolynomialValue
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) : ℂ :=
  x ^ (d + 1) + ∑ i, a i * x ^ i.1

/-- The state representing the constant polynomial one. -/
@[expose] noncomputable def generalDivisionInitialState (d : ℕ) :
    Germ.GeneralDivisionState d :=
  (0, fun i ↦ if i = 0 then 1 else 0)

@[simp]
theorem generalDivisionInitialState_fst (d : ℕ) :
    (Germ.generalDivisionInitialState d).1 = 0 :=
  rfl

@[simp]
theorem generalDivisionInitialState_snd_zero (d : ℕ) :
    (Germ.generalDivisionInitialState d).2 0 = 1 := by
  simp [Germ.generalDivisionInitialState]

/-- Multiplication by `x` on quotient and remainder states for a monic
polynomial of degree `d + 1`. -/
@[expose] noncomputable def generalDivisionOperator
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) :
    Germ.GeneralDivisionEndomorphism d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun s ↦
        (x * s.1 + s.2 (Fin.last d),
          Fin.cases
            (-a 0 * s.2 (Fin.last d))
            (fun j ↦ s.2 j.castSucc - a j.succ * s.2 (Fin.last d)))
      map_add' := by
        intro s t
        apply Prod.ext
        · simp
          ring
        · funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
            ring
          · simp
            ring
      map_smul' := by
        intro c s
        apply Prod.ext
        · simp
          ring
        · funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
            ring
          · simp
            ring }

@[simp]
theorem generalDivisionOperator_fst
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) :
    (Germ.generalDivisionOperator x a s).1 =
      x * s.1 + s.2 (Fin.last d) :=
  rfl

@[simp]
theorem generalDivisionOperator_snd_zero
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) :
    (Germ.generalDivisionOperator x a s).2 0 =
      -a 0 * s.2 (Fin.last d) :=
  rfl

@[simp]
theorem generalDivisionOperator_snd_succ
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) (j : Fin d) :
    (Germ.generalDivisionOperator x a s).2 j.succ =
      s.2 j.castSucc - a j.succ * s.2 (Fin.last d) :=
  rfl

/-- The parameter dependent part of the general division operator is
linear. -/
@[expose] noncomputable def generalDivisionOperatorLinearMap (d : ℕ) :
    (ℂ × (Fin (d + 1) → ℂ)) →ₗ[ℂ]
      Germ.GeneralDivisionEndomorphism d where
  toFun z := Germ.generalDivisionOperator z.1 z.2 -
    Germ.generalDivisionOperator 0 0
  map_add' z w := by
    apply ContinuousLinearMap.ext
    intro s
    apply Prod.ext
    · simp
      ring
    · funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
        ring
      · simp
        ring
  map_smul' c z := by
    apply ContinuousLinearMap.ext
    intro s
    apply Prod.ext
    · simp
      ring
    · funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
        ring
      · simp
        ring

/-- The continuous version of the linear parameter dependence. -/
@[expose] noncomputable def generalDivisionOperatorContinuousLinearMap
    (d : ℕ) :
    (ℂ × (Fin (d + 1) → ℂ)) →L[ℂ]
      Germ.GeneralDivisionEndomorphism d :=
  LinearMap.toContinuousLinearMap
    (Germ.generalDivisionOperatorLinearMap d)

/-- Affine linear expression for the general division operator. -/
theorem generalDivisionOperator_eq_base_add_linear
    {d : ℕ} (z : ℂ × (Fin (d + 1) → ℂ)) :
    Germ.generalDivisionOperator z.1 z.2 =
      Germ.generalDivisionOperator 0 0 +
        Germ.generalDivisionOperatorContinuousLinearMap d z := by
  change _ = _ +
    (Germ.generalDivisionOperator z.1 z.2 -
      Germ.generalDivisionOperator 0 0)
  abel

/-- The general division operator depends analytically on its evaluation
point and coefficient vector. -/
theorem analyticAt_generalDivisionOperator
    {d : ℕ} (z : ℂ × (Fin (d + 1) → ℂ)) :
    AnalyticAt ℂ
      (fun w : ℂ × (Fin (d + 1) → ℂ) ↦
        Germ.generalDivisionOperator w.1 w.2) z := by
  have hlinear :=
    (Germ.generalDivisionOperatorContinuousLinearMap d).analyticAt z
  have hsum : AnalyticAt ℂ
      (fun w : ℂ × (Fin (d + 1) → ℂ) ↦
        Germ.generalDivisionOperator 0 0 +
          Germ.generalDivisionOperatorContinuousLinearMap d w) z :=
    analyticAt_const.add hlinear
  convert hsum using 1
  funext w
  exact Germ.generalDivisionOperator_eq_base_add_linear w

/-- Evaluation of a state as quotient times divisor plus remainder. -/
@[expose] noncomputable def generalDivisionStateEvaluation
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) : ℂ :=
  Germ.generalDivisionPolynomialValue x a * s.1 +
    ∑ i, x ^ i.1 * s.2 i

/-- Applying the division operator multiplies the represented expression by
the first coordinate. -/
theorem generalDivisionStateEvaluation_operator
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) :
    Germ.generalDivisionStateEvaluation x a
        (Germ.generalDivisionOperator x a s) =
      x * Germ.generalDivisionStateEvaluation x a s := by
  have hcoefficientSum :
      ∑ j : Fin d, a j.succ * x ^ (j.1 + 1) =
        ∑ j : Fin d, x ^ (j.1 + 1) * a j.succ := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpolynomial : Germ.generalDivisionPolynomialValue x a =
      x ^ (d + 1) + a 0 +
        ∑ j : Fin d, x ^ (j.1 + 1) * a j.succ := by
    simp only [Germ.generalDivisionPolynomialValue, Fin.sum_univ_succ,
      Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [hcoefficientSum]
    ring
  have hcoefficientMultiple :
      ∑ j : Fin d,
          x ^ (j.1 + 1) * (a j.succ * s.2 (Fin.last d)) =
        (∑ j : Fin d, x ^ (j.1 + 1) * a j.succ) *
          s.2 (Fin.last d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hshift :
      x ^ (d + 1) * s.2 (Fin.last d) +
          ∑ j : Fin d, x ^ (j.1 + 1) * s.2 j.castSucc =
        x * (s.2 0 +
          ∑ j : Fin d, x ^ (j.1 + 1) * s.2 j.succ) := by
    calc
      _ = ∑ i : Fin (d + 1), x ^ (i.1 + 1) * s.2 i := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        ac_rfl
      _ = _ := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [show j.1 + 1 + 1 = j.1 + 2 by omega, pow_succ']
        ring
  simp only [Germ.generalDivisionStateEvaluation,
    Germ.generalDivisionOperator_fst, Fin.sum_univ_succ,
    Germ.generalDivisionOperator_snd_zero,
    Germ.generalDivisionOperator_snd_succ, Fin.val_zero, pow_zero,
    one_mul, Fin.val_succ]
  rw [hpolynomial]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [
    hcoefficientMultiple]
  linear_combination hshift

/-- The state obtained after `n` multiplication steps. -/
@[expose] noncomputable def generalDivisionMonomialState
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) :
    ℕ → Germ.GeneralDivisionState d
  | 0 => Germ.generalDivisionInitialState d
  | n + 1 => Germ.generalDivisionOperator x a
      (Germ.generalDivisionMonomialState x a n)

/-- Every monomial is represented by its general division state. -/
theorem generalDivisionStateEvaluation_monomialState
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) (n : ℕ) :
    Germ.generalDivisionStateEvaluation x a
        (Germ.generalDivisionMonomialState x a n) = x ^ n := by
  induction n with
  | zero =>
      simp [Germ.generalDivisionMonomialState,
        Germ.generalDivisionStateEvaluation,
        Germ.generalDivisionPolynomialValue,
        Germ.generalDivisionInitialState]
  | succ n ih =>
      rw [Germ.generalDivisionMonomialState,
        Germ.generalDivisionStateEvaluation_operator, ih, pow_succ']

/-- Recursive states agree with powers of the division operator. -/
theorem generalDivisionMonomialState_eq_pow_apply
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) (n : ℕ) :
    Germ.generalDivisionMonomialState x a n =
      ((Germ.generalDivisionOperator x a) ^ n)
        (Germ.generalDivisionInitialState d) := by
  induction n with
  | zero => simp [Germ.generalDivisionMonomialState]
  | succ n ih =>
      rw [Germ.generalDivisionMonomialState, ih, pow_succ']
      rw [mul_apply_eq_comp]

/-- Below the divisor degree, a monomial state has zero quotient and the
corresponding standard basis remainder. -/
theorem generalDivisionMonomialState_of_le
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (n : ℕ) (hn : n ≤ d) :
    (Germ.generalDivisionMonomialState x a n).1 = 0 ∧
      ∀ i : Fin (d + 1),
        (Germ.generalDivisionMonomialState x a n).2 i =
          if i.1 = n then 1 else 0 := by
  induction n with
  | zero =>
      constructor
      · rfl
      · intro i
        simp [Germ.generalDivisionMonomialState,
          Germ.generalDivisionInitialState]
  | succ n ih =>
      have hnlt : n < d := by omega
      obtain ⟨hquotient, hremainder⟩ := ih (Nat.le_of_lt hnlt)
      constructor
      · simp only [Germ.generalDivisionMonomialState,
          Germ.generalDivisionOperator_fst, hquotient]
        rw [hremainder]
        simp [Fin.val_last]
        omega
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [Germ.generalDivisionMonomialState,
            Germ.generalDivisionOperator_snd_zero]
          rw [hremainder]
          simp [Fin.val_last]
          omega
        · simp only [Germ.generalDivisionMonomialState,
            Germ.generalDivisionOperator_snd_succ]
          rw [hremainder, hremainder]
          simp only [Fin.val_castSucc, Fin.val_last, Fin.val_succ]
          have hjlt : j.1 < d := j.2
          simp only [if_neg (by omega : d ≠ n), mul_zero, sub_zero]
          by_cases hj : j.1 = n
          · simp [hj]
          · simp [hj]

/-- At the divisor degree, the monomial state consists of quotient one and
the negative coefficient vector. -/
theorem generalDivisionMonomialState_divisorDegree
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) :
    Germ.generalDivisionMonomialState x a (d + 1) =
      (1, fun i ↦ -a i) := by
  have hprevious := Germ.generalDivisionMonomialState_of_le x a d le_rfl
  rw [Germ.generalDivisionMonomialState]
  apply Prod.ext
  · simp only [Germ.generalDivisionOperator_fst, hprevious.1]
    rw [hprevious.2]
    simp [Fin.val_last]
  · funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Germ.generalDivisionOperator_snd_zero]
      rw [hprevious.2]
      simp [Fin.val_last]
    · simp only [Germ.generalDivisionOperator_snd_succ]
      rw [hprevious.2, hprevious.2]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hjlt : j.1 < d := j.2
      simp [hjlt.ne]

/-- The remainder of a monomial division state does not depend on the point
at which the quotient is evaluated. -/
theorem generalDivisionMonomialState_remainder_independent
    {d : ℕ} (x z : ℂ) (a : Fin (d + 1) → ℂ) (n : ℕ) :
    (Germ.generalDivisionMonomialState x a n).2 =
      (Germ.generalDivisionMonomialState z a n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp only [Germ.generalDivisionMonomialState,
          Germ.generalDivisionOperator_snd_zero]
        rw [congrFun ih (Fin.last d)]
      · simp only [Germ.generalDivisionMonomialState,
          Germ.generalDivisionOperator_snd_succ]
        rw [congrFun ih j.castSucc, congrFun ih (Fin.last d)]

/-- A scalar identity operator raised to a power acts by the corresponding
scalar power. -/
theorem general_scalar_identity_pow_apply
    {d : ℕ} (y : ℂ) (n : ℕ) (s : Germ.GeneralDivisionState d) :
    ((y • (1 : Germ.GeneralDivisionEndomorphism d)) ^ n) s =
      y ^ n • s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      simp only [smul_apply, one_apply_eq_self, smul_smul]
      rw [pow_succ']
      rw [mul_comm]

/-- An algebra monomial in the division operator and a scalar identity acts
on the initial state by the corresponding scalar multiple of the monomial
division state. -/
theorem algebraHomogeneousMonomial_generalDivisionOperator_apply
    {d : ℕ} (n : ℕ) (i : Fin (n + 1))
    (x y : ℂ) (a : Fin (d + 1) → ℂ) :
    Germ.algebraHomogeneousMonomial n i
        (fun _ : Fin n ↦
          (Germ.generalDivisionOperator x a,
            y • (1 : Germ.GeneralDivisionEndomorphism d)))
        (Germ.generalDivisionInitialState d) =
      y ^ (n - i.1) •
        Germ.generalDivisionMonomialState x a i.1 := by
  rw [Germ.algebraHomogeneousMonomial_apply_diagonal,
    mul_apply_eq_comp,
    Germ.general_scalar_identity_pow_apply,
    map_smul,
    Germ.generalDivisionMonomialState_eq_pow_apply]

/-- State evaluation as a continuous linear functional. -/
@[expose] noncomputable def generalDivisionStateEvaluationLinear
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ) :
    Germ.GeneralDivisionState d →L[ℂ] ℂ :=
  Germ.generalDivisionPolynomialValue x a •
      ContinuousLinearMap.fst ℂ ℂ (Fin (d + 1) → ℂ) +
    ∑ i : Fin (d + 1), x ^ i.1 •
      (ContinuousLinearMap.proj (R := ℂ) i).comp
        (ContinuousLinearMap.snd ℂ ℂ (Fin (d + 1) → ℂ))

@[simp]
theorem generalDivisionStateEvaluationLinear_apply
    {d : ℕ} (x : ℂ) (a : Fin (d + 1) → ℂ)
    (s : Germ.GeneralDivisionState d) :
    Germ.generalDivisionStateEvaluationLinear x a s =
      Germ.generalDivisionStateEvaluation x a s :=
  by
    simp [Germ.generalDivisionStateEvaluationLinear,
      Germ.generalDivisionStateEvaluation]

/-- Applying state evaluation to one homogeneous extended coefficient
recovers the corresponding scalar homogeneous coefficient. -/
theorem generalDivisionStateEvaluation_banachAlgebraExtensionSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {d : ℕ} (n : ℕ) (x y : ℂ)
    (a : Fin (d + 1) → ℂ) :
    Germ.generalDivisionStateEvaluationLinear x a
        (Germ.banachAlgebraExtensionSeries p n
          (fun _ : Fin n ↦
            (Germ.generalDivisionOperator x a,
              y • (1 : Germ.GeneralDivisionEndomorphism d)))
          (Germ.generalDivisionInitialState d)) =
      p n (fun _ : Fin n ↦ Germ.planePoint x y) := by
  rw [Germ.homogeneous_apply_planePoint_grouped]
  simp only [Germ.banachAlgebraExtensionSeries, sum_apply, smul_apply]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [Germ.algebraHomogeneousMonomial_generalDivisionOperator_apply]
  simp_rw [map_smul]
  simp_rw [Germ.generalDivisionStateEvaluationLinear_apply,
    Germ.generalDivisionStateEvaluation_monomialState]
  simp only [smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ Germ.mixedCoefficient p n i *
      (y ^ (n - i) * x ^ i)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Germ

end OnLeConjecture.Analytic
