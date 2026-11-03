/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantNonzero
public import OnLeConjecture.DThree.WeightedOrderExpansion
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Collisions from the invariant E residual factor

A nonzero homogeneous residual factor has an isolated affine root after
choosing one of the two projective charts.  The chart choice below includes
the point at infinity.  The residual parametrization then lifts the root to
two distinct points with equal values under the invariant initial map.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The three homogeneous coordinates in the invariant `E` branch. -/
@[expose]
noncomputable def eInvariantPolynomialMap
    (R : Form ℂ) : Fin 3 → Form ℂ :=
  ![cubicForm 0 3, quarticForm 1 0 0 4 0, R]

/-- The coordinate degrees of the invariant `E` initial map. -/
@[expose]
noncomputable def eInvariantDegrees (N : ℕ) : Fin 3 → ℕ :=
  ![3, 4, N]

/-- The chart polynomial of a nonzero homogeneous residual factor is
nonzero. -/
theorem ePairDehomogenize_ne_zero
    {theta : EPairRing ℂ} {n : ℕ}
    (hhomogeneous : EPairIsHomogeneous theta n)
    (htheta : theta ≠ 0) :
    ePairDehomogenize theta ≠ 0 := by
  intro hchart
  have hform : eIteratedToForm theta = 0 := by
    rw [← ePair_homogenize_dehomogenize hhomogeneous, hchart]
    simp
  apply htheta
  have hback := congrArg eFormToIterated hform
  simpa only [map_zero, AlgHom.comp_apply, AlgHom.id_apply] using
    (AlgHom.congr_fun eFormToIterated_comp_iteratedToForm theta).symm.trans
      hback

/-- Symmetry transports a residual zero to the point with exchanged
coordinates. -/
theorem ePairPointEval_eq_aevalAeval
    (theta : EPairRing ℂ) (x X : ℂ) :
    ePairPointEval ℂ x X theta = Polynomial.aevalAeval x X theta := by
  let right : EPairRing ℂ →ₐ[ℂ] ℂ := Polynomial.aevalAeval x X
  have heq : ePairPointEval ℂ x X = right := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      change ePairPointEval ℂ x X (ePairFirst ℂ) = right (ePairFirst ℂ)
      rw [ePairPointEval_first]
      simp [right, ePairFirst]
    · change ePairPointEval ℂ x X (ePairSecond ℂ) = right (ePairSecond ℂ)
      rw [ePairPointEval_second]
      simp [right, ePairSecond]
  exact AlgHom.congr_fun heq theta

theorem eThetaPolynomial_pointEval_swap
    (c : Fin 4 → EBaseRing ℂ) (x X : ℂ) :
    ePairPointEval ℂ X x (eThetaPolynomial ℂ c) =
      ePairPointEval ℂ x X (eThetaPolynomial ℂ c) := by
  calc
    ePairPointEval ℂ X x (eThetaPolynomial ℂ c) =
        Polynomial.aevalAeval X x (eThetaPolynomial ℂ c) :=
      ePairPointEval_eq_aevalAeval _ _ _
    _ = Polynomial.aevalAeval x X
        (Polynomial.Bivariate.swap (eThetaPolynomial ℂ c)) := by
      rw [Polynomial.Bivariate.aevalAeval_swap]
    _ = ePairPointEval ℂ x X (eThetaPolynomial ℂ c) := by
      rw [eThetaPolynomial_swap]
      exact (ePairPointEval_eq_aevalAeval _ _ _).symm

/-- Every nonzero projective residual zero away from the diagonal determines
an affine root away from one.  If the supplied point is at infinity, the
two coordinates are exchanged first. -/
theorem exists_eThetaPolynomial_affine_root
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (x X : ℂ) (hnonzero : x ≠ 0 ∨ X ≠ 0)
    (htheta : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0)
    (hne : x ≠ X) :
    ∃ z : ℂ,
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z ∧
      z ≠ 1 := by
  let p := ePairDehomogenize (eThetaPolynomial ℂ c)
  have hpDegree : p.natDegree ≤ n :=
    ePairDehomogenize_natDegree_le hhomogeneous
  by_cases hX : X = 0
  · have hx : x ≠ 0 := by
      rcases hnonzero with hx | hXne
      · exact hx
      · exact False.elim (hXne hX)
    refine ⟨X / x, ?_, ?_⟩
    · change p.eval (X / x) = 0
      have hswap :
          ePairPointEval ℂ X x (eThetaPolynomial ℂ c) = 0 :=
        (eThetaPolynomial_pointEval_swap c x X).trans htheta
      have hform :
          MvPolynomial.eval ![X, x]
              (p.homogenize n) = 0 := by
        rw [ePair_homogenize_dehomogenize hhomogeneous]
        rw [← ePairPointEval_eq_eval_iteratedToForm]
        exact hswap
      rw [Polynomial.eval_homogenize hpDegree ![X, x] (by simpa using hx)] at hform
      exact (mul_eq_zero.mp hform).resolve_right (pow_ne_zero n hx)
    · rw [hX, zero_div]
      exact zero_ne_one
  · refine ⟨x / X, ?_, ?_⟩
    · change p.eval (x / X) = 0
      have hform :
          MvPolynomial.eval ![x, X]
              (p.homogenize n) = 0 := by
        rw [ePair_homogenize_dehomogenize hhomogeneous]
        rw [← ePairPointEval_eq_eval_iteratedToForm]
        exact htheta
      rw [Polynomial.eval_homogenize hpDegree ![x, X] (by simpa using hX)] at hform
      exact (mul_eq_zero.mp hform).resolve_right (pow_ne_zero n hX)
    · intro hquotient
      apply hne
      exact (div_eq_one_iff_eq hX).mp hquotient

/-- The affine root selected from the projective residual zero is isolated.
The finite and discrete conclusions include roots of arbitrary
multiplicity. -/
theorem exists_eThetaPolynomial_isolated_affine_root
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hthetaNe : eThetaPolynomial ℂ c ≠ 0)
    (x X : ℂ) (hnonzero : x ≠ 0 ∨ X ≠ 0)
    (htheta : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0)
    (hne : x ≠ X) :
    ∃ z : ℂ,
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z ∧
      z ≠ 1 ∧
      Set.Finite {u : ℂ |
        (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u} ∧
      IsDiscrete {u : ℂ |
        (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u} := by
  obtain ⟨z, hz, hzone⟩ :=
    exists_eThetaPolynomial_affine_root c n hhomogeneous
      x X hnonzero htheta hne
  have hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0 :=
    ePairDehomogenize_ne_zero hhomogeneous hthetaNe
  have hfinite : Set.Finite {u : ℂ |
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u} :=
    Polynomial.finite_setOfPred_isRoot hp
  exact ⟨z, hz, hzone, hfinite, hfinite.isDiscrete⟩

/-- The invariant branch supplies a nonzero chart polynomial and an
isolated affine root away from the diagonal value one. -/
theorem exists_e_invariant_isolated_affine_residual_root
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ)) :
    ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
      ∃ z : ℂ,
        (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z ∧
        z ≠ 1 ∧
        ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0 ∧
        Set.Finite {u : ℂ |
          (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u} ∧
        IsDiscrete {u : ℂ |
          (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u} := by
  obtain ⟨Rzero, c, hdescent, hdecomposition, hthetaHomogeneous,
      _, hthetaNe, x, X, hnonzero, htheta, hne⟩ :=
    exists_e_invariant_nonzero_residual_off_diagonal_projective_zero
      R N homega hhomogeneous hinvariant hdiv hnotbase
  obtain ⟨z, hz, hzone, hfinite, hdiscrete⟩ :=
    exists_eThetaPolynomial_isolated_affine_root c (N - 1)
      hthetaHomogeneous hthetaNe x X hnonzero htheta hne
  exact ⟨Rzero, c, hdescent, hdecomposition, z, hz, hzone,
    ePairDehomogenize_ne_zero hthetaHomogeneous hthetaNe,
    hfinite, hdiscrete⟩

/-- Scalar evaluation in the descended source coordinates. -/
noncomputable def eSourcePointEval (x w : ℂ) :
    ESourceRing ℂ →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => x
    | ESourceCoordinate.w => w

/-- Evaluation commutes with the substitution `w = t^3`. -/
theorem eSourceCubeSubstitutionForm_pointEval
    (Rzero : ESourceRing ℂ) (x t : ℂ) :
    MvPolynomial.eval ![x, t] (eSourceCubeSubstitutionForm Rzero) =
      eSourcePointEval x (t ^ 3) Rzero := by
  let left : ESourceRing ℂ →ₐ[ℂ] ℂ :=
    (MvPolynomial.aeval ![x, t]).comp eSourceCubeSubstitutionForm
  have heq : left = eSourcePointEval x (t ^ 3) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | x =>
      dsimp only [left, AlgHom.comp_apply, eSourcePointEval]
      rw [MvPolynomial.aeval_X]
      change MvPolynomial.eval ![x, t]
          (eSourceCubeSubstitutionForm (eSourceX ℂ)) = x
      rw [eSourceCubeSubstitutionForm_x]
      simp [formX]
    | w =>
      dsimp only [left, AlgHom.comp_apply, eSourcePointEval]
      rw [MvPolynomial.aeval_X]
      change MvPolynomial.eval ![x, t]
          (eSourceCubeSubstitutionForm (eSourceW ℂ)) = t ^ 3
      rw [eSourceCubeSubstitutionForm_w]
      simp [formT]
  exact AlgHom.congr_fun heq Rzero

@[simp]
theorem eSourcePointEval_x (x w : ℂ) :
    eSourcePointEval x w (eSourceX ℂ) = x := by
  simp [eSourcePointEval, eSourceX]

@[simp]
theorem eSourcePointEval_w (x w : ℂ) :
    eSourcePointEval x w (eSourceW ℂ) = w := by
  simp [eSourcePointEval, eSourceW]

theorem eSourcePointEval_p (x w : ℂ) :
    eSourcePointEval x w (eSourceP ℂ) = eP x w := by
  simp [eSourceP, eP]

theorem eSourcePointEval_q (x w : ℂ) :
    eSourcePointEval x w (eSourceQ ℂ) = eQ x w := by
  simp [eSourceQ, eQ]

/-- Evaluating a coefficient pulled back from the base is the same as
evaluating it at the two common image coordinates. -/
theorem eSourcePointEval_comp_baseToSource (x w : ℂ) :
    (eSourcePointEval x w).comp (eBaseToSource ℂ) =
      eBasePointEval ℂ (eP x w) (eQ x w) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | p =>
    change eSourcePointEval x w (eBaseToSource ℂ (eBaseP ℂ)) =
      eBasePointEval ℂ (eP x w) (eQ x w) (eBaseP ℂ)
    rw [eBaseToSource_p, eSourcePointEval_p, eBasePointEval_p]
  | q =>
    change eSourcePointEval x w (eBaseToSource ℂ (eBaseQ ℂ)) =
      eBasePointEval ℂ (eP x w) (eQ x w) (eBaseQ ℂ)
    rw [eBaseToSource_q, eSourcePointEval_q, eBasePointEval_q]

/-- Scalar evaluation of a canonical basis decomposition. -/
theorem eSourcePointEval_of_basis
    (Rzero : ESourceRing ℂ) (c : Fin 4 → EBaseRing ℂ)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (x w : ℂ) :
    eSourcePointEval x w Rzero =
      eBasisValue
        (eBasePointEval ℂ (eP x w) (eQ x w) (c 0))
        (eBasePointEval ℂ (eP x w) (eQ x w) (c 1))
        (eBasePointEval ℂ (eP x w) (eQ x w) (c 2))
        (eBasePointEval ℂ (eP x w) (eQ x w) (c 3)) x := by
  rw [hdecomposition, map_sum, Fin.sum_univ_four]
  simp only [map_mul, map_pow, eSourcePointEval_x]
  have hc (i : Fin 4) :
      eSourcePointEval x w (eBaseToSource ℂ (c i)) =
        eBasePointEval ℂ (eP x w) (eQ x w) (c i) :=
    AlgHom.congr_fun (eSourcePointEval_comp_baseToSource x w) (c i)
  simp_rw [hc]
  simp [eBasisValue]

/-- A zero of the residual difference factor makes the descended third
coordinate equal at the two points of the residual parametrization. -/
theorem eSourcePointEval_eq_of_theta_zero
    (Rzero : ESourceRing ℂ) (c : Fin 4 → EBaseRing ℂ)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (x X : ℂ)
    (htheta : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0) :
    eSourcePointEval x (eResidualW x X) Rzero =
      eSourcePointEval X (eResidualW X x) Rzero := by
  let p := eP x (eResidualW x X)
  let q := eQ x (eResidualW x X)
  have hP : eP X (eResidualW X x) = p :=
    (e_residual_parametrizes_fibre x X).1.symm
  have hQ : eQ X (eResidualW X x) = q :=
    (e_residual_parametrizes_fibre x X).2.symm
  have hpairP : ePairPointEval ℂ x X (eResidualPairP ℂ) = p := by
    rw [ePairPointEval_residualPairP]
    change (4 : ℂ)⁻¹ * ((x + X) * (x ^ 2 + X ^ 2)) =
      eP x (eResidualW x X)
    rw [eP_on_residual]
    simp [div_eq_mul_inv]
    ring
  have hpairQ : ePairPointEval ℂ x X (eResidualPairQ ℂ) = q := by
    rw [ePairPointEval_residualPairQ]
    change (3 : ℂ)⁻¹ * (x * X * (x ^ 2 + x * X + X ^ 2)) =
      eQ x (eResidualW x X)
    rw [eQ_on_residual]
    simp [div_eq_mul_inv]
    ring
  have hthetaScalar :
      eTheta
        (eBasePointEval ℂ p q (c 1))
        (eBasePointEval ℂ p q (c 2))
        (eBasePointEval ℂ p q (c 3)) x X = 0 := by
    rw [← ePairPointEval_thetaPolynomial ℂ c x X p q hpairP hpairQ]
    exact htheta
  have hbasis := e_basis_difference_factorization
    (eBasePointEval ℂ p q (c 0))
    (eBasePointEval ℂ p q (c 1))
    (eBasePointEval ℂ p q (c 2))
    (eBasePointEval ℂ p q (c 3)) x X
  have hbasisEq :
      eBasisValue
          (eBasePointEval ℂ p q (c 0))
          (eBasePointEval ℂ p q (c 1))
          (eBasePointEval ℂ p q (c 2))
          (eBasePointEval ℂ p q (c 3)) x =
        eBasisValue
          (eBasePointEval ℂ p q (c 0))
          (eBasePointEval ℂ p q (c 1))
          (eBasePointEval ℂ p q (c 2))
          (eBasePointEval ℂ p q (c 3)) X := by
    apply sub_eq_zero.mp
    rw [hbasis, hthetaScalar, mul_zero]
  rw [eSourcePointEval_of_basis Rzero c hdecomposition x
      (eResidualW x X),
    eSourcePointEval_of_basis Rzero c hdecomposition X
      (eResidualW X x)]
  change eBasisValue
      (eBasePointEval ℂ p q (c 0))
      (eBasePointEval ℂ p q (c 1))
      (eBasePointEval ℂ p q (c 2))
      (eBasePointEval ℂ p q (c 3)) x =
    eBasisValue
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 0))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 1))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 2))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 3)) X
  rw [hP, hQ]
  exact hbasisEq

/-- The residual difference of the descended coordinate is the diagonal
factor times the scalar value of `Theta`. -/
theorem eSourcePointEval_residual_difference
    (Rzero : ESourceRing ℂ) (c : Fin 4 → EBaseRing ℂ)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (x X : ℂ) :
    eSourcePointEval x (eResidualW x X) Rzero -
        eSourcePointEval X (eResidualW X x) Rzero =
      (x - X) * ePairPointEval ℂ x X (eThetaPolynomial ℂ c) := by
  let p := eP x (eResidualW x X)
  let q := eQ x (eResidualW x X)
  have hP : eP X (eResidualW X x) = p :=
    (e_residual_parametrizes_fibre x X).1.symm
  have hQ : eQ X (eResidualW X x) = q :=
    (e_residual_parametrizes_fibre x X).2.symm
  have hpairP : ePairPointEval ℂ x X (eResidualPairP ℂ) = p := by
    rw [ePairPointEval_residualPairP]
    change (4 : ℂ)⁻¹ * ((x + X) * (x ^ 2 + X ^ 2)) =
      eP x (eResidualW x X)
    rw [eP_on_residual]
    simp [div_eq_mul_inv]
    ring
  have hpairQ : ePairPointEval ℂ x X (eResidualPairQ ℂ) = q := by
    rw [ePairPointEval_residualPairQ]
    change (3 : ℂ)⁻¹ * (x * X * (x ^ 2 + x * X + X ^ 2)) =
      eQ x (eResidualW x X)
    rw [eQ_on_residual]
    simp [div_eq_mul_inv]
    ring
  rw [eSourcePointEval_of_basis Rzero c hdecomposition x
      (eResidualW x X),
    eSourcePointEval_of_basis Rzero c hdecomposition X
      (eResidualW X x)]
  change eBasisValue
      (eBasePointEval ℂ p q (c 0))
      (eBasePointEval ℂ p q (c 1))
      (eBasePointEval ℂ p q (c 2))
      (eBasePointEval ℂ p q (c 3)) x -
    eBasisValue
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 0))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 1))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 2))
      (eBasePointEval ℂ (eP X (eResidualW X x))
        (eQ X (eResidualW X x)) (c 3)) X = _
  rw [hP, hQ, e_basis_difference_factorization]
  congr 1
  exact (ePairPointEval_thetaPolynomial
    ℂ c x X p q hpairP hpairQ).symm

theorem eInvariantPolynomialMap_first
    (R : Form ℂ) (x t : ℂ) :
    weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 0 =
      eP x (t ^ 3) := by
  simp [weightedPolynomialMap, eInvariantPolynomialMap, cubicForm,
    formX, formT, eP]

theorem eInvariantPolynomialMap_second
    (R : Form ℂ) (x t : ℂ) :
    weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 1 =
      eQ x (t ^ 3) := by
  simp [weightedPolynomialMap, eInvariantPolynomialMap, quarticForm,
    formX, formT, eQ]

theorem eInvariantPolynomialMap_third
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (x t : ℂ) :
    weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 2 =
      eSourcePointEval x (t ^ 3) Rzero := by
  change MvPolynomial.eval ![x, t] R = _
  rw [← hdescent]
  exact eSourceCubeSubstitutionForm_pointEval Rzero x t

/-- Cube roots of the two residual coordinates give equal values under the
invariant initial map. -/
theorem eInvariantPolynomialMap_values_eq
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (x X t T : ℂ)
    (ht : t ^ 3 = eResidualW x X)
    (hT : T ^ 3 = eResidualW X x)
    (htheta : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0) :
    weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) =
      weightedPolynomialMap (eInvariantPolynomialMap R) (X, T) := by
  funext i
  fin_cases i
  · change weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 0 =
      weightedPolynomialMap (eInvariantPolynomialMap R) (X, T) 0
    rw [eInvariantPolynomialMap_first, eInvariantPolynomialMap_first,
      ht, hT]
    exact (e_residual_parametrizes_fibre x X).1
  · change weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 1 =
      weightedPolynomialMap (eInvariantPolynomialMap R) (X, T) 1
    rw [eInvariantPolynomialMap_second, eInvariantPolynomialMap_second,
      ht, hT]
    exact (e_residual_parametrizes_fibre x X).2
  · change weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) 2 =
      weightedPolynomialMap (eInvariantPolynomialMap R) (X, T) 2
    rw [eInvariantPolynomialMap_third Rzero R hdescent,
      eInvariantPolynomialMap_third Rzero R hdescent, ht, hT]
    exact eSourcePointEval_eq_of_theta_zero
      Rzero c hdecomposition x X htheta

/-- The invariant initial coordinates have ordinary degrees three, four,
and `N`. -/
theorem eInvariantPolynomialMap_isWeightedHomogeneous
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N) (i : Fin 3) :
    (eInvariantPolynomialMap R i).IsWeightedHomogeneous ![1, 1]
      (eInvariantDegrees N i) := by
  have hx : (formX : Form ℂ).IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [formX] using
      MvPolynomial.isWeightedHomogeneous_X ℂ ![1, 1] (0 : Fin 2)
  have ht : (formT : Form ℂ).IsWeightedHomogeneous ![1, 1] 1 := by
    simpa [formT] using
      MvPolynomial.isWeightedHomogeneous_X ℂ ![1, 1] (1 : Fin 2)
  fin_cases i
  · change (cubicForm 0 3 : Form ℂ).IsWeightedHomogeneous ![1, 1] 3
    have h1 := hx.pow 3
    have h2 := (hx.mul (ht.pow 2)).C_mul (0 : ℂ)
    have h3 := (ht.pow 3).C_mul (3 : ℂ)
    simpa [cubicForm, nsmul_eq_mul] using (h1.add h2).add h3
  · change (quarticForm 1 0 0 4 0 : Form ℂ).IsWeightedHomogeneous
      ![1, 1] 4
    have h4 := (hx.pow 4).C_mul (1 : ℂ)
    have h31 := ((hx.pow 3).C_mul (0 : ℂ)).mul ht
    have h22 := ((hx.pow 2).C_mul (0 : ℂ)).mul (ht.pow 2)
    have h13 := (hx.C_mul (4 : ℂ)).mul (ht.pow 3)
    have h04 := (ht.pow 4).C_mul (0 : ℂ)
    simpa [quarticForm, nsmul_eq_mul] using
      (((h4.add h31).add h22).add h13).add h04
  · change R.IsWeightedHomogeneous ![1, 1] N
    change R.IsWeightedHomogeneous 1 N at hR
    have hw : (![1, 1] : Fin 2 → ℕ) = 1 := by
      funext j
      fin_cases j <;> rfl
    rwa [hw]

/-- Algebraic and isolation data for one invariant `E` collision. -/
structure EInvariantInitialCollisionCertificate
    (R : Form ℂ) (c : Fin 4 → EBaseRing ℂ) (n : ℕ) where
  x : ℂ
  X : ℂ
  t : ℂ
  T : ℂ
  projective_nonzero : x ≠ 0 ∨ X ≠ 0
  x_ne_X : x ≠ X
  theta_zero : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0
  t_cube : t ^ 3 = eResidualW x X
  T_cube : T ^ 3 = eResidualW X x
  sourcePoints_ne : ((x, t) : ℂ × ℂ) ≠ (X, T)
  values_eq :
    weightedPolynomialMap (eInvariantPolynomialMap R) (x, t) =
      weightedPolynomialMap (eInvariantPolynomialMap R) (X, T)
  chartRoot : ℂ
  chartRoot_isRoot :
    (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot chartRoot
  chartRoot_ne_one : chartRoot ≠ 1
  chartPolynomial_ne_zero :
    ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0
  chartRootSet_finite : Set.Finite {u : ℂ |
    (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u}
  chartRootSet_discrete : IsDiscrete {u : ℂ |
    (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot u}

/-- A nonzero residual projective zero lifts to two distinct source points
with equal invariant initial values.  Its chart root is isolated even when
the supplied projective zero is at infinity or has positive multiplicity. -/
theorem exists_eInvariantInitialCollisionCertificate
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hthetaNe : eThetaPolynomial ℂ c ≠ 0)
    (x X : ℂ) (hnonzero : x ≠ 0 ∨ X ≠ 0)
    (htheta : ePairPointEval ℂ x X (eThetaPolynomial ℂ c) = 0)
    (hne : x ≠ X) :
    Nonempty (EInvariantInitialCollisionCertificate R c n) := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq
    (eResidualW x X) (by norm_num : 0 < 3)
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq
    (eResidualW X x) (by norm_num : 0 < 3)
  obtain ⟨z, hz, hzone, hfinite, hdiscrete⟩ :=
    exists_eThetaPolynomial_isolated_affine_root c n hhomogeneous
      hthetaNe x X hnonzero htheta hne
  have hsource : ((x, t) : ℂ × ℂ) ≠ (X, T) := by
    intro hpair
    exact hne (congrArg Prod.fst hpair)
  exact ⟨{
    x := x
    X := X
    t := t
    T := T
    projective_nonzero := hnonzero
    x_ne_X := hne
    theta_zero := htheta
    t_cube := ht
    T_cube := hT
    sourcePoints_ne := hsource
    values_eq := eInvariantPolynomialMap_values_eq
      Rzero R c hdescent hdecomposition x X t T ht hT htheta
    chartRoot := z
    chartRoot_isRoot := hz
    chartRoot_ne_one := hzone
    chartPolynomial_ne_zero :=
      ePairDehomogenize_ne_zero hhomogeneous hthetaNe
    chartRootSet_finite := hfinite
    chartRootSet_discrete := hdiscrete
  }⟩

/-- The invariant `E` branch outside the base ring has an actual collision
of the homogeneous initial map and an isolated residual chart root. -/
theorem exists_e_invariant_initial_collision
    {omega : ℂ} (R : Form ℂ) (N : ℕ)
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R)
    (hnotbase : ∀ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R →
        Rzero ∉ Set.range (eBaseToSource ℂ)) :
    ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
      Nonempty (EInvariantInitialCollisionCertificate R c (N - 1)) := by
  obtain ⟨Rzero, c, hdescent, hdecomposition, hthetaHomogeneous,
      _, hthetaNe, x, X, hnonzero, htheta, hne⟩ :=
    exists_e_invariant_nonzero_residual_off_diagonal_projective_zero
      R N homega hhomogeneous hinvariant hdiv hnotbase
  exact ⟨Rzero, c, hdescent, hdecomposition,
    exists_eInvariantInitialCollisionCertificate
      Rzero R c (N - 1) hdescent hdecomposition hthetaHomogeneous
        hthetaNe x X hnonzero htheta hne⟩

end OnLeConjecture.DThree
