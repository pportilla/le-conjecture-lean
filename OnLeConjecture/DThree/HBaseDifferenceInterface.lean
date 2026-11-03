/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HPositiveLocalOrders

/-!
# The base ring and the homogeneous H difference

This module defines the abstract coordinate ring `K[P,Q]` and its map to the
weighted source ring. Every element of its image has zero conic difference.

`HConicDifferenceDetectsBase R` names the converse implication for one
polynomial `R`. It is the precise algebraic assertion supplied by the
description of the residual conic as the only non diagonal component of the
general fibre product.
-/

public section

namespace OnLeConjecture.DThree

variable (K : Type*) [Field K] [CharZero K]

/-- The two abstract coordinates of the image of the homogeneous `H` pair. -/
inductive HBaseCoordinate where
  | p
  | q
  deriving DecidableEq

/-- The abstract coordinate ring `K[P,Q]`. -/
abbrev HBaseRing := MvPolynomial HBaseCoordinate K

/-- The abstract cubic coordinate. -/
@[expose]
noncomputable def hBaseP : HBaseRing K :=
  MvPolynomial.X HBaseCoordinate.p

/-- The abstract quartic coordinate. -/
@[expose]
noncomputable def hBaseQ : HBaseRing K :=
  MvPolynomial.X HBaseCoordinate.q

/-- The homomorphism from `K[P,Q]` to the weighted source ring. -/
@[expose]
noncomputable def hBaseToWeightedForm :
    HBaseRing K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval fun
    | HBaseCoordinate.p => hPForm
    | HBaseCoordinate.q => hQForm

omit [CharZero K] in
@[simp]
theorem hBaseToWeightedForm_p :
    hBaseToWeightedForm K (hBaseP K) = hPForm := by
  rw [hBaseToWeightedForm, hBaseP, MvPolynomial.aeval_X]

omit [CharZero K] in
@[simp]
theorem hBaseToWeightedForm_q :
    hBaseToWeightedForm K (hBaseQ K) = hQForm := by
  rw [hBaseToWeightedForm, hBaseQ, MvPolynomial.aeval_X]

/-- Evaluation of a base polynomial at two elements of a `K` algebra. -/
@[expose]
noncomputable def hBaseEval
    {A : Type*} [CommRing A] [Algebra K A]
    (p q : A) : HBaseRing K →ₐ[K] A :=
  MvPolynomial.aeval fun
    | HBaseCoordinate.p => p
    | HBaseCoordinate.q => q

omit [CharZero K] in
/-- Evaluation commutes with the map from the base ring to the source. -/
theorem hFormEval_hBaseToWeightedForm
    {A : Type*} [Field A] [Algebra K A]
    (x w : A) (S : HBaseRing K) :
    hFormEval x w (hBaseToWeightedForm K S) =
      hBaseEval K (hP x w) (hQ x w) S := by
  let left : HBaseRing K →ₐ[K] A :=
    (MvPolynomial.aeval fun i : Fin 2 => if i = 0 then x else w).comp
      (hBaseToWeightedForm K)
  have heq : left = hBaseEval K (hP x w) (hQ x w) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | p =>
        simp only [left, AlgHom.comp_apply, hBaseToWeightedForm,
          MvPolynomial.aeval_X, hBaseEval]
        change hFormEval x w hPForm = hP x w
        exact hFormEval_hPForm x w
    | q =>
        simp only [left, AlgHom.comp_apply, hBaseToWeightedForm,
          MvPolynomial.aeval_X, hBaseEval]
        change hFormEval x w hQForm = hQ x w
        exact hFormEval_hQForm x w
  exact AlgHom.congr_fun heq S

/-- A polynomial pulled back from `K[P,Q]` has zero conic difference. -/
theorem hConicDifference_hBaseToWeightedForm
    (S : HBaseRing K) :
    hConicDifference (hBaseToWeightedForm K S) = 0 := by
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_fibre_equations (K := K)
  rw [hConicDifference, hFirstConicPullback, hSecondConicPullback,
    hFormEval_hBaseToWeightedForm, hFormEval_hBaseToWeightedForm,
    hPfiber, hQfiber, sub_self]

/-- The conic difference detects membership in the image coordinate ring
for the specified polynomial. -/
@[expose]
def HConicDifferenceDetectsBase
    (R : MvPolynomial (Fin 2) K) : Prop :=
  hConicDifference R = 0 → R ∈ Set.range (hBaseToWeightedForm K)

omit [CharZero K] in
/-- Detection of the base ring turns exclusion from `K[P,Q]` into
nonvanishing of the conic difference. -/
theorem hConicDifference_ne_zero_of_detectsBase
    {R : MvPolynomial (Fin 2) K}
    (hdetect : HConicDifferenceDetectsBase K R)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm K)) :
    hConicDifference R ≠ 0 := by
  intro hzero
  exact hnotbase (hdetect hzero)

/-- The algebraic detection assertion, literal Jacobian divisibility, and
base ring exclusion imply an off diagonal homogeneous fibre pair. -/
theorem exists_h_homogeneous_fibre_difference_zero_of_detectsBase
    [IsAlgClosed K]
    (N : ℕ) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdetect : HConicDifferenceDetectsBase K R)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm K))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R))
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b) :
    ∃ x t X T : K,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  apply
    exists_h_homogeneous_fibre_difference_zero_of_literal_divisibilities
      N hN R hR
      (hConicDifference_ne_zero_of_detectsBase K hdetect hnotbase)
      hPdiv hQdiv ha hb hab

/-- The conditional base ring exclusion endpoint over the complex numbers. -/
theorem exists_complex_h_homogeneous_fibre_difference_zero_of_detectsBase
    (N : ℕ) (hN : 5 ≤ N)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hdetect : HConicDifferenceDetectsBase ℂ R)
    (hnotbase : R ∉ Set.range (hBaseToWeightedForm ℂ))
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ x t X T : ℂ,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  exact exists_h_homogeneous_fibre_difference_zero_of_detectsBase
    ℂ N hN R hR hdetect hnotbase hPdiv hQdiv
      h_conic_one_roots_equations.1
      h_conic_one_roots_equations.2 h_conic_one_roots_ne

end OnLeConjecture.DThree
