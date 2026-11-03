/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProjectiveDifferencePoleBoundary

/-!
# Projective zeros of the homogeneous H difference

The affine root, parameter infinity, and the two finite boundary factors of
the pole profile all give a zero of the weighted homogeneous fibre
difference. Over an algebraically closed field, square roots lift this zero
from the variables `w = t ^ 2` and `W = T ^ 2` to the original homogeneous
variables.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Distinct ordered pairs define a nonzero quadruple. -/
theorem h_total_coordinates_nonzero_of_pair_ne
    {x w X W : K} (hdistinct : x ≠ X ∨ w ≠ W) :
    x ≠ 0 ∨ w ≠ 0 ∨ X ≠ 0 ∨ W ≠ 0 := by
  by_contra hzero
  simp only [not_or, not_ne_iff] at hzero
  rcases hzero with ⟨hx, hw, hX, hW⟩
  rcases hdistinct with hxx | hww
  · exact hxx (hx.trans hX.symm)
  · exact hww (hw.trans hW.symm)

/-- The projective zero alternative, including its three boundary loci,
produces a distinct weighted fibre pair. -/
theorem exists_h_weighted_projective_difference_zero
    [IsAlgClosed K]
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (hdifferenceA :
      hFiniteOrderAt a (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceB :
      hFiniteOrderAt b (hConicDifference R) =
        WithZero.exp (kTwo : ℤ)) :
    ∃ x w X W : K,
      (x ≠ 0 ∨ w ≠ 0 ∨ X ≠ 0 ∨ W ≠ 0) ∧
      (x ≠ X ∨ w ≠ W) ∧
      hP x w = hP X W ∧
      hQ x w = hQ X W ∧
      hFormEval x w R = hFormEval X W R := by
  rcases exists_hConicDifference_collision_or_boundary
      N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
        hLambdaP hLambdaQ ha hb hab hdifferenceA hdifferenceB with
    hcollision | ⟨p, hp, hpDegree, hrepresentation, hboundary⟩
  · rcases hcollision with
      ⟨x, w, X, W, hx, hPfiber, hQfiber, hRfiber⟩
    have hdistinct : x ≠ X ∨ w ≠ W := Or.inl hx
    exact ⟨x, w, X, W,
      h_total_coordinates_nonzero_of_pair_ne hdistinct,
      hdistinct, hPfiber, hQfiber, hRfiber⟩
  · rcases hboundary with hpole | ⟨z, hdenominator, hroot⟩
    · obtain ⟨w, W, hwW, hPfiber, hQfiber, hRfiber⟩ :=
        exists_h_projective_difference_zero_at_pole_boundary
          N R hR p hrepresentation hpole
      have hdistinct : (0 : K) ≠ 0 ∨ w ≠ W := Or.inr hwW
      exact ⟨0, w, 0, W,
        h_total_coordinates_nonzero_of_pair_ne hdistinct,
        hdistinct, hPfiber, hQfiber, hRfiber⟩
    · have hdenominatorEval :
          hConicParamDenominator (K := K).eval z = 0 :=
        hdenominator
      have hz : z ^ 2 + 2 = 0 := by
        simpa [hConicParamDenominator] using hdenominatorEval
      obtain ⟨w, X, W, hw, hX, hPfiber, hQfiber, hRfiber⟩ :=
        exists_h_projective_difference_zero_at_infinity_boundary
          N R hR p z hrepresentation hz hroot
      have hdistinct : (0 : K) ≠ X ∨ w ≠ W :=
        Or.inl (Ne.symm hX)
      exact ⟨0, w, X, W,
        h_total_coordinates_nonzero_of_pair_ne hdistinct,
        hdistinct, hPfiber, hQfiber, hRfiber⟩

/-- A weighted projective zero lifts to an off diagonal zero of the
homogeneous fibre difference in the original variables. -/
theorem exists_h_homogeneous_fibre_difference_zero
    [IsAlgClosed K]
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) K)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    {a b : K}
    (ha : a ^ 2 + 2 * a + 4 = 0)
    (hb : b ^ 2 + 2 * b + 4 = 0)
    (hab : a ≠ b)
    (hdifferenceA :
      hFiniteOrderAt a (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceB :
      hFiniteOrderAt b (hConicDifference R) =
        WithZero.exp (kTwo : ℤ)) :
    ∃ x t X T : K,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  obtain ⟨x, w, X, W, hnonzero, hdistinct,
      hPfiber, hQfiber, hRfiber⟩ :=
    exists_h_weighted_projective_difference_zero
      N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
        hLambdaP hLambdaQ ha hb hab hdifferenceA hdifferenceB
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq w
    (by norm_num : 0 < 2)
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq W
    (by norm_num : 0 < 2)
  have hdistinctLift : x ≠ X ∨ t ≠ T := by
    rcases hdistinct with hx | hw
    · exact Or.inl hx
    · right
      intro htT
      apply hw
      rw [← ht, ← hT, htT]
  refine ⟨x, t, X, T,
    h_total_coordinates_nonzero_of_pair_ne hdistinctLift,
    hdistinctLift, ?_, ?_, ?_⟩
  · simpa only [ht, hT] using hPfiber
  · simpa only [ht, hT] using hQfiber
  · simpa only [ht, hT] using hRfiber

/-- The homogeneous fibre difference endpoint over the complex numbers at
the two specified points above `X = 1`. -/
theorem exists_complex_h_homogeneous_fibre_difference_zero
    (N kOne kTwo : ℕ) (hN : 5 ≤ N)
    (hkOne : 1 ≤ kOne) (hkTwo : 1 ≤ kTwo)
    (R LambdaP LambdaQ : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (hLambdaP :
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP)
    (hLambdaQ :
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ)
    (hdifferencePlus :
      hFiniteOrderAt hConicOneRootPlus (hConicDifference R) =
        WithZero.exp (kOne : ℤ))
    (hdifferenceMinus :
      hFiniteOrderAt hConicOneRootMinus (hConicDifference R) =
        WithZero.exp (kTwo : ℤ)) :
    ∃ x t X T : ℂ,
      (x ≠ 0 ∨ t ≠ 0 ∨ X ≠ 0 ∨ T ≠ 0) ∧
      (x ≠ X ∨ t ≠ T) ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) R = hFormEval X (T ^ 2) R := by
  exact exists_h_homogeneous_fibre_difference_zero
    N kOne kTwo hN hkOne hkTwo R LambdaP LambdaQ hR
      hLambdaP hLambdaQ h_conic_one_roots_equations.1
      h_conic_one_roots_equations.2 h_conic_one_roots_ne
      hdifferencePlus hdifferenceMinus

end OnLeConjecture.DThree
