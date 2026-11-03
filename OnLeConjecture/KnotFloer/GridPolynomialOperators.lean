/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridWeightedCurvature
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficient operators of a polynomially weighted grid differential

For polynomial square weights, extract each coefficient of the actual rectangle matrix.
The curvature identity yields a convolution identity for these linear operators. Its first
and second coefficients give the chain-map and homotopy equations needed by a polynomial
deformation, without imposing a degree bound on the square weights or rectangle entries.
The coefficient calculation reuses Mathlib's `Polynomial.coeff_mul`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} {S : Type*} [CommSemiring S]

/-- Applying a scalar homomorphism commutes with every actual weighted rectangle count. -/
theorem squareWeightedCoefficient_map {T : Type*} [CommSemiring T]
    (f : S →+* T) (w : Fin n × Fin n → S) (x y : GridState n) :
    f (squareWeightedCoefficient w x y) = squareWeightedCoefficient (fun p => f (w p)) x y := by
  simp [squareWeightedCoefficient, squareWeight, map_sum, map_prod]

/-- The coefficient-k rectangle count on a grid-state generator. -/
noncomputable def polynomialCoefficientOnGenerator
    (w : Fin n × Fin n → Polynomial S) (k : ℕ) (x : GridState n) : GridState n →₀ S :=
  ∑ y : GridState n, Finsupp.single y ((squareWeightedCoefficient w x y).coeff k)

@[simp]
theorem polynomialCoefficientOnGenerator_apply
    (w : Fin n × Fin n → Polynomial S) (k : ℕ) (x y : GridState n) :
    polynomialCoefficientOnGenerator w k x y = (squareWeightedCoefficient w x y).coeff k := by
  classical
  rw [polynomialCoefficientOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- Extract coefficient k of every matrix entry of the weighted rectangle differential. -/
noncomputable def polynomialCoefficientOperator (w : Fin n × Fin n → Polynomial S) (k : ℕ) :
    (GridState n →₀ S) →ₗ[S] (GridState n →₀ S) :=
  Finsupp.lsum S fun x : GridState n =>
    (LinearMap.id : S →ₗ[S] S).smulRight (polynomialCoefficientOnGenerator w k x)

@[simp]
theorem polynomialCoefficientOperator_single (w : Fin n × Fin n → Polynomial S)
    (k : ℕ) (x : GridState n) :
    polynomialCoefficientOperator w k (Finsupp.single x 1) =
      polynomialCoefficientOnGenerator w k x := by
  rw [polynomialCoefficientOperator, Finsupp.lsum_single]
  simp

/-- Evaluation of a coefficient operator on an arbitrary chain. -/
theorem polynomialCoefficientOperator_apply_apply (w : Fin n × Fin n → Polynomial S)
    (k : ℕ) (c : GridState n →₀ S) (y : GridState n) :
    polynomialCoefficientOperator w k c y =
      c.sum fun x a => a * (squareWeightedCoefficient w x y).coeff k := by
  simp [polynomialCoefficientOperator, Finsupp.lsum_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, LinearMap.smulRight_apply]

/-- The zeroth operator is the full rectangle differential with constant square weights. -/
theorem polynomialCoefficientOperator_zero (w : Fin n × Fin n → Polynomial S) :
    polynomialCoefficientOperator w 0 = squareWeightedDifferential (fun p => (w p).coeff 0) := by
  classical
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  apply Finsupp.ext
  intro y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, polynomialCoefficientOperator_single,
    squareWeightedDifferential_single, polynomialCoefficientOnGenerator_apply,
    squareWeightedOnGenerator_apply]
  exact squareWeightedCoefficient_map Polynomial.constantCoeff w x y

/-- Composition of coefficient operators is the convolution of their matrix entries. -/
theorem polynomialCoefficientOperator_comp_single_apply
    (w : Fin n × Fin n → Polynomial S) (j k : ℕ) (x z : GridState n) :
    polynomialCoefficientOperator w k
        (polynomialCoefficientOperator w j (Finsupp.single x 1)) z =
      ∑ y : GridState n, (squareWeightedCoefficient w x y).coeff j *
        (squareWeightedCoefficient w y z).coeff k := by
  rw [polynomialCoefficientOperator_single, polynomialCoefficientOperator_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [polynomialCoefficientOnGenerator_apply]

/-- The coefficient of the actual weighted curvature identity, expressed as a matrix sum. -/
theorem polynomialCoefficient_matrix_convolution [CharP S 2]
    (w : Fin n × Fin n → Polynomial S) (k : ℕ) (x z : GridState n) :
    ∑ y : GridState n, ∑ p ∈ Finset.antidiagonal k,
        (squareWeightedCoefficient w x y).coeff p.1 *
          (squareWeightedCoefficient w y z).coeff p.2 =
      if z = x then (squareWeightCurvature w).coeff k else 0 := by
  classical
  have h := congrArg (fun c : GridState n →₀ Polynomial S => c z)
    (squareWeightedDifferential_sq_apply w (Finsupp.single x 1))
  rw [squareWeightedDifferential_single, squareWeightedDifferential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _] at h
  simp only [squareWeightedOnGenerator_apply, Finsupp.smul_apply, smul_eq_mul] at h
  have h' : ∑ y : GridState n, squareWeightedCoefficient w x y *
      squareWeightedCoefficient w y z = if z = x then squareWeightCurvature w else 0 := by
    by_cases hzx : z = x
    · subst z
      simpa only [Finsupp.single_eq_same, mul_one, if_true] using h
    · simpa only [Finsupp.single_eq_of_ne hzx, mul_zero, if_neg hzx] using h
  have hc := congrArg (fun p : Polynomial S => p.coeff k) h'
  by_cases hzx : z = x <;>
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul, hzx, if_true, if_false,
      Polynomial.coeff_zero] using hc

/-- Every coefficient of the square is the corresponding curvature coefficient times identity. -/
theorem polynomialCoefficientOperator_convolution [CharP S 2]
    (w : Fin n × Fin n → Polynomial S) (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k,
        polynomialCoefficientOperator w p.2 ∘ₗ polynomialCoefficientOperator w p.1 =
      (squareWeightCurvature w).coeff k •
        (LinearMap.id : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S)) := by
  classical
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  apply Finsupp.ext
  intro z
  simp only [Finsupp.lsingle_apply, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    LinearMap.comp_apply, polynomialCoefficientOperator_comp_single_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, polynomialCoefficient_matrix_convolution]
  by_cases hzx : z = x
  · subst z
    simp
  · simp [hzx]

/-- The first coefficient equation is the chain-map equation with its explicit curvature term. -/
theorem polynomialCoefficientOperator_one_identity [CharP S 2]
    (w : Fin n × Fin n → Polynomial S) :
    polynomialCoefficientOperator w 0 ∘ₗ polynomialCoefficientOperator w 1 +
        polynomialCoefficientOperator w 1 ∘ₗ polynomialCoefficientOperator w 0 =
      (squareWeightCurvature w).coeff 1 •
        (LinearMap.id : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S)) := by
  have h := polynomialCoefficientOperator_convolution w 1
  simpa [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, add_comm] using h

/-- The second coefficient equation gives the square of the first operator up to the
explicit degree-two homotopy terms and curvature coefficient. -/
theorem polynomialCoefficientOperator_two_identity [CharP S 2]
    (w : Fin n × Fin n → Polynomial S) :
    polynomialCoefficientOperator w 1 ∘ₗ polynomialCoefficientOperator w 1 +
        polynomialCoefficientOperator w 0 ∘ₗ polynomialCoefficientOperator w 2 +
        polynomialCoefficientOperator w 2 ∘ₗ polynomialCoefficientOperator w 0 =
      (squareWeightCurvature w).coeff 2 •
        (LinearMap.id : (GridState n →₀ S) →ₗ[S] (GridState n →₀ S)) := by
  have h := polynomialCoefficientOperator_convolution w 2
  simpa [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    add_comm, add_left_comm, add_assoc] using h

end OnLeConjecture.KnotFloer.GridFull
