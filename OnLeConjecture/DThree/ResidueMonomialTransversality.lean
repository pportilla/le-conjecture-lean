/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueMonomialCollision
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Transversality of the monomial residual collisions

This file defines the three variable difference maps in the affine chart in
which the first source point has second coordinate one.  It computes their
Fréchet derivatives at a collision with second chart coordinate one.  The
determinant is the product of the transverse determinant and the derivative of
the third difference.
-/

public section

namespace OnLeConjecture.DThree

/-- The difference of the two `E` values at `(x, 1)` and `(X, Y)`. -/
@[expose]
noncomputable def eResidueAffineDifferenceMap
    (a M : ℕ) (c : ℂ) (p : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![p 0 ^ 3 + 3 - (p 1 ^ 3 + 3 * p 2 ^ (3 * a)),
    p 0 ^ 4 + 4 * p 0 -
      (p 1 ^ 4 + 4 * p 1 * p 2 ^ (3 * a)),
    c - c * p 2 ^ M]

/-- The difference of the two `H` values at `(x, 1)` and `(X, Y)`. -/
@[expose]
noncomputable def hResidueAffineDifferenceMap
    (a M : ℕ) (c : ℂ) (p : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![p 0 ^ 3 + 3 * p 0 -
      (p 1 ^ 3 + 3 * p 1 * p 2 ^ (2 * a)),
    p 0 ^ 4 + 4 * p 0 ^ 2 + 2 -
      (p 1 ^ 4 + 4 * p 1 ^ 2 * p 2 ^ (2 * a) +
        2 * p 2 ^ (4 * a)),
    c - c * p 2 ^ M]

/-- The Jacobian matrix of the `E` difference map at `(x, X, 1)`. -/
@[expose]
noncomputable def eResidueAffineJacobian
    (a M : ℕ) (c x X : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 * x ^ 2, -(3 * X ^ 2), -(9 * (a : ℂ));
    4 * x ^ 3 + 4, -(4 * X ^ 3 + 4), -(4 * X * (3 * a : ℕ));
    0, 0, -c * (M : ℂ)]

/-- The Jacobian matrix of the `H` difference map at `(x, X, 1)`. -/
@[expose]
noncomputable def hResidueAffineJacobian
    (a M : ℕ) (c x X : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3 * x ^ 2 + 3, -(3 * X ^ 2 + 3), -(3 * X * (2 * a : ℕ));
    4 * x ^ 3 + 8 * x, -(4 * X ^ 3 + 8 * X),
      -(4 * X ^ 2 * (2 * a : ℕ) + 2 * (4 * a : ℕ));
    0, 0, -c * (M : ℂ)]

/-- The continuous linear map represented by the `E` Jacobian. -/
@[expose]
noncomputable def eResidueAffineDerivative
    (a M : ℕ) (c x X : ℂ) : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  (Matrix.toLin' (eResidueAffineJacobian a M c x X)).toContinuousLinearMap

/-- The continuous linear map represented by the `H` Jacobian. -/
@[expose]
noncomputable def hResidueAffineDerivative
    (a M : ℕ) (c x X : ℂ) : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  (Matrix.toLin' (hResidueAffineJacobian a M c x X)).toContinuousLinearMap

theorem hasStrictFDerivAt_eResidueAffineDifferenceMap
    (a M : ℕ) (c x X : ℂ) :
    HasStrictFDerivAt (eResidueAffineDifferenceMap a M c)
      (eResidueAffineDerivative a M c x X) ![x, X, 1] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals
    simp only [eResidueAffineDifferenceMap]
  · convert
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).pow 3).add_const 3).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).pow 3).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow (3 * a)).const_mul
            (3 : ℂ)))
      using 1 <;>
    ext v <;>
    simp [eResidueAffineDerivative, eResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ]
    all_goals ring
  · convert
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).pow 4).add
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).const_mul
          (4 : ℂ))).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).pow 4).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow
              (3 * a))).const_mul (4 : ℂ)))
      using 1 <;>
    ext v <;>
    simp [eResidueAffineDerivative, eResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ] <;>
    ring
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) c ![x, X, 1]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow M).const_mul c)
      using 1 <;>
    ext v <;>
    simp [eResidueAffineDerivative, eResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem hasStrictFDerivAt_hResidueAffineDifferenceMap
    (a M : ℕ) (c x X : ℂ) :
    HasStrictFDerivAt (hResidueAffineDifferenceMap a M c)
      (hResidueAffineDerivative a M c x X) ![x, X, 1] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals
    simp only [hResidueAffineDifferenceMap]
  · convert
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).pow 3).add
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).const_mul
          (3 : ℂ))).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).pow 3).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow
              (2 * a))).const_mul (3 : ℂ)))
      using 1 <;>
    ext v <;>
    simp [hResidueAffineDerivative, hResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ] <;>
    ring
  · convert
      ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).pow 4).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 3) ![x, X, 1]).pow 2).const_mul
          (4 : ℂ))).add_const 2).sub
        ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).pow 4).add
          ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 3) ![x, X, 1]).pow 2).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow
              (2 * a))).const_mul (4 : ℂ))).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow
            (4 * a)).const_mul (2 : ℂ)))
      using 1 <;>
    ext v <;>
    simp [hResidueAffineDerivative, hResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ] <;>
    ring
  · convert
      (hasStrictFDerivAt_const (𝕜 := ℂ) c ![x, X, 1]).sub
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (2 : Fin 3) ![x, X, 1]).pow M).const_mul c)
      using 1 <;>
    ext v <;>
    simp [hResidueAffineDerivative, hResidueAffineJacobian, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ]
    all_goals ring

/-- The determinant of the `E` Jacobian factors into its transverse and third
coordinate factors. -/
theorem det_eResidueAffineJacobian
    (a M : ℕ) (c x X : ℂ) :
    Matrix.det (eResidueAffineJacobian a M c x X) =
      eResidueTransverseDeterminant x X * residueThirdDerivative M c := by
  simp [eResidueAffineJacobian, eResidueTransverseDeterminant,
    residueThirdDerivative, Matrix.det_fin_three]
  ring

/-- The determinant of the `H` Jacobian factors into its transverse and third
coordinate factors. -/
theorem det_hResidueAffineJacobian
    (a M : ℕ) (c x X : ℂ) :
    Matrix.det (hResidueAffineJacobian a M c x X) =
      hResidueTransverseDeterminant x X * residueThirdDerivative M c := by
  simp [hResidueAffineJacobian, hResidueTransverseDeterminant,
    residueThirdDerivative, Matrix.det_fin_three]
  ring

theorem det_eResidueAffineDerivative
    (a M : ℕ) (c x X : ℂ) :
    (eResidueAffineDerivative a M c x X).det =
      eResidueTransverseDeterminant x X * residueThirdDerivative M c := by
  simpa [eResidueAffineDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using det_eResidueAffineJacobian a M c x X

theorem det_hResidueAffineDerivative
    (a M : ℕ) (c x X : ℂ) :
    (hResidueAffineDerivative a M c x X).det =
      hResidueTransverseDeterminant x X * residueThirdDerivative M c := by
  simpa [hResidueAffineDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using det_hResidueAffineJacobian a M c x X

/-- The invertible derivative of the `E` difference map. -/
@[expose]
noncomputable def eResidueAffineDerivativeEquiv
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    (Fin 3 → ℂ) ≃L[ℂ] (Fin 3 → ℂ) :=
  (eResidueAffineDerivative a M c x X).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_eResidueAffineDerivative]
    exact mul_ne_zero htransverse hthird

/-- The invertible derivative of the `H` difference map. -/
@[expose]
noncomputable def hResidueAffineDerivativeEquiv
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    (Fin 3 → ℂ) ≃L[ℂ] (Fin 3 → ℂ) :=
  (hResidueAffineDerivative a M c x X).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_hResidueAffineDerivative]
    exact mul_ne_zero htransverse hthird

theorem hasStrictFDerivAt_eResidueAffineDifferenceMap_equiv
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    HasStrictFDerivAt (eResidueAffineDifferenceMap a M c)
      (eResidueAffineDerivativeEquiv a M c x X htransverse hthird :
        (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) ![x, X, 1] := by
  simpa [eResidueAffineDerivativeEquiv] using
    hasStrictFDerivAt_eResidueAffineDifferenceMap a M c x X

theorem hasStrictFDerivAt_hResidueAffineDifferenceMap_equiv
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    HasStrictFDerivAt (hResidueAffineDifferenceMap a M c)
      (hResidueAffineDerivativeEquiv a M c x X htransverse hthird :
        (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) ![x, X, 1] := by
  simpa [hResidueAffineDerivativeEquiv] using
    hasStrictFDerivAt_hResidueAffineDifferenceMap a M c x X

theorem eResidueAffineDerivative_bijective
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    Function.Bijective (eResidueAffineDerivative a M c x X) := by
  constructor
  · intro u v huv
    apply (eResidueAffineDerivativeEquiv a M c x X htransverse hthird).injective
    simpa [eResidueAffineDerivativeEquiv] using huv
  · intro v
    obtain ⟨u, hu⟩ :=
      (eResidueAffineDerivativeEquiv a M c x X htransverse hthird).surjective v
    exact ⟨u, by simpa [eResidueAffineDerivativeEquiv] using hu⟩

theorem hResidueAffineDerivative_bijective
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    Function.Bijective (hResidueAffineDerivative a M c x X) := by
  constructor
  · intro u v huv
    apply (hResidueAffineDerivativeEquiv a M c x X htransverse hthird).injective
    simpa [hResidueAffineDerivativeEquiv] using huv
  · intro v
    obtain ⟨u, hu⟩ :=
      (hResidueAffineDerivativeEquiv a M c x X htransverse hthird).surjective v
    exact ⟨u, by simpa [hResidueAffineDerivativeEquiv] using hu⟩

/-- The local homeomorphism supplied by the inverse function theorem for the
`E` difference map. -/
@[expose]
noncomputable def eResidueAffineLocalHomeomorph
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (Fin 3 → ℂ) :=
  (hasStrictFDerivAt_eResidueAffineDifferenceMap_equiv
    a M c x X htransverse hthird).toOpenPartialHomeomorph
      (eResidueAffineDifferenceMap a M c)

/-- The local homeomorphism supplied by the inverse function theorem for the
`H` difference map. -/
@[expose]
noncomputable def hResidueAffineLocalHomeomorph
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (Fin 3 → ℂ) :=
  (hasStrictFDerivAt_hResidueAffineDifferenceMap_equiv
    a M c x X htransverse hthird).toOpenPartialHomeomorph
      (hResidueAffineDifferenceMap a M c)

@[simp]
theorem eResidueAffineLocalHomeomorph_coe
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    (eResidueAffineLocalHomeomorph a M c x X htransverse hthird :
      (Fin 3 → ℂ) → (Fin 3 → ℂ)) =
      eResidueAffineDifferenceMap a M c :=
  rfl

@[simp]
theorem hResidueAffineLocalHomeomorph_coe
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    (hResidueAffineLocalHomeomorph a M c x X htransverse hthird :
      (Fin 3 → ℂ) → (Fin 3 → ℂ)) =
      hResidueAffineDifferenceMap a M c :=
  rfl

theorem eResidueAffineCollision_mem_localHomeomorph_source
    (a M : ℕ) (c x X : ℂ)
    (htransverse : eResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    ![x, X, 1] ∈
      (eResidueAffineLocalHomeomorph a M c x X htransverse hthird).source :=
  (hasStrictFDerivAt_eResidueAffineDifferenceMap_equiv
    a M c x X htransverse hthird).mem_toOpenPartialHomeomorph_source

theorem hResidueAffineCollision_mem_localHomeomorph_source
    (a M : ℕ) (c x X : ℂ)
    (htransverse : hResidueTransverseDeterminant x X ≠ 0)
    (hthird : residueThirdDerivative M c ≠ 0) :
    ![x, X, 1] ∈
      (hResidueAffineLocalHomeomorph a M c x X htransverse hthird).source :=
  (hasStrictFDerivAt_hResidueAffineDifferenceMap_equiv
    a M c x X htransverse hthird).mem_toOpenPartialHomeomorph_source

/-- A collision in the affine difference map together with the two nonzero
factors in its Jacobian determinant. -/
structure ResidueAffineCollisionCertificate
    (M : ℕ) (c : ℂ)
    (differenceMap : (Fin 3 → ℂ) → (Fin 3 → ℂ))
    (transverseDeterminant : ℂ → ℂ → ℂ) where
  firstCoordinate : ℂ
  secondCoordinate : ℂ
  coordinates_ne : firstCoordinate ≠ secondCoordinate
  difference_eq_zero :
    differenceMap ![firstCoordinate, secondCoordinate, 1] = 0
  transverseDeterminant_ne_zero :
    transverseDeterminant firstCoordinate secondCoordinate ≠ 0
  thirdDerivative_ne_zero : residueThirdDerivative M c ≠ 0

theorem residueThirdDerivative_ne_zero
    (M : ℕ) (c : ℂ) (hM : 0 < M) (hc : c ≠ 0) :
    residueThirdDerivative M c ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr hc) (Nat.cast_ne_zero.mpr hM.ne')

/-- The explicit `E` collision is a regular zero of its affine difference
map. -/
theorem exists_eResidueAffineCollisionCertificate
    (a M : ℕ) (c : ℂ) (hM : 0 < M) (hc : c ≠ 0) :
    Nonempty
      (ResidueAffineCollisionCertificate M c
        (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant) := by
  let omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hprimitive : IsPrimitiveRoot omega 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have homegaCube : omega ^ 3 = 1 := hprimitive.pow_eq_one
  have homegaOne : omega ≠ 1 := hprimitive.ne_one (by norm_num)
  have homegaSq : omega ^ 2 ≠ 1 := by
    intro hsq
    have hdvd : 3 ∣ 2 := (hprimitive.pow_eq_one_iff_dvd 2).mp hsq
    norm_num at hdvd
  obtain ⟨x, hxCube⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-4 : ℂ) (by norm_num : 0 < 3)
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by norm_num)] at hxCube
    norm_num at hxCube
  have hcoordinates : x ≠ omega * x := by
    intro h
    have : (1 - omega) * x = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp this with hone | hx0
    · exact homegaOne (sub_eq_zero.mp hone).symm
    · exact hx hx0
  have homegaFourth : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [homegaCube, one_mul]
  have hxFourth : x ^ 4 = -4 * x := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = -4 * x := by
        rw [hxCube]
        ring
  have hdifference :
      eResidueAffineDifferenceMap a M c ![x, omega * x, 1] = 0 := by
    funext i
    fin_cases i
    · simp [eResidueAffineDifferenceMap, mul_pow, homegaCube]
    · simp [eResidueAffineDifferenceMap, mul_pow, homegaFourth, hxFourth]
      ring
    · simp [eResidueAffineDifferenceMap]
  have hdetFormula :
      eResidueTransverseDeterminant x (omega * x) =
        36 * x ^ 2 * (1 - omega ^ 2) := by
    simp only [eResidueTransverseDeterminant]
    rw [mul_pow, homegaCube, one_mul]
    rw [show (omega * x) ^ 2 = omega ^ 2 * x ^ 2 by rw [mul_pow]]
    rw [hxCube]
    ring
  have hdet : eResidueTransverseDeterminant x (omega * x) ≠ 0 := by
    rw [hdetFormula]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx))
      (sub_ne_zero.mpr homegaSq.symm)
  exact ⟨{
    firstCoordinate := x
    secondCoordinate := omega * x
    coordinates_ne := hcoordinates
    difference_eq_zero := hdifference
    transverseDeterminant_ne_zero := hdet
    thirdDerivative_ne_zero := residueThirdDerivative_ne_zero M c hM hc
  }⟩

/-- The explicit `H` collision is a regular zero of its affine difference
map. -/
theorem exists_hResidueAffineCollisionCertificate
    (a M : ℕ) (c : ℂ) (hM : 0 < M) (hc : c ≠ 0) :
    Nonempty
      (ResidueAffineCollisionCertificate M c
        (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant) := by
  obtain ⟨x, hxSquare⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (by norm_num : 0 < 2)
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by norm_num)] at hxSquare
    norm_num at hxSquare
  have hcoordinates : x ≠ -x := by
    intro h
    have : (2 : ℂ) * x = 0 := by
      linear_combination h
    exact hx ((mul_eq_zero.mp this).resolve_left (by norm_num))
  have hxThird : x ^ 3 = -3 * x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = -3 * x := by
        rw [hxSquare]
        ring
  have hxFifth : x ^ 5 = 9 * x := by
    calc
      x ^ 5 = x * (x ^ 2) ^ 2 := by ring
      _ = 9 * x := by
        rw [hxSquare]
        norm_num
        ring
  have hdifference :
      hResidueAffineDifferenceMap a M c ![x, -x, 1] = 0 := by
    funext i
    fin_cases i
    · change x ^ 3 + 3 * x - ((-x) ^ 3 + 3 * (-x) * 1 ^ (2 * a)) = 0
      rw [one_pow, mul_one]
      rw [show (-x) ^ 3 = -(x ^ 3) by ring, hxThird]
      ring
    · simp [hResidueAffineDifferenceMap]
      ring
    · simp [hResidueAffineDifferenceMap]
  have hdetFormula :
      hResidueTransverseDeterminant x (-x) = 48 * x := by
    simp only [hResidueTransverseDeterminant]
    calc
      (3 * x ^ 2 + 3) * (-(4 * (-x) ^ 3 + 8 * (-x))) -
          (-(3 * (-x) ^ 2 + 3)) * (4 * x ^ 3 + 8 * x) =
          48 * x + 72 * x ^ 3 + 24 * x ^ 5 := by ring
      _ = 48 * x := by
        rw [hxThird, hxFifth]
        ring
  have hdet : hResidueTransverseDeterminant x (-x) ≠ 0 := by
    rw [hdetFormula]
    exact mul_ne_zero (by norm_num) hx
  exact ⟨{
    firstCoordinate := x
    secondCoordinate := -x
    coordinates_ne := hcoordinates
    difference_eq_zero := hdifference
    transverseDeterminant_ne_zero := hdet
    thirdDerivative_ne_zero := residueThirdDerivative_ne_zero M c hM hc
  }⟩

theorem eResidueAffineDerivative_bijective_of_certificate
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant) :
    Function.Bijective
      (eResidueAffineDerivative a M c C.firstCoordinate C.secondCoordinate) :=
  eResidueAffineDerivative_bijective a M c C.firstCoordinate C.secondCoordinate
    C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero

theorem hResidueAffineDerivative_bijective_of_certificate
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant) :
    Function.Bijective
      (hResidueAffineDerivative a M c C.firstCoordinate C.secondCoordinate) :=
  hResidueAffineDerivative_bijective a M c C.firstCoordinate C.secondCoordinate
    C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero

/-- The local homeomorphism at an `E` collision certificate. -/
@[expose]
noncomputable def eResidueAffineCertificateLocalHomeomorph
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (Fin 3 → ℂ) :=
  eResidueAffineLocalHomeomorph a M c C.firstCoordinate C.secondCoordinate
    C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero

/-- The local homeomorphism at an `H` collision certificate. -/
@[expose]
noncomputable def hResidueAffineCertificateLocalHomeomorph
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant) :
    OpenPartialHomeomorph (Fin 3 → ℂ) (Fin 3 → ℂ) :=
  hResidueAffineLocalHomeomorph a M c C.firstCoordinate C.secondCoordinate
    C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero

theorem eResidueAffineCertificate_inverse_zero
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant) :
    (eResidueAffineCertificateLocalHomeomorph a M c C).symm 0 =
      ![C.firstCoordinate, C.secondCoordinate, 1] := by
  rw [← C.difference_eq_zero]
  exact (eResidueAffineCertificateLocalHomeomorph a M c C).left_inv
    (eResidueAffineCollision_mem_localHomeomorph_source
      a M c C.firstCoordinate C.secondCoordinate
        C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero)

theorem hResidueAffineCertificate_inverse_zero
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant) :
    (hResidueAffineCertificateLocalHomeomorph a M c C).symm 0 =
      ![C.firstCoordinate, C.secondCoordinate, 1] := by
  rw [← C.difference_eq_zero]
  exact (hResidueAffineCertificateLocalHomeomorph a M c C).left_inv
    (hResidueAffineCollision_mem_localHomeomorph_source
      a M c C.firstCoordinate C.secondCoordinate
        C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero)

end OnLeConjecture.DThree
