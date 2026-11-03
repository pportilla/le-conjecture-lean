/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineCubicNormFactorization
public import OnLeConjecture.DThree.ECNineLocalOrder

/-!
# Local norm factorization at the C9 point

This file factors the pullback of the rank nine unit chart norm into nine
analytic evaluations. For a hard form, the nine factors have the orders of
the three explicit analytic parametrizations, each repeated three times.
The local base coordinate is ramified with order three, which identifies the
sum of the three parametrization orders with the root multiplicity of the norm
at `X = 1`.

The final statement concerns the explicit parametrizations constructed in
`ECNineLocalOrder`. It does not identify their orders with a scheme theoretic
intersection multiplicity.
-/

public section
noncomputable section

namespace OnLeConjecture.DThree
open OnLeConjecture.Analytic
open _root_.Polynomial Module

namespace Germ

/-- Evaluation of the unit chart base at the local coordinate
`X = 1 + s(t^3)`. -/
noncomputable def eCNineUnitLocalBaseEval
    (s : Analytic.Germ 1) : ECNineUnitBase →+* Analytic.Germ 1 :=
  Polynomial.eval₂RingHom (Analytic.Germ.constRingHom 1)
    (1 + DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s)

@[simp] theorem eCNineUnitLocalBaseEval_C
    (s : Analytic.Germ 1) (c : ℂ) :
    eCNineUnitLocalBaseEval s (Polynomial.C c) =
      Analytic.Germ.constRingHom 1 c := by
  simp [eCNineUnitLocalBaseEval]

@[simp] theorem eCNineUnitLocalBaseEval_X (s : Analytic.Germ 1) :
    eCNineUnitLocalBaseEval s Polynomial.X =
      1 + DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s := by
  simp [eCNineUnitLocalBaseEval]

theorem eCNineUnitLocalBaseEval_firstRadicand
    {s : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    eCNineUnitLocalBaseEval s eCNineUnitFirstRadicand =
      Analytic.Germ.coordinate 0 ^ 3 := by
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let sSub := sub s
  have hsSub := congrArg sub hsEquation
  have hsSubEquation :
      sSub * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) =
        Analytic.Germ.constRingHom 1 12 * z ^ 3 := by
    simpa [sub, sSub, z] using hsSub
  rw [eCNineUnitFirstRadicand]
  simp only [map_neg, map_mul, eCNineUnitLocalBaseEval_C,
    map_sub, map_one, eCNineUnitLocalBaseEval_X, map_add, map_pow]
  change -(Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
    ((1 - (1 + sSub)) *
      ((1 + sSub) ^ 2 + Analytic.Germ.constRingHom 1 2 * (1 + sSub) +
        Analytic.Germ.constRingHom 1 3))) = z ^ 3
  have hc2 : Analytic.Germ.constRingHom 1 (2 : ℂ) = 2 := map_ofNat _ 2
  have hc3 : Analytic.Germ.constRingHom 1 (3 : ℂ) = 3 := map_ofNat _ 3
  have hc4 : Analytic.Germ.constRingHom 1 (4 : ℂ) = 4 := map_ofNat _ 4
  have hc6 : Analytic.Germ.constRingHom 1 (6 : ℂ) = 6 := map_ofNat _ 6
  have hc12 : Analytic.Germ.constRingHom 1 (12 : ℂ) = 12 := map_ofNat _ 12
  have hconstant :
      Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        Analytic.Germ.constRingHom 1 12 = 1 := by
    rw [← map_mul]
    norm_num
  rw [hc4, hc6, hc12] at hsSubEquation
  rw [hc2, hc3]
  calc
    -(Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        ((1 - (1 + sSub)) * ((1 + sSub) ^ 2 + 2 * (1 + sSub) + 3))) =
      Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        (sSub * (6 + 4 * sSub + sSub ^ 2)) := by ring
    _ = Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        (12 * z ^ 3) := by rw [hsSubEquation]
    _ = z ^ 3 := by
      rw [← hc12, ← mul_assoc, hconstant, one_mul]

theorem eCNineUnitLocalBaseEval_secondRadicand
    {s U : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2) :
    eCNineUnitLocalBaseEval s eCNineUnitSecondRadicand =
      -(Analytic.Germ.coordinate 0 ^ 3 *
        DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) U) := by
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let sSub := sub s
  let USub := sub U
  have hsSub := congrArg sub hsEquation
  have hrelationSub := congrArg sub hrelation
  have hsSubEquation :
      sSub * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) =
        Analytic.Germ.constRingHom 1 12 * z ^ 3 := by
    simpa [sub, sSub, z] using hsSub
  have hrelationSubEquation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) * USub =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * sSub +
            Analytic.Germ.constRingHom 1 3 * sSub ^ 2 := by
    simpa [sub, sSub, USub] using hrelationSub
  have hweighted :
      Analytic.Germ.constRingHom 1 12 * z ^ 3 * USub =
        sSub * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * sSub +
            Analytic.Germ.constRingHom 1 3 * sSub ^ 2) := by
    calc
      Analytic.Germ.constRingHom 1 12 * z ^ 3 * USub =
          (sSub * (Analytic.Germ.constRingHom 1 6 +
            Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2)) * USub := by
        rw [hsSubEquation]
      _ = sSub * ((Analytic.Germ.constRingHom 1 6 +
            Analytic.Germ.constRingHom 1 4 * sSub + sSub ^ 2) * USub) := by
        rw [mul_assoc]
      _ = _ := by rw [hrelationSubEquation]
  rw [eCNineUnitSecondRadicand]
  simp only [map_mul, eCNineUnitLocalBaseEval_C, map_sub, map_one,
    eCNineUnitLocalBaseEval_X, map_add, map_pow]
  change Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
    ((1 - (1 + sSub)) *
      (Analytic.Germ.constRingHom 1 3 * (1 + sSub) ^ 2 +
        Analytic.Germ.constRingHom 1 2 * (1 + sSub) + 1)) =
      -(z ^ 3 * USub)
  have hc2 : Analytic.Germ.constRingHom 1 (2 : ℂ) = 2 := map_ofNat _ 2
  have hc3 : Analytic.Germ.constRingHom 1 (3 : ℂ) = 3 := map_ofNat _ 3
  have hc6 : Analytic.Germ.constRingHom 1 (6 : ℂ) = 6 := map_ofNat _ 6
  have hc8 : Analytic.Germ.constRingHom 1 (8 : ℂ) = 8 := map_ofNat _ 8
  have hc12 : Analytic.Germ.constRingHom 1 (12 : ℂ) = 12 := map_ofNat _ 12
  have hconstant :
      Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        Analytic.Germ.constRingHom 1 12 = 1 := by
    rw [← map_mul]
    norm_num
  rw [hc6, hc8, hc3, hc12] at hweighted
  rw [hc2, hc3]
  calc
    Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        ((1 - (1 + sSub)) * (3 * (1 + sSub) ^ 2 + 2 * (1 + sSub) + 1)) =
      -(Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        (sSub * (6 + 8 * sSub + 3 * sSub ^ 2))) := by ring
    _ = -(Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
        (12 * z ^ 3 * USub)) := by rw [hweighted]
    _ = -(z ^ 3 * USub) := by
      rw [← hc12]
      calc
        -(Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
            ((Analytic.Germ.constRingHom 1 12 * z ^ 3) * USub)) =
          -((Analytic.Germ.constRingHom 1 (12 : ℂ)⁻¹ *
            Analytic.Germ.constRingHom 1 12) * (z ^ 3 * USub)) := by ring
        _ = -(z ^ 3 * USub) := by rw [hconstant, one_mul]

/-- The primitive cube root as a constant analytic germ. -/
@[expose]
noncomputable def eCNineLocalOmega (omega : ℂ) : Analytic.Germ 1 :=
  Analytic.Germ.constRingHom 1 omega

theorem eCNineLocalOmega_quadratic
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3) :
    eCNineLocalOmega omega ^ 2 + eCNineLocalOmega omega + 1 = 0 := by
  have hsum := homega.geom_sum_eq_zero (by norm_num : 1 < 3)
  have hcomplex : omega ^ 2 + omega + 1 = 0 := by
    norm_num [Finset.sum_range_succ] at hsum
    linear_combination hsum
  have hmap := congrArg (Analytic.Germ.constRingHom 1) hcomplex
  simpa only [eCNineLocalOmega, map_add, map_pow, map_one, map_zero] using hmap

/-- The first cubic root on the branch obtained by rotating the parameter. -/
@[expose]
noncomputable def eCNineLocalFirstRoot
    (omega : ℂ) (i : Fin 3) : Analytic.Germ 1 :=
  Analytic.Germ.constRingHom 1 (omega ^ (i : ℕ)) *
    Analytic.Germ.coordinate 0

/-- The second cubic root with the same parameter rotation. -/
@[expose]
noncomputable def eCNineLocalSecondRoot
    (omega : ℂ) (i j : Fin 3) (v : Analytic.Germ 1) :
    Analytic.Germ 1 :=
  Analytic.Germ.constRingHom 1
      (eCNineBranchKappa omega j * omega ^ (i : ℕ)) *
    Analytic.Germ.coordinate 0 *
      DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) v

theorem eCNineLocalFirstRoot_cube
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) {s : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    eCNineLocalFirstRoot omega i ^ 3 =
      eCNineUnitLocalBaseEval s eCNineUnitFirstRadicand := by
  rw [eCNineUnitLocalBaseEval_firstRadicand hsEquation]
  rw [eCNineLocalFirstRoot, mul_pow, ← map_pow]
  have hi : (omega ^ (i : ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, homega.pow_eq_one, one_pow]
  rw [hi, map_one, one_mul]

theorem eCNineLocalSecondRoot_cube
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) {s U v : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineLocalSecondRoot omega i j v ^ 3 =
      eCNineUnitLocalBaseEval s eCNineUnitSecondRadicand := by
  rw [eCNineUnitLocalBaseEval_secondRadicand hsEquation hrelation]
  rw [eCNineLocalSecondRoot, mul_pow, mul_pow, ← map_pow]
  have hi : (omega ^ (i : ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, homega.pow_eq_one, one_pow]
  rw [mul_pow, eCNineBranchKappa_cube homega j, hi, mul_one,
    map_neg, map_one]
  have hvSub := congrArg
    (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)) hvCube
  rw [map_pow] at hvSub
  rw [hvSub]
  ring_nf

theorem eCNineUnitFirstPolynomial_localRoot_zero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) {s : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    Polynomial.eval₂ (eCNineUnitLocalBaseEval s)
      (eCNineLocalFirstRoot omega i) eCNineUnitFirstPolynomial = 0 := by
  rw [eCNineUnitFirstPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, eCNineLocalFirstRoot_cube homega i hsEquation, sub_self]

/-- Evaluation of the first cubic root algebra on a rotated branch. -/
@[expose]
noncomputable def eCNineUnitLocalFirstEval
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) (s : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    ECNineUnitFirstAlgebra →+* Analytic.Germ 1 :=
  AdjoinRoot.lift (eCNineUnitLocalBaseEval s)
    (eCNineLocalFirstRoot omega i)
    (eCNineUnitFirstPolynomial_localRoot_zero homega i hsEquation)

@[simp]
theorem eCNineUnitLocalFirstEval_root
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) (s : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    eCNineUnitLocalFirstEval homega i s hsEquation
        (AdjoinRoot.root eCNineUnitFirstPolynomial) =
      eCNineLocalFirstRoot omega i := by
  exact AdjoinRoot.lift_root
    (eCNineUnitFirstPolynomial_localRoot_zero homega i hsEquation)

@[simp]
theorem eCNineUnitLocalFirstEval_algebraMap
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) (s : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (q : ECNineUnitBase) :
    eCNineUnitLocalFirstEval homega i s hsEquation
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra q) =
      eCNineUnitLocalBaseEval s q := by
  exact AdjoinRoot.lift_of
    (eCNineUnitFirstPolynomial_localRoot_zero homega i hsEquation)

theorem eCNineUnitSecondPolynomial_localRoot_zero
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) {s U v : Analytic.Germ 1}
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    Polynomial.eval₂ (eCNineUnitLocalFirstEval homega i s hsEquation)
      (eCNineLocalSecondRoot omega i j v)
      eCNineUnitSecondPolynomial = 0 := by
  rw [eCNineUnitSecondPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C, eCNineUnitLocalFirstEval_algebraMap,
    eCNineLocalSecondRoot_cube homega i j hsEquation hrelation hvCube,
    sub_self]

/-- Evaluation of the unit chart algebra on one rotated branch. -/
@[expose]
noncomputable def eCNineUnitLocalEval
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    ECNineUnitAlgebra →+* Analytic.Germ 1 :=
  AdjoinRoot.lift (eCNineUnitLocalFirstEval homega i s hsEquation)
    (eCNineLocalSecondRoot omega i j v)
    (eCNineUnitSecondPolynomial_localRoot_zero homega i j
      hsEquation hrelation hvCube)

@[simp]
theorem eCNineUnitLocalEval_root
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (AdjoinRoot.root eCNineUnitSecondPolynomial) =
      eCNineLocalSecondRoot omega i j v := by
  exact AdjoinRoot.lift_root
    (eCNineUnitSecondPolynomial_localRoot_zero homega i j
      hsEquation hrelation hvCube)

@[simp]
theorem eCNineUnitLocalEval_algebraMap_first
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (q : ECNineUnitFirstAlgebra) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra q) =
      eCNineUnitLocalFirstEval homega i s hsEquation q := by
  exact AdjoinRoot.lift_of
    (eCNineUnitSecondPolynomial_localRoot_zero homega i j
      hsEquation hrelation hvCube)

@[simp]
theorem eCNineUnitLocalEval_algebraMap
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (q : ECNineUnitBase) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (algebraMap ECNineUnitBase ECNineUnitAlgebra q) =
      eCNineUnitLocalBaseEval s q := by
  rw [IsScalarTower.algebraMap_apply ECNineUnitBase
    ECNineUnitFirstAlgebra ECNineUnitAlgebra,
    eCNineUnitLocalEval_algebraMap_first,
    eCNineUnitLocalFirstEval_algebraMap]

theorem eCNineLocalFirstRoot_eq_power
    (omega : ℂ) (i : Fin 3) :
    eCNineLocalFirstRoot omega i =
      eCNineLocalOmega omega ^ (i : ℕ) * Analytic.Germ.coordinate 0 := by
  rw [eCNineLocalFirstRoot, eCNineLocalOmega, ← map_pow]

theorem eCNineLocalSecondRoot_eq_power_mul_zero
    (omega : ℂ) (i j : Fin 3) (v : Analytic.Germ 1) :
    eCNineLocalSecondRoot omega i j v =
      eCNineLocalOmega omega ^ (j : ℕ) *
        eCNineLocalSecondRoot omega i 0 v := by
  fin_cases j <;>
    simp [eCNineLocalSecondRoot, eCNineLocalOmega,
      eCNineBranchKappa, ← map_pow] <;> ring

theorem eCNineUnitLocalEval_comp_algebraMap_first
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    (eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube).comp
        (algebraMap ECNineUnitFirstAlgebra ECNineUnitAlgebra) =
      eCNineUnitLocalFirstEval homega i s hsEquation := by
  apply DFunLike.ext _ _
  intro q
  exact eCNineUnitLocalEval_algebraMap_first
    homega i j s U v hsEquation hrelation hvCube q

theorem eCNineUnitLocalFirstEval_comp_algebraMap
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) (s : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    (eCNineUnitLocalFirstEval homega i s hsEquation).comp
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra) =
      eCNineUnitLocalBaseEval s := by
  apply DFunLike.ext _ _
  intro q
  exact eCNineUnitLocalFirstEval_algebraMap homega i s hsEquation q

/-- The inner cubic norm factors over the three second roots above one
rotated first root. -/
theorem eCNineUnitLocalFirstEval_innerNorm_eq_product
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (q : ECNineUnitAlgebra) :
    eCNineUnitLocalFirstEval homega i s hsEquation
        (Algebra.norm ECNineUnitFirstAlgebra q) =
      eCNineUnitLocalEval homega i 0 s U v hsEquation hrelation hvCube q *
        eCNineUnitLocalEval homega i 1 s U v hsEquation hrelation hvCube q *
          eCNineUnitLocalEval homega i 2 s U v hsEquation hrelation hvCube q := by
  have halpha : eCNineLocalSecondRoot omega i 0 v ^ 3 =
      eCNineUnitLocalFirstEval homega i s hsEquation
        (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra
          eCNineUnitSecondRadicand) := by
    rw [eCNineUnitLocalFirstEval_algebraMap]
    exact eCNineLocalSecondRoot_cube homega i 0
      hsEquation hrelation hvCube
  have hfactor := map_cubicBasis_norm_eq_product
    eCNineUnitSecondBasis
    (AdjoinRoot.root eCNineUnitSecondPolynomial)
    (algebraMap ECNineUnitBase ECNineUnitFirstAlgebra
      eCNineUnitSecondRadicand)
    eCNineUnitSecondBasis_apply eCNineUnitSecondRoot_cube q
    (eCNineUnitLocalFirstEval homega i s hsEquation)
    (eCNineLocalSecondRoot omega i 0 v)
    (eCNineLocalOmega omega) halpha (eCNineLocalOmega_quadratic homega)
  rw [hfactor]
  rw [cubicBasisEvaluation_eq_map eCNineUnitSecondBasis
    (AdjoinRoot.root eCNineUnitSecondPolynomial)
    eCNineUnitSecondBasis_apply q
    (eCNineUnitLocalFirstEval homega i s hsEquation)
    (eCNineUnitLocalEval homega i 0 s U v hsEquation hrelation hvCube)
    (eCNineUnitLocalEval_comp_algebraMap_first homega i 0 s U v
      hsEquation hrelation hvCube)
    (eCNineLocalSecondRoot omega i 0 v)
    (eCNineUnitLocalEval_root homega i 0 s U v hsEquation hrelation hvCube)]
  have hrootOne :
      eCNineLocalOmega omega * eCNineLocalSecondRoot omega i 0 v =
        eCNineLocalSecondRoot omega i 1 v := by
    simpa using
      (eCNineLocalSecondRoot_eq_power_mul_zero omega i 1 v).symm
  rw [hrootOne]
  rw [cubicBasisEvaluation_eq_map eCNineUnitSecondBasis
    (AdjoinRoot.root eCNineUnitSecondPolynomial)
    eCNineUnitSecondBasis_apply q
    (eCNineUnitLocalFirstEval homega i s hsEquation)
    (eCNineUnitLocalEval homega i 1 s U v hsEquation hrelation hvCube)
    (eCNineUnitLocalEval_comp_algebraMap_first homega i 1 s U v
      hsEquation hrelation hvCube)
    (eCNineLocalSecondRoot omega i 1 v)
    (eCNineUnitLocalEval_root homega i 1 s U v hsEquation hrelation hvCube)]
  have hrootTwo :
      eCNineLocalOmega omega ^ 2 * eCNineLocalSecondRoot omega i 0 v =
        eCNineLocalSecondRoot omega i 2 v := by
    simpa using
      (eCNineLocalSecondRoot_eq_power_mul_zero omega i 2 v).symm
  rw [hrootTwo]
  rw [cubicBasisEvaluation_eq_map eCNineUnitSecondBasis
    (AdjoinRoot.root eCNineUnitSecondPolynomial)
    eCNineUnitSecondBasis_apply q
    (eCNineUnitLocalFirstEval homega i s hsEquation)
    (eCNineUnitLocalEval homega i 2 s U v hsEquation hrelation hvCube)
    (eCNineUnitLocalEval_comp_algebraMap_first homega i 2 s U v
      hsEquation hrelation hvCube)
    (eCNineLocalSecondRoot omega i 2 v)
    (eCNineUnitLocalEval_root homega i 2 s U v hsEquation hrelation hvCube)]

/-- Pullback of the rank nine norm factors as the product of the nine local
evaluations. -/
theorem eCNineUnitLocalBaseEval_norm_eq_nine_product
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (q : ECNineUnitAlgebra) :
    eCNineUnitLocalBaseEval s (Algebra.norm ECNineUnitBase q) =
      ((eCNineUnitLocalEval homega 0 0 s U v hsEquation hrelation hvCube q *
          eCNineUnitLocalEval homega 0 1 s U v hsEquation hrelation hvCube q *
        eCNineUnitLocalEval homega 0 2 s U v hsEquation hrelation hvCube q) *
      (eCNineUnitLocalEval homega 1 0 s U v hsEquation hrelation hvCube q *
          eCNineUnitLocalEval homega 1 1 s U v hsEquation hrelation hvCube q *
        eCNineUnitLocalEval homega 1 2 s U v hsEquation hrelation hvCube q)) *
      (eCNineUnitLocalEval homega 2 0 s U v hsEquation hrelation hvCube q *
          eCNineUnitLocalEval homega 2 1 s U v hsEquation hrelation hvCube q *
        eCNineUnitLocalEval homega 2 2 s U v hsEquation hrelation hvCube q) := by
  let _ : Module.Free ECNineUnitBase ECNineUnitFirstAlgebra :=
    Module.Free.of_basis eCNineUnitFirstBasis
  let _ : Module.Free ECNineUnitFirstAlgebra ECNineUnitAlgebra :=
    Module.Free.of_basis eCNineUnitSecondBasis
  let innerNorm : ECNineUnitFirstAlgebra :=
    Algebra.norm ECNineUnitFirstAlgebra q
  have halpha : Analytic.Germ.coordinate 0 ^ 3 =
      eCNineUnitLocalBaseEval s eCNineUnitFirstRadicand :=
    (eCNineUnitLocalBaseEval_firstRadicand hsEquation).symm
  have hfactor := map_cubicBasis_norm_eq_product
    eCNineUnitFirstBasis
    (AdjoinRoot.root eCNineUnitFirstPolynomial)
    eCNineUnitFirstRadicand eCNineUnitFirstBasis_apply
    eCNineUnitFirstRoot_cube innerNorm (eCNineUnitLocalBaseEval s)
    (Analytic.Germ.coordinate 0) (eCNineLocalOmega omega)
    halpha (eCNineLocalOmega_quadratic homega)
  rw [← Algebra.norm_norm (R := ECNineUnitBase)
    (S := ECNineUnitFirstAlgebra) (a := q)]
  change eCNineUnitLocalBaseEval s
      (Algebra.norm ECNineUnitBase innerNorm) = _
  rw [hfactor]
  have hrootZero : Analytic.Germ.coordinate 0 =
      eCNineLocalFirstRoot omega 0 := by
    simp [eCNineLocalFirstRoot_eq_power]
  nth_rewrite 1 [hrootZero]
  rw [cubicBasisEvaluation_eq_map eCNineUnitFirstBasis
    (AdjoinRoot.root eCNineUnitFirstPolynomial)
    eCNineUnitFirstBasis_apply innerNorm (eCNineUnitLocalBaseEval s)
    (eCNineUnitLocalFirstEval homega 0 s hsEquation)
    (eCNineUnitLocalFirstEval_comp_algebraMap homega 0 s hsEquation)
    (eCNineLocalFirstRoot omega 0)
    (eCNineUnitLocalFirstEval_root homega 0 s hsEquation)]
  have hrootOne : eCNineLocalOmega omega * Analytic.Germ.coordinate 0 =
      eCNineLocalFirstRoot omega 1 := by
    simpa using (eCNineLocalFirstRoot_eq_power omega 1).symm
  rw [hrootOne]
  rw [cubicBasisEvaluation_eq_map eCNineUnitFirstBasis
    (AdjoinRoot.root eCNineUnitFirstPolynomial)
    eCNineUnitFirstBasis_apply innerNorm (eCNineUnitLocalBaseEval s)
    (eCNineUnitLocalFirstEval homega 1 s hsEquation)
    (eCNineUnitLocalFirstEval_comp_algebraMap homega 1 s hsEquation)
    (eCNineLocalFirstRoot omega 1)
    (eCNineUnitLocalFirstEval_root homega 1 s hsEquation)]
  have hrootTwo : eCNineLocalOmega omega ^ 2 * Analytic.Germ.coordinate 0 =
      eCNineLocalFirstRoot omega 2 := by
    simpa using (eCNineLocalFirstRoot_eq_power omega 2).symm
  rw [hrootTwo]
  rw [cubicBasisEvaluation_eq_map eCNineUnitFirstBasis
    (AdjoinRoot.root eCNineUnitFirstPolynomial)
    eCNineUnitFirstBasis_apply innerNorm (eCNineUnitLocalBaseEval s)
    (eCNineUnitLocalFirstEval homega 2 s hsEquation)
    (eCNineUnitLocalFirstEval_comp_algebraMap homega 2 s hsEquation)
    (eCNineLocalFirstRoot omega 2)
    (eCNineUnitLocalFirstEval_root homega 2 s hsEquation)]
  rw [eCNineUnitLocalFirstEval_innerNorm_eq_product homega 0 s U v
    hsEquation hrelation hvCube q]
  rw [eCNineUnitLocalFirstEval_innerNorm_eq_product homega 1 s U v
    hsEquation hrelation hvCube q]
  rw [eCNineUnitLocalFirstEval_innerNorm_eq_product homega 2 s U v
    hsEquation hrelation hvCube q]

@[simp]
theorem eCNineUnitLocalEval_algebraMap_complex
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (c : ℂ) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (algebraMap ℂ ECNineUnitAlgebra c) =
      Analytic.Germ.constRingHom 1 c := by
  rw [← eCNineUnit_algebraMap_C,
    eCNineUnitLocalEval_algebraMap, eCNineUnitLocalBaseEval_C]

theorem eCNineUnitLocalEval_sourceForm
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (R : Form ℂ) (x y : ECNineUnitAlgebra) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (MvPolynomial.eval₂ (algebraMap ℂ ECNineUnitAlgebra) ![x, y] R) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1) ![
        eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube x,
        eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube y] R := by
  rw [MvPolynomial.hom_eval₂]
  have hcoeff :
      (eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube).comp
          (algebraMap ℂ ECNineUnitAlgebra) =
        Analytic.Germ.constRingHom 1 := by
    apply DFunLike.ext _ _
    intro c
    exact eCNineUnitLocalEval_algebraMap_complex homega i j s U v
      hsEquation hrelation hvCube c
  rw [hcoeff]
  have hvariables :
      (fun k =>
        eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
          (![x, y] k)) =
        ![
          eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube x,
          eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube y] := by
    funext k
    fin_cases k <;> rfl
  rw [hvariables]

@[simp]
theorem eCNineUnitLocalEval_t
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        eCNineUnitT =
      eCNineLocalFirstRoot omega i := by
  rw [eCNineUnitT, eCNineUnitLocalEval_algebraMap_first,
    eCNineUnitLocalFirstEval_root]

@[simp]
theorem eCNineUnitLocalEval_capitalX
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        eCNineUnitCapitalX =
      1 + DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s := by
  rw [eCNineUnitCapitalX, eCNineUnitLocalEval_algebraMap,
    eCNineUnitLocalBaseEval_X]

@[simp]
theorem eCNineUnitLocalEval_capitalT
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        eCNineUnitCapitalT =
      eCNineLocalSecondRoot omega i j v := by
  rw [eCNineUnitCapitalT, eCNineUnitLocalEval_root]

theorem eCNineUnitLocalEval_differenceElement
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) (R : Form ℂ) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (eCNineUnitDifferenceElement R) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          ![1, eCNineLocalFirstRoot omega i] R -
        MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          ![1 + DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s,
            eCNineLocalSecondRoot omega i j v] R := by
  rw [eCNineUnitDifferenceElement, map_sub,
    eCNineUnitLocalEval_sourceForm, eCNineUnitLocalEval_sourceForm]
  simp

/-- The coefficient of the pure branch term after rotating the first cubic
root. -/
@[expose]
noncomputable def eCNineRotatedCoefficient
    (omega coefficient : ℂ) (i : Fin 3) (N : ℕ) : ℂ :=
  coefficient * (omega ^ (i : ℕ)) ^ N

set_option linter.flexible false in
theorem eCNineUnitLocalEval_hardDifference_eq_branchDifference
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U) :
    eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
        (eCNineUnitDifferenceElement
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)) =
      eCNineBranchDifference
        (eCNineLocalInvariantDifference Rzero s U) v
        (eCNineRotatedCoefficient omega coefficient i N)
        (eCNineBranchKappa omega j) N := by
  rw [eCNineUnitLocalEval_differenceElement]
  rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add,
    eCNine_sourceCube_eval_germ, eCNine_sourceCube_eval_germ]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, formT,
    eCNineBranchDifference, eCNinePureBranchTerm, eCNineBranchBracket,
    eCNineRotatedCoefficient]
  let sub := DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega)
  let z : Analytic.Germ 1 := Analytic.Germ.coordinate 0
  let sSub := sub s
  let USub := sub U
  let vSub := sub v
  let omegaPower : ℂ := omega ^ (i : ℕ)
  let kappa : ℂ := eCNineBranchKappa omega j
  have hi : omegaPower ^ 3 = 1 := by
    dsimp only [omegaPower]
    rw [← pow_mul, mul_comm, pow_mul, homega.pow_eq_one, one_pow]
  have hvCubeSub := congrArg sub hvCube
  have hvCubeSubEquation : vSub ^ 3 = USub := by
    simpa [sub, vSub, USub] using hvCubeSub
  have hkappaCube : kappa ^ 3 = -1 := by
    exact eCNineBranchKappa_cube homega j
  have hfirstCube : eCNineLocalFirstRoot omega i ^ 3 = z ^ 3 := by
    rw [eCNineLocalFirstRoot, mul_pow, ← map_pow, hi, map_one, one_mul]
  have hsecondCube : eCNineLocalSecondRoot omega i j v ^ 3 =
      -z ^ 3 * USub := by
    rw [eCNineLocalSecondRoot, mul_pow, mul_pow, ← map_pow]
    rw [mul_pow, hkappaCube, hi, mul_one, map_neg, map_one,
      hvCubeSubEquation]
    ring
  have hFsub : sub (eCNineLocalInvariantDifference Rzero s U) =
      MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          (fun
            | ESourceCoordinate.x => 1
            | ESourceCoordinate.w => z ^ 3) Rzero -
        MvPolynomial.eval₂ (Analytic.Germ.constRingHom 1)
          (fun
            | ESourceCoordinate.x => 1 + sSub
            | ESourceCoordinate.w => -z ^ 3 * USub) Rzero := by
    dsimp only [eCNineLocalInvariantDifference]
    rw [map_sub]
    congr 1
    · rw [eCNine_powerSub_eval₂]
      congr
      funext k
      cases k <;> simp [z]
    · rw [eCNine_powerSub_eval₂]
      congr
      funext k
      cases k <;> simp [sub, z, sSub, USub]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  change _ = sub (eCNineLocalInvariantDifference Rzero s U) + _
  rw [hfirstCube, hsecondCube, hFsub]
  have hfirstPower : eCNineLocalFirstRoot omega i ^ N =
      Analytic.Germ.constRingHom 1 (omegaPower ^ N) * z ^ N := by
    rw [eCNineLocalFirstRoot, mul_pow, ← map_pow]
  have hsecondPower : eCNineLocalSecondRoot omega i j v ^ N =
      Analytic.Germ.constRingHom 1 ((kappa * omegaPower) ^ N) *
        z ^ N * vSub ^ N := by
    rw [eCNineLocalSecondRoot, mul_pow, mul_pow, ← map_pow]
  rw [hfirstPower, hsecondPower]
  change _ = _ + Analytic.Germ.constRingHom 1 (coefficient * omegaPower ^ N) *
    z ^ N *
      (1 - Analytic.Germ.constRingHom 1 (kappa ^ N) * vSub ^ N)
  simp only [map_mul, map_pow]
  dsimp only [sSub, sub]
  ring_nf
  rfl

/-- Multiplying the pure term coefficient by a nonzero scalar does not
change the branch order when the degree is not divisible by three. -/
theorem eCNineBranchDifference_vanishingOrder_mul_coefficient
    {F v : Analytic.Germ 1} {coefficient lambda kappa : ℂ} {N : ℕ}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hlambda : lambda ≠ 0)
    (hnotdiv : ¬ 3 ∣ N) :
    Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v (coefficient * lambda) kappa N) =
      Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v coefficient kappa N) := by
  have hcoefficientMul : coefficient * lambda ≠ 0 :=
    mul_ne_zero hc hlambda
  by_cases hkappa : kappa ^ N = 1
  · have hN : N ≠ 0 := by
      intro hzero
      subst N
      exact hnotdiv (dvd_zero 3)
    have hpureMul := eCNine_pure_exception_order hv hcoefficientMul
      hkappa hN hvorder
    have hpure := eCNine_pure_exception_order hv hc hkappa hN hvorder
    have hne := eCNine_sub_order_ne_degree_add_three (F := F) hnotdiv
    have hleft : Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v (coefficient * lambda) kappa N) =
        min (Analytic.Germ.vanishingOrder
          (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F))
          (N + 3) := by
      rw [eCNineBranchDifference,
        eCNine_order_add_of_ne (hpureMul ▸ hne), hpureMul]
    have hright : Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v coefficient kappa N) =
        min (Analytic.Germ.vanishingOrder
          (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F))
          (N + 3) := by
      rw [eCNineBranchDifference,
        eCNine_order_add_of_ne (hpure ▸ hne), hpure]
    exact hleft.trans hright.symm
  · have hpureMul := eCNine_pure_nonexception_order hv hcoefficientMul hkappa
    have hpure := eCNine_pure_nonexception_order hv hc hkappa
    have hne := eCNine_sub_order_ne_degree (F := F) hnotdiv
    have hleft : Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v (coefficient * lambda) kappa N) =
        min (Analytic.Germ.vanishingOrder
          (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F)) N := by
      rw [eCNineBranchDifference,
        eCNine_order_add_of_ne (hpureMul ▸ hne), hpureMul]
    have hright : Analytic.Germ.vanishingOrder
        (eCNineBranchDifference F v coefficient kappa N) =
        min (Analytic.Germ.vanishingOrder
          (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) F)) N := by
      rw [eCNineBranchDifference,
        eCNine_order_add_of_ne (hpure ▸ hne), hpure]
    exact hleft.trans hright.symm

/-- Each of the nine evaluations of the hard difference has the order of
the section on the branch selected by its second index. -/
theorem eCNineUnitLocalEval_hardDifference_vanishingOrder_eq_section
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (i j : Fin 3) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ) (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    Analytic.Germ.vanishingOrder
        (eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
          (eCNineUnitDifferenceElement
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N))) =
      Analytic.Germ.vanishingOrder
        (eCNineLocalSectionPullback Rzero s v coefficient
          (eCNineBranchKappa omega j) N) := by
  rw [eCNineUnitLocalEval_hardDifference_eq_branchDifference]
  rw [eCNineLocalSectionPullback_eq_branchDifference Rzero s U v coefficient
    (eCNineBranchKappa omega j) N hvCube
    (eCNineBranchKappa_cube homega j)]
  exact eCNineBranchDifference_vanishingOrder_mul_coefficient hv hvorder hc
    (pow_ne_zero N (pow_ne_zero (i : ℕ) (homega.ne_zero (by norm_num))))
    hnotdiv

/-- Pulling back the rank nine hard norm gives three copies of the sum of
the orders on the three explicit analytic parametrizations. -/
theorem eCNineUnitLocalBaseEval_hardNorm_vanishingOrder
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : Analytic.Germ 1)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    Analytic.Germ.vanishingOrder
        (eCNineUnitLocalBaseEval s
          (eCNineUnitDifferenceNorm
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N))) =
      eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N +
        eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N +
      eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  have horder (i j : Fin 3) :
      Analytic.Germ.vanishingOrder
          (eCNineUnitLocalEval homega i j s U v hsEquation hrelation hvCube
            (eCNineUnitDifferenceElement hardForm)) =
        Analytic.Germ.vanishingOrder
          (eCNineLocalSectionPullback Rzero s v coefficient
            (eCNineBranchKappa omega j) N) := by
    exact eCNineUnitLocalEval_hardDifference_vanishingOrder_eq_section
      homega i j Rzero coefficient N s U v hsEquation hrelation hvCube
      hv hvorder hc hnotdiv
  change Analytic.Germ.vanishingOrder
      (eCNineUnitLocalBaseEval s (Algebra.norm ECNineUnitBase
        (eCNineUnitDifferenceElement hardForm))) = _
  rw [eCNineUnitLocalBaseEval_norm_eq_nine_product homega s U v
    hsEquation hrelation hvCube]
  simp only [Analytic.Germ.vanishingOrder_mul]
  rw [horder 0 0, horder 0 1, horder 0 2,
    horder 1 0, horder 1 1, horder 1 2,
    horder 2 0, horder 2 1, horder 2 2]
  simp only [eCNinePZeroExplicitBranchContribution]

/-- At the origin, the local base evaluation is ordinary polynomial
evaluation at the unit chart coordinate `X = 1`. -/
theorem eCNineUnitLocalBaseEval_value
    {s : Analytic.Germ 1}
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (q : ECNineUnitBase) :
    Analytic.Germ.valueRingHom 1 (eCNineUnitLocalBaseEval s q) =
      q.eval 1 := by
  have hhom :
      (Analytic.Germ.valueRingHom 1).comp (eCNineUnitLocalBaseEval s) =
        Polynomial.evalRingHom 1 := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · rw [RingHom.comp_apply, eCNineUnitLocalBaseEval_X, map_add,
        map_one, DTwo.Germ.oneVariablePowerSubstitutionRingHom,
        PointedMapGerm.valueRingHom_pullback, hs, add_zero]
      simp
  exact DFunLike.congr_fun hhom q

/-- The analytic coordinate `s` used in the C9 local chart has order one. -/
theorem eCNineLocalParameter_vanishingOrder
    {s : Analytic.Germ 1}
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    Analytic.Germ.vanishingOrder s = 1 := by
  let denominator : Analytic.Germ 1 :=
    Analytic.Germ.constRingHom 1 6 +
      Analytic.Germ.constRingHom 1 4 * s + s ^ 2
  have hdenominatorValue :
      Analytic.Germ.valueRingHom 1 denominator = 6 := by
    simp [denominator, hs]
  have hdenominatorUnit : IsUnit denominator := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hdenominatorValue]
    norm_num
  have hconstantUnit :
      IsUnit (Analytic.Germ.constRingHom 1 (12 : ℂ)) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    norm_num
  have horder := congrArg Analytic.Germ.vanishingOrder hsEquation
  change Analytic.Germ.vanishingOrder (s * denominator) = _ at horder
  rw [Analytic.Germ.vanishingOrder_mul,
    Analytic.Germ.vanishingOrder_mul,
    Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hdenominatorUnit,
    Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hconstantUnit,
    Analytic.Germ.vanishingOrder_coordinate] at horder
  norm_num at horder ⊢
  exact horder

/-- Cubic substitution of the local chart parameter has order three. -/
theorem eCNineLocalParameter_cubicSubstitution_vanishingOrder
    {s : Analytic.Germ 1}
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0) :
    Analytic.Germ.vanishingOrder
        (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s) = 3 := by
  have hsOrder := eCNineLocalParameter_vanishingOrder hs hsEquation
  have hsNe : s ≠ 0 := by
    intro hsZero
    rw [hsZero, Analytic.Germ.vanishingOrder_zero] at hsOrder
    norm_num at hsOrder
  have horder := eCNine_substitution_order (n := 1) (q := 3)
    (by omega) hsNe hsOrder
  norm_num at horder ⊢
  exact horder

/-- The pullback order of a nonzero base polynomial is three times its
root multiplicity at the local base coordinate `X = 1`. -/
theorem eCNineUnitLocalBaseEval_vanishingOrder_eq_rootMultiplicity
    {s : Analytic.Germ 1}
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    {q : ECNineUnitBase} (hq : q ≠ 0) :
    Analytic.Germ.vanishingOrder (eCNineUnitLocalBaseEval s q) =
      ((3 * q.rootMultiplicity 1 : ℕ) : ℕ∞) := by
  let quotient : ECNineUnitBase :=
    q /ₘ (Polynomial.X - Polynomial.C 1) ^ q.rootMultiplicity 1
  have hfactor :
      (Polynomial.X - Polynomial.C 1) ^ q.rootMultiplicity 1 * quotient = q :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq q 1
  have hquotientNonzero : quotient.eval 1 ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 1 hq
  have hquotientValue :
      Analytic.Germ.valueRingHom 1 (eCNineUnitLocalBaseEval s quotient) =
        quotient.eval 1 :=
    eCNineUnitLocalBaseEval_value hs quotient
  have hquotientUnit : IsUnit (eCNineUnitLocalBaseEval s quotient) := by
    apply Analytic.Germ.isUnit_of_valueRingHom_ne_zero
    rw [hquotientValue]
    exact hquotientNonzero
  have hlinear :
      eCNineUnitLocalBaseEval s (Polynomial.X - Polynomial.C 1) =
        DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s := by
    rw [map_sub, eCNineUnitLocalBaseEval_X,
      eCNineUnitLocalBaseEval_C]
    simp only [map_one]
    ring
  have hfactorEval :
      eCNineUnitLocalBaseEval s q =
        (DTwo.Germ.oneVariablePowerSubstitutionRingHom 3 (by omega) s) ^
            q.rootMultiplicity 1 *
          eCNineUnitLocalBaseEval s quotient := by
    have hmapped := congrArg (eCNineUnitLocalBaseEval s) hfactor
    rw [map_mul, map_pow, hlinear] at hmapped
    exact hmapped.symm
  rw [hfactorEval, Analytic.Germ.vanishingOrder_mul,
    Analytic.Germ.vanishingOrder_pow,
    eCNineLocalParameter_cubicSubstitution_vanishingOrder hs hsEquation,
    Analytic.Germ.vanishingOrder_eq_zero_iff_isUnit.mpr hquotientUnit,
    add_zero]
  norm_num [nsmul_eq_mul, ENat.natCast_mul]
  ring

/-- Three times the root multiplicity of the hard norm at `X = 1` equals
three copies of the explicit branch contribution. -/
theorem eCNineUnitDifferenceNorm_three_mul_rootMultiplicity
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : Analytic.Germ 1)
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    ((3 * (eCNineUnitDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 : ℕ) :
        ℕ∞) =
      eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N +
        eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N +
      eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  have hnorm : eCNineUnitDifferenceNorm hardForm ≠ 0 :=
    eCNineUnitDifferenceNorm_ne_zero homega hardForm Rzero coefficient N
      rfl hc hnotdiv
  calc
    ((3 * (eCNineUnitDifferenceNorm hardForm).rootMultiplicity 1 : ℕ) :
        ℕ∞) =
        Analytic.Germ.vanishingOrder
          (eCNineUnitLocalBaseEval s
            (eCNineUnitDifferenceNorm hardForm)) :=
      (eCNineUnitLocalBaseEval_vanishingOrder_eq_rootMultiplicity
        hs hsEquation hnorm).symm
    _ = _ := eCNineUnitLocalBaseEval_hardNorm_vanishingOrder
      homega Rzero coefficient N s U v hsEquation hrelation hvCube
      hv hvorder hc hnotdiv

/-- The explicit three branch contribution is finite for every hard degree. -/
theorem eCNinePZeroExplicitBranchContribution_ne_top
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    {Rzero : ESourceRing ℂ} {coefficient : ℂ} {N : ℕ}
    {s U v : Analytic.Germ 1}
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvCube : v ^ 3 = U)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N ≠ ⊤ := by
  rcases Nat.even_or_odd N with heven | hodd
  · have hbound := eCNinePZeroExplicitBranchContribution_even_le
      (Rzero := Rzero) (s := s) homega hv hvCube hvorder hc hnotdiv heven
    intro htop
    rw [htop] at hbound
    exact (not_le_of_gt (ENat.natCast_lt_top (3 * N + 3))) hbound
  · have hbound := eCNinePZeroExplicitBranchContribution_odd_le
      (Rzero := Rzero) (s := s) homega hv hvCube hc hnotdiv hodd
    intro htop
    rw [htop] at hbound
    exact (not_le_of_gt (ENat.natCast_lt_top (3 * N))) hbound

/-- The root multiplicity of the unit chart norm at `X = 1` is exactly the
sum of the section orders on the three explicit analytic parametrizations. -/
theorem eCNineUnitDifferenceNorm_rootMultiplicity_eq_branchContribution
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : Analytic.Germ 1)
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (((eCNineUnitDifferenceNorm
          (eSourceCubeSubstitutionForm Rzero +
            MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 : ℕ) :
        ℕ∞) =
      eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  let multiplicity :=
    (eCNineUnitDifferenceNorm hardForm).rootMultiplicity 1
  let contribution := eCNinePZeroExplicitBranchContribution
    omega Rzero s v coefficient N
  have htriple : ((3 * multiplicity : ℕ) : ℕ∞) =
      contribution + contribution + contribution := by
    exact eCNineUnitDifferenceNorm_three_mul_rootMultiplicity
      homega Rzero coefficient N s U v hs hsEquation hrelation hvCube
      hv hvorder hc hnotdiv
  have hcontributionTop : contribution ≠ ⊤ :=
    eCNinePZeroExplicitBranchContribution_ne_top
      (Rzero := Rzero) (s := s) homega hv hvCube hvorder hc hnotdiv
  obtain ⟨order, horder⟩ := ENat.ne_top_iff_exists.mp hcontributionTop
  have hcast : ((3 * multiplicity : ℕ) : ℕ∞) =
      ((order + order + order : ℕ) : ℕ∞) := by
    calc
      ((3 * multiplicity : ℕ) : ℕ∞) =
          contribution + contribution + contribution := htriple
      _ = (order : ℕ∞) + order + order := by rw [horder]
      _ = ((order + order + order : ℕ) : ℕ∞) := by
        norm_num [ENat.natCast_add]
  have hnat : 3 * multiplicity = order + order + order :=
    ENat.natCast_inj.mp hcast
  have hmultiplicity : multiplicity = order := by omega
  calc
    (multiplicity : ℕ∞) = (order : ℕ∞) :=
      congrArg (fun n : ℕ ↦ (n : ℕ∞)) hmultiplicity
    _ = contribution := horder

/-- The natural number form of the local norm multiplicity formula. -/
theorem eCNineUnitDifferenceNorm_rootMultiplicity_eq_branchContribution_toNat
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (s U v : Analytic.Germ 1)
    (hs : Analytic.Germ.valueRingHom 1 s = 0)
    (hsEquation :
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0)
    (hrelation :
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2)
    (hvCube : v ^ 3 = U)
    (hv : Analytic.Germ.valueRingHom 1 v = 1)
    (hvorder : Analytic.Germ.vanishingOrder (1 - v) = 1)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineUnitDifferenceNorm
        (eSourceCubeSubstitutionForm Rzero +
          MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 =
      (eCNinePZeroExplicitBranchContribution
        omega Rzero s v coefficient N).toNat := by
  have hformula :=
    eCNineUnitDifferenceNorm_rootMultiplicity_eq_branchContribution
      homega Rzero coefficient N s U v hs hsEquation hrelation hvCube
      hv hvorder hc hnotdiv
  exact congrArg ENat.toNat hformula

/-- There are simultaneous branch data for which the local root
multiplicity formula holds for every hard C9 form. -/
theorem eCNine_exists_local_norm_rootMultiplicity_formula
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    ∃ s U v : Analytic.Germ 1,
      Analytic.Germ.valueRingHom 1 s = 0 ∧
      s * (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) =
        Analytic.Germ.constRingHom 1 12 * Analytic.Germ.coordinate 0 ∧
      (Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 4 * s + s ^ 2) * U =
        Analytic.Germ.constRingHom 1 6 +
          Analytic.Germ.constRingHom 1 8 * s +
            Analytic.Germ.constRingHom 1 3 * s ^ 2 ∧
      Analytic.Germ.valueRingHom 1 U = 1 ∧
      Analytic.Germ.valueRingHom 1 v = 1 ∧
      v ^ 3 = U ∧
      Analytic.Germ.vanishingOrder (1 - v) = 1 ∧
      (((eCNineUnitDifferenceNorm
            (eSourceCubeSubstitutionForm Rzero +
              MvPolynomial.C coefficient * formT ^ N)).rootMultiplicity 1 : ℕ) :
          ℕ∞) =
        eCNinePZeroExplicitBranchContribution
          omega Rzero s v coefficient N := by
  obtain ⟨s, U, v, hs, hsEquation, hrelation, hU, hv, hvCube, hvorder⟩ :=
    eCNine_exists_local_branch_data
  refine ⟨s, U, v, hs, hsEquation, hrelation, hU, hv, hvCube, hvorder, ?_⟩
  exact eCNineUnitDifferenceNorm_rootMultiplicity_eq_branchContribution
    homega Rzero coefficient N s U v hs hsEquation hrelation hvCube
    hv hvorder hc hnotdiv

end Germ
end OnLeConjecture.DThree
