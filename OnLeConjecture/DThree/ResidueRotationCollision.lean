/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueMonomialCollision
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# The rotation branch of the residual collision for order three

When `0 < r < a`, a primitive root of order `a` relates two distinct source
points with the same first two initial coordinates.  If the dehomogenized
third form has a root, the third coordinates also agree.  This file proves
the point selection and the finiteness of the remaining root set.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The `E` initial map restricted to the rotation component.  The polynomial
`p` is the dehomogenization `H(x, 1)` of the third form. -/
@[expose]
noncomputable def eResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.2 ^ (3 * a),
    z.1 ^ 4 + 4 * z.1 * z.2 ^ (3 * a),
    z.2 ^ r * p.eval z.1]

/-- The `H` initial map restricted to the rotation component. -/
@[expose]
noncomputable def hResidueRotationMap
    (a r : ℕ) (p : ℂ[X]) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a),
    z.1 ^ 4 + 4 * z.1 ^ 2 * z.2 ^ (2 * a) +
      2 * z.2 ^ (4 * a),
    z.2 ^ r * p.eval z.1]

/-- The third difference on the rotation component. -/
@[expose]
noncomputable def rotationRestrictedDifference
    (zeta : ℂ) (r : ℕ) (p : ℂ[X]) : ℂ[X] :=
  p - C (zeta ^ r) * p

theorem rotationRestrictedDifference_eq
    (zeta : ℂ) (r : ℕ) (p : ℂ[X]) :
    rotationRestrictedDifference zeta r p = C (1 - zeta ^ r) * p := by
  rw [rotationRestrictedDifference]
  calc
    p - C (zeta ^ r) * p = C 1 * p - C (zeta ^ r) * p := by simp
    _ = (C 1 - C (zeta ^ r)) * p := by ring
    _ = C (1 - zeta ^ r) * p := by rw [map_sub, map_one]

/-- The algebraic certificate on a rotation component. -/
structure ResidueRotationCollisionCertificate
    (a r : ℕ) (p : ℂ[X]) where
  zeta : ℂ
  x : ℂ
  zeta_pow_a : zeta ^ a = 1
  zeta_pow_r_ne_one : zeta ^ r ≠ 1
  zeta_ne_one : zeta ≠ 1
  sourcePoints_ne : ((x, 1) : ℂ × ℂ) ≠ (x, zeta)
  eValues_eq :
    eResidueRotationMap a r p (x, 1) =
      eResidueRotationMap a r p (x, zeta)
  hValues_eq :
    hResidueRotationMap a r p (x, 1) =
      hResidueRotationMap a r p (x, zeta)
  restrictedDifference_zero :
    (rotationRestrictedDifference zeta r p).eval x = 0
  restrictedDifference_ne_zero :
    rotationRestrictedDifference zeta r p ≠ 0
  restrictedRootSet_finite :
    Set.Finite {u : ℂ |
      (rotationRestrictedDifference zeta r p).IsRoot u}
  restrictedRootSet_discrete :
    IsDiscrete {u : ℂ |
      (rotationRestrictedDifference zeta r p).IsRoot u}

/-- A nonzero dehomogenized third form with a root produces the isolated
root data on the rotation component for both the `E` and `H` pairs. -/
theorem exists_residueRotationCollisionCertificate
    (a r : ℕ) (p : ℂ[X]) (x : ℂ)
    (ha : 2 ≤ a) (hr0 : 0 < r) (hra : r < a)
    (hp : p ≠ 0) (hx : p.IsRoot x) :
    Nonempty (ResidueRotationCollisionCertificate a r p) := by
  obtain ⟨zeta, hzetaA, hzetaR, hzetaOne⟩ :=
    exists_root_of_unity_not_fixed a r ha hr0 hra
  have hzetaTwoA : zeta ^ (2 * a) = 1 := by
    calc
      zeta ^ (2 * a) = zeta ^ (a * 2) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [hzetaA, one_pow]
  have hzetaThreeA : zeta ^ (3 * a) = 1 := by
    calc
      zeta ^ (3 * a) = zeta ^ (a * 3) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hzetaA, one_pow]
  have hzetaFourA : zeta ^ (4 * a) = 1 := by
    calc
      zeta ^ (4 * a) = zeta ^ (a * 4) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 4 := by rw [pow_mul]
      _ = 1 := by rw [hzetaA, one_pow]
  have hsource : ((x, 1) : ℂ × ℂ) ≠ (x, zeta) := by
    intro h
    have hsecond : (1 : ℂ) = zeta := congrArg Prod.snd h
    exact hzetaOne hsecond.symm
  have hxeval : p.eval x = 0 := hx
  have hEValues :
      eResidueRotationMap a r p (x, 1) =
        eResidueRotationMap a r p (x, zeta) := by
    funext i
    fin_cases i <;>
      simp [eResidueRotationMap, hzetaThreeA, hxeval]
  have hHValues :
      hResidueRotationMap a r p (x, 1) =
        hResidueRotationMap a r p (x, zeta) := by
    funext i
    fin_cases i <;>
      simp [hResidueRotationMap, hzetaTwoA, hzetaFourA, hxeval]
  have hrestrictedZero :
      (rotationRestrictedDifference zeta r p).eval x = 0 := by
    rw [rotationRestrictedDifference_eq, eval_mul, eval_C, hxeval, mul_zero]
  have hscalar : (1 - zeta ^ r : ℂ) ≠ 0 :=
    sub_ne_zero.mpr hzetaR.symm
  have hrestrictedNe : rotationRestrictedDifference zeta r p ≠ 0 := by
    rw [rotationRestrictedDifference_eq]
    exact mul_ne_zero (C_ne_zero.mpr hscalar) hp
  have hfinite :
      Set.Finite {u : ℂ |
        (rotationRestrictedDifference zeta r p).IsRoot u} :=
    _root_.Polynomial.finite_setOfPred_isRoot hrestrictedNe
  exact ⟨{
    zeta := zeta
    x := x
    zeta_pow_a := hzetaA
    zeta_pow_r_ne_one := hzetaR
    zeta_ne_one := hzetaOne
    sourcePoints_ne := hsource
    eValues_eq := hEValues
    hValues_eq := hHValues
    restrictedDifference_zero := hrestrictedZero
    restrictedDifference_ne_zero := hrestrictedNe
    restrictedRootSet_finite := hfinite
    restrictedRootSet_discrete := hfinite.isDiscrete
  }⟩

end OnLeConjecture.DThree
