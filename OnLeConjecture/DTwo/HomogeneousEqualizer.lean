/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.RootsOfUnity
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The polynomial character equalizer in the order two case

This file proves the character calculation in the homogeneous equalizer
argument. A polynomial `K` in `T` whose coefficients are polynomials in `S`
satisfies the sector identity

`K(S, T) = ζ^e K(S, ζ^j T)`.

If `ζ` is a primitive `k`th root of unity, every nonzero coefficient of
`T^h` then satisfies `k ∣ e + j * h`. When `L = k + j`, multiplication by
`y^e` followed by `T = y^L` therefore produces a polynomial in `S` and
`y^k`.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- Substitute `χ * T` for `T` in a polynomial whose coefficients are
polynomials in `S`. -/
noncomputable def rotateSecondVariable
    (χ : ℂ) (K : _root_.Polynomial (_root_.Polynomial ℂ)) :
    _root_.Polynomial (_root_.Polynomial ℂ) :=
  K.comp (C (C χ) * X)

theorem rotateSecondVariable_eq
    (χ : ℂ) (K : _root_.Polynomial (_root_.Polynomial ℂ)) :
    rotateSecondVariable χ K = K.comp (C (C χ) * X) := by
  rfl

/-- The sector identity forces the character of every nonzero coefficient to
be trivial. This is the coefficient calculation in
`eq:kernelcharacter` of the pinned proof. -/
theorem dvd_character_of_sectorIdentity
    {k e j h : ℕ} {ζ : ℂ} (K : _root_.Polynomial (_root_.Polynomial ℂ))
    (hζ : IsPrimitiveRoot ζ k)
    (hsector : K = C (C (ζ ^ e)) * rotateSecondVariable (ζ ^ j) K)
    (hcoeff : K.coeff h ≠ 0) :
    k ∣ e + j * h := by
  have hcoefficient := congrArg (fun p : _root_.Polynomial (_root_.Polynomial ℂ) ↦
    p.coeff h) hsector
  rw [rotateSecondVariable, _root_.Polynomial.coeff_C_mul,
    _root_.Polynomial.comp_C_mul_X_coeff] at hcoefficient
  have hscaled :
      K.coeff h = C (ζ ^ (e + j * h)) * K.coeff h := by
    calc
      K.coeff h = C (ζ ^ e) *
          (K.coeff h * C ((ζ ^ j) ^ h)) := by
            simpa using hcoefficient
      _ = C (ζ ^ (e + j * h)) * K.coeff h := by
        simp only [pow_add, pow_mul, map_mul]
        ring
  have hone : (C (ζ ^ (e + j * h)) : _root_.Polynomial ℂ) = 1 := by
    apply mul_right_cancel₀ hcoeff
    simpa using hscaled.symm
  have hpower : ζ ^ (e + j * h) = 1 := by
    have hone' :
        (C (ζ ^ (e + j * h)) : _root_.Polynomial ℂ) = C 1 := by
      simpa using hone
    exact _root_.Polynomial.C_injective hone'
  exact hζ.dvd_of_pow_eq_one _ hpower

/-- Reindex a sector polynomial so that the exponent records a power of
`y^k`. Coefficients remain polynomials in `S`. -/
noncomputable def descendSector
    (k e L : ℕ) (K : _root_.Polynomial (_root_.Polynomial ℂ)) :
    _root_.Polynomial (_root_.Polynomial ℂ) :=
  K.sum fun h a ↦ C a * X ^ ((e + L * h) / k)

/-- If every exponent occurring after the substitution `T = y^L` becomes a
multiple of `k`, the sector polynomial descends to a polynomial in `S` and
`y^k`. -/
theorem eval₂_descendSector
    {k e L : ℕ} (K : _root_.Polynomial (_root_.Polynomial ℂ))
    (hdiv : ∀ h : ℕ, K.coeff h ≠ 0 → k ∣ e + L * h) :
    (descendSector k e L K).eval₂ C (X ^ k) =
      X ^ e * K.eval₂ C (X ^ L) := by
  rw [descendSector, _root_.Polynomial.eval₂_sum,
    _root_.Polynomial.eval₂_eq_sum]
  simp only [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X]
  rw [_root_.Polynomial.sum_def, _root_.Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hcoeff : K.coeff h ≠ 0 :=
    _root_.Polynomial.mem_support_iff.mp hh
  have hexponent : k * ((e + L * h) / k) = e + L * h :=
    Nat.mul_div_cancel' (hdiv h hcoeff)
  rw [← pow_mul, hexponent, pow_add, pow_mul]
  ring

/-- Reindex a sector after substituting `τ * y^L` for `T`. -/
noncomputable def descendScaledSector
    (τ : ℂ) (k e L : ℕ) (K : _root_.Polynomial (_root_.Polynomial ℂ)) :
    _root_.Polynomial (_root_.Polynomial ℂ) :=
  K.sum fun h a ↦ C (C (τ ^ h) * a) * X ^ ((e + L * h) / k)

/-- The descent identity with the scalar in the substitution
`T = τ * y^L`. -/
theorem eval₂_descendScaledSector
    (τ : ℂ) {k e L : ℕ} (K : _root_.Polynomial (_root_.Polynomial ℂ))
    (hdiv : ∀ h : ℕ, K.coeff h ≠ 0 → k ∣ e + L * h) :
    (descendScaledSector τ k e L K).eval₂ C (X ^ k) =
      X ^ e * K.eval₂ C (C (C τ) * X ^ L) := by
  rw [descendScaledSector, _root_.Polynomial.eval₂_sum,
    _root_.Polynomial.eval₂_eq_sum]
  simp only [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X]
  rw [_root_.Polynomial.sum_def, _root_.Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hcoeff : K.coeff h ≠ 0 :=
    _root_.Polynomial.mem_support_iff.mp hh
  have hexponent : k * ((e + L * h) / k) = e + L * h :=
    Nat.mul_div_cancel' (hdiv h hcoeff)
  rw [← pow_mul, hexponent, pow_add, pow_mul]
  simp only [map_mul, map_pow]
  ring

/-- The character descent used after the evenness reduction in the
homogeneous equalizer proof. -/
theorem exists_sectorDescent_of_sectorIdentity
    {k e j : ℕ} {ζ : ℂ} (K : _root_.Polynomial (_root_.Polynomial ℂ))
    (hζ : IsPrimitiveRoot ζ k)
    (hsector : K = C (C (ζ ^ e)) * rotateSecondVariable (ζ ^ j) K) :
    ∃ Q : _root_.Polynomial (_root_.Polynomial ℂ),
      Q.eval₂ C (X ^ k) = X ^ e * K.eval₂ C (X ^ (k + j)) := by
  refine ⟨descendSector k e (k + j) K, eval₂_descendSector K ?_⟩
  intro h hcoeff
  have hcharacter : k ∣ e + j * h :=
    dvd_character_of_sectorIdentity K hζ hsector hcoeff
  have hmultiple : k ∣ k * h := dvd_mul_right k h
  rw [add_mul]
  simpa [add_assoc, add_comm, add_left_comm] using
    dvd_add hcharacter hmultiple

/-- The character descent with the scalar occurring in
`T = -β_j c⁻¹ y^(k+j)` in the pinned proof. -/
theorem exists_scaledSectorDescent_of_sectorIdentity
    (τ : ℂ) {k e j : ℕ} {ζ : ℂ}
    (K : _root_.Polynomial (_root_.Polynomial ℂ))
    (hζ : IsPrimitiveRoot ζ k)
    (hsector : K = C (C (ζ ^ e)) * rotateSecondVariable (ζ ^ j) K) :
    ∃ Q : _root_.Polynomial (_root_.Polynomial ℂ),
      Q.eval₂ C (X ^ k) =
        X ^ e * K.eval₂ C (C (C τ) * X ^ (k + j)) := by
  refine ⟨descendScaledSector τ k e (k + j) K,
    eval₂_descendScaledSector τ K ?_⟩
  intro h hcoeff
  have hcharacter : k ∣ e + j * h :=
    dvd_character_of_sectorIdentity K hζ hsector hcoeff
  have hmultiple : k ∣ k * h := dvd_mul_right k h
  rw [add_mul]
  simpa [add_assoc, add_comm, add_left_comm] using
    dvd_add hcharacter hmultiple

end OnLeConjecture.DTwo
