/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.HomogeneousEqualizerQuotient
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Descent from the quadratic homogeneous equalizer

This file continues the quadratic component calculation through the change

`K(S, T) = G(S - T, T)`.

The change converts the identity obtained from the component quotient into
the character identity for `K`. The coefficient divisibility theorem and the
polynomial descent from `HomogeneousEqualizer` then apply.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open scoped Polynomial.Bivariate

/-- Evaluating a polynomial and then embedding it as a coefficient agrees
with embedding the evaluation point first. -/
theorem aeval_C_comp
    (p q : EqualizerParameterRing) :
    aeval (C q : EqualizerBaseRing) p = C (p.comp q) := by
  rw [aeval_def]
  have hmap : algebraMap ℂ EqualizerBaseRing =
      (C : EqualizerParameterRing →+* EqualizerBaseRing).comp
        (C : ℂ →+* EqualizerParameterRing) := by
    ext z
    simp
  rw [hmap]
  simpa only [comp] using
    (_root_.Polynomial.hom_eval₂
      p
      (C : ℂ →+* EqualizerParameterRing)
      (C : EqualizerParameterRing →+* EqualizerBaseRing) q).symm

/-- Replace the square variable `U` in `G(U,T)` by
`U + (1 - χ)T` and replace `T` by `χT`. -/
noncomputable def rotateSquarePolynomial
    (χ : ℂ) (G : EqualizerBaseRing) : EqualizerBaseRing :=
  (G.map (scaleEqualizerParameter χ)).comp
    (X + C (C (1 - χ) * X))

/-- The rotated square substitution as a complex algebra homomorphism. -/
noncomputable def rotateSquareAlgHom (χ : ℂ) :
    EqualizerBaseRing →ₐ[ℂ] EqualizerBaseRing :=
  _root_.Polynomial.aevalAeval
    (C (C χ * X)) (Y + C (C (1 - χ) * X))

/-- The algebra homomorphism description of the rotated square
substitution agrees with its expression using `map` and `comp`. -/
theorem rotateSquareAlgHom_apply
    (χ : ℂ) (G : EqualizerBaseRing) :
    rotateSquareAlgHom χ G = rotateSquarePolynomial χ G := by
  induction G using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
      simp [rotateSquarePolynomial, hp, hq]
  | monomial n a =>
      have hx : (C (C χ) * C X : EqualizerBaseRing) =
          C (C χ * X) := by
        rw [map_mul]
      have ha : aeval (C (C χ) * C X : EqualizerBaseRing) a =
          C (a.comp (C χ * X)) := by
        rw [hx, aeval_C_comp]
      simp [rotateSquareAlgHom, rotateSquarePolynomial,
        scaleEqualizerParameter_apply, ha]

/-- Change from `G(U,T)` to `K(S,T) = G(S-T,T)`.

The inner variable of the target is `S` and the outer variable is `T`.
-/
noncomputable def squareToSTAlgHom :
    EqualizerBaseRing →ₐ[ℂ] EqualizerBaseRing :=
  _root_.Polynomial.aevalAeval
    (Y : EqualizerBaseRing) (C X - Y)

/-- The polynomial `K(S,T) = G(S-T,T)`. -/
noncomputable def squareToST (G : EqualizerBaseRing) : EqualizerBaseRing :=
  squareToSTAlgHom G

theorem squareToST_eq_aevalAeval (G : EqualizerBaseRing) :
    squareToST G =
      G.aevalAeval (Y : EqualizerBaseRing) (C X - Y) := by
  rfl

/-- The inverse change sends `S` to `U + T` and sends `T` to `T`. -/
noncomputable def stToSquareAlgHom :
    EqualizerBaseRing →ₐ[ℂ] EqualizerBaseRing :=
  _root_.Polynomial.aevalAeval
    (Y + C X : EqualizerBaseRing) (C X)

theorem squareToST_comp_stToSquare :
    squareToSTAlgHom.comp stToSquareAlgHom =
      AlgHom.id ℂ EqualizerBaseRing := by
  apply (_root_.Polynomial.aevalAevalEquiv
    ℂ EqualizerBaseRing).symm.injective
  apply Prod.ext
  · simp [squareToSTAlgHom, stToSquareAlgHom]
  · simp [squareToSTAlgHom, stToSquareAlgHom]

theorem stToSquare_comp_squareToST :
    stToSquareAlgHom.comp squareToSTAlgHom =
      AlgHom.id ℂ EqualizerBaseRing := by
  apply (_root_.Polynomial.aevalAevalEquiv
    ℂ EqualizerBaseRing).symm.injective
  apply Prod.ext
  · simp [squareToSTAlgHom, stToSquareAlgHom]
  · simp [squareToSTAlgHom, stToSquareAlgHom]

/-- The coordinate change `U = S - T` as a complex algebra equivalence. -/
noncomputable def squareToSTAlgEquiv :
    EqualizerBaseRing ≃ₐ[ℂ] EqualizerBaseRing :=
  AlgEquiv.ofAlgHom squareToSTAlgHom stToSquareAlgHom
    squareToST_comp_stToSquare stToSquare_comp_squareToST

@[simp]
theorem squareToSTAlgEquiv_apply (G : EqualizerBaseRing) :
    squareToSTAlgEquiv G = squareToST G := by
  rfl

/-- Replace `T` by `χT` while fixing `S`. -/
noncomputable def rotateSTAlgHom (χ : ℂ) :
    EqualizerBaseRing →ₐ[ℂ] EqualizerBaseRing :=
  _root_.Polynomial.aevalAeval
    (C X) (C (C χ) * Y)

/-- The algebra homomorphism description of rotation in `T` agrees with
`rotateSecondVariable`. -/
theorem rotateSTAlgHom_apply
    (χ : ℂ) (K : EqualizerBaseRing) :
    rotateSTAlgHom χ K = rotateSecondVariable χ K := by
  induction K using _root_.Polynomial.induction_on' with
  | add p q hp hq =>
      simp [rotateSecondVariable_eq, hp, hq]
  | monomial n a =>
      have ha : aeval (C X : EqualizerBaseRing) a = C a := by
        simpa using aeval_C_comp a X
      simp [rotateSTAlgHom, rotateSecondVariable_eq, ha]

@[simp]
theorem squareToST_C_C (z : ℂ) :
    squareToST (C (C z)) = C (C z) := by
  simp [squareToST, squareToSTAlgHom]

@[simp]
theorem squareToST_inner_X :
    squareToST (C X) = Y := by
  simp [squareToST, squareToSTAlgHom]

@[simp]
theorem squareToST_outer_X :
    squareToST (Y : EqualizerBaseRing) = C X - Y := by
  simp [squareToST, squareToSTAlgHom]

/-- The change `U = S - T` intertwines the rotated square substitution with
rotation of the second variable. -/
theorem squareToST_rotateSquarePolynomial
    (χ : ℂ) (G : EqualizerBaseRing) :
    squareToST (rotateSquarePolynomial χ G) =
      rotateSecondVariable χ (squareToST G) := by
  rw [← rotateSquareAlgHom_apply, ← rotateSTAlgHom_apply]
  change squareToSTAlgHom (rotateSquareAlgHom χ G) =
    rotateSTAlgHom χ (squareToSTAlgHom G)
  have hhom : squareToSTAlgHom.comp (rotateSquareAlgHom χ) =
      (rotateSTAlgHom χ).comp squareToSTAlgHom := by
    apply (_root_.Polynomial.aevalAevalEquiv
      ℂ EqualizerBaseRing).symm.injective
    apply Prod.ext
    · simp [squareToSTAlgHom, rotateSquareAlgHom, rotateSTAlgHom]
    · simp [squareToSTAlgHom, rotateSquareAlgHom, rotateSTAlgHom]
      ring
  exact DFunLike.congr_fun hhom G

/-- Expanding after the rotated square substitution gives the coefficient of
`1` obtained by evaluating in the quadratic component. -/
theorem expand_rotateSquarePolynomial
    (χ : ℂ) (G : EqualizerBaseRing) :
    expand EqualizerParameterRing 2 (rotateSquarePolynomial χ G) =
      ((G.map (scaleEqualizerParameter χ)).map C).eval
        (componentSquare χ) := by
  rw [_root_.Polynomial.eval_map]
  change expand EqualizerParameterRing 2 (rotateSquarePolynomial χ G) =
    (G.map (scaleEqualizerParameter χ)).comp (componentSquare χ)
  rw [componentSquare_eq]
  simp only [rotateSquarePolynomial, expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp

/-- Evaluating `G(x²,T)` at `(X,χT)` in the component quotient is the
image of the rotated square polynomial evaluated at `x²`. -/
theorem componentSectorValue_comp_square
    (χ : ℂ) (G : EqualizerBaseRing) :
    componentSectorValue χ (G.comp (X ^ 2)) =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
        (expand EqualizerParameterRing 2 (rotateSquarePolynomial χ G)) := by
  rw [componentSectorValue_eq]
  rw [_root_.Polynomial.map_comp, _root_.Polynomial.map_pow,
    _root_.Polynomial.map_X, _root_.Polynomial.map_comp,
    _root_.Polynomial.map_pow, _root_.Polynomial.map_X]
  change AdjoinRoot.mk (componentPolynomial χ)
      (expand EqualizerBaseRing 2
        ((G.map (scaleEqualizerParameter χ)).map C)) = _
  rw [component_mk_expand_two, expand_rotateSquarePolynomial]

/-- The coefficient embedding into the monic quadratic quotient is
injective. -/
theorem componentAlgebraMap_injective (χ : ℂ) :
    Function.Injective
      (algebraMap EqualizerBaseRing (EqualizerComponentRing χ)) := by
  change Function.Injective (AdjoinRoot.of (componentPolynomial χ))
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [degree_eq_natDegree (componentPolynomial_monic χ).ne_zero,
    componentPolynomial_natDegree]
  norm_num

/-- Once `H(x,T) = G(x²,T)`, the component identity is the rotated square
identity for `G`. -/
theorem rotateSquareIdentity_of_componentSectorIdentity
    {ζ χ : ℂ} (e : ℕ) (G : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
          (G.comp (X ^ 2)) =
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
            (C (C (ζ ^ e))) *
          componentSectorValue χ (G.comp (X ^ 2))) :
    G = C (C (ζ ^ e)) * rotateSquarePolynomial χ G := by
  have hbase :
      G.comp (X ^ 2) =
        C (C (ζ ^ e)) *
          expand EqualizerParameterRing 2
            (rotateSquarePolynomial χ G) := by
    apply componentAlgebraMap_injective χ
    calc
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
          (G.comp (X ^ 2)) =
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
              (C (C (ζ ^ e))) *
            componentSectorValue χ (G.comp (X ^ 2)) := hsector
      _ = algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
              (C (C (ζ ^ e))) *
            algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
              (expand EqualizerParameterRing 2
                (rotateSquarePolynomial χ G)) := by
          rw [componentSectorValue_comp_square]
      _ = algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
            (C (C (ζ ^ e)) *
              expand EqualizerParameterRing 2
                (rotateSquarePolynomial χ G)) := by
          rw [map_mul]
  apply expand_injective (R := EqualizerParameterRing) (by norm_num : 0 < 2)
  simpa [expand_eq_comp_X_pow] using hbase

/-- The component identity becomes the character identity after the change
`K(S,T) = G(S-T,T)`. -/
theorem squareToST_sectorIdentity_of_componentSectorIdentity
    {ζ χ : ℂ} (e : ℕ) (G : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
          (G.comp (X ^ 2)) =
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
            (C (C (ζ ^ e))) *
          componentSectorValue χ (G.comp (X ^ 2))) :
    squareToST G =
      C (C (ζ ^ e)) * rotateSecondVariable χ (squareToST G) := by
  have hG := rotateSquareIdentity_of_componentSectorIdentity e G hsector
  calc
    squareToST G =
        squareToST (C (C (ζ ^ e)) * rotateSquarePolynomial χ G) := by
      exact congrArg squareToST hG
    _ = squareToST (C (C (ζ ^ e))) *
        squareToST (rotateSquarePolynomial χ G) := by
      exact map_mul squareToSTAlgHom _ _
    _ = C (C (ζ ^ e)) *
        rotateSecondVariable χ (squareToST G) := by
      rw [squareToST_C_C, squareToST_rotateSquarePolynomial]

/-- A single component identity yields the square factorization, the
character condition, divisibility of the exponent after `T = τy^(k+j)`,
and a polynomial in `S` and `y^k` representing the sector. -/
theorem exists_square_change_and_descent_of_componentSectorIdentity
    (τ : ℂ) {k e j : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ k)
    (H : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing
          (EqualizerComponentRing (ζ ^ j)) H =
        algebraMap EqualizerBaseRing
            (EqualizerComponentRing (ζ ^ j))
            (C (C (ζ ^ e))) * componentSectorValue (ζ ^ j) H) :
    ∃ G Q : EqualizerBaseRing,
      H = G.comp (X ^ 2) ∧
      squareToST G =
        C (C (ζ ^ e)) *
          rotateSecondVariable (ζ ^ j) (squareToST G) ∧
      (∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
        k ∣ e + j * h) ∧
      (∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
        k ∣ e + (k + j) * h) ∧
      Q.eval₂ C (X ^ k) =
        X ^ e * (squareToST G).eval₂ C
          (C (C τ) * X ^ (k + j)) := by
  rcases exists_polynomial_in_square_of_primitiveSectorIdentity
      hk hζ H hsector with ⟨G, hH⟩
  have hsectorG :
      algebraMap EqualizerBaseRing
          (EqualizerComponentRing (ζ ^ j)) (G.comp (X ^ 2)) =
        algebraMap EqualizerBaseRing
            (EqualizerComponentRing (ζ ^ j))
            (C (C (ζ ^ e))) *
          componentSectorValue (ζ ^ j) (G.comp (X ^ 2)) := by
    simpa only [hH] using hsector
  have hK := squareToST_sectorIdentity_of_componentSectorIdentity
    e G hsectorG
  have hcharacter : ∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
      k ∣ e + j * h := by
    intro h hcoeff
    exact dvd_character_of_sectorIdentity (squareToST G) hζ hK hcoeff
  have htotal : ∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
      k ∣ e + (k + j) * h := by
    intro h hcoeff
    have hmultiple : k ∣ k * h := dvd_mul_right k h
    rw [add_mul]
    simpa [add_assoc, add_comm, add_left_comm] using
      dvd_add (hcharacter h hcoeff) hmultiple
  rcases exists_scaledSectorDescent_of_sectorIdentity
      τ (squareToST G) hζ hK with ⟨Q, hQ⟩
  exact ⟨G, Q, hH, hK, hcharacter, htotal, hQ⟩

/-- Sector independence extracts the identity for any chosen exponent from
the global identity in the iterated component quotient. -/
theorem componentSectorIdentity_of_globalIdentity
    (τ : ℂ) {j L : ℕ} {ζ : ℂ} (hL : 0 < L)
    (H : Fin L → EqualizerBaseRing)
    (hglobal :
      (∑ e : Fin L,
          algebraMap EqualizerBaseRing
              (EqualizerComponentRing (ζ ^ j)) (H e) •
            AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^
              (e : ℕ)) =
        ∑ e : Fin L,
          (algebraMap EqualizerBaseRing
              (EqualizerComponentRing (ζ ^ j))
              (C (C (ζ ^ (e : ℕ)))) *
            componentSectorValue (ζ ^ j) (H e)) •
              AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^
                (e : ℕ))
    (e : Fin L) :
    algebraMap EqualizerBaseRing
        (EqualizerComponentRing (ζ ^ j)) (H e) =
      algebraMap EqualizerBaseRing
          (EqualizerComponentRing (ζ ^ j))
          (C (C (ζ ^ (e : ℕ)))) *
        componentSectorValue (ζ ^ j) (H e) := by
  let a : Fin L → EqualizerComponentRing (ζ ^ j) := fun d ↦
    algebraMap EqualizerBaseRing
        (EqualizerComponentRing (ζ ^ j)) (H d) -
      algebraMap EqualizerBaseRing
          (EqualizerComponentRing (ζ ^ j))
          (C (C (ζ ^ (d : ℕ)))) *
        componentSectorValue (ζ ^ j) (H d)
  have hzero :
      (∑ d : Fin L, a d •
        AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^
          (d : ℕ)) = 0 := by
    simpa only [a, sub_smul, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr hglobal
  have hcoefficients :=
    (sector_sum_eq_zero_iff τ (ζ ^ j) hL a).mp hzero
  exact sub_eq_zero.mp (hcoefficients e)

/-- The full polynomial conclusion of the homogeneous equalizer calculation.
Every sector admits the change `K(S,T) = G(S-T,T)`, satisfies the character
divisibility condition, and descends after `T = τy^(k+j)` to a polynomial in
`S` and `y^k`. -/
theorem every_sector_square_change_and_descent
    (τ : ℂ) {k j : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ k)
    (H : Fin (k + j) → EqualizerBaseRing)
    (hglobal :
      (∑ e : Fin (k + j),
          algebraMap EqualizerBaseRing
              (EqualizerComponentRing (ζ ^ j)) (H e) •
            AdjoinRoot.root
                (sectorPolynomial τ (ζ ^ j) (k + j)) ^
              (e : ℕ)) =
        ∑ e : Fin (k + j),
          (algebraMap EqualizerBaseRing
              (EqualizerComponentRing (ζ ^ j))
              (C (C (ζ ^ (e : ℕ)))) *
            componentSectorValue (ζ ^ j) (H e)) •
              AdjoinRoot.root
                  (sectorPolynomial τ (ζ ^ j) (k + j)) ^
                (e : ℕ)) :
    ∀ e : Fin (k + j), ∃ G Q : EqualizerBaseRing,
      H e = G.comp (X ^ 2) ∧
      squareToST G =
        C (C (ζ ^ (e : ℕ))) *
          rotateSecondVariable (ζ ^ j) (squareToST G) ∧
      (∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
        k ∣ (e : ℕ) + j * h) ∧
      (∀ h : ℕ, (squareToST G).coeff h ≠ 0 →
        k ∣ (e : ℕ) + (k + j) * h) ∧
      Q.eval₂ C (X ^ k) =
        X ^ (e : ℕ) * (squareToST G).eval₂ C
          (C (C τ) * X ^ (k + j)) := by
  have hL : 0 < k + j := by omega
  intro e
  have hsector := componentSectorIdentity_of_globalIdentity
    τ hL H hglobal e
  exact exists_square_change_and_descent_of_componentSectorIdentity
    τ hk hζ (H e) hsector

end OnLeConjecture.DTwo
