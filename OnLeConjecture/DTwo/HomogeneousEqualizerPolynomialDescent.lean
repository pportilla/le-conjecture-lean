/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicInitialComponentIdentity
public import OnLeConjecture.DTwo.HomogeneousEqualizerDescent
public import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Polynomial residue reconstruction for the homogeneous equalizer

Residues of the second exponent modulo `L` express an arbitrary polynomial
as a finite sum `Σ y^e H_e(x,τ*y^L)`. All residue polynomials are constructed
from the input polynomial, not assumed as additional equalizer data.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open scoped BigOperators Polynomial.Bivariate

/-- Substitution `T=τ*y^L` and `x=x` in the component base ring. -/
@[expose] noncomputable def sectorReconstructionAlgHom (τ : ℂ) (L : ℕ) :
    EqualizerBaseRing →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  Polynomial.aevalAeval (MvPolynomial.C τ * MvPolynomial.X 1 ^ L) (MvPolynomial.X 0)

/-- Finite residue decomposition of an actual polynomial, with coefficients
in the variables `x,T` and with `T=τ*y^L`. -/
theorem exists_sector_polynomial_representation (τ : ℂ) (hτ : τ ≠ 0)
    (L : ℕ) (hL : 0 < L) (P : MvPolynomial (Fin 2) ℂ) :
    ∃ H : Fin L → EqualizerBaseRing,
      P = ∑ e : Fin L, MvPolynomial.X 1 ^ e.1 * sectorReconstructionAlgHom τ L (H e) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨HP, hP⟩ := hP
    obtain ⟨HQ, hQ⟩ := hQ
    refine ⟨fun e => HP e + HQ e, ?_⟩
    simp only [map_add, mul_add, Finset.sum_add_distrib, ← hP, ← hQ]
  | monomial d c =>
    let e : Fin L := ⟨d 1 % L, Nat.mod_lt _ hL⟩
    let q := d 1 / L
    let H : EqualizerBaseRing := C (C (c / τ ^ q) * X ^ q) * X ^ d 0
    refine ⟨Pi.single e H, ?_⟩
    rw [Finset.sum_eq_single e]
    · simp only [Pi.single_eq_same]
      have heq : e.1 + L * q = d 1 := Nat.mod_add_div (d 1) L
      have hscalar : c / τ ^ q * τ ^ q = c := div_mul_cancel₀ _ (pow_ne_zero q hτ)
      simp only [H, sectorReconstructionAlgHom, map_mul, map_pow,
        Polynomial.aevalAeval_C, Polynomial.aevalAeval_Y,
        Polynomial.aeval_C, Polynomial.aeval_X]
      change MvPolynomial.monomial d c = MvPolynomial.X 1 ^ e.1 *
        (MvPolynomial.C (c / τ ^ q) * (MvPolynomial.C τ * MvPolynomial.X 1 ^ L) ^ q *
          MvPolynomial.X 0 ^ d 0)
      calc
        MvPolynomial.monomial d c =
            MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 :=
          MvPolynomial.monomial_fin_two d c
        _ = MvPolynomial.C (c / τ ^ q * τ ^ q) * MvPolynomial.X 0 ^ d 0 *
            MvPolynomial.X 1 ^ (e.1 + L * q) := by rw [hscalar, heq]
        _ = _ := by simp only [map_mul, map_pow, pow_add, pow_mul, mul_pow]; ring
    · intro i hi hie
      simp [hie]
    · simp

theorem aeval_sectorReconstruction {A : Type*} [CommRing A] [Algebra ℂ A]
    (τ : ℂ) (L : ℕ) (x y : A) (H : EqualizerBaseRing) :
    MvPolynomial.aeval ![x, y] (sectorReconstructionAlgHom τ L H) =
      Polynomial.aevalAeval (algebraMap ℂ A τ * y ^ L) x H := by
  have h : (MvPolynomial.aeval ![x, y]).comp (sectorReconstructionAlgHom τ L) =
      Polynomial.aevalAeval (algebraMap ℂ A τ * y ^ L) x := by
    apply (Polynomial.aevalAevalEquiv ℂ A).symm.injective
    apply Prod.ext
    · simp [sectorReconstructionAlgHom]
    · simp [sectorReconstructionAlgHom]
  exact DFunLike.congr_fun h H

private theorem map_aevalAeval {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (T x : A) (H : EqualizerBaseRing) :
    f (Polynomial.aevalAeval T x H) = Polynomial.aevalAeval (f T) (f x) H := by
  have h : f.comp (Polynomial.aevalAeval T x) = Polynomial.aevalAeval (f T) (f x) := by
    apply (Polynomial.aevalAevalEquiv ℂ B).symm.injective
    apply Prod.ext <;> simp
  exact DFunLike.congr_fun h H

private theorem component_complex_scalar (χ c : ℂ) :
    algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C (C c)) =
      algebraMap ℂ (EqualizerComponentRing χ) c := by
  exact (IsScalarTower.algebraMap_apply ℂ EqualizerBaseRing (EqualizerComponentRing χ) c).symm

/-- The component substitution `H(x,T) ↦ H(X,χT)` as an algebra homomorphism. -/
@[expose] noncomputable def componentSectorAlgHom (χ : ℂ) :
    EqualizerBaseRing →ₐ[ℂ] EqualizerComponentRing χ where
  toRingHom := (AdjoinRoot.mk (componentPolynomial χ)).comp
    ((Polynomial.mapRingHom C).comp (Polynomial.mapRingHom (scaleEqualizerParameter χ)))
  commutes' c := by
    change AdjoinRoot.mk (componentPolynomial χ)
      (((C (C c) : EqualizerBaseRing).map (scaleEqualizerParameter χ)).map C) = _
    rw [Polynomial.map_C, scaleEqualizerParameter_apply, Polynomial.C_comp,
      Polynomial.map_C, AdjoinRoot.mk_C]
    exact component_complex_scalar χ c

@[simp] theorem componentSectorAlgHom_apply (χ : ℂ) (H : EqualizerBaseRing) :
    componentSectorAlgHom χ H = componentSectorValue χ H := by
  rw [componentSectorValue_eq]
  rfl

theorem componentSectorValue_eq_aevalAeval (χ : ℂ) (H : EqualizerBaseRing) :
    componentSectorValue χ H = Polynomial.aevalAeval
      (algebraMap ℂ (EqualizerComponentRing χ) χ *
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X))
      (AdjoinRoot.root (componentPolynomial χ)) H := by
  have h : componentSectorAlgHom χ = Polynomial.aevalAeval
      (algebraMap ℂ (EqualizerComponentRing χ) χ *
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X))
      (AdjoinRoot.root (componentPolynomial χ)) := by
    apply (Polynomial.aevalAevalEquiv ℂ (EqualizerComponentRing χ)).symm.injective
    apply Prod.ext
    · change AdjoinRoot.mk (componentPolynomial χ)
        (((C X : EqualizerBaseRing).map (scaleEqualizerParameter χ)).map C) = _
      rw [Polynomial.map_C, scaleEqualizerParameter_apply, Polynomial.X_comp,
        Polynomial.map_C, AdjoinRoot.mk_C, map_mul, map_mul]
      change algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C (C χ)) *
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (C X) = _
      rw [component_complex_scalar]
      simp
    · change AdjoinRoot.mk (componentPolynomial χ)
        (((X : EqualizerBaseRing).map (scaleEqualizerParameter χ)).map C) = _
      rw [Polynomial.map_X, Polynomial.map_X, AdjoinRoot.mk_X]
      simp
  rw [← h, componentSectorAlgHom_apply]

private theorem aevalAeval_base_algebraMap {A : Type*} [CommRing A]
    [Algebra ℂ A] [Algebra EqualizerBaseRing A] [IsScalarTower ℂ EqualizerBaseRing A]
    (H : EqualizerBaseRing) :
    Polynomial.aevalAeval (algebraMap EqualizerBaseRing A (C X))
      (algebraMap EqualizerBaseRing A X) H = algebraMap EqualizerBaseRing A H := by
  have h : Polynomial.aevalAeval (algebraMap EqualizerBaseRing A (C X))
      (algebraMap EqualizerBaseRing A X) = IsScalarTower.toAlgHom ℂ EqualizerBaseRing A := by
    apply (Polynomial.aevalAevalEquiv ℂ A).symm.injective
    apply Prod.ext <;> simp
  exact DFunLike.congr_fun h H

theorem iteratedParameter_eq_scalar_mul_sector_pow (τ χ : ℂ) (L : ℕ) (hτ : τ ≠ 0) :
    iteratedCoordinate τ χ L .parameter =
      algebraMap ℂ (EqualizerSectorRing τ χ L) τ * iteratedCoordinate τ χ L .sector ^ L := by
  rw [iteratedSectorCoordinate_pow, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hτ, map_one, one_mul]

private theorem iteratedParameter_eq_base_algebraMap (τ χ : ℂ) (L : ℕ) :
    iteratedCoordinate τ χ L .parameter =
      algebraMap EqualizerBaseRing (EqualizerSectorRing τ χ L) (C X) := by
  rw [iteratedCoordinate_parameter_eq_algebraMap]
  have h : (C X : EqualizerBaseRing) =
      algebraMap EqualizerParameterRing EqualizerBaseRing X := by
    simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, ← IsScalarTower.algebraMap_apply EqualizerParameterRing EqualizerBaseRing]

theorem source_aeval_sectorReconstruction (τ χ : ℂ) (L : ℕ) (hτ : τ ≠ 0)
    (H : EqualizerBaseRing) :
    MvPolynomial.aeval
        ![iteratedCoordinate τ χ L .source, iteratedCoordinate τ χ L .sector]
        (sectorReconstructionAlgHom τ L H) =
      algebraMap EqualizerBaseRing (EqualizerSectorRing τ χ L) H := by
  rw [aeval_sectorReconstruction, ← iteratedParameter_eq_scalar_mul_sector_pow τ χ L hτ,
    iteratedParameter_eq_base_algebraMap, iteratedCoordinate_source_eq_algebraMap,
    aevalAeval_base_algebraMap]

theorem rotated_aeval_sectorReconstruction (τ ζ : ℂ) (k j : ℕ)
    (hτ : τ ≠ 0) (hζ : ζ ^ k = 1) (H : EqualizerBaseRing) :
    MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .component,
          algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) ζ *
            iteratedCoordinate τ (ζ ^ j) (k + j) .sector]
        (sectorReconstructionAlgHom τ (k + j) H) =
      algebraMap (EqualizerComponentRing (ζ ^ j))
        (EqualizerSectorRing τ (ζ ^ j) (k + j))
        (componentSectorValue (ζ ^ j) H) := by
  let A := EqualizerSectorRing τ (ζ ^ j) (k + j)
  have hpow : ζ ^ (k + j) = ζ ^ j := by rw [pow_add, hζ, one_mul]
  rw [aeval_sectorReconstruction, mul_pow, ← map_pow, hpow]
  rw [show algebraMap ℂ A τ *
      (algebraMap ℂ A (ζ ^ j) * iteratedCoordinate τ (ζ ^ j) (k + j) .sector ^ (k + j)) =
      algebraMap ℂ A (ζ ^ j) * iteratedCoordinate τ (ζ ^ j) (k + j) .parameter by
    rw [iteratedParameter_eq_scalar_mul_sector_pow τ (ζ ^ j) (k + j) hτ]; ring]
  rw [componentSectorValue_eq_aevalAeval]
  have hm := map_aevalAeval
    (IsScalarTower.toAlgHom ℂ (EqualizerComponentRing (ζ ^ j)) A)
    (algebraMap ℂ (EqualizerComponentRing (ζ ^ j)) (ζ ^ j) *
      algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (C X))
    (AdjoinRoot.root (componentPolynomial (ζ ^ j))) H
  change _ = (IsScalarTower.toAlgHom ℂ (EqualizerComponentRing (ζ ^ j)) A) _
  rw [hm]
  simp only [map_mul, AlgHom.commutes]
  change _ = Polynomial.aevalAeval
    (algebraMap ℂ A (ζ ^ j) * algebraMap (EqualizerComponentRing (ζ ^ j)) A
      (algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (C X)))
    (algebraMap (EqualizerComponentRing (ζ ^ j)) A
      (AdjoinRoot.root (componentPolynomial (ζ ^ j)))) H
  simp only [
    ← IsScalarTower.algebraMap_apply EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) A,
    iteratedParameter_eq_base_algebraMap, iteratedCoordinate_component_eq]
  rfl

/-- An equality of the two evaluations of a polynomial supplies the exact
sector identity required by the equalizer descent theorem. -/
theorem sector_identity_of_polynomial_identity (τ ζ : ℂ) (k j : ℕ)
    (hτ : τ ≠ 0) (hζ : ζ ^ k = 1) (P : MvPolynomial (Fin 2) ℂ)
    (H : Fin (k + j) → EqualizerBaseRing)
    (hH : P = ∑ e, MvPolynomial.X 1 ^ e.1 * sectorReconstructionAlgHom τ (k + j) (H e))
    (hP : MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .source,
          iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P =
      MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .component,
          algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) ζ *
            iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P) :
    (∑ e : Fin (k + j),
      algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (H e) •
        AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) (k + j)) ^ e.1) =
    ∑ e : Fin (k + j),
      (algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (C (C (ζ ^ e.1))) *
        componentSectorValue (ζ ^ j) (H e)) •
        AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) (k + j)) ^ e.1 := by
  rw [hH] at hP
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_X, Matrix.cons_val_one,
    Matrix.cons_val_zero, source_aeval_sectorReconstruction τ (ζ ^ j) (k + j) hτ,
    rotated_aeval_sectorReconstruction τ ζ k j hτ hζ] at hP
  simp only [Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply EqualizerBaseRing (EqualizerComponentRing (ζ ^ j))
      (EqualizerSectorRing τ (ζ ^ j) (k + j)),
    ← iteratedCoordinate_sector_eq]
  convert hP using 1 <;> apply Finset.sum_congr rfl <;> intro e he
  · ring
  · have hs : algebraMap EqualizerBaseRing (EqualizerSectorRing τ (ζ ^ j) (k + j))
        (C (C (ζ ^ e.1))) =
        algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) (ζ ^ e.1) :=
      (IsScalarTower.algebraMap_apply ℂ EqualizerBaseRing
        (EqualizerSectorRing τ (ζ ^ j) (k + j)) (ζ ^ e.1)).symm
    simp only [hs, mul_pow, ← map_pow]; ring

private theorem aevalAeval_comp {A : Type*} [CommRing A] [Algebra ℂ A]
    (S y : A) (H Z : EqualizerBaseRing) :
    Polynomial.aevalAeval S y (H.comp Z) =
      Polynomial.aevalAeval S (Polynomial.aevalAeval S y Z) H := by
  have h : (Polynomial.aevalAeval S y).comp (Polynomial.aevalAeval (C X) Z) =
      Polynomial.aevalAeval S (Polynomial.aevalAeval S y Z) := by
    apply (Polynomial.aevalAevalEquiv ℂ A).symm.injective
    apply Prod.ext <;> simp
  have hcomp : Polynomial.aevalAeval (C X) Z H = H.comp Z := by
    induction H using Polynomial.induction_on' with
    | add P Q hP hQ => simp only [map_add, Polynomial.add_comp, hP, hQ]
    | monomial n a =>
      have ha : Polynomial.aeval (C X : EqualizerBaseRing) a = C a := by
        simpa using Polynomial.aeval_algHom_apply
          (IsScalarTower.toAlgHom ℂ EqualizerParameterRing EqualizerBaseRing) X a
      simp [← Polynomial.C_mul_X_pow_eq_monomial, ha]
  simpa only [AlgHom.comp_apply, hcomp] using DFunLike.congr_fun h H

private theorem aevalAeval_squareToST {A : Type*} [CommRing A] [Algebra ℂ A]
    (x T : A) (G : EqualizerBaseRing) :
    Polynomial.aevalAeval (x ^ 2 + T) T (squareToST G) =
      Polynomial.aevalAeval T x (G.comp (X ^ 2)) := by
  rw [squareToST_eq_aevalAeval,
    map_aevalAeval (Polynomial.aevalAeval (x ^ 2 + T) T), aevalAeval_comp]
  simp

/-- Evaluation of the descended residue polynomial reconstructs its original
residue term as a polynomial in `x²+τ*y^L` and `y^k`. -/
theorem reconstructed_sector_eq_descended (τ : ℂ) (L k e : ℕ)
    (H G Q : EqualizerBaseRing) (hG : H = G.comp (X ^ 2))
    (hQ : Q.eval₂ C (X ^ k) = X ^ e * (squareToST G).eval₂ C (C (C τ) * X ^ L)) :
    MvPolynomial.X 1 ^ e * sectorReconstructionAlgHom τ L H =
      Polynomial.aevalAeval
        (MvPolynomial.X 0 ^ 2 + MvPolynomial.C τ * MvPolynomial.X 1 ^ L)
        (MvPolynomial.X 1 ^ k) Q := by
  let x : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0
  let y : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 1
  let T := MvPolynomial.C τ * y ^ L
  have h := congrArg (Polynomial.aevalAeval (x ^ 2 + T) y) hQ
  rw [← Polynomial.comp, ← Polynomial.comp,
    aevalAeval_comp, map_mul, map_pow, Polynomial.aevalAeval_Y,
    aevalAeval_comp] at h
  simp only [map_pow, Polynomial.aevalAeval_Y, map_mul, Polynomial.aevalAeval_C,
    Polynomial.aeval_C] at h
  change Polynomial.aevalAeval (x ^ 2 + T) (y ^ k) Q =
    y ^ e * Polynomial.aevalAeval (x ^ 2 + T) T (squareToST G) at h
  rw [aevalAeval_squareToST, ← hG] at h
  exact h.symm

/-- Polynomial equalizer descent, with the residue decomposition constructed
from `P` and the comparison supplied by its two quotient evaluations. -/
theorem exists_polynomial_descent_of_equalizer (τ : ℂ) (hτ : τ ≠ 0)
    {k j : ℕ} (hk : 0 < k) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (P : MvPolynomial (Fin 2) ℂ)
    (hP : MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .source,
          iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P =
      MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .component,
          algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) ζ *
            iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P) :
    ∃ Q : EqualizerBaseRing, P = Polynomial.aevalAeval
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.C τ * MvPolynomial.X 1 ^ (k + j))
      (MvPolynomial.X 1 ^ k) Q := by
  classical
  obtain ⟨H, hH⟩ := exists_sector_polynomial_representation τ hτ (k + j) (by omega) P
  have hglobal := sector_identity_of_polynomial_identity τ ζ k j hτ hζ.pow_eq_one P H hH hP
  choose G Q hG hrot hsupport hsupport' hQ using
    every_sector_square_change_and_descent τ hk hζ H hglobal
  refine ⟨∑ e, Q e, ?_⟩
  rw [map_sum, hH]
  apply Finset.sum_congr rfl
  intro e he
  exact reconstructed_sector_eq_descended τ (k + j) k e.1 (H e) (G e) (Q e) (hG e) (hQ e)

/-- The affine zero comparison of a homogeneous polynomial forces it to
belong to the algebra generated by `y^k` and `x²+τ*y^(k+j)`. -/
theorem exists_polynomial_descent_of_weighted_chart
    {k j d : ℕ} (hk : 0 < k) {τ ζ : ℂ} (hτ : τ ≠ 0)
    (hζ : IsPrimitiveRoot ζ k) (hchar : ζ ^ j ≠ 1)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![k + j, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + τ * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = 0) :
    ∃ Q : EqualizerBaseRing, P = Polynomial.aevalAeval
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.C τ * MvPolynomial.X 1 ^ (k + j))
      (MvPolynomial.X 1 ^ k) Q := by
  exact exists_polynomial_descent_of_equalizer τ hτ hk hζ P
    (cyclicInitial_iterated_equalizer_identity_of_chart k j d τ ζ hτ hchar P hP hchart)

/-- A scalar change of the quadratic generator expresses the descended
polynomial in the exact initial pair used by cyclic target correction. -/
theorem exists_initial_pair_polynomial_of_weighted_chart
    {k j d : ℕ} (hk : 0 < k) {b c ζ : ℂ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hζ : IsPrimitiveRoot ζ k) (hchar : ζ ^ j ≠ 1)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![k + j, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + (-b / c) * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = 0) :
    ∃ R : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.aeval
        ![MvPolynomial.X 1 ^ k,
          -MvPolynomial.C c * MvPolynomial.X 0 ^ 2 +
            MvPolynomial.C b * MvPolynomial.X 1 ^ (k + j)] R = P := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_descent_of_weighted_chart hk
    (div_ne_zero (neg_ne_zero.mpr hb) hc) hζ hchar P hP hchart
  refine ⟨Polynomial.aevalAeval
    (MvPolynomial.C (-c⁻¹) * MvPolynomial.X 1) (MvPolynomial.X 0) Q, ?_⟩
  rw [map_aevalAeval]
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero, MvPolynomial.algebraMap_eq]
  rw [hQ]
  congr 2
  have hcinv : MvPolynomial.C c * MvPolynomial.C c⁻¹ =
      (1 : MvPolynomial (Fin 2) ℂ) := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  simp only [map_neg, div_eq_mul_inv, map_mul]
  linear_combination MvPolynomial.X 0 ^ 2 * hcinv

end OnLeConjecture.DTwo
