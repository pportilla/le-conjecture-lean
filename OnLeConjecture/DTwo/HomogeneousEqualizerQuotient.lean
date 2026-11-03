/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.HomogeneousEqualizer
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The quadratic component in the homogeneous equalizer

This file formalizes the quotient ring used before the character calculation
in the homogeneous equalizer argument. The coefficient ring is
`ℂ[T][x]`. The component is obtained by adjoining `X` subject to

`X² - x² = (1 - χ)T`.

The quotient is free over `ℂ[T][x]` with basis `1, X`. A second monic
extension records the decomposition by the exponent of `y` modulo `L`.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial
open _root_.Module

/-- The index of the coefficient of even degree `2m`. -/
private def evenIndex : ℕ ↪ ℕ where
  toFun m := 2 * m
  inj' := by
    intro m n h
    exact Nat.mul_left_cancel (by omega) h

/-- The index of the coefficient of odd degree `2m + 1`. -/
private def oddIndex : ℕ ↪ ℕ where
  toFun m := 2 * m + 1
  inj' := by
    intro m n h
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h)

/-- The polynomial formed from the coefficients of even degree. -/
noncomputable def polynomialEvenPart
    {R : Type*} [Semiring R] (p : _root_.Polynomial R) :
    _root_.Polynomial R :=
  ⟨p.toFinsupp.comapDomain evenIndex evenIndex.injective⟩

/-- The polynomial formed from the coefficients of odd degree. -/
noncomputable def polynomialOddPart
    {R : Type*} [Semiring R] (p : _root_.Polynomial R) :
    _root_.Polynomial R :=
  ⟨p.toFinsupp.comapDomain oddIndex oddIndex.injective⟩

@[simp]
theorem polynomialEvenPart_coeff
    {R : Type*} [Semiring R] (p : _root_.Polynomial R) (m : ℕ) :
    (polynomialEvenPart p).coeff m = p.coeff (2 * m) := by
  change p.toFinsupp.coeff (evenIndex m) = p.toFinsupp.coeff (2 * m)
  rw [show evenIndex m = 2 * m by rfl]

@[simp]
theorem polynomialOddPart_coeff
    {R : Type*} [Semiring R] (p : _root_.Polynomial R) (m : ℕ) :
    (polynomialOddPart p).coeff m = p.coeff (2 * m + 1) := by
  change p.toFinsupp.coeff (oddIndex m) = p.toFinsupp.coeff (2 * m + 1)
  rw [show oddIndex m = 2 * m + 1 by rfl]

/-- Taking the odd part commutes with mapping coefficients. -/
theorem polynomialOddPart_map
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : _root_.Polynomial R) :
    polynomialOddPart (p.map f) = (polynomialOddPart p).map f := by
  ext m
  simp

/-- A polynomial is the sum of its even part in `X²` and `X` times its odd
part in `X²`. -/
theorem evenOdd_decomposition
    {R : Type*} [CommSemiring R] (p : _root_.Polynomial R) :
    p = expand R 2 (polynomialEvenPart p) +
      X * expand R 2 (polynomialOddPart p) := by
  ext n
  rcases n.even_or_odd with hn | hn
  · obtain ⟨m, rfl⟩ := hn
    cases m with
    | zero => simp [coeff_expand]
    | succ m =>
      rw [_root_.Polynomial.coeff_add,
        _root_.Polynomial.coeff_expand (by omega),
        show m.succ + m.succ = (m + m + 1) + 1 by omega,
        _root_.Polynomial.coeff_X_mul,
        _root_.Polynomial.coeff_expand (by omega)]
      simp only [polynomialEvenPart_coeff,
        if_neg (by omega : ¬ 2 ∣ m + m + 1), add_zero]
      rw [if_pos (by omega)]
      apply congrArg p.coeff
      omega
  · obtain ⟨m, rfl⟩ := hn
    rw [_root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_expand (by omega),
      show 2 * m + 1 = 2 * m + 1 by rfl,
      _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_expand (by omega)]
    simp only [if_neg (by omega : ¬ 2 ∣ 2 * m + 1), zero_add,
      if_pos (by omega : 2 ∣ 2 * m), polynomialOddPart_coeff]
    apply congrArg p.coeff
    omega

/-- The parameter polynomial ring `ℂ[T]`. -/
abbrev EqualizerParameterRing := _root_.Polynomial ℂ

/-- The base ring `ℂ[T][x]` of the quadratic component. -/
abbrev EqualizerBaseRing := _root_.Polynomial EqualizerParameterRing

/-- The element `x² + (1 - χ)T` of `ℂ[T][x]`. -/
noncomputable def componentSquare (χ : ℂ) : EqualizerBaseRing :=
  X ^ 2 + C (C (1 - χ) * X)

theorem componentSquare_eq (χ : ℂ) :
    componentSquare χ = X ^ 2 + C (C (1 - χ) * X) := by
  rfl

theorem componentSquare_monic (χ : ℂ) : (componentSquare χ).Monic := by
  exact monic_X_pow_add_C (C (1 - χ) * X) (by norm_num)

@[simp]
theorem componentSquare_natDegree (χ : ℂ) :
    (componentSquare χ).natDegree = 2 := by
  rw [componentSquare]
  exact natDegree_X_pow_add_C

/-- The monic equation for the component variable `X`. -/
noncomputable def componentPolynomial (χ : ℂ) :
    _root_.Polynomial EqualizerBaseRing :=
  X ^ 2 - C (componentSquare χ)

theorem componentPolynomial_eq (χ : ℂ) :
    componentPolynomial χ = X ^ 2 - C (componentSquare χ) := by
  rfl

theorem componentPolynomial_monic (χ : ℂ) :
    (componentPolynomial χ).Monic := by
  exact monic_X_pow_sub_C _ (by norm_num)

@[simp]
theorem componentPolynomial_natDegree (χ : ℂ) :
    (componentPolynomial χ).natDegree = 2 := by
  simp [componentPolynomial]

/-- The coordinate ring of the quadratic component. -/
abbrev EqualizerComponentRing (χ : ℂ) :=
  AdjoinRoot (componentPolynomial χ)

/-- The canonical power basis of the quadratic component. -/
noncomputable def componentPowerBasis (χ : ℂ) :
    PowerBasis EqualizerBaseRing (EqualizerComponentRing χ) :=
  AdjoinRoot.powerBasis' (componentPolynomial_monic χ)

@[simp]
theorem componentPowerBasis_dim (χ : ℂ) :
    (componentPowerBasis χ).dim = 2 := by
  simp [componentPowerBasis]

@[simp]
theorem componentPowerBasis_gen (χ : ℂ) :
    (componentPowerBasis χ).gen = AdjoinRoot.root (componentPolynomial χ) := by
  rfl

/-- The defining equation of the adjoined component variable. -/
theorem componentRoot_sq (χ : ℂ) :
    AdjoinRoot.root (componentPolynomial χ) ^ 2 =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
        (componentSquare χ) := by
  have hroot := AdjoinRoot.eval₂_root (componentPolynomial χ)
  rw [componentPolynomial, _root_.Polynomial.eval₂_sub,
    _root_.Polynomial.eval₂_pow, _root_.Polynomial.eval₂_X,
    _root_.Polynomial.eval₂_C, sub_eq_zero] at hroot
  exact hroot

/-- Evaluation of a polynomial in `X²` inside the quadratic component. -/
theorem component_mk_expand_two
    (χ : ℂ) (p : _root_.Polynomial EqualizerBaseRing) :
    AdjoinRoot.mk (componentPolynomial χ)
        (expand EqualizerBaseRing 2 p) =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
        (p.eval (componentSquare χ)) := by
  rw [← AdjoinRoot.aeval_eq, aeval_def,
    _root_.Polynomial.eval₂_eq_eval_map,
    _root_.Polynomial.map_expand, _root_.Polynomial.expand_eval,
    componentRoot_sq]
  simp

/-- The quadratic power basis reindexed by `Fin 2`. -/
noncomputable def componentBasis (χ : ℂ) :
    Basis (Fin 2) EqualizerBaseRing (EqualizerComponentRing χ) :=
  (componentPowerBasis χ).basis.reindex
    (finCongr (componentPowerBasis_dim χ))

@[simp]
theorem componentBasis_apply (χ : ℂ) (i : Fin 2) :
    componentBasis χ i =
      AdjoinRoot.root (componentPolynomial χ) ^ (i : ℕ) := by
  rw [componentBasis, Basis.reindex_apply,
    (componentPowerBasis χ).basis_eq_pow]
  congr 1

/-- The coordinates of `a + bX` in the basis `1, X`. -/
theorem componentBasis_repr_base_add_base_mul_root
    (χ : ℂ) (a b : EqualizerBaseRing) :
    (componentBasis χ).repr
        (algebraMap EqualizerBaseRing (EqualizerComponentRing χ) a +
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) b *
            AdjoinRoot.root (componentPolynomial χ)) =
      Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b := by
  have hb0 : componentBasis χ (0 : Fin 2) = 1 := by simp
  have hb1 : componentBasis χ (1 : Fin 2) =
      AdjoinRoot.root (componentPolynomial χ) := by simp
  have ha : algebraMap EqualizerBaseRing (EqualizerComponentRing χ) a =
      a • (1 : EqualizerComponentRing χ) := by
    change AdjoinRoot.mk (componentPolynomial χ) (C a) =
      a • AdjoinRoot.mk (componentPolynomial χ) 1
    rw [AdjoinRoot.smul_mk, _root_.Polynomial.smul_eq_C_mul, mul_one]
  have hb : algebraMap EqualizerBaseRing (EqualizerComponentRing χ) b *
      AdjoinRoot.root (componentPolynomial χ) =
        b • AdjoinRoot.root (componentPolynomial χ) := by
    change AdjoinRoot.mk (componentPolynomial χ) (C b) *
        AdjoinRoot.mk (componentPolynomial χ) X =
      b • AdjoinRoot.mk (componentPolynomial χ) X
    calc
      _ = AdjoinRoot.mk (componentPolynomial χ) (C b * X) := by
        rw [map_mul]
      _ = AdjoinRoot.mk (componentPolynomial χ) (b • X) := by
        rw [_root_.Polynomial.smul_eq_C_mul]
      _ = b • AdjoinRoot.mk (componentPolynomial χ) X := by
        rw [AdjoinRoot.smul_mk]
  rw [ha, hb, ← hb0, ← hb1, map_add, map_smul, map_smul,
    Basis.repr_self, Basis.repr_self]
  simp

/-- Every element of the component ring has unique coordinates in the basis
`1, X`. -/
theorem component_existsUnique_base_add_base_mul_root
    (χ : ℂ) (z : EqualizerComponentRing χ) :
    ∃! ab : EqualizerBaseRing × EqualizerBaseRing,
      z = algebraMap EqualizerBaseRing (EqualizerComponentRing χ) ab.1 +
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) ab.2 *
          AdjoinRoot.root (componentPolynomial χ) := by
  let a := (componentBasis χ).repr z (0 : Fin 2)
  let b := (componentBasis χ).repr z (1 : Fin 2)
  refine ⟨(a, b), ?_, ?_⟩
  · have hsum := (componentBasis χ).sum_repr z
    rw [Fin.sum_univ_two, componentBasis_apply, componentBasis_apply,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one] at hsum
    simpa [a, b, Algebra.smul_def] using hsum.symm
  · intro cd hcd
    have hrepr := congrArg (componentBasis χ).repr hcd
    rw [componentBasis_repr_base_add_base_mul_root] at hrepr
    apply Prod.ext
    · have hzero :=
        congrArg (fun v : Fin 2 →₀ EqualizerBaseRing ↦ v 0) hrepr
      simpa [a] using hzero.symm
    · have hone :=
        congrArg (fun v : Fin 2 →₀ EqualizerBaseRing ↦ v 1) hrepr
      simpa [b] using hone.symm

/-- Substitute `χT` for `T` in `ℂ[T]`. -/
noncomputable def scaleEqualizerParameter (χ : ℂ) :
    EqualizerParameterRing →+* EqualizerParameterRing :=
  compRingHom (C χ * X)

@[simp]
theorem scaleEqualizerParameter_apply
    (χ : ℂ) (p : EqualizerParameterRing) :
    scaleEqualizerParameter χ p = p.comp (C χ * X) := by
  rfl

/-- Scaling the parameter by a nonzero complex number is injective. -/
theorem scaleEqualizerParameter_injective
    {χ : ℂ} (hχ : χ ≠ 0) : Function.Injective (scaleEqualizerParameter χ) := by
  intro p q hpq
  ext n
  have hcoefficient := congrArg (fun r : EqualizerParameterRing ↦ r.coeff n) hpq
  rw [scaleEqualizerParameter_apply, scaleEqualizerParameter_apply,
    _root_.Polynomial.comp_C_mul_X_coeff,
    _root_.Polynomial.comp_C_mul_X_coeff] at hcoefficient
  exact mul_right_cancel₀ (pow_ne_zero n hχ) hcoefficient

/-- The value `H(X, χT)` in the quadratic component quotient. -/
noncomputable def componentSectorValue
    (χ : ℂ) (H : EqualizerBaseRing) : EqualizerComponentRing χ :=
  AdjoinRoot.mk (componentPolynomial χ)
    ((H.map (scaleEqualizerParameter χ)).map C)

theorem componentSectorValue_eq
    (χ : ℂ) (H : EqualizerBaseRing) :
    componentSectorValue χ H =
      AdjoinRoot.mk (componentPolynomial χ)
        ((H.map (scaleEqualizerParameter χ)).map C) := by
  rfl

/-- The coordinates of `H(X, χT)` in the basis `1, X` are obtained by
evaluating the even and odd parts at `x² + (1 - χ)T`. -/
theorem componentSectorValue_eq_even_add_odd_mul_root
    (χ : ℂ) (H : EqualizerBaseRing) :
    componentSectorValue χ H =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
          (((polynomialEvenPart (H.map (scaleEqualizerParameter χ))).map C).eval
            (componentSquare χ)) +
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
          (((polynomialOddPart (H.map (scaleEqualizerParameter χ))).map C).eval
            (componentSquare χ)) *
          AdjoinRoot.root (componentPolynomial χ) := by
  rw [componentSectorValue]
  have hdecomposition := congrArg
    (fun p : EqualizerBaseRing ↦
      AdjoinRoot.mk (componentPolynomial χ) (p.map C))
    (evenOdd_decomposition (H.map (scaleEqualizerParameter χ)))
  rw [hdecomposition]
  rw [_root_.Polynomial.map_add, _root_.Polynomial.map_mul,
    _root_.Polynomial.map_X, _root_.Polynomial.map_expand,
    _root_.Polynomial.map_expand, map_add, map_mul,
    AdjoinRoot.mk_X, component_mk_expand_two,
    component_mk_expand_two]
  ring

/-- Substitution of `x² + (1 - χ)T` into a polynomial over `ℂ[T]` is
injective. -/
theorem eval_componentSquare_eq_zero_iff
    (χ : ℂ) (p : _root_.Polynomial EqualizerParameterRing) :
    (p.map C).eval (componentSquare χ) = 0 ↔ p = 0 := by
  rw [_root_.Polynomial.eval_map]
  change p.comp (componentSquare χ) = 0 ↔ p = 0
  have hsquare : componentSquare χ ≠ C ((componentSquare χ).coeff 0) := by
    intro hconstant
    have hdegree := congrArg _root_.Polynomial.natDegree hconstant
    rw [componentSquare_natDegree, _root_.Polynomial.natDegree_C] at hdegree
    norm_num at hdegree
  constructor
  · intro hzero
    rcases _root_.Polynomial.comp_eq_zero_iff.mp hzero with hp | hp
    · exact hp
    · exact (hsquare hp.2).elim
  · rintro rfl
    exact zero_comp

/-- The sector identity in the quadratic component forces the odd part of
`H(x,T)` to vanish. -/
theorem polynomialOddPart_eq_zero_of_componentSectorIdentity
    {ζ χ : ℂ} (e : ℕ) (hζ : ζ ≠ 0) (hχ : χ ≠ 0)
    (H : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ) H =
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
            (C (C (ζ ^ e))) * componentSectorValue χ H) :
    polynomialOddPart H = 0 := by
  let pχ := H.map (scaleEqualizerParameter χ)
  let E : EqualizerBaseRing :=
    ((polynomialEvenPart pχ).map C).eval (componentSquare χ)
  let O : EqualizerBaseRing :=
    ((polynomialOddPart pχ).map C).eval (componentSquare χ)
  let s : EqualizerBaseRing := C (C (ζ ^ e))
  have hvalue : componentSectorValue χ H =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ) E +
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) O *
          AdjoinRoot.root (componentPolynomial χ) := by
    simpa [pχ, E, O] using
      componentSectorValue_eq_even_add_odd_mul_root χ H
  have hcanonical :
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ) H +
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) 0 *
            AdjoinRoot.root (componentPolynomial χ) =
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (s * E) +
          algebraMap EqualizerBaseRing (EqualizerComponentRing χ) (s * O) *
            AdjoinRoot.root (componentPolynomial χ) := by
    calc
      _ = algebraMap EqualizerBaseRing (EqualizerComponentRing χ) H := by
        simp
      _ = algebraMap EqualizerBaseRing (EqualizerComponentRing χ) s *
          componentSectorValue χ H := by
        simpa [s] using hsector
      _ = _ := by
        rw [hvalue, map_mul, map_mul]
        ring
  have hrepr := congrArg (componentBasis χ).repr hcanonical
  rw [componentBasis_repr_base_add_base_mul_root,
    componentBasis_repr_base_add_base_mul_root] at hrepr
  have hrootCoefficient :=
    congrArg (fun v : Fin 2 →₀ EqualizerBaseRing ↦ v 1) hrepr
  have hsO : s * O = 0 := by
    simpa using hrootCoefficient.symm
  have hs : s ≠ 0 := by
    dsimp [s]
    exact _root_.Polynomial.C_ne_zero.mpr
      (_root_.Polynomial.C_ne_zero.mpr (pow_ne_zero e hζ))
  have hO : O = 0 := (mul_eq_zero.mp hsO).resolve_left hs
  have hpχOdd : polynomialOddPart pχ = 0 :=
    (eval_componentSquare_eq_zero_iff χ _).mp (by simpa [O] using hO)
  have hmapped :
      (polynomialOddPart H).map (scaleEqualizerParameter χ) = 0 := by
    rw [← polynomialOddPart_map]
    simpa [pχ] using hpχOdd
  exact (_root_.Polynomial.map_eq_zero_iff
    (scaleEqualizerParameter_injective hχ)).mp hmapped

/-- Under the sector identity, `H(x,T)` is a polynomial in `x²` and `T`. -/
theorem exists_polynomial_in_square_of_componentSectorIdentity
    {ζ χ : ℂ} (e : ℕ) (hζ : ζ ≠ 0) (hχ : χ ≠ 0)
    (H : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ) H =
        algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
            (C (C (ζ ^ e))) * componentSectorValue χ H) :
    ∃ G : EqualizerBaseRing, H = G.comp (X ^ 2) := by
  have hodd := polynomialOddPart_eq_zero_of_componentSectorIdentity
    e hζ hχ H hsector
  refine ⟨polynomialEvenPart H, ?_⟩
  calc
    H = expand EqualizerParameterRing 2 (polynomialEvenPart H) +
        X * expand EqualizerParameterRing 2 (polynomialOddPart H) :=
      evenOdd_decomposition H
    _ = expand EqualizerParameterRing 2 (polynomialEvenPart H) := by
      simp [hodd]
    _ = (polynomialEvenPart H).comp (X ^ 2) :=
      _root_.Polynomial.expand_eq_comp_X_pow
        (R := EqualizerParameterRing) 2

/-- The preceding theorem for the primitive root data in the pinned proof,
where `χ = ζ^j`. -/
theorem exists_polynomial_in_square_of_primitiveSectorIdentity
    {k e j : ℕ} {ζ : ℂ} (hk : 0 < k) (hζ : IsPrimitiveRoot ζ k)
    (H : EqualizerBaseRing)
    (hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) H =
        algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j))
            (C (C (ζ ^ e))) * componentSectorValue (ζ ^ j) H) :
    ∃ G : EqualizerBaseRing, H = G.comp (X ^ 2) := by
  have hζzero : ζ ≠ 0 := hζ.ne_zero hk.ne'
  exact exists_polynomial_in_square_of_componentSectorIdentity
    e hζzero (pow_ne_zero j hζzero) H hsector

/-- The element `τ⁻¹T` in the quadratic component. -/
noncomputable def scaledParameterInComponent (τ χ : ℂ) :
    EqualizerComponentRing χ :=
  algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
    (C (C τ⁻¹ * X))

theorem scaledParameterInComponent_eq (τ χ : ℂ) :
    scaledParameterInComponent τ χ =
      algebraMap EqualizerBaseRing (EqualizerComponentRing χ)
        (C (C τ⁻¹ * X)) := by
  rfl

/-- The equation `y^L = τ⁻¹T`. -/
noncomputable def sectorPolynomial (τ χ : ℂ) (L : ℕ) :
    _root_.Polynomial (EqualizerComponentRing χ) :=
  X ^ L - C (scaledParameterInComponent τ χ)

theorem sectorPolynomial_eq (τ χ : ℂ) (L : ℕ) :
    sectorPolynomial τ χ L =
      X ^ L - C (scaledParameterInComponent τ χ) := by
  rfl

theorem sectorPolynomial_monic
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L) :
    (sectorPolynomial τ χ L).Monic := by
  exact monic_X_pow_sub_C _ hL.ne'

@[simp]
theorem sectorPolynomial_natDegree
    (τ χ : ℂ) (L : ℕ) :
    (sectorPolynomial τ χ L).natDegree = L := by
  have hdegree : (componentPolynomial χ).degree ≠ 0 := by
    rw [degree_eq_natDegree (componentPolynomial_monic χ).ne_zero,
      componentPolynomial_natDegree]
    norm_num
  have : Nontrivial (EqualizerComponentRing χ) :=
    AdjoinRoot.nontrivial (componentPolynomial χ) hdegree
  simp [sectorPolynomial]

/-- The component ring with `y` adjoined subject to `y^L = τ⁻¹T`. -/
abbrev EqualizerSectorRing (τ χ : ℂ) (L : ℕ) :=
  AdjoinRoot (sectorPolynomial τ χ L)

/-- The power basis `1, y, ..., y^(L-1)` of the sector extension. -/
noncomputable def sectorPowerBasis
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L) :
    PowerBasis (EqualizerComponentRing χ) (EqualizerSectorRing τ χ L) :=
  AdjoinRoot.powerBasis' (sectorPolynomial_monic τ χ hL)

@[simp]
theorem sectorPowerBasis_dim
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L) :
    (sectorPowerBasis τ χ hL).dim = L := by
  simp [sectorPowerBasis]

/-- The sector power basis reindexed by `Fin L`. -/
noncomputable def sectorBasis
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L) :
    Basis (Fin L) (EqualizerComponentRing χ) (EqualizerSectorRing τ χ L) :=
  (sectorPowerBasis τ χ hL).basis.reindex
    (finCongr (sectorPowerBasis_dim τ χ hL))

@[simp]
theorem sectorBasis_apply
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L) (e : Fin L) :
    sectorBasis τ χ hL e =
      AdjoinRoot.root (sectorPolynomial τ χ L) ^ (e : ℕ) := by
  rw [sectorBasis, Basis.reindex_apply,
    (sectorPowerBasis τ χ hL).basis_eq_pow]
  congr 1

/-- The sectors with exponents `0 ≤ e < L` are independent in the
component quotient. -/
theorem sector_sum_eq_zero_iff
    (τ χ : ℂ) {L : ℕ} (hL : 0 < L)
    (a : Fin L → EqualizerComponentRing χ) :
    (∑ e, a e •
      AdjoinRoot.root (sectorPolynomial τ χ L) ^ (e : ℕ)) = 0 ↔
      ∀ e, a e = 0 := by
  have hlinear : LinearIndependent (EqualizerComponentRing χ)
      (fun e : Fin L ↦
        AdjoinRoot.root (sectorPolynomial τ χ L) ^ (e : ℕ)) := by
    simpa only [← sectorBasis_apply τ χ hL] using
      (sectorBasis τ χ hL).linearIndependent
  constructor
  · exact Fintype.linearIndependent_iff.mp hlinear a
  · intro ha
    simp [ha]

/-- A global equalizer identity in the component quotient separates
into sector identities, and every sector polynomial is even in `x`. -/
theorem every_sector_is_polynomial_in_square
    (τ : ℂ) {k j L : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hL : 0 < L) (hζ : IsPrimitiveRoot ζ k)
    (H : Fin L → EqualizerBaseRing)
    (hglobal :
      (∑ e : Fin L,
          algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (H e) •
            AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^ (e : ℕ)) =
        ∑ e : Fin L,
          (algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j))
              (C (C (ζ ^ (e : ℕ)))) *
            componentSectorValue (ζ ^ j) (H e)) •
              AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^ (e : ℕ)) :
    ∀ e : Fin L, ∃ G : EqualizerBaseRing, H e = G.comp (X ^ 2) := by
  let a : Fin L → EqualizerComponentRing (ζ ^ j) := fun e ↦
    algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (H e) -
      algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j))
          (C (C (ζ ^ (e : ℕ)))) * componentSectorValue (ζ ^ j) (H e)
  have hzero :
      (∑ e : Fin L, a e •
        AdjoinRoot.root (sectorPolynomial τ (ζ ^ j) L) ^ (e : ℕ)) = 0 := by
    simpa only [a, sub_smul, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr hglobal
  have hcoefficients :=
    (sector_sum_eq_zero_iff τ (ζ ^ j) hL a).mp hzero
  intro e
  have hsector :
      algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j)) (H e) =
        algebraMap EqualizerBaseRing (EqualizerComponentRing (ζ ^ j))
            (C (C (ζ ^ (e : ℕ)))) * componentSectorValue (ζ ^ j) (H e) := by
    exact sub_eq_zero.mp (hcoefficients e)
  exact exists_polynomial_in_square_of_primitiveSectorIdentity
    hk hζ (H e) hsector

end OnLeConjecture.DTwo
