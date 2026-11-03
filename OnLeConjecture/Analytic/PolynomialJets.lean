/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PolynomialCoordinates
public import OnLeConjecture.Analytic.TaylorSeries
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial jets of analytic germs

Restriction to complex lines identifies the homogeneous components of a
polynomial with the coefficients of the corresponding one variable Taylor
series. This identifies the filtration on the polynomial coordinate subring
induced by the analytic maximal ideal.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Restriction of a coordinate germ to the line through `v`. -/
theorem lineRestriction_coordinate_eq {n : ℕ} (v : Source n) (i : Fin n) :
    Germ.lineRestriction v (Germ.coordinate i) =
      Germ.constRingHom 1 (v i) * Germ.coordinate (0 : Fin 1) := by
  have hprojection : AnalyticAt ℂ (fun z : Source n ↦ z i) 0 := by
    exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0
  have hcoordinate : Germ.coordinate i =
      Germ.ofFunction (fun z : Source n ↦ z i)
        hprojection := by
    apply Subtype.ext
    rw [Germ.coe_coordinate, Germ.coe_ofFunction]
  rw [hcoordinate, Germ.lineRestriction_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp [Germ.lineMap_apply, mul_comm]

/-- The Taylor series of the coordinate germ in one variable is the formal
variable. -/
theorem oneVariableTaylorSeries_coordinate_eq_X :
    Germ.oneVariableTaylorSeries (Germ.coordinate (0 : Fin 1)) =
      (PowerSeries.X : PowerSeries ℂ) := by
  change Germ.functionTaylorSeries
      (Germ.oneVariableRepresentative
        (fun z : Source 1 ↦ z 0)) = PowerSeries.X
  have hrepresentative : Germ.oneVariableRepresentative
      (fun z : Source 1 ↦ z 0) = id := by
    funext z
    simp [Germ.oneVariableRepresentative, Germ.oneVariableEquiv]
  rw [hrepresentative]
  ext k
  by_cases hk0 : k = 0
  · subst k
    simp [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X]
  by_cases hk1 : k = 1
  · subst k
    norm_num [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X]
  · simp [Germ.functionTaylorSeries_coeff, iteratedDeriv_id,
      PowerSeries.coeff_X, hk0, hk1]

/-- Substitution of the line `z ↦ z v` in a multivariate polynomial. -/
@[expose] noncomputable def radialPolynomial {n : ℕ} (v : Source n) :
    MvPolynomial (Fin n) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C (v i) * Polynomial.X)

/-- Radial substitution sends a monomial to a monomial whose exponent is its
total degree. -/
theorem radialPolynomial_monomial {n : ℕ} (v : Source n)
    (d : Fin n →₀ ℕ) (c : ℂ) :
    Germ.radialPolynomial v (MvPolynomial.monomial d c) =
      Polynomial.C (MvPolynomial.eval v (MvPolynomial.monomial d c)) *
        Polynomial.X ^ d.degree := by
  change MvPolynomial.eval₂ Polynomial.C
      (fun i ↦ Polynomial.C (v i) * Polynomial.X)
        (MvPolynomial.monomial d c) = _
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial]
  simp only [map_mul, Finsupp.prod]
  rw [show (∏ x ∈ d.support,
      (Polynomial.C (v x) * Polynomial.X) ^ d x) =
      (∏ x ∈ d.support, Polynomial.C (v x) ^ d x) *
        ∏ x ∈ d.support, Polynomial.X ^ d x by
        simp only [mul_pow, Finset.prod_mul_distrib]]
  have hC : (∏ x ∈ d.support, Polynomial.C (v x) ^ d x) =
      Polynomial.C (∏ x ∈ d.support, v x ^ d x) := by
    rw [map_prod]
    simp only [map_pow]
  have hX : (∏ x ∈ d.support, Polynomial.X ^ d x) =
      Polynomial.X ^ ∑ x ∈ d.support, d x :=
    Finset.prod_pow_eq_pow_sum d.support (fun x ↦ d x)
      (Polynomial.X : Polynomial ℂ)
  rw [hC, hX]
  rw [Finsupp.degree_apply, mul_assoc]

/-- The coefficient of radial degree `k` is the evaluation of the homogeneous
component of degree `k`. -/
theorem radialPolynomial_coeff {n : ℕ} (v : Source n)
    (p : MvPolynomial (Fin n) ℂ) (k : ℕ) :
    (Germ.radialPolynomial v p).coeff k =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent k p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [Germ.radialPolynomial_monomial]
      rw [MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.isHomogeneous_monomial c rfl)]
      split_ifs with h
      · subst k
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · rw [map_zero]
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h]
  | add p q hp hq =>
      rw [map_add, Polynomial.coeff_add, map_add, hp, hq]
      exact (map_add (MvPolynomial.eval v)
        (MvPolynomial.homogeneousComponent k p)
        (MvPolynomial.homogeneousComponent k q)).symm

/-- Radial substitution as a complex algebra homomorphism. -/
@[expose] noncomputable def radialPolynomialAlgHom {n : ℕ}
    (v : Source n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval
    (fun i ↦ Polynomial.C (v i) * Polynomial.X)

@[simp]
theorem radialPolynomialAlgHom_apply {n : ℕ} (v : Source n)
    (p : MvPolynomial (Fin n) ℂ) :
    Germ.radialPolynomialAlgHom v p = Germ.radialPolynomial v p :=
  rfl

@[simp]
theorem radialPolynomialAlgHom_X {n : ℕ} (v : Source n)
    (i : Fin n) :
    Germ.radialPolynomialAlgHom v (MvPolynomial.X i) =
      Polynomial.C (v i) * Polynomial.X := by
  simp [Germ.radialPolynomialAlgHom]

/-- The natural inclusion of complex polynomials into formal power series as
an algebra homomorphism. -/
@[expose] noncomputable def polynomialToPowerSeriesAlgHom :
    Polynomial ℂ →ₐ[ℂ] PowerSeries ℂ where
  __ := Polynomial.coeToPowerSeries.ringHom (R := ℂ)
  commutes' c := by
    change ((Polynomial.C c : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.C c
    exact Polynomial.coe_C c

@[simp]
theorem polynomialToPowerSeriesAlgHom_apply (p : Polynomial ℂ) :
    Germ.polynomialToPowerSeriesAlgHom p = (p : PowerSeries ℂ) :=
  rfl

/-- The radial Taylor series of a polynomial coordinate germ is its radial
polynomial regarded as a formal power series. -/
theorem radialTaylor_coordinatePolynomial {n : ℕ} (v : Source n)
    (p : MvPolynomial (Fin n) ℂ) :
    Germ.radialTaylorAlgHom n
        (Germ.coordinatePolynomialAlgHom n p) v =
      (Germ.radialPolynomial v p : PowerSeries ℂ) := by
  let left : MvPolynomial (Fin n) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    (Pi.evalAlgHom ℂ (fun _ : Source n ↦ PowerSeries ℂ) v).comp
      ((Germ.radialTaylorAlgHom n).comp
        (Germ.coordinatePolynomialAlgHom n))
  let right : MvPolynomial (Fin n) ℂ →ₐ[ℂ] PowerSeries ℂ :=
    Germ.polynomialToPowerSeriesAlgHom.comp
      (Germ.radialPolynomialAlgHom v)
  have heq : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [left, right, AlgHom.comp_apply, Pi.evalAlgHom_apply,
      Germ.coordinatePolynomialAlgHom_X,
      Germ.radialPolynomialAlgHom_X,
      Germ.radialTaylorAlgHom_apply]
    rw [← Germ.oneVariableTaylorAlgHom_apply,
      Germ.lineRestriction_coordinate_eq, map_mul]
    have hconstant : Germ.oneVariableTaylorAlgHom
        (Germ.constRingHom 1 (v i)) = PowerSeries.C (v i) := by
      change Germ.oneVariableTaylorAlgHom
          (Germ.constRingHom 1 (v i)) =
        algebraMap ℂ (PowerSeries ℂ) (v i)
      exact Germ.oneVariableTaylorAlgHom.commutes (v i)
    rw [hconstant, Germ.oneVariableTaylorAlgHom_apply,
      Germ.oneVariableTaylorSeries_coordinate_eq_X]
    rw [map_mul, Germ.polynomialToPowerSeriesAlgHom_apply,
      Germ.polynomialToPowerSeriesAlgHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  simpa only [left, right, AlgHom.comp_apply, Pi.evalAlgHom_apply,
    Germ.radialPolynomialAlgHom_apply,
    Germ.polynomialToPowerSeriesAlgHom_apply] using
      AlgHom.congr_fun heq p

/-- The radial Taylor coefficient of degree `k` is the value of the
homogeneous component of degree `k`. -/
theorem radialTaylor_coordinatePolynomial_coeff {n : ℕ}
    (v : Source n) (p : MvPolynomial (Fin n) ℂ) (k : ℕ) :
    PowerSeries.coeff k
        (Germ.radialTaylorAlgHom n
          (Germ.coordinatePolynomialAlgHom n p) v) =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent k p) := by
  rw [Germ.radialTaylor_coordinatePolynomial,
    Polynomial.coeff_coe, Germ.radialPolynomial_coeff]

/-- Taylor coefficients below `N` vanish for a one variable germ in the
`N`th power of the maximal ideal. -/
theorem oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow
    {q : Germ 1} {N k : ℕ} (hq : q ∈ Germ.maximalIdeal 1 ^ N)
    (hk : k < N) :
    PowerSeries.coeff k (Germ.oneVariableTaylorSeries q) = 0 := by
  rw [Germ.maximalIdeal_one_pow_eq_span_coordinate_pow,
    Ideal.mem_span_singleton] at hq
  rcases hq with ⟨u, hu⟩
  rw [hu, ← Germ.oneVariableTaylorAlgHom_apply, map_mul, map_pow,
    Germ.oneVariableTaylorAlgHom_apply,
    Germ.oneVariableTaylorSeries_coordinate_eq_X]
  rw [PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hk)]

/-- A polynomial has total order at least `N` if and only if its coordinate
germ belongs to the `N`th power of the analytic maximal ideal. -/
theorem mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow
    {n N : ℕ} {p : MvPolynomial (Fin n) ℂ} :
    p ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ N ↔
      Germ.coordinatePolynomialAlgHom n p ∈ Germ.maximalIdeal n ^ N := by
  constructor
  · intro hp
    have hmap :
        Ideal.map (Germ.coordinatePolynomialAlgHom n)
            (MvPolynomial.idealOfVars (Fin n) ℂ ^ N) =
          Germ.maximalIdeal n ^ N := by
      rw [Ideal.map_pow,
        Germ.map_idealOfVars_coordinatePolynomialAlgHom]
    rw [← hmap]
    exact Ideal.mem_map_of_mem (Germ.coordinatePolynomialAlgHom n) hp
  · intro hp
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    let k := d.degree
    have hall : ∀ v : Source n,
        MvPolynomial.eval v
            (MvPolynomial.homogeneousComponent k p) = 0 := by
      intro v
      have hline := Germ.lineRestriction_mem_maximalIdeal_pow v hp
      have hcoeff :=
        Germ.oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow
          hline hd
      change PowerSeries.coeff k
          (Germ.radialTaylorAlgHom n
            (Germ.coordinatePolynomialAlgHom n p) v) = 0 at hcoeff
      rw [Germ.radialTaylor_coordinatePolynomial_coeff] at hcoeff
      exact hcoeff
    have hzero : MvPolynomial.homogeneousComponent k p = 0 :=
      MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero
        (MvPolynomial.homogeneousComponent_isHomogeneous k p) hall
    have hcoeff := congrArg (MvPolynomial.coeff d) hzero
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
      MvPolynomial.coeff_zero] at hcoeff
    exact hcoeff

/-- The inverse image of an analytic maximal ideal power under coordinate
evaluation is the corresponding power of the polynomial variable ideal. -/
theorem comap_maximalIdeal_pow_coordinatePolynomialAlgHom
    (n N : ℕ) :
    Ideal.comap (Germ.coordinatePolynomialAlgHom n)
        (Germ.maximalIdeal n ^ N) =
      MvPolynomial.idealOfVars (Fin n) ℂ ^ N := by
  ext p
  exact
    Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.symm

/-- Coordinate evaluation on the quotients by the `N`th powers of the
coordinate ideals. -/
@[expose] noncomputable def coordinatePolynomialQuotientAlgHom
    (n N : ℕ) :
    (MvPolynomial (Fin n) ℂ ⧸
        MvPolynomial.idealOfVars (Fin n) ℂ ^ N) →ₐ[ℂ]
      Germ n ⧸ Germ.maximalIdeal n ^ N :=
  Ideal.quotientMapₐ (Germ.maximalIdeal n ^ N)
    (Germ.coordinatePolynomialAlgHom n) fun _ hp ↦
      Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp hp

@[simp]
theorem coordinatePolynomialQuotientAlgHom_mk
    (n N : ℕ) (p : MvPolynomial (Fin n) ℂ) :
    Germ.coordinatePolynomialQuotientAlgHom n N
        (Ideal.Quotient.mk
          (MvPolynomial.idealOfVars (Fin n) ℂ ^ N) p) =
      Ideal.Quotient.mk (Germ.maximalIdeal n ^ N)
        (Germ.coordinatePolynomialAlgHom n p) :=
  rfl

/-- Coordinate evaluation is bijective after quotienting by every power of
the coordinate ideals. -/
theorem coordinatePolynomialQuotientAlgHom_bijective
    (n N : ℕ) :
    Function.Bijective (Germ.coordinatePolynomialQuotientAlgHom n N) := by
  constructor
  · intro a b hab
    rcases Ideal.Quotient.mk_surjective a with ⟨p, rfl⟩
    rcases Ideal.Quotient.mk_surjective b with ⟨q, rfl⟩
    rw [Germ.coordinatePolynomialQuotientAlgHom_mk,
      Germ.coordinatePolynomialQuotientAlgHom_mk] at hab
    apply Ideal.Quotient.eq.mpr
    apply
      Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hab
  · intro q
    rcases Ideal.Quotient.mk_surjective q with ⟨g, rfl⟩
    rcases Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow n N g with
      ⟨p, hp⟩
    refine ⟨Ideal.Quotient.mk
      (MvPolynomial.idealOfVars (Fin n) ℂ ^ N) p, ?_⟩
    rw [Germ.coordinatePolynomialQuotientAlgHom_mk]
    exact Ideal.Quotient.eq.mpr (by
      simpa only [neg_sub] using
        (Germ.maximalIdeal n ^ N).neg_mem hp)

/-- The polynomial and analytic coordinate rings have canonically equivalent
quotients by every power of their maximal ideals. -/
@[expose] noncomputable def coordinatePolynomialQuotientAlgEquiv
    (n N : ℕ) :
    (MvPolynomial (Fin n) ℂ ⧸
        MvPolynomial.idealOfVars (Fin n) ℂ ^ N) ≃ₐ[ℂ]
      Germ n ⧸ Germ.maximalIdeal n ^ N :=
  AlgEquiv.ofBijective
    (Germ.coordinatePolynomialQuotientAlgHom n N)
    (Germ.coordinatePolynomialQuotientAlgHom_bijective n N)

@[simp]
theorem coordinatePolynomialQuotientAlgEquiv_apply
    (n N : ℕ)
    (p : MvPolynomial (Fin n) ℂ ⧸
      MvPolynomial.idealOfVars (Fin n) ℂ ^ N) :
    Germ.coordinatePolynomialQuotientAlgEquiv n N p =
      Germ.coordinatePolynomialQuotientAlgHom n N p :=
  rfl

@[simp]
theorem coordinatePolynomialQuotientAlgHom_symm_apply
    (n N : ℕ) (q : Germ n ⧸ Germ.maximalIdeal n ^ N) :
    Germ.coordinatePolynomialQuotientAlgHom n N
        ((Germ.coordinatePolynomialQuotientAlgEquiv n N).symm q) = q := by
  rw [← Germ.coordinatePolynomialQuotientAlgEquiv_apply]
  exact (Germ.coordinatePolynomialQuotientAlgEquiv n N).apply_symm_apply q

@[simp]
theorem coordinatePolynomialQuotientAlgEquiv_symm_hom_apply
    (n N : ℕ)
    (p : MvPolynomial (Fin n) ℂ ⧸
      MvPolynomial.idealOfVars (Fin n) ℂ ^ N) :
    (Germ.coordinatePolynomialQuotientAlgEquiv n N).symm
        (Germ.coordinatePolynomialQuotientAlgHom n N p) = p := by
  rw [← Germ.coordinatePolynomialQuotientAlgEquiv_apply]
  exact (Germ.coordinatePolynomialQuotientAlgEquiv n N).symm_apply_apply p

/-- The quotient equivalences commute with the transition maps between ideal
powers. -/
theorem coordinatePolynomialQuotientAlgHom_transition
    {n m N : ℕ} (hmN : m ≤ N) :
    (Ideal.Quotient.factorₐ ℂ
        (Ideal.pow_le_pow_right hmN) :
      (Germ n ⧸ Germ.maximalIdeal n ^ N) →ₐ[ℂ]
        Germ n ⧸ Germ.maximalIdeal n ^ m).comp
        (Germ.coordinatePolynomialQuotientAlgHom n N) =
      (Germ.coordinatePolynomialQuotientAlgHom n m).comp
        (Ideal.Quotient.factorₐ ℂ
          (Ideal.pow_le_pow_right hmN) :
          (MvPolynomial (Fin n) ℂ ⧸
              MvPolynomial.idealOfVars (Fin n) ℂ ^ N) →ₐ[ℂ]
            MvPolynomial (Fin n) ℂ ⧸
              MvPolynomial.idealOfVars (Fin n) ℂ ^ m) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro p
  rfl

end Germ

end OnLeConjecture.Analytic
