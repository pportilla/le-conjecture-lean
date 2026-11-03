/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricGeneralPreparation
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Resultants for analytic elimination

The lemmas in this file give the algebraic part of elimination after
parameter dependent preparation. A common root in the fraction field makes
the fixed degree resultant vanish, while specialization of the second
polynomial to a scalar computes an exact power.
-/

public section

namespace OnLeConjecture.Analytic

open Polynomial
open scoped BigOperators

namespace PolynomialResultant

/-- The polynomial used to eliminate a common source coordinate after
division by a monic polynomial. The coefficients `t i` are independent
parameters and `r` is the quantity to be eliminated. -/
@[expose] noncomputable def eliminationPolynomial
    {R ι : Type*} [CommRing R] [Fintype ι]
    (q : ι → R[X]) (t : ι → R) (r : R) : R[X] :=
  C r - ∑ i, C (t i) * q i

/-- A uniform degree bound on the coefficient polynomials bounds the degree
of the elimination polynomial. -/
theorem eliminationPolynomial_natDegree_le
    {R ι : Type*} [CommRing R] [Fintype ι]
    (q : ι → R[X]) (t : ι → R) (r : R) (n : ℕ)
    (hq : ∀ i, (q i).natDegree ≤ n) :
    (PolynomialResultant.eliminationPolynomial q t r).natDegree ≤ n := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_le (t i) (q i)).trans (hq i)

/-- A relation expressing `r` as the prescribed linear combination makes
the mapped elimination polynomial vanish at the common source coordinate. -/
theorem map_eliminationPolynomial_isRoot
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (q : ι → R[X]) (t : ι → R) (r : R)
    (φ : R →+* S) (x : S)
    (hrelation : φ r =
      ∑ i, φ (t i) * ((q i).map φ).eval x) :
    ((PolynomialResultant.eliminationPolynomial q t r).map φ).IsRoot x := by
  rw [Polynomial.IsRoot.def]
  simp only [PolynomialResultant.eliminationPolynomial,
    Polynomial.map_sub, Polynomial.map_C, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul]
  rw [hrelation]
  simp

/-- If all linear combination parameters specialize to zero, the
elimination polynomial specializes to the scalar polynomial `C (φ r)`. -/
theorem map_eliminationPolynomial_eq_C_of_parameters_eq_zero
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]
    (q : ι → R[X]) (t : ι → R) (r : R)
    (φ : R →+* S) (ht : ∀ i, φ (t i) = 0) :
    (PolynomialResultant.eliminationPolynomial q t r).map φ = C (φ r) := by
  rw [PolynomialResultant.eliminationPolynomial, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_sum]
  have hsum : ∑ i, (C (t i) * q i).map φ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [ht i]
  rw [hsum, sub_zero]

/-- Two polynomials over a field with a common root have zero resultant when
the first polynomial is nonzero. -/
theorem resultant_eq_zero_of_common_root
    {K : Type*} [Field K] {f g : K[X]} {x : K}
    (hf : f ≠ 0) (hfx : f.IsRoot x) (hgx : g.IsRoot x) :
    f.resultant g = 0 := by
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨Or.inl hf, ?_⟩
  intro hcoprime
  have hdivF : X - C x ∣ f := Polynomial.dvd_iff_isRoot.mpr hfx
  have hdivG : X - C x ∣ g := Polynomial.dvd_iff_isRoot.mpr hgx
  have hunit := hcoprime.isUnit_of_dvd' hdivF hdivG
  exact Polynomial.not_isUnit_X_sub_C x hunit

/-- A common root makes every fixed degree resultant vanish when the first
polynomial is monic and the supplied second degree is an upper bound. -/
theorem resultant_eq_zero_of_common_root_fixedDegree
    {K : Type*} [Field K] (f g : K[X]) (n : ℕ)
    (hf : f.Monic) (hg : g.natDegree ≤ n) {x : K}
    (hfx : f.IsRoot x) (hgx : g.IsRoot x) :
    f.resultant g f.natDegree n = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hg
  subst n
  rw [Polynomial.resultant_add_right_deg]
  · rw [hf.coeff_natDegree, one_pow, one_mul]
    exact PolynomialResultant.resultant_eq_zero_of_common_root
      hf.ne_zero hfx hgx
  · exact le_rfl

/-- The fixed degree resultant of a monic polynomial and a scalar
polynomial is the corresponding power of the scalar. -/
theorem resultant_C_eq_pow_of_monic
    {R : Type*} [CommRing R] (f : R[X]) (n : ℕ)
    (hf : f.Monic) (r : R) :
    f.resultant (C r) f.natDegree n = r ^ f.natDegree := by
  rw [Polynomial.resultant_C_right, hf.coeff_natDegree, one_pow, one_mul]

/-- A common root in the fraction field detects vanishing of a fixed degree
resultant over the original domain. -/
theorem resultant_eq_zero_of_fractionRing_common_root
    {R : Type*} [CommRing R] [IsDomain R]
    (f g : R[X]) (n : ℕ) (hf : f.Monic) (hg : g.natDegree ≤ n)
    {x : FractionRing R}
    (hfx : (f.map (algebraMap R (FractionRing R))).IsRoot x)
    (hgx : (g.map (algebraMap R (FractionRing R))).IsRoot x) :
    f.resultant g f.natDegree n = 0 := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hfMap : (f.map φ).Monic := hf.map φ
  have hgDegree : (g.map φ).natDegree ≤ n := by
    exact Polynomial.natDegree_map_le.trans hg
  have hzero : (f.map φ).resultant (g.map φ)
      (f.map φ).natDegree n = 0 :=
    PolynomialResultant.resultant_eq_zero_of_common_root_fixedDegree
      (f.map φ) (g.map φ) n hfMap hgDegree hfx hgx
  have hdegree : (f.map φ).natDegree = f.natDegree :=
    hf.natDegree_map φ
  rw [hdegree, Polynomial.resultant_map_map] at hzero
  exact (map_eq_zero_iff φ
    (IsFractionRing.injective R (FractionRing R))).mp hzero

/-- A common root after a coefficient substitution makes the substituted
resultant vanish. No injectivity hypothesis is required for the coefficient
substitution. -/
theorem map_resultant_eq_zero_of_common_root
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (W H : R[X]) (n : ℕ) (hW : W.Monic) (hH : H.natDegree ≤ n)
    (φ : R →+* S) {x : S}
    (hWx : (W.map φ).IsRoot x) (hHx : (H.map φ).IsRoot x) :
    φ (W.resultant H W.natDegree n) = 0 := by
  have hWMap : (W.map φ).Monic := hW.map φ
  have hHMap : (H.map φ).natDegree ≤ n :=
    Polynomial.natDegree_map_le.trans hH
  have hWxFraction := Polynomial.IsRoot.map
    (f := algebraMap S (FractionRing S)) hWx
  have hHxFraction := Polynomial.IsRoot.map
    (f := algebraMap S (FractionRing S)) hHx
  have hzero :=
    PolynomialResultant.resultant_eq_zero_of_fractionRing_common_root
      (W.map φ) (H.map φ) n hWMap hHMap
        hWxFraction hHxFraction
  have hdegree : (W.map φ).natDegree = W.natDegree :=
    hW.natDegree_map φ
  rw [hdegree, Polynomial.resultant_map_map] at hzero
  exact hzero

/-- When specialization turns the second polynomial into a scalar, the
specialized resultant is the exact power of that scalar. -/
theorem map_resultant_eq_pow_of_map_eq_C
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (W H : R[X]) (n : ℕ) (hW : W.Monic)
    (φ : R →+* S) (r : S) (hH : H.map φ = C r) :
    φ (W.resultant H W.natDegree n) = r ^ W.natDegree := by
  rw [← Polynomial.resultant_map_map, hH]
  have hWMap : (W.map φ).Monic := hW.map φ
  have hdegree : (W.map φ).natDegree = W.natDegree :=
    hW.natDegree_map φ
  rw [← hdegree]
  exact PolynomialResultant.resultant_C_eq_pow_of_monic
    (W.map φ) n hWMap r

/-- The resultant eliminant vanishes after any substitution for which the
monic polynomial and the corresponding linear combination have a common
root. -/
theorem map_resultant_eliminationPolynomial_eq_zero
    {R S ι : Type*} [CommRing R] [CommRing S] [IsDomain S] [Fintype ι]
    (W : R[X]) (q : ι → R[X]) (t : ι → R) (r : R) (n : ℕ)
    (hW : W.Monic) (hq : ∀ i, (q i).natDegree ≤ n)
    (φ : R →+* S) (x : S)
    (hWx : (W.map φ).IsRoot x)
    (hrelation : φ r =
      ∑ i, φ (t i) * ((q i).map φ).eval x) :
    φ (W.resultant
      (PolynomialResultant.eliminationPolynomial q t r)
      W.natDegree n) = 0 := by
  exact PolynomialResultant.map_resultant_eq_zero_of_common_root
    W (PolynomialResultant.eliminationPolynomial q t r) n hW
      (PolynomialResultant.eliminationPolynomial_natDegree_le
        q t r n hq)
      φ hWx
      (PolynomialResultant.map_eliminationPolynomial_isRoot
        q t r φ x hrelation)

/-- Setting every linear combination parameter to zero specializes the
resultant eliminant to the exact power of the eliminated scalar. -/
theorem map_resultant_eliminationPolynomial_eq_pow
    {R S ι : Type*} [CommRing R] [CommRing S] [Nontrivial S] [Fintype ι]
    (W : R[X]) (q : ι → R[X]) (t : ι → R) (r : R) (n : ℕ)
    (hW : W.Monic) (φ : R →+* S)
    (ht : ∀ i, φ (t i) = 0) :
    φ (W.resultant
      (PolynomialResultant.eliminationPolynomial q t r)
      W.natDegree n) = (φ r) ^ W.natDegree := by
  exact PolynomialResultant.map_resultant_eq_pow_of_map_eq_C
    W (PolynomialResultant.eliminationPolynomial q t r) n hW
      φ (φ r)
      (PolynomialResultant.map_eliminationPolynomial_eq_C_of_parameters_eq_zero
        q t r φ ht)

/-- The resultant eliminant with independent multivariable parameters. -/
@[expose] noncomputable def multivariableResultantEliminant
    {σ R : Type*} [Fintype σ] [CommRing R]
    (W : R[X]) (q : σ → R[X]) (r : R) (n : ℕ) :
    MvPolynomial σ R :=
  let coefficientMap : R →+* MvPolynomial σ R := MvPolynomial.C
  let WParameter := W.map coefficientMap
  let qParameter := fun i ↦ (q i).map coefficientMap
  WParameter.resultant
    (PolynomialResultant.eliminationPolynomial
      qParameter MvPolynomial.X (MvPolynomial.C r))
    WParameter.natDegree n

/-- Evaluating the multivariable resultant eliminant at a common root makes
it vanish. -/
theorem eval₂_multivariableResultantEliminant_eq_zero
    {σ R S : Type*} [Fintype σ] [CommRing R]
    [CommRing S] [IsDomain S]
    (W : R[X]) (q : σ → R[X]) (r : R) (n : ℕ)
    (hW : W.Monic) (hq : ∀ i, (q i).natDegree ≤ n)
    (ψ : R →+* S) (parameter : σ → S) (x : S)
    (hWx : (W.map ψ).IsRoot x)
    (hrelation : ψ r =
      ∑ i, parameter i * ((q i).map ψ).eval x) :
    MvPolynomial.eval₂ ψ parameter
      (PolynomialResultant.multivariableResultantEliminant W q r n) = 0 := by
  let φ : MvPolynomial σ R →+* S := MvPolynomial.eval₂Hom ψ parameter
  let coefficientMap : R →+* MvPolynomial σ R := MvPolynomial.C
  have hcomp : φ.comp coefficientMap = ψ := by
    ext a
    simp [φ, coefficientMap]
  have hWParameter : (W.map coefficientMap).Monic := hW.map coefficientMap
  have hqParameter : ∀ i, ((q i).map coefficientMap).natDegree ≤ n := by
    intro i
    exact Polynomial.natDegree_map_le.trans (hq i)
  have hroot : ((W.map coefficientMap).map φ).IsRoot x := by
    rw [Polynomial.map_map, hcomp]
    exact hWx
  have hconstant (a : R) : φ (MvPolynomial.C a) = ψ a := by
    exact DFunLike.congr_fun hcomp a
  have hvariable (i : σ) : φ (MvPolynomial.X i) = parameter i := by
    simp [φ]
  have hqMap (i : σ) :
      ((q i).map coefficientMap).map φ = (q i).map ψ := by
    rw [Polynomial.map_map, hcomp]
  have hlinear : φ (MvPolynomial.C r) =
      ∑ i, φ (MvPolynomial.X i) *
        (((q i).map coefficientMap).map φ).eval x := by
    rw [hconstant]
    simp_rw [hvariable, hqMap]
    exact hrelation
  have hzero :=
    PolynomialResultant.map_resultant_eliminationPolynomial_eq_zero
      (W.map coefficientMap) (fun i ↦ (q i).map coefficientMap)
      MvPolynomial.X (MvPolynomial.C r) n hWParameter hqParameter
      φ x hroot hlinear
  change φ (PolynomialResultant.multivariableResultantEliminant
    W q r n) = 0
  simpa only [PolynomialResultant.multivariableResultantEliminant,
    coefficientMap] using hzero

/-- Specializing every multivariable parameter to zero gives the exact
power of the eliminated coefficient. -/
theorem eval₂_zero_multivariableResultantEliminant_eq_pow
    {σ R S : Type*} [Fintype σ] [CommRing R]
    [Nontrivial R] [CommRing S] [Nontrivial S]
    (W : R[X]) (q : σ → R[X]) (r : R) (n : ℕ)
    (hW : W.Monic) (ψ : R →+* S) :
    MvPolynomial.eval₂ ψ (fun _ ↦ 0)
      (PolynomialResultant.multivariableResultantEliminant W q r n) =
        (ψ r) ^ W.natDegree := by
  let φ : MvPolynomial σ R →+* S :=
    MvPolynomial.eval₂Hom ψ (fun _ ↦ 0)
  let coefficientMap : R →+* MvPolynomial σ R := MvPolynomial.C
  have hcomp : φ.comp coefficientMap = ψ := by
    ext a
    simp [φ, coefficientMap]
  have hWParameter : (W.map coefficientMap).Monic := hW.map coefficientMap
  have hparameters : ∀ i, φ (MvPolynomial.X i) = 0 := by
    intro i
    simp [φ]
  have hpower :=
    PolynomialResultant.map_resultant_eliminationPolynomial_eq_pow
      (W.map coefficientMap) (fun i ↦ (q i).map coefficientMap)
      MvPolynomial.X (MvPolynomial.C r) n hWParameter φ hparameters
  have hdegree : (W.map coefficientMap).natDegree = W.natDegree :=
    hW.natDegree_map coefficientMap
  have hconstant : φ (MvPolynomial.C r) = ψ r := by
    exact DFunLike.congr_fun hcomp r
  change φ (PolynomialResultant.multivariableResultantEliminant
    W q r n) = (ψ r) ^ W.natDegree
  change φ ((W.map coefficientMap).resultant
    (PolynomialResultant.eliminationPolynomial
      (fun i ↦ (q i).map coefficientMap) MvPolynomial.X
        (MvPolynomial.C r))
    (W.map coefficientMap).natDegree n) = (ψ r) ^ W.natDegree
  calc
    φ ((W.map coefficientMap).resultant
        (PolynomialResultant.eliminationPolynomial
          (fun i ↦ (q i).map coefficientMap) MvPolynomial.X
            (MvPolynomial.C r))
        (W.map coefficientMap).natDegree n) =
      φ (MvPolynomial.C r) ^ (W.map coefficientMap).natDegree := hpower
    _ = (ψ r) ^ W.natDegree := by rw [hconstant, hdegree]

end PolynomialResultant

end OnLeConjecture.Analytic
