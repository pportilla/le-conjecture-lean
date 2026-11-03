/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IsolatedFiberFiniteness
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Elimination for an isolated plane fibre

Weierstrass preparation replaces one element of the coordinate ideal by a
monic polynomial in the first coordinate. Division replaces the remaining
components by polynomials of smaller degree. If the parameter contraction
vanishes, localization gives a common polynomial divisor over the fraction
field. Integrally closedness descends its monic normalization. Its roots on
nearby parameter fibres contradict isolation of the zero fibre.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open _root_.Polynomial
open scoped NNReal Topology

namespace PolynomialRootBound

/-- A monic complex polynomial whose lower coefficients have norm less than
one has all its roots in the ball of radius two. -/
theorem norm_lt_two_of_monic_of_coeff_norm_lt_one
    {p : ℂ[X]} (hp : p.Monic)
    (hcoeff : ∀ i, i < p.natDegree → ‖p.coeff i‖ < 1)
    {x : ℂ} (hx : p.IsRoot x) :
    ‖x‖ < 2 := by
  have hpNe : p ≠ 0 := hp.ne_zero
  have hbound : p.cauchyBound < 2 := by
    rw [Polynomial.cauchyBound]
    have hlead : ‖p.leadingCoeff‖₊ = 1 := by
      rw [hp.leadingCoeff, nnnorm_one]
    rw [hlead, div_one]
    have hsup : (Finset.range p.natDegree).sup
        (fun i ↦ ‖p.coeff i‖₊) < 1 := by
      rw [Finset.sup_lt_iff zero_lt_one]
      intro i hi
      exact_mod_cast hcoeff i (Finset.mem_range.mp hi)
    calc
      (Finset.range p.natDegree).sup
            (fun i ↦ ‖p.coeff i‖₊) + 1 < 1 + 1 :=
        by simpa only [add_comm] using (add_lt_add_right hsup 1)
      _ = 2 := by norm_num
  exact_mod_cast (hx.norm_lt_cauchyBound hpNe).trans hbound

/-- Scaling a monic polynomial bounds its roots by twice the scaling
factor when every scaled lower coefficient has norm less than one. -/
theorem norm_lt_two_mul_of_monic_of_coeff_norm_lt_pow
    {p : ℂ[X]} (hp : p.Monic) {s x : ℂ} (hs : s ≠ 0)
    (hcoeff : ∀ i, i < p.natDegree →
      ‖p.coeff i‖ < ‖s‖ ^ (p.natDegree - i))
    (hx : p.IsRoot x) :
    ‖x‖ < 2 * ‖s‖ := by
  let q : ℂ[X] := p.scaleRoots s⁻¹
  have hqMonic : q.Monic :=
    (Polynomial.monic_scaleRoots_iff s⁻¹).mpr hp
  have hqRoot : q.IsRoot (s⁻¹ * x) := by
    exact Polynomial.scaleRoots_eval₂_eq_zero
      (RingHom.id ℂ) hx
  have hqCoeff : ∀ i, i < q.natDegree → ‖q.coeff i‖ < 1 := by
    intro i hi
    have hi' : i < p.natDegree := by simpa [q] using hi
    change ‖(p.scaleRoots s⁻¹).coeff i‖ < 1
    rw [Polynomial.coeff_scaleRoots, norm_mul, norm_pow, norm_inv]
    have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hpow : 0 < ‖s‖ ^ (p.natDegree - i) := pow_pos hsNorm _
    rw [inv_pow]
    exact (div_lt_one hpow).mpr (hcoeff i hi')
  have hscaled : ‖s⁻¹ * x‖ < 2 :=
    PolynomialRootBound.norm_lt_two_of_monic_of_coeff_norm_lt_one
      hqMonic hqCoeff hqRoot
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  rw [norm_mul, norm_inv] at hscaled
  have hxRewrite : ‖x‖ = ‖s‖ * (‖s‖⁻¹ * ‖x‖) := by
    field_simp
  rw [hxRewrite]
  nlinarith

end PolynomialRootBound

namespace PolynomialMonicDivisor

/-- A monic divisor of a power of the variable over a domain is the power
of the variable given by its degree. -/
theorem eq_X_pow_natDegree_of_dvd_X_pow
    {R : Type*} [CommRing R] [IsDomain R]
    {H : R[X]} (hH : H.Monic) {n : ℕ}
    (hdiv : H ∣ X ^ n) :
    H = X ^ H.natDegree := by
  obtain ⟨Q, hQ⟩ := hdiv
  have hQNe : Q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hQ
    exact (Polynomial.monic_X_pow n).ne_zero hQ
  have hdegree : H.natDegree + Q.natDegree = n := by
    have h := congrArg Polynomial.natDegree hQ
    simpa only [Polynomial.natDegree_X_pow,
      Polynomial.natDegree_mul hH.ne_zero hQNe] using h.symm
  have htrailing : H.natTrailingDegree + Q.natTrailingDegree = n := by
    have h := congrArg Polynomial.natTrailingDegree hQ
    simpa only [Polynomial.natTrailingDegree_X_pow,
      Polynomial.natTrailingDegree_mul hH.ne_zero hQNe] using h.symm
  apply hH.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr
  have hHTrailing := Polynomial.natTrailingDegree_le_natDegree H
  have hQTrailing := Polynomial.natTrailingDegree_le_natDegree Q
  omega

end PolynomialMonicDivisor

namespace PolynomialLocalization

/-- If an ideal becomes the unit ideal after localization, then it contains
an element of the localized submonoid. -/
theorem exists_mem_submonoid_of_map_eq_top
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S))
    (I : Ideal R)
    (h : Ideal.map (algebraMap R S) I = ⊤) :
    ∃ r : R, r ∈ I ∧ r ∈ M := by
  have h1 : (1 : S) ∈ Ideal.map (algebraMap R S) I := by simp [h]
  rw [IsLocalization.mem_map_algebraMap_iff M] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x.2, ?_, x.2.2⟩
  have heq : algebraMap R S x.2 = algebraMap R S x.1 := by
    simpa using hx
  exact hinj heq ▸ x.1.2

/-- An ideal of a polynomial ring whose contraction along constants is zero
stays proper over the fraction field. -/
theorem fraction_map_ne_top_of_comap_C_eq_bot
    (A : Type*) [CommRing A] [IsDomain A]
    (J : Ideal A[X])
    (hJ : Ideal.comap Polynomial.C J = ⊥) :
    Ideal.map
      (Polynomial.mapRingHom (algebraMap A (FractionRing A))) J ≠ ⊤ := by
  let M : Submonoid A[X] :=
    (nonZeroDivisors A).map Polynomial.C.toMonoidHom
  let _ : Algebra A[X] (FractionRing A)[X] :=
    Polynomial.algebra A (FractionRing A)
  have _ : IsLocalization M (FractionRing A)[X] :=
    Polynomial.isLocalization (nonZeroDivisors A) (FractionRing A)
  change Ideal.map (algebraMap A[X] (FractionRing A)[X]) J ≠ ⊤
  intro htop
  obtain ⟨q, hqJ, hqM⟩ :=
    exists_mem_submonoid_of_map_eq_top M
      (Polynomial.map_injective (algebraMap A (FractionRing A))
        (IsFractionRing.injective A (FractionRing A))) J htop
  obtain ⟨a, ha, hqa⟩ := hqM
  have hCaJ : Polynomial.C a ∈ J := hqa ▸ hqJ
  have ha0 : a = 0 := by
    have : a ∈ Ideal.comap Polynomial.C J := hCaJ
    rw [hJ] at this
    exact this
  exact (nonZeroDivisors.ne_zero ha) ha0

/-- A proper polynomial ideal over the fraction field which contains the
image of a monic polynomial has a positive degree monic common divisor over
the original integrally closed domain. -/
theorem monic_common_divisor_of_fraction_map_proper
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (J : Ideal A[X]) (P : A[X]) (hP : P.Monic) (hPJ : P ∈ J)
    (hproper : Ideal.map
      (Polynomial.mapRingHom (algebraMap A (FractionRing A))) J ≠ ⊤) :
    ∃ H : A[X], H.Monic ∧ 0 < H.natDegree ∧
      ∀ Q ∈ J, H ∣ Q := by
  let φ : A →+* FractionRing A := algebraMap A (FractionRing A)
  let JK : Ideal (FractionRing A)[X] :=
    Ideal.map (Polynomial.mapRingHom φ) J
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal JK).1
  have hPJK : P.map φ ∈ JK :=
    Ideal.mem_map_of_mem (Polynomial.mapRingHom φ) hPJ
  have hqDvdP : q ∣ P.map φ := by
    rw [hq] at hPJK
    exact Ideal.mem_span_singleton.mp hPJK
  have hq0 : q ≠ 0 := by
    intro hq0
    have : JK = ⊥ := by simpa [hq0] using hq
    have hPmap0 : P.map φ = 0 := by
      rw [this] at hPJK
      exact hPJK
    exact (hP.map φ).ne_zero hPmap0
  let HK : (FractionRing A)[X] :=
    q * Polynomial.C q.leadingCoeff⁻¹
  have hHK : HK.Monic := Polynomial.monic_mul_leadingCoeff_inv hq0
  have hassoc : Associated HK q := by
    symm
    apply (associated_mul_isUnit_right_iff ?_).mpr (Associated.refl q)
    exact Polynomial.isUnit_C.mpr
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq0)).isUnit
  have hHKDvdP : HK ∣ P.map φ :=
    hassoc.dvd_iff_dvd_left.mpr hqDvdP
  obtain ⟨H, hHlift⟩ :=
    IsIntegrallyClosed.eq_map_mul_C_of_dvd
      (FractionRing A) hP hHKDvdP
  have hHKlc : HK.leadingCoeff = 1 := hHK.leadingCoeff
  rw [hHKlc, Polynomial.C_1, mul_one] at hHlift
  have hH : H.Monic :=
    Polynomial.monic_of_injective
      (IsFractionRing.injective A (FractionRing A))
      (hHlift.symm ▸ hHK)
  refine ⟨H, hH, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro hdegree
    have hH1 : H = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hH hdegree
    have hHKmem : HK ∈ JK := by
      rw [hq]
      exact Ideal.mem_span_singleton.mpr hassoc.symm.dvd
    have hOneMem : (1 : (FractionRing A)[X]) ∈ JK := by
      have hHKone : HK = 1 := by
        rw [← hHlift, hH1, Polynomial.map_one]
      rwa [hHKone] at hHKmem
    exact hproper (by
      simpa [JK, φ] using ((Ideal.eq_top_iff_one JK).2 hOneMem))
  · intro Q hQJ
    have hQJK : Q.map φ ∈ JK :=
      Ideal.mem_map_of_mem (Polynomial.mapRingHom φ) hQJ
    have hqDvdQ : q ∣ Q.map φ := by
      rw [hq] at hQJK
      exact Ideal.mem_span_singleton.mp hQJK
    have hHKDvdQ : HK ∣ Q.map φ :=
      hassoc.dvd_iff_dvd_left.mpr hqDvdQ
    have hHmapDvdQ : H.map φ ∣ Q.map φ :=
      hHlift.symm ▸ hHKDvdQ
    exact (Polynomial.map_dvd_map φ
      (IsFractionRing.injective A (FractionRing A)) hH).mp hHmapDvdQ

end PolynomialLocalization

namespace Germ

/-- Specializing a distinguished monic polynomial at the origin gives a
power of the polynomial variable. -/
theorem map_valueRingHom_eq_X_pow
    (P : Polynomial (Germ 1)) (hP : P.Monic)
    (hcoeff : ∀ k, k < P.natDegree →
      P.coeff k ∈ Germ.maximalIdeal 1) :
    P.map (Germ.valueRingHom 1) = X ^ P.natDegree := by
  have hzero : ∀ i ∈ Finset.range P.natDegree,
      Germ.valueRingHom 1 (P.coeff i) = 0 := by
    intro i hi
    exact Germ.mem_maximalIdeal_iff.mp
      (hcoeff i (Finset.mem_range.mp hi))
  calc
    P.map (Germ.valueRingHom 1) =
        (X ^ P.natDegree +
          ∑ i ∈ Finset.range P.natDegree,
            Polynomial.C (P.coeff i) * X ^ i).map
              (Germ.valueRingHom 1) :=
      congrArg (Polynomial.map (Germ.valueRingHom 1)) hP.as_sum
    _ = X ^ P.natDegree +
        ∑ i ∈ Finset.range P.natDegree,
          Polynomial.C (Germ.valueRingHom 1 (P.coeff i)) * X ^ i := by
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
      congr 1
      change (Polynomial.mapRingHom (Germ.valueRingHom 1))
          (∑ i ∈ Finset.range P.natDegree,
            Polynomial.C (P.coeff i) * X ^ i) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [map_mul, Polynomial.coe_mapRingHom,
        Polynomial.map_C, map_pow, Polynomial.map_X]
    _ = X ^ P.natDegree := by
      rw [Finset.sum_eq_zero]
      · simp
      · intro i hi
        rw [hzero i hi, Polynomial.C_0, zero_mul]

/-- Evaluation of a finite polynomial written through its coefficients is
the corresponding finite sum of plane germs. -/
theorem firstCoordinatePolynomialEvaluation_fin_sum_C_mul_X_pow
    {n : ℕ} (r : Fin n → Germ 1) :
    Germ.firstCoordinatePolynomialEvaluation
        (∑ i : Fin n, Polynomial.C (r i) * X ^ i.1) =
      ∑ i : Fin n,
        Germ.coordinate (0 : Fin 2) ^ i.1 *
          Germ.hyperplaneExtension 1 (r i) := by
  rw [Germ.firstCoordinatePolynomialEvaluation]
  change Polynomial.eval₂ (Germ.hyperplaneExtension 1)
      (Germ.coordinate (0 : Fin 2))
      (∑ i ∈ Finset.univ, Polynomial.C (r i) * X ^ i.1) = _
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  exact mul_comm _ _

/-- A monic polynomial with chosen analytic coefficient representatives is
represented by the corresponding polynomial function on the plane. -/
theorem coe_firstCoordinatePolynomialEvaluation_monic
    (H : Polynomial (Germ 1)) (hH : H.Monic)
    (A : Fin H.natDegree → Source 1 → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAeq : ∀ i, H.coeff i.1 = Germ.ofFunction (A i) (hA i)) :
    ((Germ.firstCoordinatePolynomialEvaluation H : Germ 2) :
        FunctionGerm 2) =
      ((fun z : Source 2 ↦
          z 0 ^ H.natDegree +
            ∑ i : Fin H.natDegree,
              A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
        FunctionGerm 2) := by
  calc
    ((Germ.firstCoordinatePolynomialEvaluation H : Germ 2) :
        FunctionGerm 2) =
        ((Germ.firstCoordinatePolynomialEvaluation
          (X ^ H.natDegree +
            ∑ i : Fin H.natDegree,
              Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
          FunctionGerm 2) := by
      have hsum : H = X ^ H.natDegree +
          ∑ i : Fin H.natDegree,
            Polynomial.C (H.coeff i.1) * X ^ i.1 := by
        simpa only [← Fin.sum_univ_eq_sum_range] using hH.as_sum
      exact congrArg (fun p : Polynomial (Germ 1) ↦
        ((Germ.firstCoordinatePolynomialEvaluation p : Germ 2) :
          FunctionGerm 2)) hsum
    _ = ((fun z : Source 2 ↦
          z 0 ^ H.natDegree +
            ∑ i : Fin H.natDegree,
              A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
        FunctionGerm 2) := by
      rw [Germ.firstCoordinatePolynomialEvaluation]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_X]
      have hlead :
          (((Germ.coordinate (0 : Fin 2)) ^ H.natDegree : Germ 2) :
              FunctionGerm 2) =
            ((fun z : Source 2 ↦ z 0 ^ H.natDegree) :
              FunctionGerm 2) :=
        Filter.Germ.coe_pow (fun z : Source 2 ↦ z 0) H.natDegree
      have hterms :
          ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
              (Germ.coordinate (0 : Fin 2))
              (∑ i : Fin H.natDegree,
                Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
            FunctionGerm 2) =
          ((fun z : Source 2 ↦
            ∑ i : Fin H.natDegree,
              A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
            FunctionGerm 2) := by
        have hterm (i : Fin H.natDegree) :
            ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                (Germ.coordinate (0 : Fin 2))
                (Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
              FunctionGerm 2) =
            ((fun z : Source 2 ↦
                A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
              FunctionGerm 2) := by
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
            Polynomial.eval₂_pow, Polynomial.eval₂_X]
          rw [hAeq i, Germ.hyperplaneExtension_ofFunction]
          exact Filter.Germ.coe_mul
            (A i ∘ Germ.hyperplaneTail 1)
            (fun z : Source 2 ↦ z 0 ^ i.1)
        have hsum (s : Finset (Fin H.natDegree)) :
            ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                (Germ.coordinate (0 : Fin 2))
                (∑ i ∈ s,
                  Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
              FunctionGerm 2) =
            ((fun z : Source 2 ↦
                ∑ i ∈ s,
                  A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
              FunctionGerm 2) := by
          induction s using Finset.induction_on with
          | empty =>
              rw [Finset.sum_empty, Polynomial.eval₂_zero]
              simp only [Finset.sum_empty]
              rfl
          | @insert i s hi ih =>
              simp only [Finset.sum_insert hi]
              rw [Polynomial.eval₂_add]
              calc
                (((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                    (Germ.coordinate (0 : Fin 2))
                    (Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) +
                  Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                    (Germ.coordinate (0 : Fin 2))
                    (∑ j ∈ s,
                      Polynomial.C (H.coeff j.1) * X ^ j.1) : Germ 2) :
                    FunctionGerm 2) =
                  ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                      (Germ.coordinate (0 : Fin 2))
                      (Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
                    FunctionGerm 2) +
                  ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                      (Germ.coordinate (0 : Fin 2))
                      (∑ j ∈ s,
                        Polynomial.C (H.coeff j.1) * X ^ j.1) : Germ 2) :
                    FunctionGerm 2) := rfl
                _ = ((fun z : Source 2 ↦
                      A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
                      FunctionGerm 2) +
                    ((fun z : Source 2 ↦
                      ∑ j ∈ s,
                        A j (Germ.hyperplaneTail 1 z) * z 0 ^ j.1) :
                      FunctionGerm 2) := congrArg₂ (· + ·) (hterm i) ih
                _ = ((fun z : Source 2 ↦
                      A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1 +
                        ∑ j ∈ s,
                          A j (Germ.hyperplaneTail 1 z) * z 0 ^ j.1) :
                      FunctionGerm 2) :=
                  (Filter.Germ.coe_add
                    (fun z : Source 2 ↦
                      A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1)
                    (fun z : Source 2 ↦
                      ∑ j ∈ s,
                        A j (Germ.hyperplaneTail 1 z) * z 0 ^ j.1)).symm
        exact hsum Finset.univ
      calc
        (((Germ.coordinate (0 : Fin 2)) ^ H.natDegree +
            Polynomial.eval₂ (Germ.hyperplaneExtension 1)
              (Germ.coordinate (0 : Fin 2))
              (∑ i : Fin H.natDegree,
                Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
          FunctionGerm 2) =
            (((Germ.coordinate (0 : Fin 2)) ^ H.natDegree : Germ 2) :
                FunctionGerm 2) +
              ((Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                  (Germ.coordinate (0 : Fin 2))
                  (∑ i : Fin H.natDegree,
                    Polynomial.C (H.coeff i.1) * X ^ i.1) : Germ 2) :
                FunctionGerm 2) := rfl
        _ = ((fun z : Source 2 ↦ z 0 ^ H.natDegree) :
              FunctionGerm 2) +
            ((fun z : Source 2 ↦
              ∑ i : Fin H.natDegree,
                A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
              FunctionGerm 2) := congrArg₂ (· + ·) hlead hterms
        _ = ((fun z : Source 2 ↦
              z 0 ^ H.natDegree +
                ∑ i : Fin H.natDegree,
                  A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1) :
            FunctionGerm 2) :=
          (Filter.Germ.coe_add
            (fun z : Source 2 ↦ z 0 ^ H.natDegree)
            (fun z : Source 2 ↦
              ∑ i : Fin H.natDegree,
                A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1)).symm

end Germ

namespace PointedMapGerm

/-- Composing an isolated zero fibre with a locally injective pointed germ
preserves isolation. -/
theorem comp_hasIsolatedZeroRepresentative
    {l n m : ℕ} (g : PointedMapGerm n m) (h : PointedMapGerm l n)
    (hg : g.HasIsolatedZeroRepresentative)
    (hh : h.HasInjectiveRepresentative) :
    (g.comp h).HasIsolatedZeroRepresentative := by
  rcases hg with ⟨G, hGan, hG0, hgerm, s, hs, hGzero⟩
  rcases hh with ⟨H, hHan, hH0, hhgerm, t, ht, hHinj⟩
  have hGatH0 : AnalyticAt ℂ G (H 0) := by
    simpa only [hH0] using hGan
  have hcompAnalytic : AnalyticAt ℂ (G ∘ H) 0 := hGatH0.comp hHan
  have hcompZero : (G ∘ H) 0 = 0 := by
    simp only [Function.comp_apply, hH0, hG0]
  have hpre : H ⁻¹' s ∈ 𝓝 (0 : Source l) := by
    have hsH0 : s ∈ 𝓝 (H 0) := by simpa only [hH0] using hs
    exact hHan.continuousAt hsH0
  refine ⟨G ∘ H, hcompAnalytic, hcompZero, ?_,
    t ∩ H ⁻¹' s, inter_mem ht hpre, ?_⟩
  · rw [hgerm, hhgerm]
    exact PointedMapGerm.comp_ofFunction G hGan hG0 H hHan hH0
  · intro x hx hzero
    have hHzero : H x = 0 := hGzero (H x) hx.2 hzero
    exact hHinj hx.1 (mem_of_mem_nhds ht) (by simpa only [hH0] using hHzero)

/-- An invertible source coordinate change preserves an isolated zero
fibre. -/
theorem comp_equivForward_hasIsolatedZeroRepresentative
    {n m : ℕ} (f : PointedMapGerm n m) (e : PointedEquivGerm n)
    (hf : f.HasIsolatedZeroRepresentative) :
    (f.comp e.forward).HasIsolatedZeroRepresentative :=
  PointedMapGerm.comp_hasIsolatedZeroRepresentative f e.forward hf
    e.forward_hasInjectiveRepresentative

/-- A plane map germ whose components have a common distinguished monic
divisor of positive degree cannot have an isolated zero fibre. -/
theorem not_hasIsolatedZeroRepresentative_of_monic_common_divisor
    {m : ℕ} (f : PointedMapGerm 2 m)
    (H : Polynomial (Germ 1))
    (hH : H.Monic) (hHdegree : 0 < H.natDegree)
    (hHcoeff : ∀ k, k < H.natDegree →
      H.coeff k ∈ Germ.maximalIdeal 1)
    (hdiv : ∀ i : Fin m,
      Germ.firstCoordinatePolynomialEvaluation H ∣ f.1.component i) :
    ¬ f.HasIsolatedZeroRepresentative := by
  intro hisolated
  rcases hisolated with
    ⟨F, hF, hF0, hf, isolatedSet, hisolatedSet, hzero⟩
  choose A hA hAeq using fun i : Fin H.natDegree ↦
    Germ.exists_analyticRepresentative_allOrders (H.coeff i.1)
  let a : Fin H.natDegree → ℂ → ℂ := fun i ↦
    Germ.oneVariableRepresentative (A i)
  have haAnalytic (i : Fin H.natDegree) : AnalyticAt ℂ (a i) 0 :=
    Germ.oneVariableRepresentative_analyticAt (hA i)
  have hAZero (i : Fin H.natDegree) : A i 0 = 0 := by
    have hi := hHcoeff i.1 i.2
    rw [Germ.mem_maximalIdeal_iff, hAeq i,
      Germ.valueRingHom_ofFunction] at hi
    exact hi
  have haZero (i : Fin H.natDegree) : a i 0 = 0 := by
    simp [a, Germ.oneVariableRepresentative_apply, hAZero i]
  let W : Source 2 → ℂ := fun z ↦
    z 0 ^ H.natDegree +
      ∑ i : Fin H.natDegree,
        A i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1
  have hWgerm :
      ((Germ.firstCoordinatePolynomialEvaluation H : Germ 2) :
          FunctionGerm 2) = (W : FunctionGerm 2) := by
    exact Germ.coe_firstCoordinatePolynomialEvaluation_monic
      H hH A hA hAeq
  choose Q hQ using hdiv
  choose Qfun hQfun hQrepr using fun i : Fin m ↦
    Germ.exists_analyticRepresentative_allOrders (Q i)
  have hcomponentGerm (i : Fin m) :
      ((f.1.component i : Germ 2) : FunctionGerm 2) =
        ((fun z : Source 2 ↦ F z i) : FunctionGerm 2) := by
    rw [hf]
    exact MapGerm.component_ofFunction F hF i
  have hQgerm (i : Fin m) :
      ((Q i : Germ 2) : FunctionGerm 2) =
        (Qfun i : FunctionGerm 2) := by
    exact congrArg (fun q : Germ 2 ↦ (q : FunctionGerm 2))
      (hQrepr i)
  have hcomponentRelation (i : Fin m) :
      ∀ᶠ z : Source 2 in 𝓝 0,
        F z i = W z * Qfun i z := by
    apply Filter.Germ.coe_eq.mp
    calc
      ((fun z : Source 2 ↦ F z i) : FunctionGerm 2) =
          ((f.1.component i : Germ 2) : FunctionGerm 2) :=
        (hcomponentGerm i).symm
      _ = ((Germ.firstCoordinatePolynomialEvaluation H * Q i : Germ 2) :
          FunctionGerm 2) :=
        congrArg (fun q : Germ 2 ↦ (q : FunctionGerm 2)) (hQ i)
      _ = ((Germ.firstCoordinatePolynomialEvaluation H : Germ 2) :
            FunctionGerm 2) *
          ((Q i : Germ 2) : FunctionGerm 2) := rfl
      _ = (W : FunctionGerm 2) * (Qfun i : FunctionGerm 2) :=
        congrArg₂ (· * ·) hWgerm (hQgerm i)
      _ = ((fun z : Source 2 ↦ W z * Qfun i z) :
          FunctionGerm 2) :=
        (Filter.Germ.coe_mul W (Qfun i)).symm
  have hcomponentRelationAll :
      ∀ᶠ z : Source 2 in 𝓝 0,
        ∀ i : Fin m, F z i = W z * Qfun i z :=
    Filter.eventually_all.mpr hcomponentRelation
  have hcommon : isolatedSet ∩
      {z : Source 2 | ∀ i : Fin m, F z i = W z * Qfun i z} ∈
        𝓝 (0 : Source 2) :=
    Filter.inter_mem hisolatedSet hcomponentRelationAll
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hcommon
  let scale : ℂ := (epsilon / 4 : ℝ)
  have hscale : scale ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero hepsilon.ne' (by norm_num : (4 : ℝ) ≠ 0))
  have hscaleNorm : ‖scale‖ = epsilon / 4 := by
    simp [scale, abs_of_pos hepsilon]
  have hcoefficientEventually (i : Fin H.natDegree) :
      ∀ᶠ y : ℂ in 𝓝 0,
        ‖a i y‖ < ‖scale‖ ^ (H.natDegree - i.1) := by
    have hpower : 0 < ‖scale‖ ^ (H.natDegree - i.1) :=
      pow_pos (norm_pos_iff.mpr hscale) _
    have htendsto : Tendsto (a i) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, haZero i] using (haAnalytic i).continuousAt
    have hballCoefficient := htendsto.eventually
      (Metric.ball_mem_nhds (0 : ℂ) hpower)
    filter_upwards [hballCoefficient] with y hy
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hcoefficientEventuallyAll :
      ∀ᶠ y : ℂ in 𝓝 0,
        ∀ i : Fin H.natDegree,
          ‖a i y‖ < ‖scale‖ ^ (H.natDegree - i.1) :=
    Filter.eventually_all.mpr hcoefficientEventually
  obtain ⟨delta, hdelta, hballCoefficient⟩ :=
    Metric.mem_nhds_iff.mp hcoefficientEventuallyAll
  let eta : ℝ := min delta (epsilon / 4)
  have heta : 0 < eta := lt_min hdelta (div_pos hepsilon (by norm_num))
  let y : ℂ := (eta / 2 : ℝ)
  have hyNorm : ‖y‖ = eta / 2 := by
    simp [y, abs_of_pos heta]
  have hyNe : y ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero heta.ne' (by norm_num : (2 : ℝ) ≠ 0))
  have hyDelta : y ∈ Metric.ball (0 : ℂ) delta := by
    rw [Metric.mem_ball, dist_zero_right, hyNorm]
    have hetaDelta : eta ≤ delta := min_le_left _ _
    linarith
  have hySmall : ‖y‖ < epsilon := by
    rw [hyNorm]
    have hetaEpsilon : eta ≤ epsilon / 4 := min_le_right _ _
    linarith
  let p : ℂ[X] := X ^ H.natDegree +
    ∑ i : Fin H.natDegree, Polynomial.C (a i y) * X ^ i.1
  have hlowerDegree :
      (∑ i : Fin H.natDegree,
        Polynomial.C (a i y) * X ^ i.1 : ℂ[X]).degree < H.natDegree :=
    Polynomial.degree_sum_fin_lt (fun i : Fin H.natDegree ↦ a i y)
  have hpMonic : p.Monic := by
    exact Polynomial.monic_X_pow_add hlowerDegree
  have hpDegree : p.degree = H.natDegree := by
    change (X ^ H.natDegree +
      ∑ i : Fin H.natDegree,
        Polynomial.C (a i y) * X ^ i.1 : ℂ[X]).degree = H.natDegree
    calc
      _ = (X ^ H.natDegree : ℂ[X]).degree :=
        Polynomial.degree_add_eq_left_of_degree_lt
          (by simpa only [Polynomial.degree_X_pow] using hlowerDegree)
      _ = H.natDegree := Polynomial.degree_X_pow _
  have hpNatDegree : p.natDegree = H.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq_some hpDegree
  have hpCoeff (k : ℕ) (hk : k < H.natDegree) :
      p.coeff k = a ⟨k, hk⟩ y := by
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      if_neg hk.ne, zero_add, Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro j _hj hne
      rw [if_neg]
      intro heq
      apply hne
      apply Fin.ext
      exact heq.symm
    · simp
  have hpCoefficientBound : ∀ k, k < p.natDegree →
      ‖p.coeff k‖ < ‖scale‖ ^ (p.natDegree - k) := by
    intro k hk
    have hk' : k < H.natDegree := hpNatDegree ▸ hk
    rw [hpCoeff k hk', hpNatDegree]
    exact hballCoefficient hyDelta ⟨k, hk'⟩
  have hpDegreeNe : p.degree ≠ 0 := by
    rw [hpDegree]
    exact_mod_cast hHdegree.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hpDegreeNe
  have hxSmall : ‖x‖ < epsilon := by
    have hxBound :=
      PolynomialRootBound.norm_lt_two_mul_of_monic_of_coeff_norm_lt_pow
        hpMonic hscale hpCoefficientBound hx
    rw [hscaleNorm] at hxBound
    linarith
  let z : Source 2 := fun i ↦ Fin.cases x (fun _ ↦ y) i
  have hz0 : z (0 : Fin 2) = x := by rfl
  have hz1 : z (1 : Fin 2) = y := by rfl
  have hzSucc : z (Fin.succ (0 : Fin 1)) = y := by rfl
  have hzZero : W z = 0 := by
    have htail (i : Fin H.natDegree) :
        A i (Germ.hyperplaneTail 1 z) = a i y := by
      have hrepresentative :=
        congrFun (Germ.oneVariableRepresentative_comp_coordinate (A i))
          (Germ.hyperplaneTail 1 z)
      calc
        A i (Germ.hyperplaneTail 1 z) =
            a i ((Germ.hyperplaneTail 1 z) 0) := by
          simpa only [a] using hrepresentative.symm
        _ = a i y := by
          rw [Germ.hyperplaneTail_apply, hzSucc]
    have hroot : Polynomial.eval x p = 0 := hx
    rw [show W z = x ^ H.natDegree +
        ∑ i : Fin H.natDegree, a i y * x ^ i.1 by
      simp only [W, hz0, htail]]
    simpa only [p, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C] using hroot
  have hzNorm : ‖z‖ < epsilon := by
    rw [pi_norm_lt_iff hepsilon]
    intro i
    fin_cases i
    · change ‖z (0 : Fin 2)‖ < epsilon
      rw [hz0]
      exact hxSmall
    · change ‖z (1 : Fin 2)‖ < epsilon
      rw [hz1]
      exact hySmall
  have hzBall : z ∈ Metric.ball (0 : Source 2) epsilon := by
    rwa [Metric.mem_ball, dist_zero_right]
  have hzCommon := hball hzBall
  have hFz : F z = 0 := by
    funext i
    rw [hzCommon.2 i, hzZero, zero_mul]
    rfl
  have hzEq : z = 0 := hzero z hzCommon.1 hFz
  have hyZero := congrFun hzEq (1 : Fin 2)
  rw [hz1] at hyZero
  exact hyNe hyZero

/-- The coordinate ideal of an isolated plane zero fibre has nonzero
contraction to the one variable parameter ring after preparation in the
first coordinate. -/
theorem planeIsolatedFiberElimination (m : ℕ) :
    PointedMapGerm.PlaneIsolatedFiberElimination m := by
  intro f e g d hisolated hg hregular
  let transformed : PointedMapGerm 2 m := f.comp e.forward
  let I : Ideal (Germ 2) := transformed.1.coordinateIdeal
  have htransformedIsolated : transformed.HasIsolatedZeroRepresentative :=
    PointedMapGerm.comp_equivForward_hasIsolatedZeroRepresentative
      f e hisolated
  obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hregular
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  have hWI : W ∈ I := by
    have hgI : g ∈ I := by exact hg
    have hproduct : g * (↑(hu.unit⁻¹) : Germ 2) ∈ I := by
      simpa [mul_comm] using
        I.mul_mem_left (↑(hu.unit⁻¹) : Germ 2) hgI
    have hproductEq : g * (↑(hu.unit⁻¹) : Germ 2) = W := by
      calc
        g * (↑(hu.unit⁻¹) : Germ 2) =
            (W * u) * (↑(hu.unit⁻¹) : Germ 2) := by
          rw [hfactor]
        _ = W * ((↑hu.unit : Germ 2) *
            (↑(hu.unit⁻¹) : Germ 2)) := by
          rw [hu.unit_spec, mul_assoc]
        _ = W := by simp
    rwa [hproductEq] at hproduct
  let a : Fin (d + 1) → Germ 1 := fun i ↦ P.coeff i.1
  have ha : ∀ i, a i ∈ Germ.maximalIdeal 1 := by
    intro i
    exact hPCoeff i.1 i.2
  have hPgeneral :
      P = Germ.generalWeierstrassPolynomial d a :=
    Germ.eq_generalWeierstrassPolynomial_of_monic_natDegree
      d P hPMonic hPDegree
  choose q r hdivision using fun i : Fin m ↦
    Germ.exists_generalWeierstrassDivision d a ha
      (transformed.1.component i)
  let R : Fin m → Polynomial (Germ 1) := fun i ↦
    ∑ j : Fin (d + 1), Polynomial.C (r i j) * X ^ j.1
  have hREvaluation (i : Fin m) :
      Germ.firstCoordinatePolynomialEvaluation (R i) =
        ∑ j : Fin (d + 1),
          Germ.coordinate (0 : Fin 2) ^ j.1 *
            Germ.hyperplaneExtension 1 (r i j) := by
    exact Germ.firstCoordinatePolynomialEvaluation_fin_sum_C_mul_X_pow
      (r i)
  have hdivisionEvaluation (i : Fin m) :
      transformed.1.component i = W * q i +
        Germ.firstCoordinatePolynomialEvaluation (R i) := by
    have hi := hdivision i
    rw [← hPgeneral] at hi
    rw [hREvaluation i]
    exact hi
  have hRI (i : Fin m) :
      Germ.firstCoordinatePolynomialEvaluation (R i) ∈ I := by
    have hcomponentI : transformed.1.component i ∈ I :=
      transformed.1.component_mem_coordinateIdeal i
    have hproductI : W * q i ∈ I := I.mul_mem_right (q i) hWI
    have hsub := I.sub_mem hcomponentI hproductI
    have heq : transformed.1.component i - W * q i =
        Germ.firstCoordinatePolynomialEvaluation (R i) := by
      rw [hdivisionEvaluation i]
      ring
    rwa [heq] at hsub
  let evaluation : Polynomial (Germ 1) →+* Germ 2 :=
    Polynomial.eval₂RingHom (Germ.hyperplaneExtension 1)
      (Germ.coordinate (0 : Fin 2))
  let J : Ideal (Polynomial (Germ 1)) :=
    Ideal.span (insert P (Set.range R))
  have hJle : J ≤ Ideal.comap evaluation I := by
    rw [Ideal.span_le]
    intro Q hQ
    rcases hQ with hQP | hQR
    · subst Q
      exact hWI
    · obtain ⟨i, rfl⟩ := hQR
      exact hRI i
  intro hcontraction
  have hcontractionI :
      Ideal.comap (Germ.hyperplaneExtension 1) I = ⊥ := by
    exact hcontraction
  have hJcontraction : Ideal.comap Polynomial.C J = ⊥ := by
    apply le_antisymm
    · intro c hc
      rw [Ideal.mem_bot]
      have hevaluation : evaluation (Polynomial.C c) ∈ I := hJle hc
      have hcI : Germ.hyperplaneExtension 1 c ∈ I := by
        change Polynomial.eval₂ (Germ.hyperplaneExtension 1)
          (Germ.coordinate (0 : Fin 2)) (Polynomial.C c) ∈ I at hevaluation
        simpa only [Polynomial.eval₂_C] using hevaluation
      have hcContraction : c ∈
          Ideal.comap (Germ.hyperplaneExtension 1) I := hcI
      rw [hcontractionI] at hcContraction
      exact Ideal.mem_bot.mp hcContraction
    · exact bot_le
  have hproper :=
    PolynomialLocalization.fraction_map_ne_top_of_comap_C_eq_bot
      (Germ 1) J hJcontraction
  have hPJ : P ∈ J :=
    Ideal.subset_span (Set.mem_insert P (Set.range R))
  obtain ⟨H, hHMonic, hHDegree, hHdiv⟩ :=
    PolynomialLocalization.monic_common_divisor_of_fraction_map_proper
      (Germ 1) J P hPMonic hPJ hproper
  have hHdivP : H ∣ P := hHdiv P hPJ
  have hHdivR (i : Fin m) : H ∣ R i := by
    apply hHdiv (R i)
    exact Ideal.subset_span
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_range_self i)))
  have hPCoeffDegree : ∀ k, k < P.natDegree →
      P.coeff k ∈ Germ.maximalIdeal 1 := by
    intro k hk
    rw [hPDegree] at hk
    exact hPCoeff k hk
  have hPvalue : P.map (Germ.valueRingHom 1) = X ^ P.natDegree :=
    Germ.map_valueRingHom_eq_X_pow P hPMonic hPCoeffDegree
  have hHmapDvd : H.map (Germ.valueRingHom 1) ∣
      X ^ P.natDegree := by
    rw [← hPvalue]
    exact Polynomial.map_dvd (Germ.valueRingHom 1) hHdivP
  have hHmapEq : H.map (Germ.valueRingHom 1) = X ^ H.natDegree := by
    have h :=
      PolynomialMonicDivisor.eq_X_pow_natDegree_of_dvd_X_pow
        (hHMonic.map (Germ.valueRingHom 1)) hHmapDvd
    rw [hHMonic.natDegree_map] at h
    exact h
  have hHCoeff : ∀ k, k < H.natDegree →
      H.coeff k ∈ Germ.maximalIdeal 1 := by
    intro k hk
    rw [Germ.mem_maximalIdeal_iff]
    have hcoeff := congrArg
      (fun Q : ℂ[X] ↦ Q.coeff k) hHmapEq
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow,
      if_neg hk.ne] at hcoeff
    exact hcoeff
  have hcomponentDiv (i : Fin m) :
      Germ.firstCoordinatePolynomialEvaluation H ∣
        transformed.1.component i := by
    have hEvalP := map_dvd evaluation hHdivP
    have hEvalR := map_dvd evaluation (hHdivR i)
    change Germ.firstCoordinatePolynomialEvaluation H ∣
      Germ.firstCoordinatePolynomialEvaluation P at hEvalP
    change Germ.firstCoordinatePolynomialEvaluation H ∣
      Germ.firstCoordinatePolynomialEvaluation (R i) at hEvalR
    rw [hdivisionEvaluation i]
    exact dvd_add (dvd_mul_of_dvd_left hEvalP (q i)) hEvalR
  exact
    (PointedMapGerm.not_hasIsolatedZeroRepresentative_of_monic_common_divisor
      transformed H hHMonic hHDegree hHCoeff hcomponentDiv)
      htransformedIsolated

/-- The local analytic Nullstellensatz holds for coordinate ideals of plane
map germs. -/
theorem localAnalyticNullstellensatzAtOrigin_two (m : ℕ) :
    PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin 2 m :=
  (PointedMapGerm.localAnalyticNullstellensatzAtOrigin_two_iff_elimination
    m).mpr (PointedMapGerm.planeIsolatedFiberElimination m)

/-- An isolated zero fibre of a plane map germ has finite coordinate
colength. -/
theorem isolatedFiberHasFiniteColengthAtOrigin_two (m : ℕ) :
    PointedMapGerm.IsolatedFiberHasFiniteColengthAtOrigin 2 m :=
  (PointedMapGerm.isolatedFiberHasFiniteColengthAtOrigin_two_iff_elimination
    m).mpr (PointedMapGerm.planeIsolatedFiberElimination m)

end PointedMapGerm

end OnLeConjecture.Analytic
