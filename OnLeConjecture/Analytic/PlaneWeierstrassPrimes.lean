/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneNoetherian
public import OnLeConjecture.Analytic.OneVariableOrder
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Prime divisors of analytic Weierstrass polynomials

Analytic Weierstrass division is unique because completed Taylor expansion is
injective and formal Weierstrass division is unique. It follows that the
analytic quotient by a distinguished polynomial is isomorphic to the
corresponding polynomial quotient over the one variable germ ring.

A monic divisor of a distinguished polynomial is distinguished. This follows
by reducing modulo the maximal ideal and observing that a monic divisor of a
power of the polynomial variable is a power of that variable. Unique
factorization over the one variable germ ring then supplies a prime factor
inside any prime ideal containing a distinguished Weierstrass polynomial.
-/

public section

open scoped Polynomial

namespace OnLeConjecture.Analytic

namespace Germ

/-- Evaluation of a polynomial over one variable analytic germs at the first
plane coordinate. The coefficient map extends germs along the second
coordinate. -/
@[expose] noncomputable def firstCoordinatePolynomialEvaluationRingHom :
    Polynomial (Germ 1) →+* Germ 2 :=
  Polynomial.eval₂RingHom (Germ.hyperplaneExtension 1)
    (Germ.coordinate (0 : Fin 2))

/-- The bundled polynomial evaluation agrees with the existing evaluation
definition. -/
@[simp]
theorem firstCoordinatePolynomialEvaluationRingHom_apply
    (P : Polynomial (Germ 1)) :
    Germ.firstCoordinatePolynomialEvaluationRingHom P =
      Germ.firstCoordinatePolynomialEvaluation P :=
  rfl

/-- Evaluation of polynomials with one variable analytic coefficients in the
first plane coordinate is injective. -/
theorem firstCoordinatePolynomialEvaluation_injective :
    Function.Injective Germ.firstCoordinatePolynomialEvaluation := by
  intro P Q hPQ
  apply Polynomial.map_injective Germ.oneVariableTaylorRingHom
    Germ.oneVariableTaylorRingHom_injective
  apply Polynomial.ext
  intro k
  have hTaylor := congrArg Germ.completedPlaneTaylorRingHom hPQ
  rw [Germ.completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation,
    Germ.completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation] at hTaylor
  simpa only [Polynomial.coeff_coe] using
    congrArg (PowerSeries.coeff k) hTaylor

/-- Evaluation of a polynomial indexed by `Fin n` is the corresponding sum of
plane analytic germs. -/
theorem firstCoordinatePolynomialEvaluation_sum_fin
    {n : ℕ} (r : Fin n → Germ 1) :
    Germ.firstCoordinatePolynomialEvaluation
        (∑ i : Fin n, Polynomial.C (r i) *
          (Polynomial.X : Polynomial (Germ 1)) ^ i.1) =
      ∑ i : Fin n,
        Germ.coordinate (0 : Fin 2) ^ i.1 *
          Germ.hyperplaneExtension 1 (r i) := by
  rw [Germ.firstCoordinatePolynomialEvaluation]
  change Polynomial.eval₂ (Germ.hyperplaneExtension 1)
      (Germ.coordinate (0 : Fin 2))
      (∑ i ∈ Finset.univ, Polynomial.C (r i) *
        (Polynomial.X : Polynomial (Germ 1)) ^ i.1) = _
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  have hpow :
      Polynomial.eval₂ (Germ.hyperplaneExtension 1)
          (Germ.coordinate (0 : Fin 2))
            ((Polynomial.X : Polynomial (Germ 1)) ^ i.1) =
        Germ.coordinate (0 : Fin 2) ^ i.1 := by
    calc
      Polynomial.eval₂ (Germ.hyperplaneExtension 1)
          (Germ.coordinate (0 : Fin 2))
            ((Polynomial.X : Polynomial (Germ 1)) ^ i.1) =
          (Polynomial.eval₂ (Germ.hyperplaneExtension 1)
            (Germ.coordinate (0 : Fin 2))
              (Polynomial.X : Polynomial (Germ 1))) ^ i.1 :=
        map_pow
          (Polynomial.eval₂RingHom (Germ.hyperplaneExtension 1)
            (Germ.coordinate (0 : Fin 2)))
              (Polynomial.X : Polynomial (Germ 1)) i.1
      _ = Germ.coordinate (0 : Fin 2) ^ i.1 := by
        have hx :
            Polynomial.eval₂ (Germ.hyperplaneExtension 1)
                (Germ.coordinate (0 : Fin 2))
                (Polynomial.X : Polynomial (Germ 1)) =
              Germ.coordinate (0 : Fin 2) :=
          Polynomial.eval₂_X (Germ.hyperplaneExtension 1)
            (Germ.coordinate (0 : Fin 2))
        rw [hx]
  rw [hpow]
  exact mul_comm _ _

/-- The quotient and polynomial remainder in analytic division by a
distinguished Weierstrass polynomial are unique. -/
theorem distinguishedWeierstrass_division_unique
    {n : ℕ} {P R R' : Polynomial (Germ 1)} {q q' : Germ 2}
    (hPMonic : P.Monic)
    (hPDegree : P.natDegree = n)
    (hPCoeff : ∀ k, k < n →
      P.coeff k ∈ Germ.maximalIdeal 1)
    (hRDegree : R.degree < n)
    (hR'Degree : R'.degree < n)
    (heq :
      Germ.firstCoordinatePolynomialEvaluation P * q +
          Germ.firstCoordinatePolynomialEvaluation R =
        Germ.firstCoordinatePolynomialEvaluation P * q' +
          Germ.firstCoordinatePolynomialEvaluation R') :
    q = q' ∧ R = R' := by
  let Pformal : Polynomial (PowerSeries ℂ) :=
    P.map Germ.oneVariableTaylorRingHom
  have hPformalMonic : Pformal.Monic :=
    hPMonic.map Germ.oneVariableTaylorRingHom
  have hPformalDegree : Pformal.natDegree = n := by
    dsimp only [Pformal]
    rw [Polynomial.natDegree_map_eq_of_injective
      Germ.oneVariableTaylorRingHom_injective, hPDegree]
  have hPformalDistinguished :
      Pformal.IsDistinguishedAt
        (IsLocalRing.maximalIdeal (PowerSeries ℂ)) := by
    refine ⟨⟨?_⟩, hPformalMonic⟩
    intro k hk
    dsimp only [Pformal]
    rw [Polynomial.coeff_map]
    apply Germ.oneVariableTaylorRingHom_mem_maximalIdeal
    apply hPCoeff k
    simpa only [hPformalDegree] using hk
  have horder :
      ((Pformal : PowerSeries (PowerSeries ℂ)).map
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (PowerSeries ℂ)))).order.toNat = n := by
    have horder' :=
      hPformalDistinguished.coe_natDegree_eq_order_map
        (Pformal : PowerSeries (PowerSeries ℂ)) 1
        (by simp) (by simp)
    have horderToNat := congrArg ENat.toNat horder'
    simp only [ENat.toNat_natCast] at horderToNat
    exact horderToNat.symm.trans hPformalDegree
  have hformalEq := congrArg Germ.completedPlaneTaylorRingHom heq
  simp only [map_add, map_mul,
    Germ.completedPlaneTaylorRingHom_firstCoordinatePolynomialEvaluation]
      at hformalEq
  have hformalUnique :=
    hPformalDistinguished.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add
      (I := IsLocalRing.maximalIdeal (PowerSeries ℂ))
      (q := Germ.completedPlaneTaylorRingHom q)
      (q' := Germ.completedPlaneTaylorRingHom q')
      (r := R.map Germ.oneVariableTaylorRingHom)
      (r' := R'.map Germ.oneVariableTaylorRingHom)
      (by
        apply lt_of_le_of_lt Polynomial.degree_map_le
        simpa only [horder] using hRDegree)
      (by
        apply lt_of_le_of_lt Polynomial.degree_map_le
        simpa only [horder] using hR'Degree)
      hformalEq
  constructor
  · exact Germ.completedPlaneTaylorRingHom_injective hformalUnique.1
  · exact Polynomial.map_injective Germ.oneVariableTaylorRingHom
      Germ.oneVariableTaylorRingHom_injective hformalUnique.2

/-- A distinguished analytic Weierstrass quotient is the corresponding
polynomial quotient over the one variable germ ring. -/
@[expose] noncomputable def distinguishedWeierstrassQuotientRingEquiv
    (d : ℕ) (P : Polynomial (Germ 1))
    (hPMonic : P.Monic)
    (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 →
      P.coeff k ∈ Germ.maximalIdeal 1) :
    (Polynomial (Germ 1) ⧸ Ideal.span {P}) ≃+*
      (Germ 2 ⧸ Ideal.span
        {Germ.firstCoordinatePolynomialEvaluation P}) := by
  let eval : Polynomial (Germ 1) →+* Germ 2 :=
    Germ.firstCoordinatePolynomialEvaluationRingHom
  let J : Ideal (Polynomial (Germ 1)) := Ideal.span {P}
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  let K : Ideal (Germ 2) := Ideal.span {W}
  have hJK : J ≤ Ideal.comap eval K := by
    change Ideal.span {P} ≤ Ideal.comap eval (Ideal.span {W})
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change eval P ∈ K
    change W ∈ K
    exact Ideal.subset_span (Set.mem_singleton W)
  let F : (Polynomial (Germ 1) ⧸ J) →+* (Germ 2 ⧸ K) :=
    Ideal.quotientMap K eval hJK
  have hFInjective : Function.Injective F := by
    apply Ideal.quotientMap_injective'
    intro p hp
    change Germ.firstCoordinatePolynomialEvaluation p ∈
      Ideal.span {W} at hp
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, hq⟩ := hp
    let R : Polynomial (Germ 1) := p %ₘ P
    have hRDegree : R.degree < d + 1 := by
      apply lt_of_lt_of_eq (Polynomial.degree_modByMonic_lt p hPMonic)
      rw [Polynomial.degree_eq_natDegree hPMonic.ne_zero, hPDegree]
      norm_num
    have hdivision :
        Germ.firstCoordinatePolynomialEvaluation P *
              Germ.firstCoordinatePolynomialEvaluation (p /ₘ P) +
            Germ.firstCoordinatePolynomialEvaluation R =
          Germ.firstCoordinatePolynomialEvaluation P * q +
            Germ.firstCoordinatePolynomialEvaluation 0 := by
      change eval P * eval (p /ₘ P) + eval R = eval P * q + eval 0
      rw [map_zero, add_zero]
      calc
        eval P * eval (p /ₘ P) + eval R =
            eval (P * (p /ₘ P) + R) := by
          rw [map_add, map_mul]
        _ = eval p := by
          apply congrArg eval
          rw [add_comm, Polynomial.modByMonic_add_div]
        _ = eval P * q := by
          simpa only [eval, W,
            Germ.firstCoordinatePolynomialEvaluationRingHom_apply] using hq
    have hRZero :=
      (Germ.distinguishedWeierstrass_division_unique
        hPMonic hPDegree hPCoeff hRDegree (by simp) hdivision).2
    change p ∈ Ideal.span {P}
    rw [Ideal.mem_span_singleton,
      ← Polynomial.modByMonic_eq_zero_iff_dvd hPMonic]
    exact hRZero
  have hFSurjective : Function.Surjective F := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    let a : Fin (d + 1) → Germ 1 := fun i ↦ P.coeff i.1
    have ha : ∀ i, a i ∈ Germ.maximalIdeal 1 := by
      intro i
      exact hPCoeff i.1 i.2
    have hPGeneral : P = Germ.generalWeierstrassPolynomial d a :=
      Germ.eq_generalWeierstrassPolynomial_of_monic_natDegree
        d P hPMonic hPDegree
    obtain ⟨q, r, hdivision⟩ :=
      Germ.exists_generalWeierstrassDivision d a ha f
    let R : Polynomial (Germ 1) :=
      ∑ i : Fin (d + 1), Polynomial.C (r i) *
        (Polynomial.X : Polynomial (Germ 1)) ^ i.1
    refine ⟨Ideal.Quotient.mk J R, ?_⟩
    change Ideal.Quotient.mk K (eval R) = Ideal.Quotient.mk K f
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hREval :
        Germ.firstCoordinatePolynomialEvaluation R =
          ∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) := by
      exact Germ.firstCoordinatePolynomialEvaluation_sum_fin r
    have hWMem : W ∈ K :=
      Ideal.subset_span (Set.mem_singleton W)
    change Germ.firstCoordinatePolynomialEvaluation R - f ∈ K
    rw [hdivision, ← hPGeneral, ← hREval]
    have hproduct :
        Germ.firstCoordinatePolynomialEvaluation P * q ∈ K := by
      exact K.mul_mem_right q hWMem
    have hneg :
        -(Germ.firstCoordinatePolynomialEvaluation P * q) ∈ K :=
      K.neg_mem hproduct
    have heq : Germ.firstCoordinatePolynomialEvaluation R -
          (Germ.firstCoordinatePolynomialEvaluation P * q +
            Germ.firstCoordinatePolynomialEvaluation R) =
        -(Germ.firstCoordinatePolynomialEvaluation P * q) := by
      ring
    rwa [heq]
  exact RingEquiv.ofBijective F ⟨hFInjective, hFSurjective⟩

/-- A prime distinguished polynomial evaluates to a prime plane analytic
germ. -/
theorem prime_firstCoordinatePolynomialEvaluation_of_distinguished
    {d : ℕ} {P : Polynomial (Germ 1)}
    (hPPrime : Prime P)
    (hPMonic : P.Monic)
    (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 →
      P.coeff k ∈ Germ.maximalIdeal 1) :
    Prime (Germ.firstCoordinatePolynomialEvaluation P) := by
  let J : Ideal (Polynomial (Germ 1)) := Ideal.span {P}
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  let K : Ideal (Germ 2) := Ideal.span {W}
  have hJPrime : J.IsPrime := by
    change (Ideal.span {P}).IsPrime
    exact (Ideal.span_singleton_prime hPPrime.ne_zero).mpr hPPrime
  let _ : J.IsPrime := hJPrime
  let e : (Polynomial (Germ 1) ⧸ J) ≃+* (Germ 2 ⧸ K) :=
    Germ.distinguishedWeierstrassQuotientRingEquiv
      d P hPMonic hPDegree hPCoeff
  let _ : IsDomain (Polynomial (Germ 1) ⧸ J) :=
    Ideal.Quotient.isDomain J
  have hKDomain : IsDomain (Germ 2 ⧸ K) :=
    e.symm.injective.isDomain e.symm.toRingHom
  have hKPrime : K.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime K).mp hKDomain
  have hWNe : W ≠ 0 := by
    intro hW
    change Germ.firstCoordinatePolynomialEvaluation P = 0 at hW
    apply hPPrime.ne_zero
    apply Germ.firstCoordinatePolynomialEvaluation_injective
    change Germ.firstCoordinatePolynomialEvaluation P =
      Germ.firstCoordinatePolynomialEvaluation 0
    have hzero : Germ.firstCoordinatePolynomialEvaluation
        (0 : Polynomial (Germ 1)) = 0 := by
      rw [Germ.firstCoordinatePolynomialEvaluation]
      exact Polynomial.eval₂_zero _ _
    rw [hzero]
    exact hW
  exact (Ideal.span_singleton_prime hWNe).mp hKPrime

/-- A monic polynomial over a domain that divides a power of the polynomial
variable equals the power determined by its degree. -/
theorem monic_eq_X_pow_of_dvd_X_pow
    {R : Type*} [CommRing R] [IsDomain R]
    {Q : Polynomial R} {n : ℕ}
    (hQMonic : Q.Monic)
    (hQDiv : Q ∣ (Polynomial.X : Polynomial R) ^ n) :
    Q = Polynomial.X ^ Q.natDegree := by
  obtain ⟨S, hproduct⟩ := hQDiv
  have hQZero : Q ≠ 0 := hQMonic.ne_zero
  have hXZero : (Polynomial.X : Polynomial R) ^ n ≠ 0 := by
    exact pow_ne_zero n Polynomial.X_ne_zero
  have hSZero : S ≠ 0 := by
    intro hS
    apply hXZero
    rw [hproduct, hS, mul_zero]
  have hdegree := congrArg Polynomial.natDegree hproduct
  have htrailing := congrArg Polynomial.natTrailingDegree hproduct
  rw [Polynomial.natDegree_X_pow,
    Polynomial.natDegree_mul hQZero hSZero] at hdegree
  rw [Polynomial.natTrailingDegree_X_pow,
    Polynomial.natTrailingDegree_mul hQZero hSZero] at htrailing
  apply hQMonic.eq_X_pow_iff_natDegree_le_natTrailingDegree.mpr
  have hQBound := Polynomial.natTrailingDegree_le_natDegree Q
  have hSBound := Polynomial.natTrailingDegree_le_natDegree S
  omega

/-- A monic divisor of a distinguished polynomial over the one variable
germ ring is distinguished. -/
theorem monic_divisor_coeff_mem_maximalIdeal
    {d : ℕ} {P Q : Polynomial (Germ 1)}
    (hPMonic : P.Monic)
    (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 →
      P.coeff k ∈ Germ.maximalIdeal 1)
    (hQMonic : Q.Monic)
    (hQDiv : Q ∣ P) :
    ∀ k, k < Q.natDegree →
      Q.coeff k ∈ Germ.maximalIdeal 1 := by
  let residue := Ideal.Quotient.mk (Germ.maximalIdeal 1)
  let _ : (Germ.maximalIdeal 1).IsPrime :=
    (Germ.maximalIdeal_isMaximal 1).isPrime
  let _ : IsDomain (Germ 1 ⧸ Germ.maximalIdeal 1) :=
    Ideal.Quotient.isDomain (Germ.maximalIdeal 1)
  have hPDistinguished :
      P.IsDistinguishedAt (Germ.maximalIdeal 1) := by
    refine ⟨⟨?_⟩, hPMonic⟩
    intro k hk
    apply hPCoeff k
    simpa only [hPDegree] using hk
  have hQMapMonic : (Q.map residue).Monic := hQMonic.map residue
  have hQMapDiv : Q.map residue ∣
      (Polynomial.X : Polynomial (Germ 1 ⧸ Germ.maximalIdeal 1)) ^
        P.natDegree := by
    rw [← hPDistinguished.map_eq_X_pow]
    exact Polynomial.map_dvd residue hQDiv
  have hQMapEq : Q.map residue =
      (Polynomial.X : Polynomial (Germ 1 ⧸ Germ.maximalIdeal 1)) ^
        (Q.map residue).natDegree :=
    Germ.monic_eq_X_pow_of_dvd_X_pow hQMapMonic hQMapDiv
  intro k hk
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hcoeff := congrArg
    (fun T : Polynomial (Germ 1 ⧸ Germ.maximalIdeal 1) ↦ T.coeff k)
    hQMapEq
  have hQMapDegree : (Q.map residue).natDegree = Q.natDegree :=
    hQMonic.natDegree_map residue
  rw [hQMapDegree, Polynomial.coeff_X_pow,
    if_neg (ne_of_lt hk)] at hcoeff
  simpa only [residue, Polynomial.coeff_map] using hcoeff

/-- A prime ideal containing a distinguished Weierstrass polynomial
contains a prime plane analytic germ. -/
theorem exists_prime_mem_of_distinguishedWeierstrass_mem_prime
    (d : ℕ) (P : Polynomial (Germ 1))
    (hPMonic : P.Monic)
    (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 →
      P.coeff k ∈ Germ.maximalIdeal 1)
    (I : Ideal (Germ 2))
    (hIPrime : I.IsPrime)
    (hPI : Germ.firstCoordinatePolynomialEvaluation P ∈ I) :
    ∃ q ∈ I, Prime q := by
  let eval : Polynomial (Germ 1) →+* Germ 2 :=
    Germ.firstCoordinatePolynomialEvaluationRingHom
  let J : Ideal (Polynomial (Germ 1)) := Ideal.comap eval I
  have hJPrime : J.IsPrime := hIPrime.comap eval
  have hPJ : P ∈ J := by
    exact hPI
  have hfactorProduct :
      (UniqueFactorizationMonoid.factors P).prod ∈ J := by
    exact (Ideal.mem_iff_of_associated
      (UniqueFactorizationMonoid.factors_prod hPMonic.ne_zero)).mpr hPJ
  obtain ⟨p, hpFactor, hpJ⟩ :=
    (hJPrime.multiset_prod_mem_iff_exists_mem
      (UniqueFactorizationMonoid.factors P)).mp hfactorProduct
  have hpPrime : Prime p :=
    UniqueFactorizationMonoid.prime_of_factor p hpFactor
  have hpDiv : p ∣ P :=
    UniqueFactorizationMonoid.dvd_of_mem_factors hpFactor
  let hLeading : IsUnit p.leadingCoeff :=
    hPMonic.isUnit_leadingCoeff_of_dvd hpDiv
  let Q : Polynomial (Germ 1) := hLeading.unit⁻¹ • p
  have hQMonic : Q.Monic := by
    exact Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hLeading
  have hQAssociated : Associated Q p := by
    dsimp only [Q]
    rw [Units.smul_def, Polynomial.smul_eq_C_mul]
    exact associated_unit_mul_left p _
      (Polynomial.isUnit_C.mpr (Units.isUnit hLeading.unit⁻¹))
  have hQPrime : Prime Q := hQAssociated.symm.prime hpPrime
  have hQDiv : Q ∣ P :=
    hQAssociated.dvd_iff_dvd_left.mpr hpDiv
  have hQJ : Q ∈ J :=
    (Ideal.mem_iff_of_associated hQAssociated).mpr hpJ
  have hQDegreeNe : Q.natDegree ≠ 0 := by
    intro hdegree
    apply hQPrime.not_isUnit
    have hQOne := Polynomial.eq_one_of_monic_natDegree_zero
      hQMonic hdegree
    rw [hQOne]
    exact isUnit_one
  obtain ⟨e, hQDegree⟩ :=
    Nat.exists_eq_succ_of_ne_zero hQDegreeNe
  have hQCoeff : ∀ k, k < e + 1 →
      Q.coeff k ∈ Germ.maximalIdeal 1 := by
    intro k hk
    apply Germ.monic_divisor_coeff_mem_maximalIdeal
      hPMonic hPDegree hPCoeff hQMonic hQDiv k
    simpa only [hQDegree] using hk
  have hQEvaluationPrime :
      Prime (Germ.firstCoordinatePolynomialEvaluation Q) :=
    Germ.prime_firstCoordinatePolynomialEvaluation_of_distinguished
      hQPrime hQMonic hQDegree hQCoeff
  refine ⟨Germ.firstCoordinatePolynomialEvaluation Q, ?_,
    hQEvaluationPrime⟩
  exact hQJ

end Germ

end OnLeConjecture.Analytic
