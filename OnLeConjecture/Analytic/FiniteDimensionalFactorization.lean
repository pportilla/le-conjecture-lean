/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from lean-SCV (https://github.com/bjbraams/lean-SCV); see THIRD_PARTY_NOTICES.md.
Authors: Pablo Portilla Cuadrado, Bastiaan J Braams

The polynomial reconstruction and distinguished-divisor arguments adapt
Bastiaan J Braams's lean-SCV, commit 336759b39640, AnalyticGerm/Polynomial.lean
and Polynomial/OfFn.lean, released under Apache 2.0.
-/
module

public import OnLeConjecture.Analytic.FiniteDimensionalNoetherian
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# Unique factorization of finite-dimensional analytic germ rings

Unique Weierstrass division identifies a distinguished polynomial quotient
with its analytic quotient. Prime polynomials therefore give prime germs.
Coordinate regularization and Kaplansky's criterion prove unique
factorization by induction on the number of variables.
-/

@[expose] public noncomputable section

open scoped Polynomial Topology
open LocalComplexGeometry LocalComplexGeometry.WPTBridge ClassicalComplexWPT

namespace OnLeConjecture.Analytic.HolomorphicFactorization

local instance (n : ℕ) : IsDomain (HolomorphicGerm n) :=
  (holomorphicGermRingEquiv n).symm.injective.isDomain
    (holomorphicGermRingEquiv n).symm.toRingHom

/-- Polynomial evaluation in the last coordinate with analytic parameter coefficients. -/
def polynomialEvaluation (n : ℕ) : (HolomorphicGerm n)[X] →+* HolomorphicGerm (n + 1) :=
  Polynomial.eval₂RingHom (lowerDimensionalInclusion n) (lastCoordinateGerm n)

open Classical in
theorem polynomialEvaluation_ofFn {n d : ℕ} (r : Fin d → HolomorphicGerm n) :
    polynomialEvaluation n (Polynomial.ofFn d r) = remainderPolynomialGerm r := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [polynomialEvaluation, Polynomial.eval₂_monomial]

private theorem ofFn_toFn {R : Type*} [Semiring R] [DecidableEq R] {d : ℕ} {P : R[X]}
    (hP : P.degree < (d : WithBot ℕ)) :
    Polynomial.ofFn d (Polynomial.toFn d P) = P := by
  classical
  ext i
  by_cases hi : i < d
  · simp [hi, Polynomial.toFn]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
    exact (Polynomial.coeff_eq_zero_of_degree_lt
      (hP.trans_le (by exact_mod_cast Nat.le_of_not_gt hi))).symm

private theorem monic_shape {R : Type*} [Semiring R] [DecidableEq R] {P : R[X]} (hP : P.Monic) :
    P = Polynomial.X ^ P.natDegree +
      Polynomial.ofFn P.natDegree (Polynomial.toFn P.natDegree P) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.toFn, LinearMap.pi_apply, Polynomial.lcoeff_apply,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    Polynomial.C (P.coeff i) * Polynomial.X ^ i) P.natDegree]
  exact hP.as_sum

open Classical in
/-- Evaluation of the prepared polynomial agrees with the analytic prepared germ. -/
theorem polynomialEvaluation_prepared {n d : ℕ} (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    polynomialEvaluation n (Polynomial.X ^ d +
      Polynomial.ofFn d (fun i ↦ HolomorphicGerm.ofFunction (a i) (ha i))) =
        preparedPolynomialGerm a ha := by
  classical
  rw [map_add, map_pow, polynomialEvaluation_ofFn]
  rw [show polynomialEvaluation n Polynomial.X = lastCoordinateGerm n from
    Polynomial.eval₂_X _ _]
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_pow]
  rw [coe_remainderPolynomialGerm_ofFunction]
  change (lastCoordinateCLM n : FunctionGerm (n + 1)) ^ d + _ = _
  rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_add]
  rfl

/-- Coefficient representatives of a distinguished polynomial vanish at the origin. -/
private theorem exists_prepared_rep {n : ℕ} (P : (HolomorphicGerm n)[X])
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    ∃ (a : Fin P.natDegree → Base n → ℂ)
      (ha : ∀ i, AnalyticAt ℂ (a i) 0),
      (∀ i, a i 0 = 0) ∧
      polynomialEvaluation n P = preparedPolynomialGerm a ha := by
  classical
  choose a ha hrep using fun i : Fin P.natDegree ↦
    HolomorphicGerm.exists_rep (P.coeff i)
  have hg : ∀ i, HolomorphicGerm.ofFunction (a i) (ha i) = P.coeff i :=
    fun i ↦ Subtype.ext (hrep i)
  refine ⟨a, ha, ?_, ?_⟩
  · intro i
    have hm := hP.mem i.isLt
    rw [holomorphicGerm_maximalIdeal_eq_ker, RingHom.mem_ker] at hm
    simpa only [← hg i, evalAtOrigin_ofFunction] using hm
  · rw [← polynomialEvaluation_prepared a ha]
    congr 1
    trans Polynomial.X ^ P.natDegree +
      Polynomial.ofFn P.natDegree (Polynomial.toFn P.natDegree P)
    · exact monic_shape hP.monic
    congr 2
    funext i
    exact (hg i).symm

/-- Every germ has polynomial remainder of degree below a distinguished divisor. -/
theorem exists_division {n : ℕ} (P : (HolomorphicGerm n)[X])
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (h : HolomorphicGerm (n + 1)) :
    ∃ q R, R.degree < (P.natDegree : WithBot ℕ) ∧
      h = q * polynomialEvaluation n P + polynomialEvaluation n R := by
  classical
  obtain ⟨a, ha, ha0, heq⟩ := exists_prepared_rep P hP
  obtain ⟨q, r, hqr⟩ := exists_preparedGermDivision a ha ha0 h
  refine ⟨q, Polynomial.ofFn _ r, Polynomial.ofFn_degree_lt _, ?_⟩
  simpa only [heq, polynomialEvaluation_ofFn, IsPreparedGermDivision] using hqr

/-- Uniqueness of analytic division gives uniqueness of polynomial remainders. -/
theorem division_unique {n : ℕ} (P : (HolomorphicGerm n)[X])
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    {q q' : HolomorphicGerm (n + 1)} {R R' : (HolomorphicGerm n)[X]}
    (hR : R.degree < (P.natDegree : WithBot ℕ))
    (hR' : R'.degree < (P.natDegree : WithBot ℕ))
    (heq : q * polynomialEvaluation n P + polynomialEvaluation n R =
      q' * polynomialEvaluation n P + polynomialEvaluation n R') :
    q = q' ∧ R = R' := by
  classical
  obtain ⟨a, ha, ha0, hPval⟩ := exists_prepared_rep P hP
  have hRval : polynomialEvaluation n R =
      remainderPolynomialGerm (Polynomial.toFn P.natDegree R) := by
    rw [← polynomialEvaluation_ofFn]
    exact congrArg (polynomialEvaluation n) (ofFn_toFn hR).symm
  have hR'val : polynomialEvaluation n R' =
      remainderPolynomialGerm (Polynomial.toFn P.natDegree R') := by
    rw [← polynomialEvaluation_ofFn]
    exact congrArg (polynomialEvaluation n) (ofFn_toFn hR').symm
  have hu := preparedGermDivision_unique a ha ha0
    (q * polynomialEvaluation n P + polynomialEvaluation n R) q q'
    (Polynomial.toFn P.natDegree R) (Polynomial.toFn P.natDegree R')
    (by simp only [IsPreparedGermDivision, hPval, hRval])
    (by simpa only [IsPreparedGermDivision, hPval, hR'val] using heq)
  refine ⟨hu.1, ?_⟩
  rw [← ofFn_toFn hR, hu.2, ofFn_toFn hR']

/-- Evaluation of parameter-coefficient polynomials is injective. -/
theorem polynomialEvaluation_injective (n : ℕ) :
    Function.Injective (polynomialEvaluation n) := by
  have hker : ∀ P : (HolomorphicGerm n)[X], polynomialEvaluation n P = 0 → P = 0 := by
    intro P hP
    let W : (HolomorphicGerm n)[X] := Polynomial.X ^ (P.natDegree + 1)
    have hW : W.IsDistinguishedAt (IsLocalRing.maximalIdeal _) := by
      refine ⟨⟨?_⟩, Polynomial.monic_X_pow _⟩
      intro k hk
      simp only [W, Polynomial.natDegree_X_pow] at hk
      simp [W, Polynomial.coeff_X_pow, hk.ne]
    have hbound : P.degree < (W.natDegree : WithBot ℕ) := by
      simp only [W, Polynomial.natDegree_X_pow]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    have hu := division_unique W hW (q := 0) (q' := 0) (R := P) (R' := 0)
      hbound (by simp [W]) (by simp [hP])
    exact hu.2
  intro P Q h
  exact sub_eq_zero.mp (hker (P - Q) (by simp [h]))

/-- A distinguished analytic quotient equals its polynomial quotient. -/
def distinguishedQuotientEquiv {n : ℕ} (P : (HolomorphicGerm n)[X])
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    ((HolomorphicGerm n)[X] ⧸ Ideal.span {P}) ≃+*
      (HolomorphicGerm (n + 1) ⧸ Ideal.span {polynomialEvaluation n P}) := by
  let J : Ideal ((HolomorphicGerm n)[X]) := Ideal.span {P}
  let K : Ideal (HolomorphicGerm (n + 1)) := Ideal.span {polynomialEvaluation n P}
  have hJK : J ≤ Ideal.comap (polynomialEvaluation n) K := by
    rw [Ideal.span_le]
    rintro x (rfl : x = P)
    exact Ideal.subset_span (Set.mem_singleton _)
  let F := Ideal.quotientMap K (polynomialEvaluation n) hJK
  have hinj : Function.Injective F := by
    apply Ideal.quotientMap_injective'
    intro p hp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
    have hrem : (p %ₘ P).degree < (P.natDegree : WithBot ℕ) := by
      simpa only [Polynomial.degree_eq_natDegree hP.monic.ne_zero] using
        Polynomial.degree_modByMonic_lt p hP.monic
    have heq : polynomialEvaluation n (p /ₘ P) * polynomialEvaluation n P +
        polynomialEvaluation n (p %ₘ P) = q * polynomialEvaluation n P +
          polynomialEvaluation n 0 := by
      rw [map_zero, add_zero, ← map_mul, ← map_add]
      rw [mul_comm (p /ₘ P), add_comm (P * (p /ₘ P)), Polynomial.modByMonic_add_div]
      exact hq.trans (mul_comm _ _)
    have hz := (division_unique P hP hrem (by simp) heq).2
    exact Ideal.mem_span_singleton.mpr ((Polynomial.modByMonic_eq_zero_iff_dvd hP.monic).mp hz)
  have hsurj : Function.Surjective F := by
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, R, _, heq⟩ := exists_division P hP h
    refine ⟨Ideal.Quotient.mk J R, ?_⟩
    change Ideal.Quotient.mk K (polynomialEvaluation n R) = Ideal.Quotient.mk K h
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, heq]
    have hm : q * polynomialEvaluation n P ∈ K :=
      K.mul_mem_left q (Ideal.subset_span (Set.mem_singleton _))
    convert K.neg_mem hm using 1
    ring
  exact RingEquiv.ofBijective F ⟨hinj, hsurj⟩

/-- A prime distinguished polynomial evaluates to a prime analytic germ. -/
theorem prime_polynomialEvaluation {n : ℕ} {P : (HolomorphicGerm n)[X]}
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (hp : Prime P) :
    Prime (polynomialEvaluation n P) := by
  let J : Ideal ((HolomorphicGerm n)[X]) := Ideal.span {P}
  let K : Ideal (HolomorphicGerm (n + 1)) := Ideal.span {polynomialEvaluation n P}
  let : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let e := distinguishedQuotientEquiv P hP
  let : IsDomain (HolomorphicGerm (n + 1) ⧸ K) :=
    e.symm.injective.isDomain e.symm.toRingHom
  have hK := (Ideal.Quotient.isDomain_iff_prime K).mp inferInstance
  have hne : polynomialEvaluation n P ≠ 0 :=
    fun h ↦ hp.ne_zero (polynomialEvaluation_injective n (by simpa using h))
  exact (Ideal.span_singleton_prime hne).mp hK

/-- A monic divisor of a distinguished polynomial is distinguished. -/
theorem distinguished_of_monic_dvd {n : ℕ} {P Q : (HolomorphicGerm n)[X]}
    (hQ : Q.Monic) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (hdiv : Q ∣ P) : Q.IsDistinguishedAt (IsLocalRing.maximalIdeal _) := by
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolomorphicGerm n))
  have hd : Q.map π ∣ Polynomial.X ^ P.natDegree := by
    rw [← hP.map_eq_X_pow]
    exact Polynomial.map_dvd π hdiv
  obtain ⟨k, _, hk⟩ := (dvd_prime_pow Polynomial.prime_X P.natDegree).mp hd
  have he : Q.map π = Polynomial.X ^ k :=
    Polynomial.eq_of_monic_of_associated (hQ.map π) (Polynomial.monic_X_pow k) hk
  have hdeg : Q.natDegree = k := by
    simpa only [hQ.natDegree_map, Polynomial.natDegree_X_pow] using
      congrArg Polynomial.natDegree he
  refine ⟨⟨?_⟩, hQ⟩
  intro j hj
  have hc := congrArg (fun r ↦ Polynomial.coeff r j) he
  have hjk : j ≠ k := ne_of_lt (hdeg ▸ hj)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [Polynomial.coeff_map, Polynomial.coeff_X_pow, if_neg hjk] using hc

/-- A prime ideal containing a distinguished polynomial contains a prime germ. -/
theorem exists_prime_mem_of_distinguished {n : ℕ}
    [UniqueFactorizationMonoid (HolomorphicGerm n)]
    (P : (HolomorphicGerm n)[X])
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (I : Ideal (HolomorphicGerm (n + 1))) (hI : I.IsPrime)
    (hPI : polynomialEvaluation n P ∈ I) : ∃ q ∈ I, Prime q := by
  let J := I.comap (polynomialEvaluation n)
  have hJ : J.IsPrime := hI.comap _
  have hf : (UniqueFactorizationMonoid.factors P).prod ∈ J :=
    (Ideal.mem_iff_of_associated (UniqueFactorizationMonoid.factors_prod hP.monic.ne_zero)).mpr hPI
  obtain ⟨p, hp, hpJ⟩ := hJ.multiset_prod_mem_iff_exists_mem _ |>.mp hf
  have hprime := UniqueFactorizationMonoid.prime_of_factor p hp
  have hdiv := UniqueFactorizationMonoid.dvd_of_mem_factors hp
  let hu := hP.monic.isUnit_leadingCoeff_of_dvd hdiv
  let Q : (HolomorphicGerm n)[X] := hu.unit⁻¹ • p
  have hQ : Q.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu
  have hassoc : Associated Q p := by
    dsimp only [Q]
    rw [Units.smul_def, Polynomial.smul_eq_C_mul]
    exact associated_unit_mul_left p _
      (Polynomial.isUnit_C.mpr (Units.isUnit hu.unit⁻¹))
  have hQprime := hassoc.symm.prime hprime
  have hQdist := distinguished_of_monic_dvd hQ hP (hassoc.dvd_iff_dvd_left.mpr hdiv)
  exact ⟨polynomialEvaluation n Q, (Ideal.mem_iff_of_associated hassoc).mpr hpJ,
    prime_polynomialEvaluation hQdist hQprime⟩

open Classical in
/-- A polynomial made from vanishing coefficient germs is distinguished. -/
theorem prepared_distinguished {n d : ℕ} (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) :
    (Polynomial.X ^ d + Polynomial.ofFn d
      (fun i ↦ HolomorphicGerm.ofFunction (a i) (ha i))).IsDistinguishedAt
        (IsLocalRing.maximalIdeal (HolomorphicGerm n)) := by
  classical
  let r := fun i ↦ HolomorphicGerm.ofFunction (a i) (ha i)
  have hdeg : (Polynomial.X ^ d + Polynomial.ofFn d r).natDegree = d := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by
      rw [Polynomial.degree_X_pow]
      exact Polynomial.ofFn_degree_lt r), Polynomial.degree_X_pow]
  refine ⟨⟨?_⟩, Polynomial.monic_X_pow_add (Polynomial.ofFn_degree_lt r)⟩
  intro j hj
  change j < (Polynomial.X ^ d + Polynomial.ofFn d r).natDegree at hj
  rw [hdeg] at hj
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hj.ne, zero_add,
    Polynomial.ofFn_coeff_eq_val_of_lt _ hj,
    holomorphicGerm_maximalIdeal_eq_ker, RingHom.mem_ker]
  exact ha0 ⟨j, hj⟩

/-- The induction step for unique factorization, using analytic preparation. -/
theorem exists_prime_mem_of_nonzero_prime {n : ℕ}
    [UniqueFactorizationMonoid (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm (n + 1))) (hI0 : I ≠ ⊥) (hI : I.IsPrime) :
    ∃ p ∈ I, Prime p := by
  classical
  obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨L, d, H, a, u, _, hcoord, _, _, hprep⟩ :=
    exists_regularized_weierstrassPreparation hf0
  let e := coordinatePullback L
  let J := I.map e.toRingHom
  let P : (HolomorphicGerm n)[X] := Polynomial.X ^ d +
    Polynomial.ofFn d (fun i ↦ HolomorphicGerm.ofFunction (a i) (hprep.1 i))
  have hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal _) :=
    prepared_distinguished a hprep.1 hprep.2.1
  let : I.IsPrime := hI
  have hJ : J.IsPrime := by
    exact Ideal.map_isPrime_of_equiv e
  have hfJ : e f ∈ J := Ideal.mem_map_of_mem e.toRingHom hfI
  have hpJ : polynomialEvaluation n P ∈ J := by
    rw [polynomialEvaluation_prepared]
    exact (Ideal.mem_iff_of_associated
      (coordinatePullback_associated_preparedPolynomialGerm L H a u hcoord hprep)).mp hfJ
  obtain ⟨p, hpJ, hp⟩ := exists_prime_mem_of_distinguished P hP J hJ hpJ
  exact ⟨e.symm p, Ideal.symm_apply_mem_of_equiv_iff.mpr hpJ,
    (MulEquiv.prime_iff e.symm.toMulEquiv).mpr hp⟩

/-- Unique factorization of holomorphic germs in every finite dimension. -/
theorem uniqueFactorizationMonoid (n : ℕ) :
    UniqueFactorizationMonoid (HolomorphicGerm n) := by
  induction n with
  | zero =>
      exact holomorphicGermZeroEquiv.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  | succ n ih =>
      let := ih
      exact UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr
        exists_prime_mem_of_nonzero_prime

end OnLeConjecture.Analytic.HolomorphicFactorization

namespace OnLeConjecture.Analytic.Germ

/-- Analytic germs in any finite number of variables form a unique factorization domain. -/
theorem uniqueFactorizationMonoid_all (n : ℕ) : UniqueFactorizationMonoid (Germ n) :=
  (holomorphicGermRingEquiv n).symm.toMulEquiv.uniqueFactorizationMonoid
    (HolomorphicFactorization.uniqueFactorizationMonoid n)

/-- Irreducible analytic germs in any finite dimension are prime. -/
theorem prime_of_irreducible_all {n : ℕ} {f : Germ n} (hf : Irreducible f) : Prime f := by
  let := uniqueFactorizationMonoid_all n
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hf

end OnLeConjecture.Analytic.Germ
