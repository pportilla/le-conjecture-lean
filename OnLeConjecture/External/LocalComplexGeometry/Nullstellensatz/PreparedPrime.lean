/-
Vendored from BochaoKong/nullstellensatz, commit
029697242294aea7989bf5d391199696a43490df, retrieved 2026-10-29.
Original source: LocalComplexGeometry/Nullstellensatz/PreparedPrime.lean
https://github.com/BochaoKong/nullstellensatz/tree/029697242294aea7989bf5d391199696a43490df
Licensed under Apache 2.0. See the retained LICENSE in this source directory.
-/
module

public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.GenericFiber
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.DivisibilitySpecialization
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.DivisionRepresentatives
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.MinpolyResultant
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PolynomialFibers
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PolynomialRepresentativeOperations
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PrimeCancellation
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PrimeInduction
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PreparedRootLocality
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.ResultantSpecialization
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PolynomialSpecialization

@[expose] public section

open Filter
open scoped Topology

/-!
# The prepared-prime geometric step

This file joins the generic-fibre algebra to the local geometry of finite
prepared fibres.  The small certificate below deliberately records only the
finite pointwise information used by the geometric argument.  Its fields are
later furnished by denominator-cleared minimal-polynomial identities.
-/

namespace LocalComplexGeometry

noncomputable section

/-- Chosen representatives respect a finite product after one common
shrinking. -/
theorem eventually_representative_finsetProd {n : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (∏ i ∈ S, f i) z =
        ∏ i ∈ S, HolomorphicGerm.representative (f i) z := by
  apply Filter.Germ.coe_eq.mp
  calc
    (HolomorphicGerm.representative (∏ i ∈ S, f i) : FunctionGerm n) =
        ((∏ i ∈ S, f i : HolomorphicGerm n) : FunctionGerm n) :=
      HolomorphicGerm.coe_representative (∏ i ∈ S, f i)
    _ = ∏ i ∈ S, (f i : FunctionGerm n) := by
      exact map_prod (holomorphicGermSubring n).subtype f S
    _ = ∏ i ∈ S,
        (HolomorphicGerm.representative (f i) : FunctionGerm n) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (HolomorphicGerm.coe_representative (f i)).symm
    _ = (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
          (∏ i ∈ S, HolomorphicGerm.representative (f i)) := by
      exact (map_prod
        (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (fun i ↦ HolomorphicGerm.representative (f i)) S).symm
    _ = ((fun z ↦ ∏ i ∈ S,
        HolomorphicGerm.representative (f i) z) : FunctionGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun _ ↦ by simp)

/-- Binary form of representative multiplication. -/
theorem eventually_representative_mul {n : ℕ}
    (f g : HolomorphicGerm n) :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (f * g) z =
        HolomorphicGerm.representative f z *
          HolomorphicGerm.representative g z := by
  apply Filter.Germ.coe_eq.mp
  calc
    (HolomorphicGerm.representative (f * g) : FunctionGerm n) =
        (f * g : FunctionGerm n) :=
      HolomorphicGerm.coe_representative (f * g)
    _ = (f : FunctionGerm n) * (g : FunctionGerm n) := rfl
    _ = (HolomorphicGerm.representative f : FunctionGerm n) *
        (HolomorphicGerm.representative g : FunctionGerm n) := by
      rw [HolomorphicGerm.coe_representative,
        HolomorphicGerm.coe_representative]
    _ = (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (HolomorphicGerm.representative f *
          HolomorphicGerm.representative g) := by
      exact (map_mul
        (Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n)))
        (HolomorphicGerm.representative f)
        (HolomorphicGerm.representative g)).symm
    _ = ((fun z ↦ HolomorphicGerm.representative f z *
        HolomorphicGerm.representative g z) : FunctionGerm n) := rfl

/-- Finite pointwise data extracted from the denominator-cleared generic
minimal polynomial for one target germ.  The final field is the purely
algebraic return path: once all coefficients of the small remainder lie in
the contraction, generic divisibility puts the target back in the ambient
prime. -/
structure PreparedPrimeFiberCertificate {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (P : Ideal (HolomorphicGerm (n + 1)))
    (g : HolomorphicGerm (n + 1)) where
  e : ℕ
  positiveDegree : 0 < e
  q : Fin (e + 1) → HolomorphicGerm n
  b : Fin e → HolomorphicGerm n
  bad : HolomorphicGerm n
  bad_not_mem : bad ∉ lowerDimensionalContraction P
  eventually_specializes :
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      (∀ f : idealGeneratorFinset (lowerDimensionalContraction P),
          HolomorphicGerm.representative (f : HolomorphicGerm n) z = 0) →
      HolomorphicGerm.representative bad z ≠ 0 →
      let Qz := fixedDegreePolynomialAt
        (HolomorphicGerm.coefficientRepresentatives q) z
      Qz.natDegree = e ∧ Qz.Separable ∧
        ∀ w : ℂ, Qz.eval w = 0 →
          preparedValue a z w = 0 ∧
          (∀ f : idealGeneratorFinset P,
              HolomorphicGerm.representative
                (f : HolomorphicGerm (n + 1))
                (appendLastCLE n (z, w)) = 0) ∧
          (HolomorphicGerm.representative g
                (appendLastCLE n (z, w)) = 0 →
            (remainderPolynomialAt
              (HolomorphicGerm.coefficientRepresentatives b) z).eval w = 0)
  mem_of_coeff_mem :
    (∀ i, b i ∈ lowerDimensionalContraction P) → g ∈ P

/-- The geometric heart of the prepared-prime argument.  A finite-fibre
certificate turns vanishing on the ambient prime zero set into membership in
the prime, using the lower-dimensional prime theorem and cancellation of one
common bad factor. -/
theorem mem_prime_of_preparedPrimeFiberCertificate {n d : ℕ}
    (hprime : PrimeZeroSetProperty n)
    (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1))) (hP : P.IsPrime)
    (g : HolomorphicGerm (n + 1))
    (hg : g ∈ vanishingIdeal (idealZeroSetGerm P))
    (C : PreparedPrimeFiberCertificate a P g) :
    g ∈ P := by
  let P₀ : Ideal (HolomorphicGerm n) := lowerDimensionalContraction P
  have hP₀ : P₀.IsPrime := lowerDimensionalContraction_isPrime hP
  let S₀ := idealGeneratorFinset P₀
  let S := idealGeneratorFinset P
  let F₀ : S₀ → ComplexEuclidean n → ℂ :=
    fun f ↦ HolomorphicGerm.representative (f : HolomorphicGerm n)
  let F : S → ComplexEuclidean (n + 1) → ℂ :=
    fun f ↦ HolomorphicGerm.representative
      (f : HolomorphicGerm (n + 1))
  let G : ComplexEuclidean (n + 1) → ℂ :=
    HolomorphicGerm.representative g
  have hF₀ : ∀ f, AnalyticAt ℂ (F₀ f) 0 := by
    intro f
    exact HolomorphicGerm.analyticAt_representative (f : HolomorphicGerm n)
  have hF : ∀ f, AnalyticAt ℂ (F f) 0 := by
    intro f
    exact HolomorphicGerm.analyticAt_representative
      (f : HolomorphicGerm (n + 1))
  have hG : AnalyticAt ℂ G 0 :=
    HolomorphicGerm.analyticAt_representative g
  have hzeroG : ∀ᶠ x in nhds (0 : ComplexEuclidean (n + 1)),
      (∀ f, F f x = 0) → G x = 0 := by
    have hZG : idealZeroSetGerm P ≤ germZeroLocus g := hg
    rw [idealZeroSetGerm_eq_of_span_eq P S
      (by simpa only [S] using span_idealGeneratorFinset P)] at hZG
    rw [finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype] at hZG
    have hfamily :
        (fun f ↦ HolomorphicGerm.ofFunction (F f) (hF f)) =
          (fun f : S ↦ (f : HolomorphicGerm (n + 1))) := by
      funext f
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative
        (f : HolomorphicGerm (n + 1))
    have hgerm : HolomorphicGerm.ofFunction G hG = g := by
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative g
    have hZG' :
        fintypeCommonZeroSet
            (fun f ↦ HolomorphicGerm.ofFunction (F f) (hF f)) ≤
          germZeroLocus (HolomorphicGerm.ofFunction G hG) := by
      rw [hfamily, hgerm]
      exact hZG
    exact (fintypeCommonZeroSet_le_iff_eventually F hF G hG).mp hZG'
  have hzeroGOnRoots :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ w : ℂ,
        preparedValue a z w = 0 →
          ((∀ f, F f (appendLastCLE n (z, w)) = 0) →
            G (appendLastCLE n (z, w)) = 0) :=
    eventually_on_all_prepared_roots hd a ha ha0 hzeroG
  have hcoeff (i : Fin C.e) : C.b i ∈ P₀ := by
    apply mem_prime_of_mul_vanishes_on_zeroSet hprime P₀ hP₀
      C.bad_not_mem
    let Bfun : ComplexEuclidean n → ℂ :=
      HolomorphicGerm.representative (C.b i)
    let Dfun : ComplexEuclidean n → ℂ :=
      HolomorphicGerm.representative C.bad
    have hBfun : AnalyticAt ℂ Bfun 0 :=
      HolomorphicGerm.analyticAt_representative (C.b i)
    have hDfun : AnalyticAt ℂ Dfun 0 :=
      HolomorphicGerm.analyticAt_representative C.bad
    have hDBfun : AnalyticAt ℂ (Dfun * Bfun) 0 := hDfun.mul hBfun
    have hprod : HolomorphicGerm.ofFunction (Dfun * Bfun) hDBfun =
        C.bad * C.b i := by
      apply Subtype.ext
      change ((Dfun * Bfun : ComplexEuclidean n → ℂ) : FunctionGerm n) =
        (C.bad : FunctionGerm n) * (C.b i : FunctionGerm n)
      rw [Filter.Germ.coe_mul,
        HolomorphicGerm.coe_representative,
        HolomorphicGerm.coe_representative]
    rw [← hprod]
    rw [idealZeroSetGerm_eq_of_span_eq P₀ S₀
      (by simpa only [S₀] using span_idealGeneratorFinset P₀)]
    rw [finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype]
    have hfamily :
        (fun f ↦ HolomorphicGerm.ofFunction (F₀ f) (hF₀ f)) =
          (fun f : S₀ ↦ (f : HolomorphicGerm n)) := by
      funext f
      apply Subtype.ext
      exact HolomorphicGerm.coe_representative (f : HolomorphicGerm n)
    rw [← hfamily]
    apply (fintypeCommonZeroSet_le_iff_eventually F₀ hF₀
      (Dfun * Bfun) hDBfun).mpr
    filter_upwards [C.eventually_specializes, hzeroGOnRoots] with z hspec hzG
    intro hz₀
    by_cases hDz : Dfun z = 0
    · simp [hDz]
    · have hdata := hspec (by simpa only [F₀, S₀, P₀] using hz₀)
          (by simpa only [Dfun] using hDz)
      dsimp only at hdata
      obtain ⟨hdegree, hsep, hroots⟩ := hdata
      have hQne : fixedDegreePolynomialAt
          (HolomorphicGerm.coefficientRepresentatives C.q) z ≠ 0 := by
        intro hQzero
        rw [hQzero, Polynomial.natDegree_zero] at hdegree
        exact (Nat.ne_of_gt C.positiveDegree) hdegree.symm
      have hBzero : remainderPolynomialAt
          (HolomorphicGerm.coefficientRepresentatives C.b) z = 0 := by
        apply polynomial_eq_zero_of_natDegree_lt_of_vanishes_on_separableRoots
          hQne hsep
        · rw [hdegree]
          exact remainderPolynomialAt_natDegree_lt C.positiveDegree _ z
        · intro w hw
          obtain ⟨hprepared, hgens, htarget⟩ := hroots w hw
          apply htarget
          apply hzG w hprepared
          simpa only [F, S] using hgens
      have hbiz : Bfun z = 0 := by
        simpa only [Bfun, HolomorphicGerm.coefficientRepresentatives] using
          remainderPolynomialAt_coeff_eq_zero
            (HolomorphicGerm.coefficientRepresentatives C.b) z hBzero i
      simp [hbiz]
  exact C.mem_of_coeff_mem fun i ↦ by
    simpa only [P₀] using hcoeff i

def preparedPrimeFiberCertificate_of_genericMinpoly {n d : ℕ}
    (hd : 0 < d)
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1))) (hP : P.IsPrime)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (g : HolomorphicGerm (n + 1)) :
    PreparedPrimeFiberCertificate a P g := by
  classical
  letI : P.IsPrime := hP
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let Q : Polynomial (HolomorphicGerm n) := c.polynomial
  let e : ℕ := Q.natDegree
  let S := IdealGeneratorIndex P
  have hgenerator (f : S) : (f : HolomorphicGerm (n + 1)) ∈ P :=
    idealGenerator_mem P f
  let R : Option S → Polynomial (HolomorphicGerm n)
    | none => preparedGermPolynomial a ha
    | some f => remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0
          (f : HolomorphicGerm (n + 1)))
  let Cdiv : ∀ i : Option S,
      GenericMinpolyDivisibilityLiftCertificate P Q (R i) := fun i ↦ by
    cases i with
    | none =>
        simpa only [Q, c, R] using
          preparedPolynomialMinpolyDivisibilityLiftCertificate
            P a ha ha0 hmem
    | some f =>
        simpa only [Q, c, R] using
          primeMemberRemainderMinpolyDivisibilityLiftCertificate
            P a ha ha0 hmem (f : HolomorphicGerm (n + 1)) (hgenerator f)
  let Ccommon :=
    commonGenericMinpolyDivisibilityLiftCertificate P Q R Cdiv
  let Cspec (i : Option S) :
      GenericMinpolyDivisibilityLiftCertificate P Q (R i) :=
    { denominator := Ccommon.denominator
      quotient := Ccommon.quotient i
      error := Ccommon.error i
      denominator_not_mem := Ccommon.denominator_not_mem
      identity := Ccommon.identity i
      error_coeff_mem := Ccommon.error_coeff_mem i }
  let Ctarget := ambientGermRemainderModMinpolyLiftCertificate
    P a ha ha0 hmem g
  let baseBad := genericMinpolyLiftSpecializationBadFactor
    P a ha ha0 hmem
  let bad : HolomorphicGerm n := baseBad * Ccommon.denominator
  let Δ : HolomorphicGerm n :=
    Polynomial.resultant Q Q.derivative e (e - 1)
  have hQdegree : Q.natDegree ≤ e := by exact le_rfl
  have hpreparedDegree : (preparedGermPolynomial a ha).natDegree ≤ d := by
    rw [preparedGermPolynomial_natDegree]
  have hremainderDegree (h : HolomorphicGerm (n + 1)) :
      (remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0 h)).natDegree ≤ d :=
    remainderGermPolynomial_natDegree_le _
  have hbadRepresentative := eventually_representative_mul
    baseBad Ccommon.denominator
  have hbaseBadRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        HolomorphicGerm.representative baseBad z =
          HolomorphicGerm.representative Q.leadingCoeff z *
            HolomorphicGerm.representative Δ z := by
    simpa only [baseBad, genericMinpolyLiftSpecializationBadFactor,
      c, Q, e, Δ] using eventually_representative_mul Q.leadingCoeff Δ
  have hdegreeSeparable :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        HolomorphicGerm.representative Q.leadingCoeff z ≠ 0 →
        HolomorphicGerm.representative Δ z ≠ 0 →
          (germPolynomialRepresentativeAt e Q z).natDegree = e ∧
            (germPolynomialRepresentativeAt e Q z).Separable := by
    simpa only [c, Q, e, Δ] using
      eventually_genericMinpolyLift_natDegree_eq_and_separable
        P a ha ha0 hmem
  have hpreparedDivides :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        HolomorphicGerm.representative Ccommon.denominator z ≠ 0 →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (germPolynomialRepresentativeAt d
            (preparedGermPolynomial a ha) z).eval w = 0 := by
    simpa only [Cspec, R] using
      eventually_eval_eq_zero_of_genericMinpolyDivisibilityLiftCertificate
        P (Cspec none) hQdegree hpreparedDegree
  have hpreparedRepresentative :=
    eventually_germPolynomialRepresentativeAt_preparedGermPolynomial a ha
  have hgeneratorDivides :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S,
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        HolomorphicGerm.representative Ccommon.denominator z ≠ 0 →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z).eval w = 0 := by
    apply Filter.eventually_all.mpr
    intro f
    simpa only [Cspec, R] using
      eventually_eval_eq_zero_of_genericMinpolyDivisibilityLiftCertificate
        P (Cspec (some f)) hQdegree
          (hremainderDegree (f : HolomorphicGerm (n + 1)))
  have hgeneratorPolynomialRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S,
        germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z =
          remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z := by
    apply Filter.eventually_all.mpr
    intro f
    exact eventually_germPolynomialRepresentativeAt_remainderGermPolynomial _
  have hgeneratorAmbientRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S, ∀ w : ℂ,
        preparedValue a z w = 0 →
          HolomorphicGerm.representative
              (f : HolomorphicGerm (n + 1)) (appendLastCLE n (z, w)) =
            ∑ i : Fin d,
              HolomorphicGerm.representative
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0
                    (f : HolomorphicGerm (n + 1)) i) z *
                w ^ (i : ℕ) := by
    apply Filter.eventually_all.mpr
    intro f
    exact eventually_representative_eq_remainder_on_preparedRoots
      hd a ha ha0 (f : HolomorphicGerm (n + 1))
  have htargetRemainderIdentity :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (remainderPolynomialAt
              (HolomorphicGerm.coefficientRepresentatives
                Ctarget.coefficients) z).eval w =
            HolomorphicGerm.representative Ctarget.denominator z *
              (germPolynomialRepresentativeAt d
                (remainderGermPolynomial
                  (WPTBridge.preparedGermDivisionRemainder
                    a ha ha0 g)) z).eval w := by
    simpa only [Ctarget, c, Q] using
      eventually_remainder_eval_eq_denominator_mul_of_genericRemainderModMinpolyLiftCertificate
        P Ctarget hQdegree (hremainderDegree g)
  have htargetPolynomialRepresentative :=
    eventually_germPolynomialRepresentativeAt_remainderGermPolynomial
      (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)
  have htargetAmbientRepresentative :=
    eventually_representative_eq_remainder_on_preparedRoots
      hd a ha ha0 g
  refine
    { e := e
      positiveDegree := ?_
      q := fun i ↦ Q.coeff (i : ℕ)
      b := Ctarget.coefficients
      bad := bad
      bad_not_mem := ?_
      eventually_specializes := ?_
      mem_of_coeff_mem := ?_ }
  · simpa only [e, Q, c] using c.natDegree_pos
  · have hbase : baseBad ∉ lowerDimensionalContraction P := by
      simpa only [baseBad] using
        genericMinpolyLiftSpecializationBadFactor_not_mem P a ha ha0 hmem
    have hcommon : Ccommon.denominator ∉ lowerDimensionalContraction P :=
      Ccommon.denominator_not_mem
    intro hbad
    exact (lowerDimensionalContraction_isPrime hP).mul_mem_iff_mem_or_mem.mp hbad
      |>.elim hbase hcommon
  · filter_upwards [hbadRepresentative, hbaseBadRepresentative,
      hdegreeSeparable, hpreparedDivides, hpreparedRepresentative,
      hgeneratorDivides, hgeneratorPolynomialRepresentative,
      hgeneratorAmbientRepresentative, htargetRemainderIdentity,
      htargetPolynomialRepresentative, htargetAmbientRepresentative]
      with z hbadz hbasez hsepz hpreparedz hpreparedRepz hgeneratorz
        hgeneratorRepz hgeneratorAmbientz htargetz htargetRepz
        htargetAmbientz
    intro hZ hbadNonzero
    change
      (germPolynomialRepresentativeAt e Q z).natDegree = e ∧
        (germPolynomialRepresentativeAt e Q z).Separable ∧
          ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
            preparedValue a z w = 0 ∧
              (∀ f : idealGeneratorFinset P,
                HolomorphicGerm.representative
                    (f : HolomorphicGerm (n + 1))
                    (appendLastCLE n (z, w)) = 0) ∧
              (HolomorphicGerm.representative g
                    (appendLastCLE n (z, w)) = 0 →
                (remainderPolynomialAt
                  (HolomorphicGerm.coefficientRepresentatives
                    Ctarget.coefficients) z).eval w = 0)
    have hfactorNonzero :
        HolomorphicGerm.representative baseBad z ≠ 0 ∧
          HolomorphicGerm.representative Ccommon.denominator z ≠ 0 := by
      apply mul_ne_zero_iff.mp
      rw [← hbadz]
      exact hbadNonzero
    have hleadingNonzero :
        HolomorphicGerm.representative Q.leadingCoeff z ≠ 0 := by
      intro hzero
      apply hfactorNonzero.1
      rw [hbasez, hzero, zero_mul]
    have hresultantNonzero : HolomorphicGerm.representative Δ z ≠ 0 := by
      intro hzero
      apply hfactorNonzero.1
      rw [hbasez, hzero, mul_zero]
    obtain ⟨hdegree, hseparable⟩ := hsepz hleadingNonzero hresultantNonzero
    refine ⟨hdegree, hseparable, ?_⟩
    intro w hQroot
    have hZ' : idealGeneratorZeroPredicate
        (lowerDimensionalContraction P) z := by
      simpa only [idealGeneratorZeroPredicate, idealGeneratorRepresentatives]
        using hZ
    have hpreparedRepRoot := hpreparedz hZ' hfactorNonzero.2 w hQroot
    have hpreparedPolynomialRoot : (preparedPolynomialAt a z).eval w = 0 := by
      rw [← hpreparedRepz]
      exact hpreparedRepRoot
    have hpreparedRoot : preparedValue a z w = 0 := by
      rwa [preparedPolynomialAt_eval] at hpreparedPolynomialRoot
    refine ⟨hpreparedRoot, ?_, ?_⟩
    · intro f
      have hremainderRepRoot := hgeneratorz f hZ' hfactorNonzero.2 w hQroot
      have hremainderRoot :
          (remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z).eval w = 0 := by
        rw [← hgeneratorRepz f]
        exact hremainderRepRoot
      calc
        HolomorphicGerm.representative (f : HolomorphicGerm (n + 1))
            (appendLastCLE n (z, w)) =
            ∑ i : Fin d,
              HolomorphicGerm.representative
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0
                    (f : HolomorphicGerm (n + 1)) i) z *
                w ^ (i : ℕ) := hgeneratorAmbientz f w hpreparedRoot
        _ = 0 := by
          simpa only [remainderPolynomialAt_eval,
            HolomorphicGerm.coefficientRepresentatives] using hremainderRoot
    · intro hgzero
      have htargetDisplayedRoot :
          (remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)) z).eval w =
              0 := by
        rw [remainderPolynomialAt_eval]
        calc
          ∑ i : Fin d,
              HolomorphicGerm.coefficientRepresentatives
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0 g) i z *
                w ^ (i : ℕ) =
              HolomorphicGerm.representative g
                (appendLastCLE n (z, w)) := by
                  simpa only [HolomorphicGerm.coefficientRepresentatives] using
                    (htargetAmbientz w hpreparedRoot).symm
          _ = 0 := hgzero
      have htargetGermRoot :
          (germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)) z).eval w =
              0 := by
        rw [htargetRepz]
        exact htargetDisplayedRoot
      rw [htargetz hZ' w hQroot, htargetGermRoot, mul_zero]
  · simpa only [Ctarget] using
      ambientGermRemainderModMinpolyLiftCertificate_mem_of_coeff_mem
        P a ha ha0 hmem g

/-- The lower-dimensional prime theorem supplies the geometric cancellation
step needed to close the prepared successor case. -/
theorem preparedPrimeZeroSetStep_of_primeZeroSetProperty {n : ℕ}
    (hprime : PrimeZeroSetProperty n) : PreparedPrimeZeroSetStep n := by
  intro d hd a ha ha0 P hP hmem
  apply le_antisymm
  · intro g hg
    exact mem_prime_of_preparedPrimeFiberCertificate
      hprime hd a ha ha0 P hP g hg
        (preparedPrimeFiberCertificate_of_genericMinpoly
          hd a ha ha0 P hP hmem g)
  · intro g hg
    exact idealZeroSetGerm_le_germZeroLocus_of_mem P hg

/-- The prepared-prime construction closes the prime zero-set theorem in
every dimension by induction. -/
theorem primeZeroSetProperty_all : ∀ n : ℕ, PrimeZeroSetProperty n
  | 0 => primeZeroSetProperty_zero
  | n + 1 =>
      primeZeroSetProperty_succ_of_preparedPrimeZeroSetStep
        (preparedPrimeZeroSetStep_of_primeZeroSetProperty
          (primeZeroSetProperty_all n))

end

end LocalComplexGeometry
