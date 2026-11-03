/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.KnotFloer.SpectralDualCertificate

/-!
# Laurent-linear extensions of degree-zero dual certificates

A functional on Maslov degree zero extends to a Laurent-linear functional by
normalizing even degrees with powers of U and sending odd degrees to zero.
The filtration shift is measured using the Laurent monomial coordinate −j.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) {K : Type*} [Field K]

def dualAmbientExtension (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K) :
    LaurentChain K n →ₗ[K] K := Classical.choose ℓ.exists_extend

theorem dualAmbientExtension_apply (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (c : laurentMaslovPiece G K 0) : dualAmbientExtension G ℓ c = ℓ c := by
  have h := Classical.choose_spec ℓ.exists_extend
  exact LinearMap.congr_fun h c

/-- Normalize a basis state's even Maslov degree to zero. Odd states contribute zero. -/
def laurentDualBasisValue (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (x : GridState n) : LaurentPolynomial K :=
  if Even (G.maslovOℤ x) then
    LaurentPolynomial.C (dualAmbientExtension G ℓ
      (laurentMonomialGenerator K (G.maslovOℤ x / 2) x)) *
        LaurentPolynomial.T (-(G.maslovOℤ x / 2))
  else 0

/-- The Laurent-linear extension of a functional on Maslov degree zero. -/
def laurentDualExtension (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K) :
    LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K :=
  Finsupp.lsum (LaurentPolynomial K) fun x =>
    (LinearMap.id : LaurentPolynomial K →ₗ[LaurentPolynomial K] LaurentPolynomial K).smulRight
      (laurentDualBasisValue G ℓ x)

@[simp]
theorem laurentDualExtension_single (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (x : GridState n) (p : LaurentPolynomial K) :
    laurentDualExtension G ℓ (Finsupp.single x p) = p * laurentDualBasisValue G ℓ x := by
  simp [laurentDualExtension]

/-- Multiplication by every positive or negative power of U commutes with the extension. -/
theorem laurentDualExtension_T_smul (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (j : ℤ) (c : LaurentChain K n) :
    laurentDualExtension G ℓ ((LaurentPolynomial.T j : LaurentPolynomial K) • c) =
      LaurentPolynomial.T j * laurentDualExtension G ℓ c :=
  (laurentDualExtension G ℓ).map_smul _ _

private theorem chain_mem_of_monomials (S : Submodule K (LaurentChain K n))
    (c : LaurentChain K n)
    (hc : ∀ x j, j ∈ (c x).coeff.support → laurentMonomialGenerator K j x ∈ S) :
    c ∈ S := by
  classical
  have hexp : c = ∑ x ∈ c.support, ∑ j ∈ (c x).coeff.support,
      (c x).coeff j • laurentMonomialGenerator K j x := by
    conv_lhs => rw [← c.sum_single]
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro x hx
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (c x), Finsupp.sum]
    rw [Finsupp.single_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [laurentMonomialGenerator, LaurentPolynomial.T, Finsupp.smul_single,
      AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hexp]
  exact S.sum_mem fun x _ => S.sum_mem fun j hj => S.smul_mem _ (hc x j hj)

private theorem T_smul_monomial (j k : ℤ) (x : GridState n) :
    (LaurentPolynomial.T j : LaurentPolynomial K) • laurentMonomialGenerator K k x =
      laurentMonomialGenerator K (j + k) x := by
  simp only [laurentMonomialGenerator, Finsupp.smul_single, smul_eq_mul,
    ← LaurentPolynomial.T_add]

private def normalizedDualMap (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K) (k : ℤ) :
    LaurentChain K n →ₗ[K] LaurentPolynomial K where
  toFun c := LaurentPolynomial.C (dualAmbientExtension G ℓ
    ((LaurentPolynomial.T k : LaurentPolynomial K) • c)) *
    LaurentPolynomial.T (-k)
  map_add' c d := by simp [smul_add, add_mul]
  map_smul' a c := by
    rw [smul_comm (LaurentPolynomial.T k : LaurentPolynomial K) a, map_smul]
    simp [Algebra.smul_def, mul_assoc]

private theorem laurentDualExtension_even_ambient
    (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K) (k : ℤ)
    {c : LaurentChain K n} (hc : c ∈ laurentMaslovPiece G K (2 * k)) :
    laurentDualExtension G ℓ c = normalizedDualMap G ℓ k c := by
  apply chain_mem_of_monomials
    (LinearMap.eqLocus ((laurentDualExtension G ℓ).restrictScalars K)
      (normalizedDualMap G ℓ k)) c
  intro x j hj
  have hdeg := hc x j hj
  change G.maslovOℤ x - 2 * j = 2 * k at hdeg
  have heven : Even (G.maslovOℤ x) := ⟨j + k, by omega⟩
  have hhalf : G.maslovOℤ x / 2 = j + k := by omega
  change laurentDualExtension G ℓ (laurentMonomialGenerator K j x) = _
  rw [laurentMonomialGenerator, laurentDualExtension_single]
  simp only [laurentDualBasisValue, if_pos heven, hhalf]
  change LaurentPolynomial.T j *
    (LaurentPolynomial.C _ * LaurentPolynomial.T (-(j + k))) =
      LaurentPolynomial.C (dualAmbientExtension G ℓ
        ((LaurentPolynomial.T k : LaurentPolynomial K) • laurentMonomialGenerator K j x)) *
          LaurentPolynomial.T (-k)
  rw [T_smul_monomial]
  rw [add_comm k j]
  rw [mul_left_comm, ← LaurentPolynomial.T_add]
  congr 2
  omega

/-- On degree 2k, the extension is U⁻ᵏ times the value of the normalized chain. -/
theorem laurentDualExtension_even (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (k : ℤ) (c : LaurentChain K n) (hc : c ∈ laurentMaslovPiece G K (2 * k)) :
    ∃ hzero : (LaurentPolynomial.T k : LaurentPolynomial K) • c ∈ laurentMaslovPiece G K 0,
      laurentDualExtension G ℓ c =
        LaurentPolynomial.C (ℓ ⟨(LaurentPolynomial.T k : LaurentPolynomial K) • c, hzero⟩) *
          LaurentPolynomial.T (-k) := by
  have hzero : (LaurentPolynomial.T k : LaurentPolynomial K) • c ∈ laurentMaslovPiece G K 0 := by
    simpa using laurentMonomial_smul_mem_maslovPiece G k (1 : K) hc
  refine ⟨hzero, ?_⟩
  rw [laurentDualExtension_even_ambient G ℓ k hc]
  change LaurentPolynomial.C (dualAmbientExtension G ℓ _) * _ = _
  rw [dualAmbientExtension_apply G ℓ ⟨_, hzero⟩]

/-- Odd Maslov degrees have zero image. -/
theorem laurentDualExtension_odd (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (k : ℤ) (c : LaurentChain K n) (hc : c ∈ laurentMaslovPiece G K (2 * k + 1)) :
    laurentDualExtension G ℓ c = 0 := by
  apply chain_mem_of_monomials ((laurentDualExtension G ℓ).restrictScalars K).ker c
  intro x j hj
  have hdeg := hc x j hj
  change G.maslovOℤ x - 2 * j = 2 * k + 1 at hdeg
  have hodd : ¬ Even (G.maslovOℤ x) := by
    rintro ⟨v, hv⟩
    omega
  change laurentDualExtension G ℓ (laurentMonomialGenerator K j x) = 0
  simp only [laurentMonomialGenerator, laurentDualExtension_single,
    laurentDualBasisValue, if_neg hodd, mul_zero]

/-- The extension agrees with the original functional in degree zero. -/
theorem laurentDualExtension_degree_zero (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (c : laurentMaslovPiece G K 0) :
    laurentDualExtension G ℓ c = LaurentPolynomial.C (ℓ c) := by
  obtain ⟨h, heq⟩ := laurentDualExtension_even G ℓ 0 c (by simpa only [mul_zero] using c.property)
  simpa using heq

/-- Killing degree-one boundaries suffices to kill the entire Laurent differential. -/
theorem laurentDualExtension_differential (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K)
    (hℓ : ∀ b : laurentMaslovPiece G K 1, ℓ (laurentGradedDifferential G K 0 b) = 0)
    (c : LaurentChain K n) :
    laurentDualExtension G ℓ (laurentDifferential G K c) = 0 := by
  apply chain_mem_of_monomials
    (((laurentDualExtension G ℓ).comp (laurentDifferential G K)).restrictScalars K).ker c
  intro x j hj
  let v := laurentMonomialGenerator K j x
  let m := laurentMaslovDegree G j x
  have hv : v ∈ laurentMaslovPiece G K m :=
    laurentMonomialGenerator_mem_laurentMaslovPiece G K j x
  have hd := laurentDifferential_mem_maslovPiece G hv
  change laurentDualExtension G ℓ (laurentDifferential G K v) = 0
  by_cases he : Even (m - 1)
  · obtain ⟨k, hk⟩ := he
    have hm : m = 2 * k + 1 := by omega
    have hz : (LaurentPolynomial.T k : LaurentPolynomial K) • v ∈
        laurentMaslovPiece G K 1 := by
      have hh := laurentMonomial_smul_mem_maslovPiece G k (1 : K) hv
      rw [show m - 2 * k = 1 by omega] at hh
      exact hh
    obtain ⟨hzero, heq⟩ := laurentDualExtension_even G ℓ k
      (laurentDifferential G K v) (by simpa only [show m - 1 = 2 * k by omega] using hd)
    rw [heq]
    have hz' : ℓ ⟨(LaurentPolynomial.T k : LaurentPolynomial K) •
        laurentDifferential G K v, hzero⟩ = 0 := by
      convert hℓ ⟨_, hz⟩ using 1
      congr 1
      apply Subtype.ext
      exact ((laurentDifferential G K).map_smul _ _).symm
    rw [hz', map_zero, zero_mul]
  · have hm : m - 1 = 2 * ((m - 1) / 2) + 1 := by
      have hmod : (m - 1) % 2 ≠ 0 := by
        intro h
        exact he ⟨(m - 1) / 2, by omega⟩
      omega
    exact laurentDualExtension_odd G ℓ ((m - 1) / 2) _ (by rwa [← hm])

/-- Laurent polynomials supported on exponents whose filtration coordinate is at most s. -/
def laurentCoefficientLevel (s : ℝ) : Submodule K (LaurentPolynomial K) where
  carrier := {p | ∀ j ∈ p.coeff.support, -(j : ℝ) ≤ s}
  zero_mem' := by simp
  add_mem' hp hq j hj := by
    rw [AddMonoidAlgebra.coeff_add] at hj
    exact (Finset.mem_union.mp (Finsupp.support_add hj)).elim (hp j) (hq j)
  smul_mem' a p hp j hj := by
    rw [AddMonoidAlgebra.coeff_smul] at hj
    exact hp j (Finsupp.support_smul hj)

private theorem C_mul_T_mem_coefficientLevel (a : K) (j : ℤ) {s : ℝ}
    (hj : -(j : ℝ) ≤ s) :
    LaurentPolynomial.C a * LaurentPolynomial.T j ∈ laurentCoefficientLevel (K := K) s := by
  intro k hk
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single] at hk
  have hkj := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
  simpa only [hkj] using hj

/-- The weighted filtration on the underlying Laurent module, without fixing Maslov degree. -/
def laurentWeightedLevel (t s : ℝ) : Submodule K (LaurentChain K n) :=
  Submodule.span K {c | ∃ a b : ℝ, c ∈ laurentBifiltrationLevel G K a b ∧
    (1 - t / 2) * a + (t / 2) * b ≤ s}

private theorem monomial_mem_bifiltration (j : ℤ) (x : GridState n) :
    laurentMonomialGenerator K j x ∈
      laurentBifiltrationLevel G K (-(j : ℝ)) ((G.alexander x : ℝ) - j) := by
  classical
  intro y k hk
  change k ∈ ((Finsupp.single x (AddMonoidAlgebra.single j (1 : K))) y).coeff.support at hk
  rcases eq_or_ne y x with rfl | hy
  · rw [Finsupp.single_eq_same, AddMonoidAlgebra.coeff_single] at hk
    have hkj := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    simp only [hkj, le_refl, and_self]
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

/-- The degree-zero vanishing condition forces a filtration shift by minus a on every
Laurent chain. The target filtration counts exponent j with coordinate −j. -/
theorem laurentDualExtension_mem_coefficientLevel
    (ℓ : laurentMaslovPiece G K 0 →ₗ[K] K) (t a : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (hℓ : ∀ A B : ℝ, ∀ c : laurentMaslovPiece G K 0,
      (c : LaurentChain K n) ∈ laurentBifiltrationLevel G K A B →
      (1 - t / 2) * A + (t / 2) * B < a → ℓ c = 0)
    {s : ℝ} {c : LaurentChain K n} (hc : c ∈ laurentWeightedLevel G (K := K) t s) :
    laurentDualExtension G ℓ c ∈ laurentCoefficientLevel (K := K) (s - a) := by
  have hA : 0 ≤ 1 - t / 2 := by linarith
  have hB : 0 ≤ t / 2 := by linarith
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨A, B, hc, hs⟩ := hc
    apply chain_mem_of_monomials
      ((laurentCoefficientLevel (K := K) (s - a)).comap
        ((laurentDualExtension G ℓ).restrictScalars K)) c
    intro x j hj
    change laurentDualExtension G ℓ (laurentMonomialGenerator K j x) ∈
      laurentCoefficientLevel (K := K) (s - a)
    rw [laurentMonomialGenerator, laurentDualExtension_single]
    by_cases he : Even (G.maslovOℤ x)
    · let k := G.maslovOℤ x / 2
      have hk : G.maslovOℤ x = 2 * k := by
        obtain ⟨v, hv⟩ := he
        change G.maslovOℤ x = 2 * (G.maslovOℤ x / 2)
        omega
      have hz : laurentMonomialGenerator K k x ∈ laurentMaslovPiece G K 0 := by
        convert laurentMonomialGenerator_mem_laurentMaslovPiece G K k x using 1
        simp only [laurentMaslovDegree, hk, sub_self]
      let z : laurentMaslovPiece G K 0 := ⟨laurentMonomialGenerator K k x, hz⟩
      have hvalue : laurentDualBasisValue G ℓ x =
          LaurentPolynomial.C (ℓ z) * LaurentPolynomial.T (-k) := by
        simp only [laurentDualBasisValue, if_pos he]
        rw [dualAmbientExtension_apply G ℓ z]
      rw [hvalue, mul_left_comm, ← LaurentPolynomial.T_add]
      by_cases hzero : ℓ z = 0
      · rw [hzero, map_zero, zero_mul]
        exact Submodule.zero_mem _
      · have ha : a ≤ (1 - t / 2) * (-(k : ℝ)) +
            (t / 2) * ((G.alexander x : ℝ) - k) := by
          by_contra h
          exact hzero (hℓ _ _ z (monomial_mem_bifiltration G k x) (lt_of_not_ge h))
        obtain ⟨hcoordA, hcoordB⟩ := hc x j hj
        have hcoord := add_le_add
          (mul_le_mul_of_nonneg_left hcoordA hA)
          (mul_le_mul_of_nonneg_left hcoordB hB)
        apply C_mul_T_mem_coefficientLevel
        push_cast
        nlinarith
    · simp only [laurentDualBasisValue, if_neg he, mul_zero]
      exact Submodule.zero_mem _
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add c d _ _ hc hd => simpa using Submodule.add_mem _ hc hd
  | smul r c _ hc =>
    change ((laurentDualExtension G ℓ).restrictScalars K) (r • c) ∈ _
    rw [map_smul]
    exact (laurentCoefficientLevel (K := K) (s - a)).smul_mem r hc

/-- Every finite real degree-zero threshold has a Laurent-linear certificate, normalized
on the entire represented class and with the filtration shift needed for tensor products. -/
theorem exists_laurent_dual_of_spectralThreshold_eq [CharP K 2]
    (ξ : (laurentMaslovComplex G K).homology 0) (t a : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal)) :
    ∃ Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K,
      (∀ c, Λ (laurentDifferential G K c) = 0) ∧
      (∀ z : (laurentMaslovComplex G K).cycles 0,
        (laurentMaslovComplex G K).homologyπ 0 z = ξ →
        Λ (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 z)) = 1) ∧
      (∀ s : ℝ, ∀ c ∈ laurentWeightedLevel G (K := K) t s,
        Λ c ∈ laurentCoefficientLevel (K := K) (s - a)) := by
  obtain ⟨l, hboundary, hclass, hvanish⟩ :=
    RealFiltration.exists_dual_of_spectralThreshold_eq _ ξ a ha
  let ℓ : laurentMaslovPiece G K 0 →ₗ[K] K :=
    l.comp (laurentMaslovChainEquiv G K 0).symm.toLinearMap
  refine ⟨laurentDualExtension G ℓ, ?_, ?_, ?_⟩
  · apply laurentDualExtension_differential
    intro b
    have hb : (laurentMaslovChainEquiv G K 0).symm
        (laurentGradedDifferential G K 0 b) =
        (laurentMaslovComplex G K).d 1 0 ((laurentMaslovChainEquiv G K 1).symm b) := by
      apply (laurentMaslovChainEquiv G K 0).injective
      apply Subtype.ext
      simp only [LinearEquiv.apply_symm_apply, coe_laurentGradedDifferential]
      have haux := laurentMaslovChainEquiv_d G K 0
        ((laurentMaslovChainEquiv G K 1).symm b)
      change ((laurentMaslovChainEquiv G K 0)
        ((laurentMaslovComplex G K).d 1 0 ((laurentMaslovChainEquiv G K 1).symm b)) :
          LaurentChain K n) = laurentDifferential G K
            (laurentMaslovChainEquiv G K 1 ((laurentMaslovChainEquiv G K 1).symm b)) at haux
      rw [LinearEquiv.apply_symm_apply] at haux
      exact haux.symm
    calc
      ℓ (laurentGradedDifferential G K 0 b) =
          l ((laurentMaslovChainEquiv G K 0).symm (laurentGradedDifferential G K 0 b)) := rfl
      _ = l ((laurentMaslovComplex G K).d 1 0
          ((laurentMaslovChainEquiv G K 1).symm b)) := congrArg l hb
      _ = 0 := hboundary _
  · intro z hz
    rw [laurentDualExtension_degree_zero]
    change LaurentPolynomial.C (l ((laurentMaslovChainEquiv G K 0).symm
      (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 z)))) = 1
    rw [LinearEquiv.symm_apply_apply, hclass z hz, map_one]
  · intro s c hc
    apply laurentDualExtension_mem_coefficientLevel G ℓ t a ht0 ht2 _ hc
    intro A B v hv hw
    have hv' : (laurentMaslovChainEquiv G K 0).symm v ∈
        (laurentMaslovBifiltration G K).level A B 0 := by
      change ((laurentMaslovChainEquiv G K 0)
        ((laurentMaslovChainEquiv G K 0).symm v) : LaurentChain K n) ∈
          laurentBifiltrationLevel G K A B
      simpa only [LinearEquiv.apply_symm_apply] using hv
    exact hvanish _ hw _ (Submodule.subset_span ⟨A, B, hv', le_rfl⟩)

end OnLeConjecture.KnotFloer.GridFull
