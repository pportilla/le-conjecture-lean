/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentTensorMaslov

/-!
# A native degree-zero certificate for the Laurent tensor class

The constant coefficient of the product Laurent cocycle is a scalar functional
on the native degree-zero chain group. It is normalized on the homology class
of the selected tensor cycle and vanishes below the sum of the input thresholds.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti TensorProduct CategoryTheory

variable {K : Type*} [Field K] [CharP K 2] {n m : ℕ}
variable (G : GridDiagram n) (H : GridDiagram m)

/-- The homogeneous degree-zero chain obtained from two native degree-zero cycles. -/
def laurentTensorNativeChain
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    (laurentTensorMaslovComplex (K := K) G H).X 0 :=
  (laurentTensorMaslovChainEquiv G H 0).symm
    ⟨(laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c) :
        LaurentChain K n) ⊗ₜ[LaurentPolynomial K]
      (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d) :
        LaurentChain K m), by
      simpa only [zero_add] using tmul_mem_laurentTensorMaslovPiece G H
        (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c)).property
        (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d)).property⟩

/-- The selected tensor chain is a cycle in the native Maslov complex. -/
theorem laurentTensorNativeChain_d
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    (laurentTensorMaslovComplex (K := K) G H).d 0 (-1)
      (laurentTensorNativeChain G H c d) = 0 := by
  apply (laurentTensorMaslovChainEquiv G H (-1)).injective
  apply Subtype.ext
  rw [laurentTensorMaslovChainEquiv_d_zero]
  simp only [laurentTensorNativeChain, LinearEquiv.apply_symm_apply,
    laurentTensorDifferential_native_cycles, map_zero, ZeroMemClass.coe_zero]

/-- The selected tensor cycle, as a native cycle object. -/
def laurentTensorNativeCycle
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    (laurentTensorMaslovComplex (K := K) G H).cycles 0 :=
  (laurentTensorMaslovComplex (K := K) G H).cyclesMk
    (laurentTensorNativeChain G H c d) (-1) (by simp [ChainComplex.next])
    (laurentTensorNativeChain_d G H c d)

/-- The native cycle constructor retains the chosen balanced pure tensor. -/
theorem laurentTensorNativeCycle_iCycles
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    (laurentTensorMaslovComplex (K := K) G H).iCycles 0 (laurentTensorNativeCycle G H c d) =
      laurentTensorNativeChain G H c d :=
  (laurentTensorMaslovComplex (K := K) G H).i_cyclesMk _ _ (by simp [ChainComplex.next]) _

/-- The actual homology class of the selected tensor cycle. -/
def laurentTensorNativeClass
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    (laurentTensorMaslovComplex (K := K) G H).homology 0 :=
  (laurentTensorMaslovComplex (K := K) G H).homologyπ 0 (laurentTensorNativeCycle G H c d)

/-- Constant-coefficient extraction from the Laurent product pairing. -/
def laurentTensorNativeFunctional
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K) :
    (laurentTensorMaslovComplex (K := K) G H).X 0 →ₗ[K] K where
  toFun z := (laurentTensorPairing Λ Μ (laurentTensorMaslovChainEquiv G H 0 z)).coeff 0
  map_add' z w := by simp
  map_smul' a z := by
    change (((laurentTensorPairing Λ Μ).restrictScalars K)
      (a • (laurentTensorMaslovChainEquiv G H 0 z :
        LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m))).coeff 0 = _
    rw [map_smul]
    simp

/-- The scalar functional annihilates native degree-one boundaries. -/
theorem laurentTensorNativeFunctional_d
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (hΛ : ∀ c, Λ (laurentDifferential G K c) = 0)
    (hΜ : ∀ d, Μ (laurentDifferential H K d) = 0)
    (z : (laurentTensorMaslovComplex (K := K) G H).X 1) :
    laurentTensorNativeFunctional G H Λ Μ
      ((laurentTensorMaslovComplex (K := K) G H).d 1 0 z) = 0 := by
  have haux := laurentTensorMaslovChainEquiv_d (K := K) G H 0 z
  change ((laurentTensorMaslovChainEquiv G H 0)
    ((laurentTensorMaslovComplex (K := K) G H).d 1 0 z) :
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) =
        laurentTensorDifferential (K := K) G H (laurentTensorMaslovChainEquiv G H 1 z) at haux
  change (laurentTensorPairing Λ Μ _).coeff 0 = 0
  rw [haux, laurentTensorPairing_differential G H Λ Μ hΛ hΜ]
  rfl

/-- Normalization on the two selected cycles normalizes their tensor cycle. -/
theorem laurentTensorNativeFunctional_cycle
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : Λ (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c)) = 1)
    (hd : Μ (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d)) = 1) :
    laurentTensorNativeFunctional G H Λ Μ
      ((laurentTensorMaslovComplex (K := K) G H).iCycles 0
        (laurentTensorNativeCycle G H c d)) = 1 := by
  rw [laurentTensorNativeCycle_iCycles]
  change (laurentTensorPairing Λ Μ
    (laurentTensorMaslovChainEquiv G H 0 (laurentTensorNativeChain G H c d))).coeff 0 = 1
  simp only [laurentTensorNativeChain, LinearEquiv.apply_symm_apply,
    laurentTensorPairing_tmul, hc, hd, mul_one]
  simp

/-- Two input thresholds supply the complete native degree-zero dual certificate
for their selected tensor homology class. -/
theorem exists_native_laurentTensor_dual
    (ξ : (laurentMaslovComplex G K).homology 0)
    (η : (laurentMaslovComplex H K).homology 0) (t a b : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal))
    (hb : ((laurentMaslovBifiltration H K).weighted t).spectralThreshold 0 η = (b : EReal))
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : (laurentMaslovComplex G K).homologyπ 0 c = ξ)
    (hd : (laurentMaslovComplex H K).homologyπ 0 d = η) :
    ∃ ℓ : (laurentTensorMaslovComplex (K := K) G H).X 0 →ₗ[K] K,
      (∀ v : (laurentTensorMaslovComplex (K := K) G H).X 1,
        ℓ ((laurentTensorMaslovComplex (K := K) G H).d 1 0 v) = 0) ∧
      (∀ z : (laurentTensorMaslovComplex (K := K) G H).cycles 0,
        (laurentTensorMaslovComplex (K := K) G H).homologyπ 0 z =
          laurentTensorNativeClass G H c d →
        ℓ ((laurentTensorMaslovComplex (K := K) G H).iCycles 0 z) = 1) ∧
      (∀ s : ℝ, s < a + b → ∀ v ∈
        ((laurentTensorMaslovBifiltration G H).weighted t).level s 0, ℓ v = 0) := by
  obtain ⟨Λ, hΛd, hΛclass, hΛ⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq G ξ t a ht0 ht2 ha
  obtain ⟨Μ, hΜd, hΜclass, hΜ⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq H η t b ht0 ht2 hb
  let ℓ := laurentTensorNativeFunctional G H Λ Μ
  have hboundary := laurentTensorNativeFunctional_d G H Λ Μ hΛd hΜd
  refine ⟨ℓ, hboundary, ?_, ?_⟩
  · intro z hz
    obtain ⟨v, hv⟩ := RealFiltration.exists_boundary_of_homologyπ_eq
      ((ChainComplex.prev ℤ 0).trans (zero_add 1)) hz
    rw [hv, map_add, hboundary, add_zero]
    exact laurentTensorNativeFunctional_cycle G H Λ Μ c d (hΛclass c hc) (hΜclass d hd)
  · intro s hs v hv
    have hraw := native_weighted_mem_laurentTensorLevel G H t ht0 ht2 0 hv
    have hbound := laurentTensorPairing_mem_coefficientLevel G H Λ Μ t a b hΛ hΜ hraw
    change (laurentTensorPairing Λ Μ (laurentTensorMaslovChainEquiv G H 0 v)).coeff 0 = 0
    by_contra hne
    have hzero := hbound 0 (Finsupp.mem_support_iff.mpr hne)
    norm_num at hzero
    linarith

/-- The tensor class is nonzero, as witnessed by its constructed scalar dual. -/
theorem laurentTensorNativeClass_ne_zero
    (ξ : (laurentMaslovComplex G K).homology 0)
    (η : (laurentMaslovComplex H K).homology 0) (t a b : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal))
    (hb : ((laurentMaslovBifiltration H K).weighted t).spectralThreshold 0 η = (b : EReal))
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : (laurentMaslovComplex G K).homologyπ 0 c = ξ)
    (hd : (laurentMaslovComplex H K).homologyπ 0 d = η) :
    laurentTensorNativeClass G H c d ≠ 0 := by
  obtain ⟨ℓ, _, hclass, _⟩ := exists_native_laurentTensor_dual G H ξ η t a b ht0 ht2 ha hb c d hc hd
  intro hz
  have h := hclass 0 (by simpa using hz.symm)
  simp at h

/-- The native tensor spectral threshold is bounded below by the sum of the input thresholds. -/
theorem add_le_native_laurentTensor_spectralThreshold
    (ξ : (laurentMaslovComplex G K).homology 0)
    (η : (laurentMaslovComplex H K).homology 0) (t a b : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal))
    (hb : ((laurentMaslovBifiltration H K).weighted t).spectralThreshold 0 η = (b : EReal))
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : (laurentMaslovComplex G K).homologyπ 0 c = ξ)
    (hd : (laurentMaslovComplex H K).homologyπ 0 d = η) :
    ((a + b : ℝ) : EReal) ≤
      ((laurentTensorMaslovBifiltration G H).weighted t).spectralThreshold 0
        (laurentTensorNativeClass G H c d) := by
  obtain ⟨ℓ, _, hclass, hlevel⟩ := exists_native_laurentTensor_dual G H ξ η t a b
    ht0 ht2 ha hb c d hc hd
  exact RealFiltration.le_spectralThreshold_of_dual _ ℓ hclass hlevel

end OnLeConjecture.KnotFloer.GridFull
