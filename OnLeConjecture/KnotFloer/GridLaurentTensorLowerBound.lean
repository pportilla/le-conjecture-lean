/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentDualCertificate
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The Laurent tensor certificate and the spectral lower bound

The tensor product is balanced over the Laurent ring. Its convolution filtration
is the base-field span of pure tensors with bounded sum of filtration levels.
The product of two Laurent dual certificates detects their tensor class and rules
out representatives below the sum of the two thresholds.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti TensorProduct CategoryTheory
open scoped Pointwise

variable {K : Type*} [Field K] {n m : ℕ}
variable (G : GridDiagram n) (H : GridDiagram m)

/-- Multiply the values of two Laurent-linear functionals on a Laurent tensor product. -/
def laurentTensorPairing
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K) :
    LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m →ₗ[LaurentPolynomial K]
      LaurentPolynomial K :=
  (TensorProduct.lid (LaurentPolynomial K) (LaurentPolynomial K)).toLinearMap.comp
    (TensorProduct.map Λ Μ)

@[simp]
theorem laurentTensorPairing_tmul
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (c : LaurentChain K n) (d : LaurentChain K m) :
    laurentTensorPairing Λ Μ (c ⊗ₜ[LaurentPolynomial K] d) = Λ c * Μ d := by
  simp [laurentTensorPairing]

/-- The characteristic-two tensor differential on the total Laurent modules. -/
def laurentTensorDifferential :
    LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m →ₗ[LaurentPolynomial K]
      LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m :=
  TensorProduct.map (laurentDifferential G K) LinearMap.id +
    TensorProduct.map LinearMap.id (laurentDifferential H K)

@[simp]
theorem laurentTensorDifferential_tmul (c : LaurentChain K n) (d : LaurentChain K m) :
    laurentTensorDifferential (K := K) G H (c ⊗ₜ[LaurentPolynomial K] d) =
      (laurentDifferential G K c) ⊗ₜ[LaurentPolynomial K] d +
        c ⊗ₜ[LaurentPolynomial K] (laurentDifferential H K d) := by
  simp [laurentTensorDifferential]

/-- The tensor differential squares to zero over a field of characteristic two. -/
theorem laurentTensorDifferential_sq_eq_zero [CharP K 2]
    (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) :
    laurentTensorDifferential (K := K) G H (laurentTensorDifferential (K := K) G H z) = 0 := by
  have hcomp : (laurentTensorDifferential (K := K) G H).comp
      (laurentTensorDifferential (K := K) G H) = 0 := by
    apply TensorProduct.ext'
    intro c d
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, laurentTensorDifferential_tmul,
      map_add, laurentDifferential_sq_eq_zero, zero_tmul, tmul_zero, zero_add, add_zero]
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [← two_smul K, htwo, zero_smul]
  exact LinearMap.congr_fun hcomp z

/-- The convolution filtration over the base field, on a tensor product over the Laurent ring. -/
def laurentTensorLevel (t s : ℝ) :
    Submodule K (LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) :=
  Submodule.span K {z | ∃ a b : ℝ, ∃ c : LaurentChain K n, ∃ d : LaurentChain K m,
    c ∈ laurentWeightedLevel G t a ∧ d ∈ laurentWeightedLevel H t b ∧
      a + b ≤ s ∧ z = c ⊗ₜ[LaurentPolynomial K] d}

/-- The full differential preserves each weighted level on the underlying Laurent module. -/
theorem laurentDifferential_mem_weightedLevel (t s : ℝ) (c : LaurentChain K n)
    (hc : c ∈ laurentWeightedLevel G t s) :
    laurentDifferential G K c ∈ laurentWeightedLevel G t s := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, b, hc, hab⟩ := hc
    exact Submodule.subset_span ⟨a, b,
      laurentDifferential_mem_bifiltrationLevel G K a b c hc, hab⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add c d _ _ hc hd => simpa using Submodule.add_mem _ hc hd
  | smul r c _ hc =>
    change ((laurentDifferential G K).restrictScalars K) (r • c) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hc

/-- The convolution filtration is preserved by the tensor differential. -/
theorem laurentTensorDifferential_mem_level (t s : ℝ)
    (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m)
    (hz : z ∈ laurentTensorLevel G H t s) :
    laurentTensorDifferential (K := K) G H z ∈ laurentTensorLevel G H t s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, c, d, hc, hd, hab, rfl⟩ := hz
    rw [laurentTensorDifferential_tmul]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨a, b, _, _,
        laurentDifferential_mem_weightedLevel G t a c hc, hd, hab, rfl⟩
    · exact Submodule.subset_span ⟨a, b, _, _, hc,
        laurentDifferential_mem_weightedLevel H t b d hd, hab, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul r z _ hz =>
    change ((laurentTensorDifferential (K := K) G H).restrictScalars K) (r • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hz

/-- Laurent polynomial filtration levels add under multiplication. -/
theorem laurentCoefficientLevel_mul {p q : LaurentPolynomial K} {s t : ℝ}
    (hp : p ∈ laurentCoefficientLevel (K := K) s)
    (hq : q ∈ laurentCoefficientLevel (K := K) t) :
    p * q ∈ laurentCoefficientLevel (K := K) (s + t) := by
  classical
  intro j hj
  obtain ⟨k, hk, l, hl, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset p q hj)
  have hk' := hp k hk
  have hl' := hq l hl
  push_cast
  linarith

/-- The product certificate has the sum of the two filtration shifts. -/
theorem laurentTensorPairing_mem_coefficientLevel
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (t a b : ℝ)
    (hΛ : ∀ s c, c ∈ laurentWeightedLevel G t s →
      Λ c ∈ laurentCoefficientLevel (K := K) (s - a))
    (hΜ : ∀ s d, d ∈ laurentWeightedLevel H t s →
      Μ d ∈ laurentCoefficientLevel (K := K) (s - b))
    {s : ℝ} {z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m}
    (hz : z ∈ laurentTensorLevel G H t s) :
    laurentTensorPairing Λ Μ z ∈ laurentCoefficientLevel (K := K) (s - (a + b)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, u, c, d, hc, hd, hrs, rfl⟩ := hz
    rw [laurentTensorPairing_tmul]
    have hprod := laurentCoefficientLevel_mul (hΛ r c hc) (hΜ u d hd)
    intro j hj
    have h := hprod j hj
    linarith
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul r z _ hz =>
    change ((laurentTensorPairing Λ Μ).restrictScalars K) (r • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hz

/-- Tensor products of cocycles kill the tensor differential. -/
theorem laurentTensorPairing_differential
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (hΛ : ∀ c, Λ (laurentDifferential G K c) = 0)
    (hΜ : ∀ d, Μ (laurentDifferential H K d) = 0)
    (z : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) :
    laurentTensorPairing Λ Μ (laurentTensorDifferential (K := K) G H z) = 0 := by
  have hcomp : (laurentTensorPairing Λ Μ).comp (laurentTensorDifferential (K := K) G H) = 0 := by
    apply TensorProduct.ext'
    intro c d
    simp [hΛ, hΜ]
  exact LinearMap.congr_fun hcomp z

/-- A chain equivalent modulo tensor boundaries to a normalized tensor cycle cannot
lie below the sum of the two certificate thresholds. -/
theorem le_of_laurentTensor_representative
    (Λ : LaurentChain K n →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (Μ : LaurentChain K m →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (t a b : ℝ)
    (hΛd : ∀ c, Λ (laurentDifferential G K c) = 0)
    (hΜd : ∀ d, Μ (laurentDifferential H K d) = 0)
    (hΛ : ∀ s c, c ∈ laurentWeightedLevel G t s →
      Λ c ∈ laurentCoefficientLevel (K := K) (s - a))
    (hΜ : ∀ s d, d ∈ laurentWeightedLevel H t s →
      Μ d ∈ laurentCoefficientLevel (K := K) (s - b))
    (c : LaurentChain K n) (d : LaurentChain K m) (hc : Λ c = 1) (hd : Μ d = 1)
    {s : ℝ} (z w : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m)
    (hz : z ∈ laurentTensorLevel G H t s)
    (hrep : z = c ⊗ₜ[LaurentPolynomial K] d + laurentTensorDifferential (K := K) G H w) :
    a + b ≤ s := by
  have hval : laurentTensorPairing Λ Μ z = 1 := by
    rw [hrep, map_add, laurentTensorPairing_tmul, hc, hd,
      laurentTensorPairing_differential G H Λ Μ hΛd hΜd, mul_one, add_zero]
  have hbound := laurentTensorPairing_mem_coefficientLevel G H Λ Μ t a b hΛ hΜ hz
  rw [hval] at hbound
  have h := hbound 0 (by simp)
  norm_num at h
  linarith

/-- The lower tensor bound obtained directly from the two native spectral thresholds.
No tensor decomposition of homology or geometric connected-sum identification is assumed. -/
theorem spectralThresholds_le_of_laurentTensor_representative [CharP K 2]
    (ξ : (laurentMaslovComplex G K).homology 0)
    (η : (laurentMaslovComplex H K).homology 0) (t a b : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal))
    (hb : ((laurentMaslovBifiltration H K).weighted t).spectralThreshold 0 η = (b : EReal))
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : (laurentMaslovComplex G K).homologyπ 0 c = ξ)
    (hd : (laurentMaslovComplex H K).homologyπ 0 d = η)
    {s : ℝ} (z w : LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m)
    (hz : z ∈ laurentTensorLevel G H t s)
    (hrep : z =
      (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c) :
        LaurentChain K n) ⊗ₜ[LaurentPolynomial K]
      (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d) :
        LaurentChain K m) + laurentTensorDifferential (K := K) G H w) :
    a + b ≤ s := by
  obtain ⟨Λ, hΛd, hΛclass, hΛ⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq G ξ t a ht0 ht2 ha
  obtain ⟨Μ, hΜd, hΜclass, hΜ⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq H η t b ht0 ht2 hb
  exact le_of_laurentTensor_representative G H Λ Μ t a b hΛd hΜd hΛ hΜ
    _ _ (hΛclass c hc) (hΜclass d hd) z w hz hrep

/-- A native degree-zero cycle remains a cycle in the total Laurent module. -/
theorem laurentDifferential_native_cycle [CharP K 2]
    (c : (laurentMaslovComplex G K).cycles 0) :
    laurentDifferential G K
      (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c)) = 0 := by
  have hc : (laurentMaslovComplex G K).d 0 (-1)
      ((laurentMaslovComplex G K).iCycles 0 c) = 0 :=
    congrArg (fun f : (laurentMaslovComplex G K).cycles 0 ⟶
      (laurentMaslovComplex G K).X (-1) => f c)
        ((laurentMaslovComplex G K).iCycles_d 0 (-1))
  have haux := laurentMaslovChainEquiv_d G K (-1)
    ((laurentMaslovComplex G K).iCycles 0 c)
  change ((laurentMaslovChainEquiv G K (-1))
    ((laurentMaslovComplex G K).d 0 (-1) ((laurentMaslovComplex G K).iCycles 0 c)) :
      LaurentChain K n) = laurentDifferential G K
        (laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c)) at haux
  rw [hc, map_zero, ZeroMemClass.coe_zero] at haux
  exact haux.symm

/-- The tensor of native cycles is a cycle for the constructed tensor differential. -/
theorem laurentTensorDifferential_native_cycles [CharP K 2]
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0) :
    laurentTensorDifferential (K := K) G H
      ((laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c) :
        LaurentChain K n) ⊗ₜ[LaurentPolynomial K]
      (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d) :
        LaurentChain K m)) = 0 := by
  rw [laurentTensorDifferential_tmul, laurentDifferential_native_cycle,
    laurentDifferential_native_cycle, zero_tmul, tmul_zero, add_zero]

/-- Two finite real spectral thresholds determine a tensor cycle which is not a boundary. -/
theorem native_tensor_cycle_not_boundary [CharP K 2]
    (ξ : (laurentMaslovComplex G K).homology 0)
    (η : (laurentMaslovComplex H K).homology 0) (t a b : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ((laurentMaslovBifiltration G K).weighted t).spectralThreshold 0 ξ = (a : EReal))
    (hb : ((laurentMaslovBifiltration H K).weighted t).spectralThreshold 0 η = (b : EReal))
    (c : (laurentMaslovComplex G K).cycles 0) (d : (laurentMaslovComplex H K).cycles 0)
    (hc : (laurentMaslovComplex G K).homologyπ 0 c = ξ)
    (hd : (laurentMaslovComplex H K).homologyπ 0 d = η) :
    ((laurentMaslovChainEquiv G K 0 ((laurentMaslovComplex G K).iCycles 0 c) :
      LaurentChain K n) ⊗ₜ[LaurentPolynomial K]
    (laurentMaslovChainEquiv H K 0 ((laurentMaslovComplex H K).iCycles 0 d) :
      LaurentChain K m)) ∉ LinearMap.range (laurentTensorDifferential (K := K) G H) := by
  obtain ⟨Λ, hΛd, hΛclass, _⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq G ξ t a ht0 ht2 ha
  obtain ⟨Μ, hΜd, hΜclass, _⟩ :=
    exists_laurent_dual_of_spectralThreshold_eq H η t b ht0 ht2 hb
  rintro ⟨w, hw⟩
  have h := laurentTensorPairing_differential G H Λ Μ hΛd hΜd w
  rw [hw, laurentTensorPairing_tmul, hΛclass c hc, hΜclass d hd, mul_one] at h
  exact one_ne_zero h

end OnLeConjecture.KnotFloer.GridFull
