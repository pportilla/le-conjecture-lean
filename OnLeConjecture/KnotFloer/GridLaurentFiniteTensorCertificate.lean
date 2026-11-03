/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorMaslov

/-!
# The finite-factor lower spectral certificate

A finite family of selected degree-zero grid cycles determines a cycle in the
balanced finite tensor complex. The constant coefficient of the product Laurent
cocycle normalizes its entire homology class and vanishes below the sum of the
factor thresholds. The theorem also applies to empty and singleton families.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct CategoryTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [CharP K 2] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- The selected finite pure tensor in native degree zero. -/
def laurentFiniteNativeChain (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    (laurentFiniteMaslovComplex (K := K) G).X 0 :=
  (laurentFiniteMaslovChainEquiv G 0).symm
    ⟨tprod (LaurentPolynomial K) (fun i =>
      (laurentMaslovChainEquiv (G i) K 0 ((laurentMaslovComplex (G i) K).iCycles 0 (c i)) :
        LaurentChain K (n i))), Submodule.subset_span
      ⟨0, fun _ => 0, _, fun i =>
        (laurentMaslovChainEquiv (G i) K 0
          ((laurentMaslovComplex (G i) K).iCycles 0 (c i))).property, by simp, by simp⟩⟩

/-- A finite tensor of the selected native cycles is a native cycle. -/
theorem laurentFiniteNativeChain_d (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    (laurentFiniteMaslovComplex (K := K) G).d 0 (-1) (laurentFiniteNativeChain G c) = 0 := by
  apply (laurentFiniteMaslovChainEquiv G (-1)).injective
  apply Subtype.ext
  rw [laurentFiniteMaslovChainEquiv_d_zero]
  simp only [laurentFiniteNativeChain, LinearEquiv.apply_symm_apply,
    map_zero, ZeroMemClass.coe_zero]
  rw [laurentFiniteDifferential_tprod]
  apply Finset.sum_eq_zero
  intro i hi
  apply (tprod (LaurentPolynomial K)).map_coord_zero i
  rw [Function.update_self, laurentDifferential_native_cycle]

/-- The selected finite tensor as a native cycle object. -/
def laurentFiniteNativeCycle (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    (laurentFiniteMaslovComplex (K := K) G).cycles 0 :=
  (laurentFiniteMaslovComplex (K := K) G).cyclesMk (laurentFiniteNativeChain G c) (-1)
    (by simp [ChainComplex.next]) (laurentFiniteNativeChain_d G c)

/-- The selected cycle retains its specified pure tensor chain. -/
theorem laurentFiniteNativeCycle_iCycles (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    (laurentFiniteMaslovComplex (K := K) G).iCycles 0 (laurentFiniteNativeCycle G c) =
      laurentFiniteNativeChain G c :=
  (laurentFiniteMaslovComplex (K := K) G).i_cyclesMk _ _ (by simp [ChainComplex.next]) _

/-- The selected finite tensor homology class. -/
def laurentFiniteNativeClass (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    (laurentFiniteMaslovComplex (K := K) G).homology 0 :=
  (laurentFiniteMaslovComplex (K := K) G).homologyπ 0 (laurentFiniteNativeCycle G c)

/-- Constant coefficient of the finite product of Laurent cocycles. -/
def laurentFiniteNativeFunctional
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K) :
    (laurentFiniteMaslovComplex (K := K) G).X 0 →ₗ[K] K where
  toFun z := (laurentFinitePairing Λ (laurentFiniteMaslovChainEquiv G 0 z)).coeff 0
  map_add' z w := by simp
  map_smul' a z := by
    change (((laurentFinitePairing Λ).restrictScalars K)
      (a • (laurentFiniteMaslovChainEquiv G 0 z :
        LaurentFiniteTensor (K := K) (n := n)))).coeff 0 = _
    rw [map_smul]
    simp

/-- The finite scalar functional annihilates native incoming boundaries. -/
theorem laurentFiniteNativeFunctional_d
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (hΛ : ∀ i x, Λ i (laurentDifferential (G i) K x) = 0)
    (z : (laurentFiniteMaslovComplex (K := K) G).X 1) :
    laurentFiniteNativeFunctional G Λ ((laurentFiniteMaslovComplex (K := K) G).d 1 0 z) = 0 := by
  have haux := laurentFiniteMaslovChainEquiv_d (K := K) G 0 z
  change ((laurentFiniteMaslovChainEquiv G 0)
    ((laurentFiniteMaslovComplex (K := K) G).d 1 0 z) :
      LaurentFiniteTensor (K := K) (n := n)) =
        laurentFiniteDifferential G (laurentFiniteMaslovChainEquiv G 1 z) at haux
  change (laurentFinitePairing Λ _).coeff 0 = 0
  rw [haux, laurentFinitePairing_differential G Λ hΛ]
  rfl

/-- Factorwise normalization normalizes the finite tensor cycle, including the empty unit. -/
theorem laurentFiniteNativeFunctional_cycle
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0)
    (hc : ∀ i, Λ i (laurentMaslovChainEquiv (G i) K 0
      ((laurentMaslovComplex (G i) K).iCycles 0 (c i))) = 1) :
    laurentFiniteNativeFunctional G Λ
      ((laurentFiniteMaslovComplex (K := K) G).iCycles 0 (laurentFiniteNativeCycle G c)) = 1 := by
  rw [laurentFiniteNativeCycle_iCycles]
  change (laurentFinitePairing Λ
    (laurentFiniteMaslovChainEquiv G 0 (laurentFiniteNativeChain G c))).coeff 0 = 1
  simp only [laurentFiniteNativeChain, LinearEquiv.apply_symm_apply,
    laurentFinitePairing_tprod, hc, Finset.prod_const_one]
  simp

/-- A finite family of native factor thresholds produces a scalar dual for the selected
finite tensor homology class. No nonempty-family hypothesis is required. -/
theorem exists_native_laurentFiniteTensor_dual
    (ξ : ∀ i, (laurentMaslovComplex (G i) K).homology 0) (t : ℝ) (a : ι → ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ∀ i, ((laurentMaslovBifiltration (G i) K).weighted t).spectralThreshold 0 (ξ i) =
      (a i : EReal))
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0)
    (hc : ∀ i, (laurentMaslovComplex (G i) K).homologyπ 0 (c i) = ξ i) :
    ∃ ℓ : (laurentFiniteMaslovComplex (K := K) G).X 0 →ₗ[K] K,
      (∀ v : (laurentFiniteMaslovComplex (K := K) G).X 1,
        ℓ ((laurentFiniteMaslovComplex (K := K) G).d 1 0 v) = 0) ∧
      (∀ z : (laurentFiniteMaslovComplex (K := K) G).cycles 0,
        (laurentFiniteMaslovComplex (K := K) G).homologyπ 0 z = laurentFiniteNativeClass G c →
          ℓ ((laurentFiniteMaslovComplex (K := K) G).iCycles 0 z) = 1) ∧
      (∀ s : ℝ, s < ∑ i, a i → ∀ v ∈
        ((laurentFiniteMaslovBifiltration G).weighted t).level s 0, ℓ v = 0) := by
  choose Λ hΛd hΛclass hΛ using fun i =>
    exists_laurent_dual_of_spectralThreshold_eq (G i) (ξ i) t (a i) ht0 ht2 (ha i)
  let ℓ := laurentFiniteNativeFunctional G Λ
  have hboundary := laurentFiniteNativeFunctional_d G Λ hΛd
  refine ⟨ℓ, hboundary, ?_, ?_⟩
  · intro z hz
    obtain ⟨v, hv⟩ := RealFiltration.exists_boundary_of_homologyπ_eq
      ((ChainComplex.prev ℤ 0).trans (zero_add 1)) hz
    rw [hv, map_add, hboundary, add_zero]
    exact laurentFiniteNativeFunctional_cycle G Λ c (fun i => hΛclass i (c i) (hc i))
  · intro s hs v hv
    have hraw := native_weighted_mem_laurentFiniteWeightedLevel G t 0 hv
    have hbound := laurentFinitePairing_mem_coefficientLevel G Λ t a ht0 ht2 hΛ hraw
    change (laurentFinitePairing Λ (laurentFiniteMaslovChainEquiv G 0 v)).coeff 0 = 0
    by_contra hne
    have hzero := hbound 0 (Finsupp.mem_support_iff.mpr hne)
    norm_num at hzero
    linarith

/-- The selected finite tensor class is nonzero. -/
theorem laurentFiniteNativeClass_ne_zero
    (ξ : ∀ i, (laurentMaslovComplex (G i) K).homology 0) (t : ℝ) (a : ι → ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ∀ i, ((laurentMaslovBifiltration (G i) K).weighted t).spectralThreshold 0 (ξ i) =
      (a i : EReal))
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0)
    (hc : ∀ i, (laurentMaslovComplex (G i) K).homologyπ 0 (c i) = ξ i) :
    laurentFiniteNativeClass G c ≠ 0 := by
  obtain ⟨ℓ, _, hclass, _⟩ := exists_native_laurentFiniteTensor_dual G ξ t a ht0 ht2 ha c hc
  intro hz
  have h := hclass 0 (by simpa using hz.symm)
  simp at h

/-- The native finite tensor threshold is bounded below by the sum of the factor thresholds. -/
theorem sum_le_native_laurentFiniteTensor_spectralThreshold
    (ξ : ∀ i, (laurentMaslovComplex (G i) K).homology 0) (t : ℝ) (a : ι → ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ∀ i, ((laurentMaslovBifiltration (G i) K).weighted t).spectralThreshold 0 (ξ i) =
      (a i : EReal))
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0)
    (hc : ∀ i, (laurentMaslovComplex (G i) K).homologyπ 0 (c i) = ξ i) :
    ((∑ i, a i : ℝ) : EReal) ≤
      ((laurentFiniteMaslovBifiltration G).weighted t).spectralThreshold 0
        (laurentFiniteNativeClass G c) := by
  obtain ⟨ℓ, _, hclass, hlevel⟩ := exists_native_laurentFiniteTensor_dual G ξ t a
    ht0 ht2 ha c hc
  exact RealFiltration.le_spectralThreshold_of_dual _ ℓ hclass hlevel

end OnLeConjecture.KnotFloer.GridFull
