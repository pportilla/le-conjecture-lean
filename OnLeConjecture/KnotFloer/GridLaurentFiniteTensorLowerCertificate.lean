/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorCertificate

/-!
# Finite tensor certificates from lower bounds alone

The numerical comparison requires only lower bounds on the factor thresholds.
A real lower bound excludes the zero class. The already proved finiteness
of nonzero grid thresholds then permits the exact-threshold construction,
and its certificate also vanishes below the smaller prescribed bound.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [CharP K 2] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- Lower bounds on all factor thresholds supply the complete finite tensor dual. -/
theorem exists_native_laurentFiniteTensor_dual_of_le
    (ξ : ∀ i, (laurentMaslovComplex (G i) K).homology 0) (t : ℝ) (a : ι → ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (ha : ∀ i, (a i : EReal) ≤
      ((laurentMaslovBifiltration (G i) K).weighted t).spectralThreshold 0 (ξ i))
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
  have hne (i : ι) : ξ i ≠ 0 := by
    obtain ⟨ℓ, _, hclass, _⟩ := RealFiltration.exists_dual_of_le_spectralThreshold
      ((laurentMaslovBifiltration (G i) K).weighted t)
      ((ChainComplex.prev ℤ 0).trans (zero_add 1)) (ξ i) (a i) (ha i)
    intro hz
    have h := hclass 0 (by simpa using hz.symm)
    rw [map_zero, map_zero] at h
    exact zero_ne_one h
  choose b hb using fun i => exists_real_weighted_laurentMaslov_spectralThreshold
    (G i) K 0 (ξ i) (hne i) t ht0 ht2
  have hab : ∀ i, a i ≤ b i := by
    intro i
    have h := ha i
    rw [hb i] at h
    exact EReal.coe_le_coe_iff.mp h
  obtain ⟨ℓ, hd, hclass, hlevel⟩ := exists_native_laurentFiniteTensor_dual
    G ξ t b ht0 ht2 hb c hc
  exact ⟨ℓ, hd, hclass, fun s hs v hv =>
    hlevel s (hs.trans_le (Finset.sum_le_sum fun i _ => hab i)) v hv⟩

end OnLeConjecture.KnotFloer.GridFull
