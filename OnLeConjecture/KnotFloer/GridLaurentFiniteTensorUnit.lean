/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorCertificate

/-!
# Empty and singleton tensor factors

Mathlib's finite tensor equivalences identify the empty tensor with the Laurent
ring and the singleton tensor with its sole factor. These identifications retain
the tensor differential and the selected pure tensor chains.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct CategoryTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- The empty finite tensor has zero differential. -/
theorem laurentFiniteDifferential_eq_zero_of_isEmpty [IsEmpty ι] :
    laurentFiniteDifferential (K := K) G = 0 := by
  simp [laurentFiniteDifferential]

/-- The singleton tensor equivalence intertwines the tensor and factor differentials. -/
theorem laurentFiniteDifferential_subsingleton [Subsingleton ι] (i₀ : ι)
    (z : LaurentFiniteTensor (K := K) (n := n)) :
    PiTensorProduct.subsingletonEquiv i₀ (laurentFiniteDifferential G z) =
      laurentDifferential (G i₀) K (PiTensorProduct.subsingletonEquiv i₀ z) := by
  let : Unique ι := ⟨⟨i₀⟩, fun i => Subsingleton.elim i i₀⟩
  have h : (PiTensorProduct.subsingletonEquiv i₀).toLinearMap.comp
      (laurentFiniteDifferential (K := K) G) =
      (laurentDifferential (G i₀) K).comp
        (PiTensorProduct.subsingletonEquiv i₀).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp [LinearMap.compMultilinearMap_apply, laurentFiniteDifferential_tprod,
      show (default : ι) = i₀ from rfl]
  exact LinearMap.congr_fun h z

variable [CharP K 2]

/-- The selected empty tensor chain is the Laurent unit. -/
theorem laurentFiniteNativeChain_isEmpty [IsEmpty ι]
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    PiTensorProduct.isEmptyEquiv ι
      (laurentFiniteMaslovChainEquiv G 0 (laurentFiniteNativeChain G c) :
        LaurentFiniteTensor (K := K) (n := n)) = 1 := by
  simp [laurentFiniteNativeChain]

/-- The selected singleton tensor chain is the selected chain in its sole factor. -/
theorem laurentFiniteNativeChain_subsingleton [Subsingleton ι] (i₀ : ι)
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    PiTensorProduct.subsingletonEquiv i₀
      (laurentFiniteMaslovChainEquiv G 0 (laurentFiniteNativeChain G c) :
        LaurentFiniteTensor (K := K) (n := n)) =
      (laurentMaslovChainEquiv (G i₀) K 0
        ((laurentMaslovComplex (G i₀) K).iCycles 0 (c i₀)) : LaurentChain K (n i₀)) := by
  simp [laurentFiniteNativeChain]

/-- The empty tensor unit represents a nonzero native homology class. -/
theorem laurentFiniteNativeClass_ne_zero_of_isEmpty [IsEmpty ι]
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    laurentFiniteNativeClass G c ≠ 0 := by
  apply laurentFiniteNativeClass_ne_zero G
    (fun i => (laurentMaslovComplex (G i) K).homologyπ 0 (c i)) 0 (fun _ => 0)
    (by norm_num) (by norm_num) (fun i => isEmptyElim i) c
  intro i
  rfl

/-- The empty tensor unit has spectral threshold at least zero. -/
theorem zero_le_native_laurentFiniteTensor_threshold_of_isEmpty [IsEmpty ι]
    (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (c : ∀ i, (laurentMaslovComplex (G i) K).cycles 0) :
    0 ≤ ((laurentFiniteMaslovBifiltration G).weighted t).spectralThreshold 0
      (laurentFiniteNativeClass G c) := by
  simpa using sum_le_native_laurentFiniteTensor_spectralThreshold G
    (fun i => (laurentMaslovComplex (G i) K).homologyπ 0 (c i)) t (fun _ => 0)
    ht0 ht2 (fun i => isEmptyElim i) c (fun _ => rfl)

end OnLeConjecture.KnotFloer.GridFull
