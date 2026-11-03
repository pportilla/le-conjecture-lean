/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorLowerCertificate
public import OnLeConjecture.KnotFloer.TwoCycleComparison

/-!
# Connecting the finite transverse tensor certificate to the two-cycle estimates

The constructed finite tensor dual supplies the functional in
`estimates_of_two_cycles_and_dual`. The remaining inputs are two source
representatives, a shifted map carrying their class to the specified tensor
class, lower bounds on the branch thresholds, and the numerical genus identity.
No geometric knot or connected-sum identification is asserted here.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Staircase

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {sizes : ι → ℕ}
variable {C : ChainComplex (ModuleCat K) ℤ} {F : Bifiltration C}

/-- The final two inequalities from a map into the actual finite tensor complex.
The dual certificate is constructed internally from the factor thresholds. -/
theorem estimates_of_two_cycles_and_finite_tensor_map
    (G : ∀ j, GridDiagram (sizes j))
    (φ : C ⟶ laurentFiniteMaslovComplex (K := K) G)
    (gCob : ℝ) (hφ : F.Shifts (laurentFiniteMaslovBifiltration G) φ 0 gCob)
    (ξ : C.homology 0) (n M m : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (hcycle₁ : (F.weighted (2 / (m : ℝ))).RepresentedBelow 0 ξ
      (consecutiveWeight n (2 / (m : ℝ)) ⟨1, by omega⟩))
    (hcycle₂ : (F.weighted (2 / (m : ℝ))).RepresentedBelow 0 ξ
      (consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩))
    (η : ∀ j, (laurentMaslovComplex (G j) K).homology 0)
    (c : ∀ j, (laurentMaslovComplex (G j) K).cycles 0)
    (hc : ∀ j, (laurentMaslovComplex (G j) K).homologyπ 0 (c j) = η j)
    (g : ι → ℝ)
    (hthreshold : ∀ j, ((g j * (2 / (m : ℝ)) / 2 : ℝ) : EReal) ≤
      ((laurentMaslovBifiltration (G j) K).weighted (2 / (m : ℝ))).spectralThreshold 0 (η j))
    (hclass : homologyMap φ 0 ξ = laurentFiniteNativeClass G c)
    (hgenus : (n : ℝ) * ((n : ℝ) + 1) / 2 - (∑ j, g j) + gCob =
      ((n : ℝ) + 1) - (M : ℝ)) :
    M ≤ m ∧ n + 1 + M ≤ 3 * m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht0 : 0 ≤ 2 / (m : ℝ) := by positivity
  have ht2 : 2 / (m : ℝ) ≤ 2 := (div_le_iff₀ hmR).mpr (by linarith)
  obtain ⟨ℓ, _, hℓclass, hℓlevel⟩ := exists_native_laurentFiniteTensor_dual_of_le G η
    (2 / (m : ℝ)) (fun j => g j * (2 / (m : ℝ)) / 2) ht0 ht2 hthreshold c hc
  apply Bifiltration.estimates_of_two_cycles_and_dual (gTr := ∑ j, g j) hφ 0 ξ n M m hn hm
    hcycle₁ hcycle₂ ℓ
  · intro z hz
    exact hℓclass z (hz.trans hclass)
  · intro s hs x hx
    apply hℓlevel s _ x hx
    simpa only [div_eq_mul_inv, ← Finset.sum_mul] using hs
  · exact hgenus

end OnLeConjecture.KnotFloer.GridFull
