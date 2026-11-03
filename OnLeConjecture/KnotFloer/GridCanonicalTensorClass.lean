/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalClass
public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorCertificate
public import Mathlib.Algebra.Field.ZMod

/-!
# Canonical classes in a finite tensor of native grid complexes

The normalized class has a polynomial cycle representative constructed
from the proved image criterion. These cycles define the selected finite
tensor class without additional cycle or nonvanishing hypotheses. This
does not identify the tensor with a geometric connected sum.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {n : ℕ}

/-- A polynomial representative of the unique normalized grid class. -/
def gridCanonicalCycle (G : GridDiagram n) (hn : 2 ≤ n) :
    (laurentMaslovComplex G (ZMod 2)).cycles 0 :=
  ((mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G ⟨0, by omega⟩ 0 _).mp
    (gridCanonicalClass_mem_polynomialImage G hn ⟨0, by omega⟩)).choose

/-- The constructed cycle represents the normalized class. -/
theorem gridCanonicalCycle_class (G : GridDiagram n) (hn : 2 ≤ n) :
    (laurentMaslovComplex G (ZMod 2)).homologyπ 0 (gridCanonicalCycle G hn) =
      gridCanonicalClass G hn :=
  ((mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G ⟨0, by omega⟩ 0 _).mp
    (gridCanonicalClass_mem_polynomialImage G hn ⟨0, by omega⟩)).choose_spec.2

/-- Every exponent in the selected representative is nonnegative. -/
theorem gridCanonicalCycle_nonnegative (G : GridDiagram n) (hn : 2 ≤ n)
    (x : GridState n) (k : ℤ)
    (hk : k ∈ ((laurentMaslovChainEquiv G (ZMod 2) 0
      ((laurentMaslovComplex G (ZMod 2)).iCycles 0 (gridCanonicalCycle G hn)) :
        LaurentChain (ZMod 2) n) x).coeff.support) : 0 ≤ k :=
  ((mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2) G ⟨0, by omega⟩ 0 _).mp
    (gridCanonicalClass_mem_polynomialImage G hn ⟨0, by omega⟩)).choose_spec.1 x k hk

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {sizes : ι → ℕ} (G : ∀ i, GridDiagram (sizes i)) (hn : ∀ i, 2 ≤ sizes i)

/-- The finite pure tensor class of the actual normalized grid classes. -/
def gridCanonicalFiniteTensorClass :
    (laurentFiniteMaslovComplex (K := ZMod 2) G).homology 0 :=
  laurentFiniteNativeClass G (fun i => gridCanonicalCycle (G i) (hn i))

/-- The selected tensor class is nonzero, including the empty tensor. -/
theorem gridCanonicalFiniteTensorClass_ne_zero :
    gridCanonicalFiniteTensorClass G hn ≠ 0 := by
  exact laurentFiniteNativeClass_ne_zero G (fun i => gridCanonicalClass (G i) (hn i))
    0 (fun _ => 0) le_rfl (by norm_num)
    (fun i => by simpa using gridCanonicalClass_spectralThreshold_zero (G i) (hn i))
    (fun i => gridCanonicalCycle (G i) (hn i)) (fun i => gridCanonicalCycle_class (G i) (hn i))

end OnLeConjecture.KnotFloer.GridFull
