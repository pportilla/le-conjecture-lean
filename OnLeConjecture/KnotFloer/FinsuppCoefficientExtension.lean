/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.MatchingContraction

/-!
# Extending the coefficients of a finite free differential module

Applying a ring homomorphism to each matrix entry preserves addition, composition,
and the identity. Consequently a proved contracting homotopy extends to the new ring.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open Finsupp

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]

/-- Apply a coefficient homomorphism to every matrix entry in the distinguished finite basis. -/
noncomputable def coefficientExtension (φ : R →+* S) (f : Module.End R (ι →₀ R)) :
    Module.End S (ι →₀ S) :=
  Finsupp.linearCombination S fun i => (f (single i 1)).mapRange φ (map_zero φ)

omit [Fintype ι] in
@[simp]
theorem coefficientExtension_single_apply (φ : R →+* S) (f : Module.End R (ι →₀ R))
    (i j : ι) (a : S) : coefficientExtension φ f (single i a) j = a * φ (f (single i 1) j) := by
  simp [coefficientExtension]

/-- The matrix formula for any endomorphism of a finite free module. -/
theorem finiteEnd_apply_apply (f : Module.End R (ι →₀ R)) (c : ι →₀ R) (j : ι) :
    f c j = ∑ i : ι, c i * f (single i 1) j := by
  classical
  have hsingle (i : ι) (a : R) : f (single i a) = a • f (single i 1) := by
    rw [← Finsupp.smul_single_one, map_smul]
  conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
  simp only [Finsupp.sum, Finsupp.finsetSum_apply]
  calc
    ∑ i ∈ c.support, f (single i (c i)) j =
        ∑ i ∈ c.support, c i * f (single i 1) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsingle, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ i : ι, c i * f (single i 1) j :=
      Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [Finsupp.notMem_support_iff.mp hi, zero_mul]

/-- The extended operator acts by the extended matrix coefficients. -/
theorem coefficientExtension_apply_apply (φ : R →+* S) (f : Module.End R (ι →₀ R))
    (c : ι →₀ S) (j : ι) :
    coefficientExtension φ f c j = ∑ i : ι, c i * φ (f (single i 1) j) := by
  rw [finiteEnd_apply_apply]
  simp

omit [Fintype ι] in
/-- Extending the entries commutes with composition of actual linear operators. -/
theorem coefficientExtension_comp [Finite ι] (φ : R →+* S) (f g : Module.End R (ι →₀ R)) :
    coefficientExtension φ (f ∘ₗ g) = coefficientExtension φ f ∘ₗ coefficientExtension φ g := by
  classical
  let := Fintype.ofFinite ι
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro j
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [coefficientExtension_single_apply, one_mul, LinearMap.comp_apply,
    coefficientExtension_apply_apply, finiteEnd_apply_apply f (g (single i 1)) j]
  simp only [map_sum, map_mul, coefficientExtension_single_apply, one_mul]

/-- Coefficient extension is a ring homomorphism of endomorphism rings. -/
noncomputable def coefficientExtensionRingHom (φ : R →+* S) :
    Module.End R (ι →₀ R) →+* Module.End S (ι →₀ S) where
  toFun := coefficientExtension φ
  map_one' := by
    classical
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    apply Finsupp.ext
    intro j
    simp [coefficientExtension_single_apply, Finsupp.single_apply]
  map_mul' f g := coefficientExtension_comp φ f g
  map_zero' := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    apply Finsupp.ext
    intro j
    simp
  map_add' f g := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    apply Finsupp.ext
    intro j
    simp [mul_add]

@[simp]
theorem coefficientExtensionRingHom_apply (φ : R →+* S) (f : Module.End R (ι →₀ R)) :
    coefficientExtensionRingHom φ f = coefficientExtension φ f := rfl

end OnLeConjecture.KnotFloer
