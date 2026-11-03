/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NilpotentDiagonalSurjectivity
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Uniqueness of primes from a nilpotent diagonal

Two residue fields above the same base prime have a nontrivial tensor
product over the base residue field. If an element belongs to one prime
but not the other, its two tensor images differ by a unit. Nilpotence of
the diagonal excludes this possibility.
-/

public noncomputable section

open scoped TensorProduct

namespace OnLeConjecture

/-- Every coordinate-free diagonal difference belongs to a nilpotent
diagonal ideal and is therefore nilpotent. -/
theorem tensor_differences_nilpotent_of_diagonalIdeal
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S)) (b : S) :
    IsNilpotent ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S)) := by
  obtain ⟨N, hN⟩ := hnil
  refine ⟨N, ?_⟩
  have h := Ideal.pow_mem_pow (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b) N
  rw [hN] at h
  exact h

/-- Nilpotent diagonal differences force comparable containment of primes
above the same base prime. -/
theorem prime_le_of_nilpotent_tensor_differences
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hnil : ∀ b : S, IsNilpotent ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S)))
    (p : Ideal R) [p.IsPrime] (q₁ q₂ : Ideal S) [q₁.IsPrime] [q₂.IsPrime]
    [q₁.LiesOver p] [q₂.LiesOver p] : q₁ ≤ q₂ := by
  let := Localization.AtPrime.algebraOfLiesOver p q₁
  let := Localization.AtPrime.algebraOfLiesOver p q₂
  let K := p.ResidueField
  let L₁ := q₁.ResidueField
  let L₂ := q₂.ResidueField
  let T := L₁ ⊗[K] L₂
  let : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    K L₁ L₂ (algebraMap K L₁).injective (algebraMap K L₂).injective
  let f : S →ₐ[R] T :=
    (Algebra.TensorProduct.includeLeft : L₁ →ₐ[K] T).restrictScalars R |>.comp
      (IsScalarTower.toAlgHom R S L₁)
  let g : S →ₐ[R] T :=
    (Algebra.TensorProduct.includeRight : L₂ →ₐ[K] T).restrictScalars R |>.comp
      (IsScalarTower.toAlgHom R S L₂)
  let Φ : S ⊗[R] S →ₐ[R] T :=
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all ..)
  intro b hb
  by_contra hb₂
  have hzero : f b = 0 := by
    change (Algebra.TensorProduct.includeLeft : L₁ →ₐ[K] T) (algebraMap S L₁ b) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hb, map_zero]
  have hunit : IsUnit (g b) := by
    exact (isUnit_iff_ne_zero.mpr
      (mt Ideal.algebraMap_residueField_eq_zero.mp hb₂)).map
        (Algebra.TensorProduct.includeRight : L₂ →ₐ[K] T)
  apply hunit.not_isNilpotent
  have h := (hnil b).map Φ
  simpa only [Φ, map_sub, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one,
    hzero, sub_zero] using h

/-- Nilpotent diagonal differences give a unique prime above each base
prime that has a prime above it. -/
theorem primesOver_eq_singleton_of_nilpotent_tensor_differences
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hnil : ∀ b : S, IsNilpotent ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S)))
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    p.primesOver S = {q} := by
  ext q'
  constructor
  · rintro ⟨hq', hqp⟩
    let := hq'
    let := hqp
    exact Set.mem_singleton_iff.mpr
      ((prime_le_of_nilpotent_tensor_differences R S hnil p q' q).antisymm
        (prime_le_of_nilpotent_tensor_differences R S hnil p q q'))
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

/-- A nilpotent diagonal gives exactly one prime above the contraction of
any prime of the extension ring. -/
theorem primesOver_eq_singleton_of_nilpotent_diagonal
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S))
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    p.primesOver S = {q} :=
  primesOver_eq_singleton_of_nilpotent_tensor_differences R S
    (tensor_differences_nilpotent_of_diagonalIdeal R S hnil) p q

namespace Analytic.PointedMapGerm

/-- A finite injective analytic germ induces unique primes above every
prime in its image ring that has a source prime above it. -/
theorem primesOver_eq_singleton_of_finite_of_injective
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative)
    (p : Ideal g.ImageRing) [p.IsPrime] (q : Ideal (Germ n)) [q.IsPrime]
    [q.LiesOver p] : p.primesOver (Germ n) = {q} :=
  primesOver_eq_singleton_of_nilpotent_diagonal g.ImageRing (Germ n)
    (g.isNilpotent_diagonalIdeal_of_finite_of_injective hf hi) p q

end Analytic.PointedMapGerm

end OnLeConjecture
