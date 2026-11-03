/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NilpotentDiagonalPrimes
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Residue fields of an algebra with nilpotent diagonal

Nilpotent diagonal differences make every two residue-field embeddings
agree. The induced residue-field extension is therefore purely inseparable.
At an unramified prime it is also separable, so its algebra map is surjective.
-/

public noncomputable section

open scoped TensorProduct

namespace OnLeConjecture

/-- Nilpotent diagonal differences imply that residue-field extensions are
purely inseparable. -/
theorem isPurelyInseparable_residueField_of_nilpotent_diagonal
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S))
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    IsPurelyInseparable p.ResidueField q.ResidueField := by
  rw [isPurelyInseparable_iff_subsingleton_emb]
  refine ⟨fun σ τ => ?_⟩
  let σS : S →ₐ[R] AlgebraicClosure q.ResidueField :=
    ((AlgHomClass.toAlgHom σ).restrictScalars R).comp
      (IsScalarTower.toAlgHom R S q.ResidueField)
  let τS : S →ₐ[R] AlgebraicClosure q.ResidueField :=
    ((AlgHomClass.toAlgHom τ).restrictScalars R).comp
      (IsScalarTower.toAlgHom R S q.ResidueField)
  apply AlgHom.coe_ringHom_injective
  apply Ideal.ResidueField.ringHom_ext
  ext b
  exact algHom_eq_of_nilpotent_tensor_difference σS τS b
    (by simpa only [neg_sub] using
      (tensor_differences_nilpotent_of_diagonalIdeal R S hnil b).neg)

/-- The residue-field map is surjective at an unramified prime when the
diagonal ideal is nilpotent. -/
theorem residueField_algebraMap_surjective_of_nilpotent_diagonal
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S))
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [Algebra.IsUnramifiedAt R q] :
    Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
  let _ := isPurelyInseparable_residueField_of_nilpotent_diagonal R S hnil p q
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    p.ResidueField q.ResidueField

/-- At every unramified prime, a finite algebra with nilpotent diagonal has
surjective localization map. -/
theorem localRingHom_surjective_of_finite_of_nilpotent_diagonal
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (hnil : IsNilpotent (KaehlerDifferential.ideal R S))
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [Algebra.IsUnramifiedAt R q] :
    Function.Surjective (Localization.localRingHom p q (algebraMap R S) (q.over_def p)) :=
  Localization.localRingHom_surjective_of_primesOver_eq_singleton
    (primesOver_eq_singleton_of_nilpotent_diagonal R S hnil p q)
    (residueField_algebraMap_surjective_of_nilpotent_diagonal R S hnil p q)

end OnLeConjecture
