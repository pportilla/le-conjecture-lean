/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteCoordinateGeneration
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent coordinate differences and birationality

Two algebra homomorphisms into a reduced ring agree on an element when its
two copies differ by a nilpotent in the relative tensor product. For a
finite plane germ, the source coordinates generate the source algebra over
the image ring. Nilpotence of their tensor differences therefore makes all
generic field embeddings agree and proves birationality.

This is the algebraic step. The nilpotence of these differences is an
explicit hypothesis here, to be supplied from local analytic injectivity.
-/

public section

open scoped TensorProduct

namespace OnLeConjecture

/-- Nilpotent differences in a relative tensor product are invisible to any
two algebra homomorphisms into a reduced commutative ring. -/
theorem algHom_eq_of_nilpotent_tensor_difference
    {A B K : Type*} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] [IsReduced K]
    (σ τ : B →ₐ[A] K) (b : B)
    (h : IsNilpotent (b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b)) : σ b = τ b := by
  let φ : B ⊗[A] B →ₐ[A] K :=
    Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)
  have hz := isNilpotent_iff_eq_zero.mp (h.map φ)
  have hsub : σ b - τ b = 0 := by
    simpa [φ, Algebra.TensorProduct.lift_tmul] using hz
  exact sub_eq_zero.mp hsub

namespace Analytic.PointedMapGerm

set_option maxHeartbeats 400000 in
-- The scalar towers include the image field, source field, and algebraic closure.
/-- For a finite plane germ, nilpotent tensor differences of its two source
coordinates imply uniqueness of the generic field embedding. -/
theorem hasUniqueGenericEmbedding_of_nilpotent_coordinate_differences
    {m : ℕ} (f : PointedMapGerm 2 m) (hfinite : f.IsFiniteAtOrigin)
    (hnil : ∀ j : Fin 2, IsNilpotent
      (Germ.coordinate j ⊗ₜ[f.ImageRing] (1 : Germ 2) -
        (1 : Germ 2) ⊗ₜ[f.ImageRing] Germ.coordinate j)) :
    f.HasUniqueGenericEmbedding := by
  let _ : Algebra (FractionRing f.ImageRing) (FractionRing (Germ 2)) :=
    f.genericFractionFieldAlgebra
  let _ : IsScalarTower f.ImageRing (Germ 2) (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing) (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap x).symm
  unfold HasUniqueGenericEmbedding
  change Subsingleton (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ 2)))
  refine ⟨fun σ τ => ?_⟩
  let σSource : Germ 2 →ₐ[f.ImageRing] AlgebraicClosure (FractionRing (Germ 2)) :=
    AlgHom.comp ((AlgHomClass.toAlgHom σ).restrictScalars f.ImageRing)
      (IsScalarTower.toAlgHom f.ImageRing (Germ 2) (FractionRing (Germ 2)))
  let τSource : Germ 2 →ₐ[f.ImageRing] AlgebraicClosure (FractionRing (Germ 2)) :=
    AlgHom.comp ((AlgHomClass.toAlgHom τ).restrictScalars f.ImageRing)
      (IsScalarTower.toAlgHom f.ImageRing (Germ 2) (FractionRing (Germ 2)))
  by_contra hne
  obtain ⟨j, hj⟩ := f.exists_coordinate_separating_generic_embeddings hfinite σ τ hne
  exact hj (algHom_eq_of_nilpotent_tensor_difference σSource τSource (Germ.coordinate j) (hnil j))

/-- The same nilpotence condition gives a birational finite plane germ. -/
theorem isBirationalAtOrigin_of_nilpotent_coordinate_differences
    {m : ℕ} (f : PointedMapGerm 2 m) (hfinite : f.IsFiniteAtOrigin)
    (hnil : ∀ j : Fin 2, IsNilpotent
      (Germ.coordinate j ⊗ₜ[f.ImageRing] (1 : Germ 2) -
        (1 : Germ 2) ⊗ₜ[f.ImageRing] Germ.coordinate j)) :
    f.IsBirationalAtOrigin :=
  (f.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin hfinite).mpr
    (f.hasUniqueGenericEmbedding_of_nilpotent_coordinate_differences hfinite hnil)

end Analytic.PointedMapGerm

end OnLeConjecture
