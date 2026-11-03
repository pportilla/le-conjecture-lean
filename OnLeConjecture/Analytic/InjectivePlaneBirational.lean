/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteDoublePointNilpotence
public import OnLeConjecture.Analytic.TensorCoordinateBirational
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Locally injective plane germs are birational onto their analytic images

Analytic injectivity makes powers of the double-point coordinate differences
vanish in the relative tensor product of the source ring over its image ring.
The nilpotence theorem follows from the local analytic Nullstellensatz,
finite polynomial jets, and Krull intersection. The two copies therefore
agree under all generic embeddings into an algebraically closed field.
Characteristic zero then makes the generic degree one.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- Both source coordinates in a relative tensor product differ by nilpotent
elements when the analytic map is finite and locally injective. -/
theorem isNilpotent_tensor_coordinate_difference_of_finite_of_injective
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) (i : Fin n) :
    IsNilpotent (Germ.coordinate i ⊗ₜ[g.ImageRing] (1 : Germ n) -
      (1 : Germ n) ⊗ₜ[g.ImageRing] Germ.coordinate i) := by
  let S := Germ n ⊗[g.ImageRing] Germ n
  let : Module.Finite g.ImageRing (Germ n) := hf
  let : Module.Finite (Germ n) S := inferInstance
  let right : Germ n →ₐ[g.ImageRing] S := Algebra.TensorProduct.includeRight
  let ψ : Germ n →ₐ[ℂ] S :=
    { __ := right.toRingHom
      commutes' c := by
        let a : g.ImageRing := g.pullbackToImageRing (Germ.constRingHom m c)
        have ha : algebraMap g.ImageRing (Germ n) a = algebraMap ℂ (Germ n) c :=
          g.pullback_constRingHom c
        change right (algebraMap ℂ (Germ n) c) = algebraMap ℂ S c
        rw [← ha, right.commutes]
        change algebraMap g.ImageRing (Germ n) a ⊗ₜ[g.ImageRing] (1 : Germ n) =
          algebraMap ℂ (Germ n) c ⊗ₜ[g.ImageRing] (1 : Germ n)
        rw [ha] }
  have hagree (j : Fin m) :
      algebraMap (Germ n) S (g.1.component j) = ψ (g.1.component j) := by
    let a : g.ImageRing := g.pullbackToImageRing (Germ.coordinate j)
    have ha : algebraMap g.ImageRing (Germ n) a = g.1.component j :=
      g.pullback_coordinate j
    rw [← ha]
    exact DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := g.ImageRing) (A := Germ n) (B := Germ n)) a
  exact g.isNilpotent_coordinate_difference_of_finite_algebra hf hi ψ hagree i

/-- A finite plane germ with an injective representative is birational onto
its analytic image. -/
theorem isBirationalAtOrigin_of_finite_of_injective
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) : g.IsBirationalAtOrigin :=
  g.isBirationalAtOrigin_of_nilpotent_coordinate_differences hf
    (g.isNilpotent_tensor_coordinate_difference_of_finite_of_injective hf hi)

/-- Every locally injective plane germ is birational onto its analytic image. -/
theorem isBirationalAtOrigin_of_injective_two
    {m : ℕ} (g : PointedMapGerm 2 m) (hi : g.HasInjectiveRepresentative) :
    g.IsBirationalAtOrigin :=
  g.isBirationalAtOrigin_of_finite_of_injective (g.injective_isFiniteAtOrigin_two hi) hi

/-- Every source germ of an injective plane germ descends meromorphically
to the analytic image ring. -/
theorem hasMeromorphicDescent_of_injective_two
    {m : ℕ} (g : PointedMapGerm 2 m) (hi : g.HasInjectiveRepresentative) :
    g.HasMeromorphicDescent :=
  g.isBirationalAtOrigin_iff_hasMeromorphicDescent.mp (g.isBirationalAtOrigin_of_injective_two hi)

/-- Scalar source germs are fractions of pullbacks of target analytic germs. -/
theorem exists_pullback_quotient_of_injective_two
    {m : ℕ} (g : PointedMapGerm 2 m) (hi : g.HasInjectiveRepresentative)
    (a : Germ 2) :
    ∃ p q : Germ m, g.pullbackRingHom q ≠ 0 ∧
      g.pullbackRingHom q * a = g.pullbackRingHom p :=
  g.isBirationalAtOrigin_iff_pullback_crossMultiplication.mp
    (g.isBirationalAtOrigin_of_injective_two hi) a

end OnLeConjecture.Analytic.PointedMapGerm
