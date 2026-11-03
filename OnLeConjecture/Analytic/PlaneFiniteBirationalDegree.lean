/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectiveBirationalReduction
public import OnLeConjecture.Analytic.PlaneIntegralClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Generic degree of finite plane map germs

The fraction field of the source is a finite extension of the fraction field
of the analytic image ring when the map germ is finite. Its degree equals the
module rank of the source germ ring over the image ring.

In characteristic zero, this degree is the number of embeddings of the source
fraction field into its algebraic closure over the image fraction field. Thus
a finite map germ is birational exactly when this embedding is unique. For a
plane source, the remaining injective to birational implication is equivalent
to proving that local analytic injectivity gives this uniqueness.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- The algebra structure on the source fraction field induced by the
inclusion of the analytic image ring in the source germ ring. -/
noncomputable abbrev genericFractionFieldAlgebra {n m : ℕ}
    (f : PointedMapGerm n m) :
    Algebra (FractionRing f.ImageRing) (FractionRing (Germ n)) :=
  f.fractionFieldMap.toAlgebra

/-- The degree of the source fraction field over the image fraction field. -/
noncomputable def GenericDegree {n m : ℕ}
    (f : PointedMapGerm n m) : ℕ :=
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  Module.finrank (FractionRing f.ImageRing) (FractionRing (Germ n))

/-- The source fraction field has at most one embedding into its algebraic
closure over the image fraction field. -/
@[expose] def HasUniqueGenericEmbedding {n m : ℕ}
    (f : PointedMapGerm n m) : Prop :=
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  Subsingleton
    (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ n)))

/-- A finite map germ induces a finite extension of fraction fields. -/
theorem genericFractionField_moduleFinite_of_isFiniteAtOrigin
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
    Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  let _ : FaithfulSMul f.ImageRing (Germ n) :=
    (faithfulSMul_iff_algebraMap_injective f.ImageRing (Germ n)).mpr
      f.ImageRing.subtype_injective
  let _ : Module.IsTorsionFree f.ImageRing (Germ n) :=
    (Module.isTorsionFree_iff_algebraMap_injective).2
      f.ImageRing.subtype_injective
  let _ : IsScalarTower f.ImageRing (Germ n)
      (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
      (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap a).symm
  apply Module.finite_of_finrank_pos
  rw [IsFractionRing.finrank_eq f.ImageRing
    (FractionRing f.ImageRing) (Germ n) (FractionRing (Germ n))]
  exact Module.finrank_pos

/-- For a finite map germ, the generic degree equals the module rank of the
source germ ring over the image ring. -/
theorem genericDegree_eq_source_finrank_of_isFiniteAtOrigin
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    f.GenericDegree = Module.finrank f.ImageRing (Germ n) := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  let _ : FaithfulSMul f.ImageRing (Germ n) :=
    (faithfulSMul_iff_algebraMap_injective f.ImageRing (Germ n)).mpr
      f.ImageRing.subtype_injective
  let _ : IsScalarTower f.ImageRing (Germ n)
      (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
      (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap a).symm
  change Module.finrank (FractionRing f.ImageRing)
      (FractionRing (Germ n)) = Module.finrank f.ImageRing (Germ n)
  exact IsFractionRing.finrank_eq f.ImageRing
    (FractionRing f.ImageRing) (Germ n) (FractionRing (Germ n))

/-- Birationality is equivalent to generic degree one. -/
theorem isBirationalAtOrigin_iff_genericDegree_eq_one
    {n m : ℕ} (f : PointedMapGerm n m) :
    f.IsBirationalAtOrigin ↔ f.GenericDegree = 1 := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  let _ : Module.Free (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := Module.Free.of_divisionRing _ _
  change Function.Surjective f.fractionFieldMap ↔
    Module.finrank (FractionRing f.ImageRing)
      (FractionRing (Germ n)) = 1
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
  rw [RingHom.algebraMap_toAlgebra]
  exact (and_iff_right f.fractionFieldMap_injective).symm

/-- A finite map germ is birational exactly when its generic field embedding
is unique. -/
theorem isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    f.IsBirationalAtOrigin ↔ f.HasUniqueGenericEmbedding := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite (FractionRing f.ImageRing)
      (FractionRing (Germ n)) :=
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite
  let _ : CharZero (FractionRing (Germ n)) :=
    charZero_of_injective_ringHom
      (RingHom.injective
        (algebraMap ℂ (FractionRing (Germ n))))
  let _ : CharZero (FractionRing f.ImageRing) :=
    ⟨fun a b hab => by
      apply CharZero.cast_injective (R := FractionRing (Germ n))
      simpa only [map_natCast] using congrArg f.fractionFieldMap hab⟩
  let _ : Algebra.IsAlgebraic (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := inferInstance
  let _ : Algebra.IsSeparable (FractionRing f.ImageRing)
      (FractionRing (Germ n)) := inferInstance
  rw [f.isBirationalAtOrigin_iff_genericDegree_eq_one]
  change Module.finrank (FractionRing f.ImageRing)
      (FractionRing (Germ n)) = 1 ↔
    Subsingleton
      (Field.Emb (FractionRing f.ImageRing) (FractionRing (Germ n)))
  rw [← Field.finSepDegree_eq_finrank_of_isSeparable]
  rw [Field.finSepDegree, Nat.card_eq_one_iff_unique]
  exact and_iff_left inferInstance

/-- For a finite plane map, the source is the integral closure of the image
ring and the induced extension of fraction fields is finite. -/
theorem plane_source_isIntegralClosure_and_genericFractionField_finite
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin) :
    IsIntegralClosure (Germ 2) f.ImageRing (FractionRing (Germ 2)) ∧
      let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
      Module.Finite (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := by
  exact ⟨f.source_isIntegralClosure_of_isFiniteAtOrigin hfinite,
    f.genericFractionField_moduleFinite_of_isFiniteAtOrigin hfinite⟩

/-- Meromorphic descent is equivalent to uniqueness of the generic field
embedding for a finite map germ. -/
theorem hasMeromorphicDescent_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    f.HasMeromorphicDescent ↔ f.HasUniqueGenericEmbedding :=
  f.isBirationalAtOrigin_iff_hasMeromorphicDescent.symm.trans
    (f.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
      hfinite)

/-- Local injectivity of a finite map germ gives uniqueness of its generic
field embedding. -/
@[expose] def FiniteInjectiveImpliesUniqueGenericEmbedding
    (n m : ℕ) : Prop :=
  ∀ f : PointedMapGerm n m,
    f.IsFiniteAtOrigin → f.HasInjectiveRepresentative →
      f.HasUniqueGenericEmbedding

/-- The existing finite injective descent principle implies uniqueness of the
generic field embedding. -/
theorem finiteInjectiveImpliesUniqueGenericEmbedding_of_meromorphicDescent
    {n m : ℕ}
    (hdescent : FiniteInjectiveImpliesMeromorphicDescent n m) :
    FiniteInjectiveImpliesUniqueGenericEmbedding n m := by
  intro f hfinite hinjective
  apply
    (f.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
      hfinite).1
  exact isBirationalAtOrigin_of_finite_of_injective_of_descent
    hdescent f hfinite hinjective

/-- Local injectivity of a plane map germ gives uniqueness of its generic
field embedding. -/
@[expose] def PlaneInjectiveImpliesUniqueGenericEmbedding (m : ℕ) : Prop :=
  ∀ f : PointedMapGerm 2 m,
    f.HasInjectiveRepresentative → f.HasUniqueGenericEmbedding

/-- For a plane source, finite injective meromorphic descent is equivalent to
uniqueness of the generic field embedding for injective representatives. -/
theorem finiteInjective_meromorphicDescent_two_iff_uniqueGenericEmbedding
    (m : ℕ) :
    (∀ f : PointedMapGerm 2 m,
      f.IsFiniteAtOrigin → f.HasInjectiveRepresentative →
        f.HasMeromorphicDescent) ↔
      PlaneInjectiveImpliesUniqueGenericEmbedding m := by
  constructor
  · intro hdescent f hinjective
    have hfinite := f.injective_isFiniteAtOrigin_two hinjective
    exact
      (f.hasMeromorphicDescent_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
        hfinite).1 (hdescent f hfinite hinjective)
  · intro hembedding f _hfinite hinjective
    have hfinite := f.injective_isFiniteAtOrigin_two hinjective
    exact
      (f.hasMeromorphicDescent_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
        hfinite).2 (hembedding f hinjective)

/-- The existing finite injective descent principle for a plane source
implies uniqueness of the generic field embedding. -/
theorem planeInjectiveImpliesUniqueGenericEmbedding_of_meromorphicDescent
    {m : ℕ}
    (hdescent : FiniteInjectiveImpliesMeromorphicDescent 2 m) :
    PlaneInjectiveImpliesUniqueGenericEmbedding m := by
  intro f hinjective
  have hfinite := f.injective_isFiniteAtOrigin_two hinjective
  exact
    (f.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
      hfinite).1
      (isBirationalAtOrigin_of_finite_of_injective_of_descent
        hdescent f hfinite hinjective)

/-- Uniqueness of the generic field embedding for injective plane
representatives gives meromorphic descent. -/
theorem hasMeromorphicDescent_two_of_injective_of_planeUniqueGenericEmbedding
    {m : ℕ} (hembedding : PlaneInjectiveImpliesUniqueGenericEmbedding m)
    (f : PointedMapGerm 2 m)
    (hinjective : f.HasInjectiveRepresentative) :
    f.HasMeromorphicDescent := by
  have hfinite := f.injective_isFiniteAtOrigin_two hinjective
  exact
    (f.hasMeromorphicDescent_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin
      hfinite).2 (hembedding f hinjective)

/-- Uniqueness of the generic field embedding for injective plane
representatives gives birationality. -/
theorem isBirationalAtOrigin_two_of_injective_of_planeUniqueGenericEmbedding
    {m : ℕ} (hembedding : PlaneInjectiveImpliesUniqueGenericEmbedding m)
    (f : PointedMapGerm 2 m)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsBirationalAtOrigin :=
  (f.isBirationalAtOrigin_iff_hasMeromorphicDescent).2
    (hasMeromorphicDescent_two_of_injective_of_planeUniqueGenericEmbedding
      hembedding f hinjective)

end PointedMapGerm

end OnLeConjecture.Analytic
