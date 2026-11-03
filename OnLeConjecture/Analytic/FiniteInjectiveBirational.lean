/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.InjectivePlaneBirational
public import OnLeConjecture.Analytic.CurveFinite

/-!
# Birationality of finite injective analytic germs in every source dimension

The analytic double-point theorem proves that the two copies of each source
coordinate differ by a nilpotent in the relative tensor product. The source
coordinates generate the finite source algebra over the image ring. Hence
all generic field embeddings agree, and characteristic zero makes the
extension have degree one.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic.PointedMapGerm

set_option maxHeartbeats 400000 in
-- The algebra structures on the two fraction fields require additional elaboration.
/-- A finite analytic germ with an injective representative has a unique generic embedding. -/
theorem hasUniqueGenericEmbedding_of_finite_of_injective
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) : g.HasUniqueGenericEmbedding := by
  let _ : Algebra (FractionRing g.ImageRing) (FractionRing (Germ n)) :=
    g.genericFractionFieldAlgebra
  let _ : IsScalarTower g.ImageRing (Germ n) (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let _ : IsScalarTower g.ImageRing (FractionRing g.ImageRing) (FractionRing (Germ n)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (g.fractionFieldMap_algebraMap x).symm
  change Subsingleton (Field.Emb (FractionRing g.ImageRing) (FractionRing (Germ n)))
  refine ⟨fun σ τ => ?_⟩
  let σSource : Germ n →ₐ[g.ImageRing] AlgebraicClosure (FractionRing (Germ n)) :=
    AlgHom.comp ((AlgHomClass.toAlgHom σ).restrictScalars g.ImageRing)
      (IsScalarTower.toAlgHom g.ImageRing (Germ n) (FractionRing (Germ n)))
  let τSource : Germ n →ₐ[g.ImageRing] AlgebraicClosure (FractionRing (Germ n)) :=
    AlgHom.comp ((AlgHomClass.toAlgHom τ).restrictScalars g.ImageRing)
      (IsScalarTower.toAlgHom g.ImageRing (Germ n) (FractionRing (Germ n)))
  have hsource : σSource = τSource := by
    apply AlgHom.ext_of_adjoin_eq_top (g.coordinateAdjoin_eq_top_of_isFiniteAtOrigin hf)
    rintro _ ⟨j, rfl⟩
    exact algHom_eq_of_nilpotent_tensor_difference σSource τSource (Germ.coordinate j)
      (g.isNilpotent_tensor_coordinate_difference_of_finite_of_injective hf hi j)
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Germ n)
  intro f
  exact AlgHom.congr_fun hsource f

/-- Finiteness and local injectivity imply birationality in every source dimension. -/
theorem isBirationalAtOrigin_of_finite_of_injective_any_dimension
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative) : g.IsBirationalAtOrigin :=
  (g.isBirationalAtOrigin_iff_hasUniqueGenericEmbedding_of_isFiniteAtOrigin hf).mpr
    (g.hasUniqueGenericEmbedding_of_finite_of_injective hf hi)

/-- Every locally injective analytic curve is birational onto its image. -/
theorem isBirationalAtOrigin_of_injective_curve {m : ℕ} (g : PointedMapGerm 1 m)
    (hi : g.HasInjectiveRepresentative) : g.IsBirationalAtOrigin :=
  g.isBirationalAtOrigin_of_finite_of_injective_any_dimension
    (g.isFiniteAtOrigin_of_injective_curve hi) hi

/-- Every scalar source germ of an injective curve descends meromorphically to the image. -/
theorem hasMeromorphicDescent_of_injective_curve {m : ℕ} (g : PointedMapGerm 1 m)
    (hi : g.HasInjectiveRepresentative) : g.HasMeromorphicDescent :=
  g.isBirationalAtOrigin_iff_hasMeromorphicDescent.mp (g.isBirationalAtOrigin_of_injective_curve hi)

end OnLeConjecture.Analytic.PointedMapGerm
