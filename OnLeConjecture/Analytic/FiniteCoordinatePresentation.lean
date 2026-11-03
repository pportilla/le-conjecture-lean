/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteCoordinateGeneration
public import OnLeConjecture.Analytic.PlaneIntegralPrimitiveElement

/-!
# Coordinate presentations of finite analytic map germs

The source germ ring of a finite analytic map germ is a quotient of the
polynomial ring over the image ring whose variables map to the source
coordinates. Every generic field embedding sends the source coordinates to
a tuple satisfying all relations in this presentation.

For a finite nonbirational plane map, two such tuples are distinct. This is
an algebraic statement about the generic fibre. It does not realize either
tuple by points of a holomorphic representative.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- The polynomial presentation that sends each variable to the
corresponding source coordinate germ. -/
noncomputable def sourceCoordinatePresentation
    {n m : ℕ} (f : PointedMapGerm n m) :
    MvPolynomial (Fin n) f.ImageRing →ₐ[f.ImageRing] Germ n :=
  MvPolynomial.aeval Germ.coordinate

@[simp]
theorem sourceCoordinatePresentation_X
    {n m : ℕ} (f : PointedMapGerm n m) (j : Fin n) :
    f.sourceCoordinatePresentation (MvPolynomial.X j) =
      Germ.coordinate j := by
  simp only [sourceCoordinatePresentation, MvPolynomial.aeval_X]

/-- For a finite map germ, the coordinate presentation is surjective. -/
theorem sourceCoordinatePresentation_surjective_of_isFiniteAtOrigin
    {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) :
    Function.Surjective f.sourceCoordinatePresentation := by
  rw [← AlgHom.range_eq_top,
    sourceCoordinatePresentation,
    MvPolynomial.aeval_range]
  exact f.coordinateAdjoin_eq_top_of_isFiniteAtOrigin hfinite

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- Every generic field embedding sends the source coordinates to a tuple
satisfying each relation in the coordinate presentation. -/
theorem genericEmbedding_satisfies_coordinate_relation
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∀ (sigma : Field.Emb (FractionRing f.ImageRing)
        (FractionRing (Germ 2)))
      (p : MvPolynomial (Fin 2) f.ImageRing),
      f.sourceCoordinatePresentation p = 0 →
        MvPolynomial.aeval
          (fun j => sigma
            (algebraMap (Germ 2) (FractionRing (Germ 2))
              (Germ.coordinate j))) p = 0 := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  let _ : Module.Finite f.ImageRing (Germ 2) := hfinite
  let _ : FaithfulSMul f.ImageRing (Germ 2) :=
    (faithfulSMul_iff_algebraMap_injective
      f.ImageRing (Germ 2)).mpr f.ImageRing.subtype_injective
  let _ : Module.IsTorsionFree f.ImageRing (Germ 2) :=
    (Module.isTorsionFree_iff_algebraMap_injective).2
      f.ImageRing.subtype_injective
  let _ : IsScalarTower f.ImageRing (Germ 2)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let _ : IsScalarTower f.ImageRing (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (f.fractionFieldMap_algebraMap x).symm
  change ∀ (sigma : Field.Emb (FractionRing f.ImageRing)
      (FractionRing (Germ 2)))
    (p : MvPolynomial (Fin 2) f.ImageRing),
    f.sourceCoordinatePresentation p = 0 →
      MvPolynomial.aeval
        (fun j => sigma
          (algebraMap (Germ 2) (FractionRing (Germ 2))
            (Germ.coordinate j))) p = 0
  intro sigma p hp
  let sourceToClosure : Germ 2 →ₐ[f.ImageRing]
      AlgebraicClosure (FractionRing (Germ 2)) :=
    AlgHom.comp
      ((AlgHomClass.toAlgHom sigma).restrictScalars f.ImageRing)
      (IsScalarTower.toAlgHom f.ImageRing (Germ 2)
        (FractionRing (Germ 2)))
  have hmapped : sourceToClosure
      (f.sourceCoordinatePresentation p) = 0 := by
    rw [hp, map_zero]
  change sourceToClosure
      (MvPolynomial.aeval Germ.coordinate p) = 0 at hmapped
  rw [MvPolynomial.comp_aeval_apply] at hmapped
  exact hmapped

set_option maxHeartbeats 500000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- A finite nonbirational plane map has two distinct generic coordinate
tuples, and both tuples satisfy every relation in the coordinate
presentation. -/
theorem exists_distinct_generic_coordinate_solutions_of_not_birational
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
        (FractionRing (Germ 2)),
      (∃ j : Fin 2,
        sigma
            (algebraMap (Germ 2) (FractionRing (Germ 2))
              (Germ.coordinate j)) ≠
          tau
            (algebraMap (Germ 2) (FractionRing (Germ 2))
              (Germ.coordinate j))) ∧
      ∀ p : MvPolynomial (Fin 2) f.ImageRing,
        f.sourceCoordinatePresentation p = 0 →
          MvPolynomial.aeval
              (fun j => sigma
                (algebraMap (Germ 2) (FractionRing (Germ 2))
                  (Germ.coordinate j))) p = 0 ∧
            MvPolynomial.aeval
              (fun j => tau
                (algebraMap (Germ 2) (FractionRing (Germ 2))
                  (Germ.coordinate j))) p = 0 := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  change ∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
      (FractionRing (Germ 2)),
    (∃ j : Fin 2,
      sigma
          (algebraMap (Germ 2) (FractionRing (Germ 2))
            (Germ.coordinate j)) ≠
        tau
          (algebraMap (Germ 2) (FractionRing (Germ 2))
            (Germ.coordinate j))) ∧
    ∀ p : MvPolynomial (Fin 2) f.ImageRing,
      f.sourceCoordinatePresentation p = 0 →
        MvPolynomial.aeval
            (fun j => sigma
              (algebraMap (Germ 2) (FractionRing (Germ 2))
                (Germ.coordinate j))) p = 0 ∧
          MvPolynomial.aeval
            (fun j => tau
              (algebraMap (Germ 2) (FractionRing (Germ 2))
                (Germ.coordinate j))) p = 0
  obtain ⟨sigma, tau, hne⟩ :=
    f.exists_distinct_generic_embeddings_of_isFiniteAtOrigin_of_not_isBirationalAtOrigin
      hfinite hnot
  obtain ⟨j, hj⟩ :=
    f.exists_coordinate_separating_generic_embeddings
      hfinite sigma tau hne
  refine ⟨sigma, tau, ⟨j, hj⟩, fun p hp => ⟨?_, ?_⟩⟩
  · exact f.genericEmbedding_satisfies_coordinate_relation
      hfinite sigma p hp
  · exact f.genericEmbedding_satisfies_coordinate_relation
      hfinite tau p hp

end PointedMapGerm

end OnLeConjecture.Analytic
