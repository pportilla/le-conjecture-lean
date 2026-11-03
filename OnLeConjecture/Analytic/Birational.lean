/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Birational finite analytic map germs

The image ring of a pointed map germ is a domain contained in the source germ
ring. This module constructs the induced homomorphism between their fraction
fields. Birationality at the origin means that this homomorphism is
surjective. A finite map makes the source ring integral over the image ring.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- The inclusion of the analytic image ring into the fraction field of the
source germ ring. -/
@[expose]
noncomputable def imageToSourceFractionRingHom {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.ImageRing →+* FractionRing (Germ n) :=
  (algebraMap (Germ n) (FractionRing (Germ n))).comp
    f.ImageRing.subtype

/-- The inclusion of the image ring into the source fraction field is
injective. -/
theorem imageToSourceFractionRingHom_injective {n m : ℕ}
    (f : PointedMapGerm n m) :
    Function.Injective f.imageToSourceFractionRingHom := by
  exact (IsFractionRing.injective (Germ n) (FractionRing (Germ n))).comp
    f.ImageRing.subtype_injective

/-- The homomorphism between the fraction fields induced by inclusion of the
analytic image ring into the source ring. -/
@[expose]
noncomputable def fractionFieldMap {n m : ℕ}
    (f : PointedMapGerm n m) :
    FractionRing f.ImageRing →+* FractionRing (Germ n) :=
  IsFractionRing.lift f.imageToSourceFractionRingHom_injective

/-- The fraction field homomorphism agrees with the original inclusion on the
image ring. -/
@[simp]
theorem fractionFieldMap_algebraMap {n m : ℕ}
    (f : PointedMapGerm n m) (a : f.ImageRing) :
    f.fractionFieldMap (algebraMap f.ImageRing
      (FractionRing f.ImageRing) a) =
        algebraMap (Germ n) (FractionRing (Germ n)) (a : Germ n) := by
  exact IsFractionRing.lift_algebraMap
    f.imageToSourceFractionRingHom_injective a

/-- The induced homomorphism of fraction fields is injective. -/
theorem fractionFieldMap_injective {n m : ℕ}
    (f : PointedMapGerm n m) :
    Function.Injective f.fractionFieldMap :=
  RingHom.injective f.fractionFieldMap

/-- A pointed map germ is birational at the origin when the inclusion of its
image ring induces a surjection onto the source fraction field. -/
@[expose]
def IsBirationalAtOrigin {n m : ℕ} (f : PointedMapGerm n m) : Prop :=
  Function.Surjective f.fractionFieldMap

/-- Birationality identifies the two fraction fields as rings. -/
@[expose]
noncomputable def fractionFieldEquiv {n m : ℕ}
    (f : PointedMapGerm n m) (hbirational : f.IsBirationalAtOrigin) :
    FractionRing f.ImageRing ≃+* FractionRing (Germ n) :=
  RingEquiv.ofBijective f.fractionFieldMap
    ⟨f.fractionFieldMap_injective, hbirational⟩

@[simp]
theorem fractionFieldEquiv_apply {n m : ℕ}
    (f : PointedMapGerm n m) (hbirational : f.IsBirationalAtOrigin)
    (x : FractionRing f.ImageRing) :
    f.fractionFieldEquiv hbirational x = f.fractionFieldMap x :=
  rfl

/-- A finite pointed map makes the source germ ring integral over its image
ring. -/
theorem isIntegral_source_of_isFiniteAtOrigin {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) :
    Algebra.IsIntegral f.ImageRing (Germ n) := by
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  infer_instance

/-- If the source germ ring is integrally closed, a finite map realizes it as
the integral closure of the image ring inside the source fraction field. -/
theorem source_isIntegralClosure_of_isFiniteAtOrigin {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin)
    [IsIntegrallyClosed (Germ n)] :
    IsIntegralClosure (Germ n) f.ImageRing (FractionRing (Germ n)) := by
  let _ : Module.Finite f.ImageRing (Germ n) := hfinite
  infer_instance

end PointedMapGerm

end OnLeConjecture.Analytic
