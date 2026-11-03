/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Domain
public import OnLeConjecture.Analytic.Pullback
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The analytic image ring of a map germ

The image ring of a pointed analytic map germ is the range of its pullback
homomorphism on scalar analytic germs. This realizes the analytic local ring
of the parametrized image as a subring of the source ring.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- The subring of source germs obtained by pulling back target germs. -/
noncomputable abbrev ImageRing {n m : ℕ} (f : PointedMapGerm n m) :=
  f.pullbackRingHom.range

/-- Pullback with codomain restricted to the image ring. -/
@[expose] noncomputable def pullbackToImageRing {n m : ℕ}
    (f : PointedMapGerm n m) : Germ m →+* f.ImageRing :=
  f.pullbackRingHom.codRestrict f.ImageRing fun q ↦ ⟨q, rfl⟩

@[simp]
theorem coe_pullbackToImageRing {n m : ℕ} (f : PointedMapGerm n m)
    (q : Germ m) :
    (f.pullbackToImageRing q : Germ n) = f.pullbackRingHom q :=
  rfl

/-- Every element of the image ring is represented by a target germ. -/
theorem pullbackToImageRing_surjective {n m : ℕ}
    (f : PointedMapGerm n m) :
    Function.Surjective f.pullbackToImageRing := by
  rintro ⟨q, r, hr⟩
  exact ⟨r, Subtype.ext hr⟩

/-- Evaluation at the origin on the image ring. -/
@[expose] noncomputable def imageValueRingHom {n m : ℕ}
    (f : PointedMapGerm n m) : f.ImageRing →+* ℂ :=
  Germ.valueRingHom n |>.comp f.ImageRing.subtype

@[simp]
theorem imageValueRingHom_apply {n m : ℕ} (f : PointedMapGerm n m)
    (q : f.ImageRing) :
    f.imageValueRingHom q = Germ.valueRingHom n (q : Germ n) :=
  rfl

@[simp]
theorem imageValueRingHom_pullback {n m : ℕ}
    (f : PointedMapGerm n m) (q : Germ m) :
    f.imageValueRingHom (f.pullbackToImageRing q) =
      Germ.valueRingHom m q := by
  rw [imageValueRingHom_apply, coe_pullbackToImageRing,
    PointedMapGerm.valueRingHom_pullback]

/-- Evaluation on the image ring is surjective. -/
theorem imageValueRingHom_surjective {n m : ℕ}
    (f : PointedMapGerm n m) :
    Function.Surjective f.imageValueRingHom := by
  intro c
  refine ⟨f.pullbackToImageRing (Germ.constRingHom m c), ?_⟩
  rw [imageValueRingHom_pullback, Germ.valueRingHom_const]

/-- The maximal ideal of the analytic image ring. -/
@[expose] noncomputable def imageMaximalIdeal {n m : ℕ}
    (f : PointedMapGerm n m) : Ideal f.ImageRing :=
  RingHom.ker f.imageValueRingHom

@[simp]
theorem mem_imageMaximalIdeal_iff {n m : ℕ}
    (f : PointedMapGerm n m) {q : f.ImageRing} :
    q ∈ f.imageMaximalIdeal ↔ f.imageValueRingHom q = 0 :=
  RingHom.mem_ker

/-- The kernel of evaluation is maximal in the image ring. -/
theorem imageMaximalIdeal_isMaximal {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.imageMaximalIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective f.imageValueRingHom
    f.imageValueRingHom_surjective

/-- An image-ring germ is a unit when its value at the origin is nonzero. -/
theorem image_isUnit_of_value_ne_zero {n m : ℕ}
    (f : PointedMapGerm n m) {q : f.ImageRing}
    (hq : f.imageValueRingHom q ≠ 0) : IsUnit q := by
  rcases f.pullbackToImageRing_surjective q with ⟨r, rfl⟩
  have hr : Germ.valueRingHom m r ≠ 0 := by
    simpa only [imageValueRingHom_pullback] using hq
  exact (Germ.isUnit_of_valueRingHom_ne_zero hr).map f.pullbackToImageRing

/-- A unit of the image ring has nonzero value at the origin. -/
theorem image_value_ne_zero_of_isUnit {n m : ℕ}
    (f : PointedMapGerm n m) {q : f.ImageRing}
    (hq : IsUnit q) : f.imageValueRingHom q ≠ 0 :=
  isUnit_iff_ne_zero.mp (hq.map f.imageValueRingHom)

/-- The analytic image ring is a local ring. -/
noncomputable instance instImageRingIsLocalRing {n m : ℕ}
    (f : PointedMapGerm n m) : IsLocalRing f.ImageRing :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun q ↦ by
    by_cases hq : f.imageValueRingHom q = 0
    · right
      apply f.image_isUnit_of_value_ne_zero
      rw [map_sub, map_one, hq, sub_zero]
      exact one_ne_zero
    · left
      exact f.image_isUnit_of_value_ne_zero hq

/-- The pullback to the image ring takes the target maximal ideal onto the
maximal ideal of the image ring. -/
theorem comap_imageMaximalIdeal {n m : ℕ}
    (f : PointedMapGerm n m) :
    Ideal.comap f.pullbackToImageRing f.imageMaximalIdeal =
      Germ.maximalIdeal m := by
  ext q
  rw [Ideal.mem_comap, mem_imageMaximalIdeal_iff,
    imageValueRingHom_pullback, Germ.mem_maximalIdeal_iff]

/-- The image maximal ideal is the image of the target maximal ideal. -/
theorem map_maximalIdeal_eq_imageMaximalIdeal {n m : ℕ}
    (f : PointedMapGerm n m) :
    Ideal.map f.pullbackToImageRing (Germ.maximalIdeal m) =
      f.imageMaximalIdeal := by
  rw [← f.comap_imageMaximalIdeal]
  exact Ideal.map_comap_of_surjective f.pullbackToImageRing
    f.pullbackToImageRing_surjective f.imageMaximalIdeal

/-- Extending the image maximal ideal to the source gives the coordinate
ideal of the map germ. -/
theorem map_imageMaximalIdeal_eq_coordinateIdeal {n m : ℕ}
    (f : PointedMapGerm n m) :
    Ideal.map f.ImageRing.subtype f.imageMaximalIdeal =
      f.1.coordinateIdeal := by
  rw [← f.map_maximalIdeal_eq_imageMaximalIdeal, Ideal.map_map]
  have hcomp :
      f.ImageRing.subtype.comp f.pullbackToImageRing =
        f.pullbackRingHom := by
    ext q
    rfl
  rw [hcomp, f.map_maximalIdeal_eq_coordinateIdeal]

/-- The explicitly defined image maximal ideal is the maximal ideal supplied
by the local ring instance. -/
theorem imageMaximalIdeal_eq_isLocalRing {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.imageMaximalIdeal = IsLocalRing.maximalIdeal f.ImageRing :=
  IsLocalRing.eq_maximalIdeal f.imageMaximalIdeal_isMaximal

/-- A pointed analytic map germ is finite at the origin when its source
analytic local ring is finite as a module over its image ring. -/
@[expose] def IsFiniteAtOrigin {n m : ℕ} (f : PointedMapGerm n m) : Prop :=
  Module.Finite f.ImageRing (Germ n)

end PointedMapGerm

end OnLeConjecture.Analytic
