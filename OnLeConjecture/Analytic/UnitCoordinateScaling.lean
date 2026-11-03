/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism
public import OnLeConjecture.Analytic.DiagonalCoordinates
public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# Multiplication of analytic coordinates by units

Multiplying each coordinate by an arbitrary analytic unit defines an
invertible pointed germ. The units may depend on all coordinates. The
proof uses their values at the origin to identify the differential.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Realize a tuple of germs as analytic coordinates when its differential
is a specified continuous linear equivalence. -/
theorem exists_equiv_with_coordinate_pullbacks
    {n : ℕ} (q : Fin n → Germ n)
    (hq : ∀ i, q i ∈ Germ.maximalIdeal n)
    (A : Source n ≃L[ℂ] Source n)
    (hD : ∀ i z, Germ.differential (q i) z = A z i) :
    ∃ e : PointedEquivGerm n,
      ∀ i, e.forward.pullbackRingHom (Germ.coordinate i) = q i := by
  obtain ⟨g, hg⟩ := exists_with_components q hq
  have hd : g.differential = (A : Source n →L[ℂ] Source n) := by
    ext z i
    have hi := hD i z
    rw [← hg i, MapGerm.germDifferential_component,
      MapGerm.componentDifferential_apply] at hi
    exact hi
  obtain ⟨e, he⟩ := g.exists_pointedEquivGerm_of_differential_eq A hd
  refine ⟨e, fun i => ?_⟩
  rw [he, pullback_coordinate, hg]

end PointedMapGerm

namespace Germ

/-- Arbitrary analytic unit multiples of the coordinate germs are again
analytic coordinates. -/
theorem exists_equiv_coordinate_mul_units
    {n : ℕ} (u : Fin n → Germ n) (hu : ∀ i, IsUnit (u i)) :
    ∃ e : PointedEquivGerm n,
      ∀ i, e.forward.pullbackRingHom (coordinate i) = coordinate i * u i := by
  let a : Fin n → ℂ := fun i => valueRingHom n (u i)
  have ha : ∀ i, a i ≠ 0 := fun i =>
    isUnit_iff_valueRingHom_ne_zero.mp (hu i)
  apply PointedMapGerm.exists_equiv_with_coordinate_pullbacks
    (fun i => coordinate i * u i)
    (fun i => (maximalIdeal n).mul_mem_right (u i) (coordinate_mem_maximalIdeal i))
    (diagonalContinuousLinearEquiv a ha)
  intro i z
  rw [differential_mul]
  simp [smul_apply, differential_coordinate_apply, a]

end Germ

namespace PointedEquivGerm

/-- Multiplication by units also preserves an arbitrary analytic coordinate
system. The units are specified in the original coordinates. -/
theorem exists_coordinate_mul_units
    {n : ℕ} (e : PointedEquivGerm n)
    (u : Fin n → Germ n) (hu : ∀ i, IsUnit (u i)) :
    ∃ e' : PointedEquivGerm n,
      ∀ i, e'.forward.pullbackRingHom (Germ.coordinate i) =
        e.forward.pullbackRingHom (Germ.coordinate i) * u i := by
  let v : Fin n → Germ n := fun i => e.inverse.pullbackRingHom (u i)
  have hv : ∀ i, IsUnit (v i) := fun i => (hu i).map e.inverse.pullbackRingHom
  obtain ⟨d, hd⟩ := Germ.exists_equiv_coordinate_mul_units v hv
  refine ⟨d.comp e, fun i => ?_⟩
  change (d.forward.comp e.forward).pullbackRingHom _ = _
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, hd, map_mul]
  have hinv : e.forward.pullbackRingHom (v i) = u i :=
    e.pullbackRingEquiv.apply_symm_apply (u i)
  rw [hinv]

end PointedEquivGerm

end OnLeConjecture.Analytic
