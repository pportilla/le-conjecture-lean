/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Pullback order along parametrized plane curve germs

This file defines the order obtained by restricting a plane analytic function
germ to a pointed analytic curve parametrization. The definition depends on
the parametrization. Identifying it with ordinary local intersection
multiplicity requires an additional hypothesis that the parametrization is a
normalization parametrization. No such hypothesis is imposed here.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Pullback by a pointed analytic map reflects units. -/
theorem isUnit_pullbackRingHom_iff {n m : ℕ}
    (f : PointedMapGerm n m) {q : Germ m} :
    IsUnit (f.pullbackRingHom q) ↔ IsUnit q := by
  rw [Germ.isUnit_iff_valueRingHom_ne_zero,
    Germ.isUnit_iff_valueRingHom_ne_zero,
    PointedMapGerm.valueRingHom_pullback]

end PointedMapGerm

namespace Germ

/-- Every ring automorphism of the ring of analytic germs in one variable
preserves vanishing order. -/
theorem vanishingOrder_ringEquiv (e : Germ 1 ≃+* Germ 1) (q : Germ 1) :
    Germ.vanishingOrder (e q) = Germ.vanishingOrder q := by
  by_cases hq : q = 0
  · subst q
    simp only [map_zero, Germ.vanishingOrder_zero]
  · obtain ⟨n, u, hu, hfactor⟩ :=
      Germ.exists_eq_coordinate_pow_mul_unit hq
    have hcoordinate :
        Irreducible (e (Germ.coordinate (0 : Fin 1))) :=
      (MulEquiv.irreducible_iff e).mpr Germ.coordinate_zero_irreducible
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible
      (Germ 1) Germ.coordinate_zero_irreducible hcoordinate
    have huImage : IsUnit (e u) := hu.map e
    have hcoordinateOrder :
        Germ.vanishingOrder (e (Germ.coordinate (0 : Fin 1))) = 1 :=
      Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit v.isUnit
        (by simpa only [pow_one] using hv.symm)
    have hqOrder : Germ.vanishingOrder q = n :=
      Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    calc
      Germ.vanishingOrder (e q) =
          Germ.vanishingOrder
            (e (Germ.coordinate (0 : Fin 1)) ^ n * e u) := by
        rw [hfactor, map_mul, map_pow]
      _ = n • Germ.vanishingOrder
            (e (Germ.coordinate (0 : Fin 1))) +
          Germ.vanishingOrder (e u) := by
        rw [Germ.vanishingOrder_mul, Germ.vanishingOrder_pow]
      _ = n := by
        rw [hcoordinateOrder,
          Germ.vanishingOrder_eq_zero_iff_isUnit.mpr huImage]
        simp
      _ = Germ.vanishingOrder q := hqOrder.symm

end Germ

end OnLeConjecture.Analytic

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- The vanishing order of a plane analytic function germ after pullback by a
pointed analytic curve parametrization. This is a parametrization dependent
order. -/
noncomputable def pullbackIntersectionOrder
    (gamma : PointedMapGerm 1 2) (g : Germ 2) : ℕ∞ :=
  Germ.vanishingOrder (gamma.pullbackRingHom g)

@[simp]
theorem pullbackIntersectionOrder_zero (gamma : PointedMapGerm 1 2) :
    pullbackIntersectionOrder gamma 0 = ⊤ := by
  rw [pullbackIntersectionOrder, map_zero, Germ.vanishingOrder_zero]

@[simp]
theorem pullbackIntersectionOrder_one (gamma : PointedMapGerm 1 2) :
    pullbackIntersectionOrder gamma 1 = 0 := by
  rw [pullbackIntersectionOrder, map_one, Germ.vanishingOrder_one]

/-- The pullback order is infinite exactly when the pulled back germ is zero.
-/
theorem pullbackIntersectionOrder_eq_top_iff
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    pullbackIntersectionOrder gamma g = ⊤ ↔
      gamma.pullbackRingHom g = 0 := by
  exact Germ.vanishingOrder_eq_top_iff

/-- The pullback order is infinite exactly on the kernel of pullback. -/
theorem pullbackIntersectionOrder_eq_top_iff_mem_ker
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    pullbackIntersectionOrder gamma g = ⊤ ↔
      g ∈ RingHom.ker gamma.pullbackRingHom := by
  rw [pullbackIntersectionOrder_eq_top_iff, RingHom.mem_ker]

/-- The pullback order is not infinite exactly when the pulled back germ is
nonzero. -/
theorem pullbackIntersectionOrder_ne_top_iff
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    pullbackIntersectionOrder gamma g ≠ ⊤ ↔
      gamma.pullbackRingHom g ≠ 0 :=
  not_congr (pullbackIntersectionOrder_eq_top_iff gamma)

/-- The pullback order is strictly below infinity exactly when the pulled back
germ is nonzero. -/
theorem pullbackIntersectionOrder_lt_top_iff
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    pullbackIntersectionOrder gamma g < ⊤ ↔
      gamma.pullbackRingHom g ≠ 0 := by
  rw [lt_top_iff_ne_top, pullbackIntersectionOrder_ne_top_iff]

/-- The pullback order is finite exactly when the pulled back germ is nonzero.
-/
theorem pullbackIntersectionOrder_exists_nat_iff
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    (∃ n : ℕ, pullbackIntersectionOrder gamma g = (n : ℕ∞)) ↔
      gamma.pullbackRingHom g ≠ 0 := by
  constructor
  · rintro ⟨n, hn⟩ hzero
    have htop :=
      (pullbackIntersectionOrder_eq_top_iff gamma).mpr hzero
    exact ENat.natCast_ne_top n (hn.symm.trans htop)
  · intro hnonzero
    have hfinite : pullbackIntersectionOrder gamma g ≠ ⊤ :=
      (pullbackIntersectionOrder_ne_top_iff gamma).mpr hnonzero
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
    exact ⟨n, hn.symm⟩

/-- The order of a pulled back product is the sum of the two pullback orders.
-/
theorem pullbackIntersectionOrder_mul (gamma : PointedMapGerm 1 2)
    (g h : Germ 2) :
    pullbackIntersectionOrder gamma (g * h) =
      pullbackIntersectionOrder gamma g +
        pullbackIntersectionOrder gamma h := by
  simp only [pullbackIntersectionOrder, map_mul, Germ.vanishingOrder_mul]

/-- The order of a pulled back power is the corresponding multiple of the
pullback order. -/
theorem pullbackIntersectionOrder_pow (gamma : PointedMapGerm 1 2)
    (g : Germ 2) (n : ℕ) :
    pullbackIntersectionOrder gamma (g ^ n) =
      n • pullbackIntersectionOrder gamma g := by
  simp only [pullbackIntersectionOrder, map_pow, Germ.vanishingOrder_pow]

/-- A plane germ has pullback order zero exactly when it is a unit. -/
theorem pullbackIntersectionOrder_eq_zero_iff_isUnit
    (gamma : PointedMapGerm 1 2) {g : Germ 2} :
    pullbackIntersectionOrder gamma g = 0 ↔ IsUnit g := by
  rw [pullbackIntersectionOrder,
    Germ.vanishingOrder_eq_zero_iff_isUnit,
    gamma.isUnit_pullbackRingHom_iff]

/-- A unit has pullback order zero. -/
theorem pullbackIntersectionOrder_of_isUnit
    (gamma : PointedMapGerm 1 2) {g : Germ 2} (hg : IsUnit g) :
    pullbackIntersectionOrder gamma g = 0 :=
  (pullbackIntersectionOrder_eq_zero_iff_isUnit gamma).mpr hg

/-- An invertible analytic reparametrization of the source preserves pullback
order. -/
theorem pullbackIntersectionOrder_sourceEquiv
    (gamma : PointedMapGerm 1 2) (e : PointedEquivGerm 1) (g : Germ 2) :
    pullbackIntersectionOrder (gamma.comp e.forward) g =
      pullbackIntersectionOrder gamma g := by
  rw [pullbackIntersectionOrder, pullbackIntersectionOrder,
    PointedMapGerm.pullbackRingHom_comp]
  change Germ.vanishingOrder
      (e.pullbackRingEquiv (gamma.pullbackRingHom g)) =
    Germ.vanishingOrder (gamma.pullbackRingHom g)
  exact Germ.vanishingOrder_ringEquiv e.pullbackRingEquiv _

/-- Applying the forward plane equivalence to the parametrization and the
inverse pullback to the equation preserves pullback order. -/
theorem pullbackIntersectionOrder_targetEquiv
    (gamma : PointedMapGerm 1 2) (e : PointedEquivGerm 2) (g : Germ 2) :
    pullbackIntersectionOrder (e.forward.comp gamma)
        (e.pullbackRingEquiv.symm g) =
      pullbackIntersectionOrder gamma g := by
  rw [pullbackIntersectionOrder, pullbackIntersectionOrder,
    PointedMapGerm.pullbackRingHom_comp]
  change Germ.vanishingOrder
      (gamma.pullbackRingHom
        (e.pullbackRingEquiv (e.pullbackRingEquiv.symm g))) =
    Germ.vanishingOrder (gamma.pullbackRingHom g)
  rw [e.pullbackRingEquiv.apply_symm_apply]

end OnLeConjecture.PlaneCurve
