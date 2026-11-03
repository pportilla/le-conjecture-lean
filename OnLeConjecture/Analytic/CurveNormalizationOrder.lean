/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NormalizationComparison
public import OnLeConjecture.Analytic.InjectiveIntersectionParametrization
public import OnLeConjecture.Analytic.CurveImageEquation

/-!
# Intersection orders for every injective plane-curve parametrization

Two injective parametrizations with equal kernel induce an equivalence of
their source discrete valuation rings. Ring equivalences preserve the
valuation. Consequently the intersection-order formula constructed by
resolution holds for every injective parametrization of the same branch.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Every automorphism of the analytic discrete valuation ring preserves vanishing order. -/
theorem vanishingOrder_ringEquiv (e : Germ 1 ≃+* Germ 1) (f : Germ 1) :
    vanishingOrder (e f) = vanishingOrder f := by
  by_cases hf : f = 0
  · simp only [hf, map_zero]
  obtain ⟨d, u, hu, hfactor⟩ := exists_eq_coordinate_pow_mul_unit hf
  have hassoc : Associated (e (coordinate 0)) (coordinate (0 : Fin 1)) :=
    IsDiscreteValuationRing.associated_of_irreducible (Germ 1)
      ((MulEquiv.irreducible_iff e.toMulEquiv).mpr coordinate_zero_irreducible)
      coordinate_zero_irreducible
  have hecoord : vanishingOrder (e (coordinate 0)) = 1 := by
    rw [← vanishingOrder_coordinate]
    exact le_antisymm (vanishingOrder_le_iff_dvd.mpr hassoc.dvd)
      (vanishingOrder_le_iff_dvd.mpr hassoc.symm.dvd)
  have heunit : vanishingOrder (e u) = 0 :=
    vanishingOrder_eq_zero_iff_isUnit.mpr (hu.map e.toRingHom)
  rw [hfactor, map_mul, map_pow, vanishingOrder_mul, vanishingOrder_pow,
    hecoord, heunit, add_zero,
    vanishingOrder_mul, vanishingOrder_coordinate_pow,
    vanishingOrder_eq_zero_iff_isUnit.mpr hu, add_zero, nsmul_one]

end Germ

namespace PointedMapGerm

/-- Two injective curve parametrizations with equal kernel give identical orders
for all pullbacks. -/
theorem vanishingOrder_pullback_eq_of_injective_of_kernel_eq {m : ℕ}
    (f g : PointedMapGerm 1 m) (hf : f.HasInjectiveRepresentative)
    (hg : g.HasInjectiveRepresentative)
    (hker : RingHom.ker f.pullbackRingHom = RingHom.ker g.pullbackRingHom) (q : Germ m) :
    Germ.vanishingOrder (f.pullbackRingHom q) = Germ.vanishingOrder (g.pullbackRingHom q) := by
  obtain ⟨e, he⟩ := f.exists_normalization_ringEquiv g
    (f.isFiniteAtOrigin_of_injective_curve hf) (g.isFiniteAtOrigin_of_injective_curve hg)
    (f.isBirationalAtOrigin_of_injective_curve hf)
    (g.isBirationalAtOrigin_of_injective_curve hg) hker
  rw [← he q, Germ.vanishingOrder_ringEquiv]

/-- Every injective parametrization of an irreducible branch computes its finite intersections. -/
theorem intersectionMultiplicity_eq_pullback_order_of_injective_curve
    (g : PointedMapGerm 1 2) (hg : g.HasInjectiveRepresentative)
    (f : Germ 2) (hf : Irreducible f) (hgf : g.pullbackRingHom f = 0)
    (q : Germ 2) (hq : PlaneCurve.HasFiniteIntersection f q) :
    PlaneCurve.intersectionMultiplicity f q hq =
      (Germ.vanishingOrder (g.pullbackRingHom q)).toNat := by
  obtain ⟨P, hP⟩ := exists_injective_intersectionParametrization_of_irreducible f hf
  have hker : RingHom.ker P.map.pullbackRingHom = RingHom.ker g.pullbackRingHom := by
    rw [Germ.parametrization_kernel_eq_span_singleton f hf P.map P.curve_eq_zero P.nonconstant,
      Germ.parametrization_kernel_eq_span_singleton f hf g hgf
        (g.exists_nonzero_coordinate_pullback_of_injective_curve hg)]
  rw [P.intersection_order q hq,
    P.map.vanishingOrder_pullback_eq_of_injective_of_kernel_eq g hP hg hker q]

end PointedMapGerm
end OnLeConjecture.Analytic
