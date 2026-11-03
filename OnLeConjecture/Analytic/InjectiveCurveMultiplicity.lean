/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveNormalizationOrder
public import OnLeConjecture.Analytic.IntersectionParametrizationMultiplicity

/-!
# Multiplicity of the image of an injective analytic curve

The minimum component order of every injective plane-curve parametrization
equals the maximal-ideal order of its irreducible image equation. Finiteness,
birationality, the image equation, and normalization comparison are proved
inputs, not additional hypotheses on the parametrization.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.PointedMapGerm

/-- The exact order of an irreducible equation equals the minimum component order
of any injective parametrization annihilating it. -/
theorem min_component_orders_eq_equation_order_of_injective_curve
    (g : PointedMapGerm 1 2) (hg : g.HasInjectiveRepresentative)
    (f : Germ 2) (hirr : Irreducible f) (hgf : g.pullbackRingHom f = 0)
    (m : ℕ) (hf : f ∈ Germ.maximalIdeal 2 ^ m)
    (hnext : f ∉ Germ.maximalIdeal 2 ^ (m + 1)) :
    min (Germ.vanishingOrder (g.1.component 0))
      (Germ.vanishingOrder (g.1.component 1)) = m := by
  obtain ⟨P, hP⟩ := exists_injective_intersectionParametrization_of_irreducible f hirr
  have hker : RingHom.ker P.map.pullbackRingHom = RingHom.ker g.pullbackRingHom := by
    rw [Germ.parametrization_kernel_eq_span_singleton f hirr P.map P.curve_eq_zero P.nonconstant,
      Germ.parametrization_kernel_eq_span_singleton f hirr g hgf
        (g.exists_nonzero_coordinate_pullback_of_injective_curve hg)]
  have horder (i : Fin 2) : Germ.vanishingOrder (P.map.1.component i) =
      Germ.vanishingOrder (g.1.component i) := by
    simpa only [pullback_coordinate] using
      P.map.vanishingOrder_pullback_eq_of_injective_of_kernel_eq g hP hg hker (Germ.coordinate i)
  rw [← horder 0, ← horder 1]
  exact P.min_component_orders_eq_equation_order hirr m hf hnext

/-- A finite minimum component order gives an irreducible image equation of that exact order. -/
theorem exists_irreducible_image_equation_of_order
    (g : PointedMapGerm 1 2) (hg : g.HasInjectiveRepresentative) (m : ℕ)
    (horder : min (Germ.vanishingOrder (g.1.component 0))
      (Germ.vanishingOrder (g.1.component 1)) = m) :
    ∃ f : Germ 2, Irreducible f ∧ g.pullbackRingHom f = 0 ∧
      RingHom.ker g.pullbackRingHom = Ideal.span {f} ∧
      f ∈ Germ.maximalIdeal 2 ^ m ∧ f ∉ Germ.maximalIdeal 2 ^ (m + 1) := by
  obtain ⟨f, hirr, _, hzero, hker⟩ := g.exists_irreducible_equation_of_injective_curve hg
  obtain ⟨d, hd, hnext⟩ := Germ.exists_exact_maximalIdeal_order_of_ne_zero f hirr.ne_zero
  have hdm : d = m := by
    exact ENat.natCast_inj.mp
      ((g.min_component_orders_eq_equation_order_of_injective_curve
        hg f hirr hzero d hd hnext).symm.trans horder)
  subst d
  exact ⟨f, hirr, hzero, hker, hd, hnext⟩

end OnLeConjecture.Analytic.PointedMapGerm
