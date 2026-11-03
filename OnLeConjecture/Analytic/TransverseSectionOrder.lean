/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TransverseSourceCoordinates

/-!
# Constructed transverse sections with exact parameter order

The section is the restriction of the original map to the smooth zero
fiber of its first component, expressed in constructed source coordinates
and projected onto the other two target coordinates. Local injectivity
and the common-minor order formula apply to this same section.
-/

@[expose] public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

/-- Restriction to the first source coordinate hyperplane after a source
change, followed by projection to the last two target coordinates. -/
noncomputable def transverseRestriction (g : PointedMapGerm 2 3) (e : PointedEquivGerm 2) :
    PointedMapGerm 1 2 :=
  (hyperplaneTailGerm 2).comp (g.comp (e.forward.comp (hyperplaneInclusionGerm 1)))

theorem inclusion_comp_transverseRestriction
    (g : PointedMapGerm 2 3) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom (g.1.component 0) = coordinate 0) :
    (hyperplaneInclusionGerm 2).comp (g.transverseRestriction e) =
      g.comp (e.forward.comp (hyperplaneInclusionGerm 1)) := by
  apply hyperplaneInclusion_tail_comp_of_component_zero
  rw [component_comp_eq_pullback, pullbackRingHom_comp, RingHom.comp_apply, he]
  exact hyperplaneRestriction_coordinate_zero 1

theorem transverseRestriction_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom (g.1.component 0) = coordinate 0) :
    (g.transverseRestriction e).HasInjectiveRepresentative := by
  apply (hyperplaneInclusionGerm 2).hasInjectiveRepresentative_of_comp
  rw [inclusion_comp_transverseRestriction g e he]
  exact g.comp_hasInjectiveRepresentative _ hi
    (e.forward.comp_hasInjectiveRepresentative _ e.forward_hasInjectiveRepresentative
      (hyperplaneInclusionGerm_hasInjectiveRepresentative 1))

theorem transverseRestriction_component
    (g : PointedMapGerm 2 3) (e : PointedEquivGerm 2) (j : Fin 2) :
    (g.transverseRestriction e).1.component j =
      hyperplaneRestriction 1 (e.forward.pullbackRingHom (g.1.component j.succ)) := by
  have htail : (hyperplaneTailGerm 2).1.component j = coordinate j.succ := by
    apply Subtype.ext
    rfl
  rw [transverseRestriction, component_comp_eq_pullback, htail, pullback_coordinate,
    component_comp_eq_pullback, pullbackRingHom_comp]
  rfl

/-- A unit residual of the common Jacobian power determines the exact
parameter order of an explicitly constructed locally injective section. -/
theorem exists_injective_transverse_section_with_order
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (p u v w : Germ 2) (k : ℕ) (hp : p ∈ maximalIdeal 2)
    (hgp : IsUnit (jacobian (g.1.component 0) p))
    (h01 : jacobian (g.1.component 0) (g.1.component 1) = p ^ k * u)
    (h02 : jacobian (g.1.component 0) (g.1.component 2) = p ^ k * v)
    (h12 : jacobian (g.1.component 1) (g.1.component 2) = p ^ k * w)
    (hunit : IsUnit u ∨ IsUnit v ∨ IsUnit w) :
    ∃ (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
      e.forward.pullbackRingHom (g.1.component 0) = coordinate 0 ∧
      e.forward.pullbackRingHom p = coordinate 1 ∧
      (hyperplaneInclusionGerm 2).comp β =
        g.comp (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
      β.HasInjectiveRepresentative ∧
      min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) =
        (k + 1 : ℕ) := by
  have hmem (j : Fin 3) : g.1.component j ∈ maximalIdeal 2 :=
    g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal j)
  obtain ⟨e, he, hep, horder⟩ := exists_transverse_coordinates_and_order_of_jacobian_factors
    (g.1.component 0) (g.1.component 1) (g.1.component 2) p u v w k
    (hmem 0) (hmem 1) (hmem 2) hp hgp h01 h02 h12 hunit
  refine ⟨e, g.transverseRestriction e, he, hep,
    g.inclusion_comp_transverseRestriction e he,
    g.transverseRestriction_hasInjectiveRepresentative hi e he, ?_⟩
  simpa only [transverseRestriction_component,
    show (0 : Fin 2).succ = (1 : Fin 3) from rfl,
    show (1 : Fin 2).succ = (2 : Fin 3) from rfl] using horder

end OnLeConjecture.Analytic.PointedMapGerm
