/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionHoleImageTangent
public import OnLeConjecture.Analytic.InjectiveCompositionCancellation

/-! # Comparison with the retained transverse section branch

An immersed parametrization of the regular source level factors through
the earlier transverse coordinates by an invertible one-variable analytic
germ. Consequently its image parametrization has the same pullback kernel.
-/

@[expose] public noncomputable section

open Function

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

/-- The source reparametrization is constructed from the transverse
coordinate inverse and its second coordinate. Its invertibility follows
from the immersed source parametrization. -/
theorem exists_sectionBranch_sourceEquiv
    (h : PointedMapGerm 2 3) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom (h.1.component 0) = coordinate 0)
    (β : PointedMapGerm 1 2)
    (hβ : (hyperplaneInclusionGerm 2).comp β =
      h.comp (e.forward.comp (hyperplaneInclusionGerm 1)))
    (γ : PointedMapGerm 1 2) (hγ : Injective γ.differential)
    (hzero : γ.pullbackRingHom (h.1.component 0) = 0) :
    ∃ α : PointedEquivGerm 1,
      γ = (e.forward.comp (hyperplaneInclusionGerm 1)).comp α.forward ∧
      h.sectionBranch γ = β.comp α.forward := by
  let k := e.inverse.comp γ
  let a := (hyperplaneTailGerm 1).comp k
  have hei : e.inverse.pullbackRingHom (coordinate 0) = h.1.component 0 := by
    have hc := congrArg e.inverse.pullbackRingHom he
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv (h.1.component 0)) =
      e.inverse.pullbackRingHom (coordinate 0) at hc
    exact (e.pullbackRingEquiv.symm_apply_apply _).symm.trans hc |>.symm
  have hk0 : k.1.component 0 = 0 := by
    rw [show k = e.inverse.comp γ from rfl, component_comp_eq_pullback,
      ← pullback_coordinate, hei, hzero]
  have hfact : γ = (e.forward.comp (hyperplaneInclusionGerm 1)).comp a := by
    rw [comp_assoc, show (hyperplaneInclusionGerm 1).comp a = k from
      k.hyperplaneInclusion_tail_comp_of_component_zero hk0]
    dsimp only [k]
    rw [← comp_assoc, e.forward_inverse, identity_comp]
  have hai : Injective a.differential := by
    intro v w hvw
    apply hγ
    rw [hfact, differential_comp]
    exact congrArg (e.forward.comp (hyperplaneInclusionGerm 1)).differential hvw
  have hab : Bijective a.differential :=
    ⟨hai, (LinearMap.injective_iff_surjective).mp hai⟩
  obtain ⟨α, hα⟩ := a.exists_pointedEquivGerm_of_differential_bijective hab
  refine ⟨α, hα.symm ▸ hfact, ?_⟩
  apply (hyperplaneInclusionGerm_hasInjectiveRepresentative 2).comp_left_cancel
  rw [h.inclusion_comp_sectionBranch γ hzero, ← comp_assoc, hβ, comp_assoc, ← comp_assoc]
  rw [hα, comp_assoc, ← hfact]

/-- An immersed source-level parametrization gives precisely the same
kernel as the earlier transverse branch, via the derived source equivalence. -/
theorem sectionBranch_kernel_eq_of_source_immersion
    (h : PointedMapGerm 2 3) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom (h.1.component 0) = coordinate 0)
    (β : PointedMapGerm 1 2)
    (hβ : (hyperplaneInclusionGerm 2).comp β =
      h.comp (e.forward.comp (hyperplaneInclusionGerm 1)))
    (γ : PointedMapGerm 1 2) (hγ : Injective γ.differential)
    (hzero : γ.pullbackRingHom (h.1.component 0) = 0) :
    RingHom.ker (h.sectionBranch γ).pullbackRingHom = RingHom.ker β.pullbackRingHom := by
  obtain ⟨α, _, hα⟩ := h.exists_sectionBranch_sourceEquiv e he β hβ γ hγ hzero
  rw [hα, pullbackRingHom_comp]
  exact RingHom.ker_comp_of_injective β.pullbackRingHom α.pullbackRingEquiv.injective

end PointedMapGerm
end OnLeConjecture.Analytic
