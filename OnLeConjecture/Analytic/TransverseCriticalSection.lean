/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CriticalCurveTangent
public import OnLeConjecture.Analytic.InjectivityFactor
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction

/-!
# Analytic sections transverse to a rank-one image tangent

A target coordinate whose pullback is smooth defines a smooth source
section. Straightening its pullback gives an explicit parametrization of
that section. At a critical point the restriction to the two remaining
target coordinates has zero differential and remains locally injective.
-/

@[expose] public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

/-- A germ with zero first component factors through the coordinate
hyperplane using the actual projection to the remaining coordinates. -/
theorem hyperplaneInclusion_tail_comp_of_component_zero
    {n m : ℕ} (f : PointedMapGerm n (m + 1)) (hf : f.1.component 0 = 0) :
    (hyperplaneInclusionGerm m).comp ((hyperplaneTailGerm m).comp f) = f := by
  obtain ⟨F, hF, hF0, rfl⟩ := f.exists_ofFunction
  have hzero : ∀ᶠ x in 𝓝 (0 : Source n), F x 0 = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun a : Germ n => a.1) hf)
  rw [hyperplaneInclusionGerm, hyperplaneTailGerm, comp_ofFunction, comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hzero] with x hx
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [Function.comp_apply, hyperplaneInclusion_apply_zero] using hx.symm
  · simp only [Function.comp_apply, hyperplaneInclusion_apply_succ, hyperplaneTail_apply]

/-- A transverse hyperplane restriction at a critical point is constructed
from a source analytic equivalence. Its differential vanishes, and local
injectivity is inherited from the original plane map. -/
theorem exists_injective_transverse_section_of_first_component_smooth
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (hs : Germ.differential (g.1.component 0) ≠ 0)
    (hc : ∀ i j : Fin 3,
      g.differential (coordinateVector 0) i * g.differential (coordinateVector 1) j -
        g.differential (coordinateVector 1) i * g.differential (coordinateVector 0) j = 0) :
    ∃ (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
      e.forward.pullbackRingHom (g.1.component 0) = coordinate 0 ∧
      (hyperplaneInclusionGerm 2).comp β =
        g.comp (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
      β.HasInjectiveRepresentative ∧ β.differential = 0 := by
  have hmem := g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal 0)
  obtain ⟨e, he⟩ := PlaneCurve.exists_equiv_pullback_eq_coordinate (g.1.component 0) hmem hs
  change e.forward.pullbackRingHom (g.1.component 0) = coordinate 0 at he
  let γ := e.forward.comp (hyperplaneInclusionGerm 1)
  let f := g.comp γ
  let β := (hyperplaneTailGerm 2).comp f
  have hfzero : f.1.component 0 = 0 := by
    rw [show f = g.comp γ from rfl, component_comp_eq_pullback]
    rw [show γ = e.forward.comp (hyperplaneInclusionGerm 1) from rfl,
      pullbackRingHom_comp, RingHom.comp_apply, he]
    exact hyperplaneRestriction_coordinate_zero 1
  have hfactor : (hyperplaneInclusionGerm 2).comp β = f :=
    f.hyperplaneInclusion_tail_comp_of_component_zero hfzero
  have hγi : γ.HasInjectiveRepresentative :=
    e.forward.comp_hasInjectiveRepresentative (hyperplaneInclusionGerm 1)
      e.forward_hasInjectiveRepresentative (hyperplaneInclusionGerm_hasInjectiveRepresentative 1)
  have hfi : f.HasInjectiveRepresentative := g.comp_hasInjectiveRepresentative γ hi hγi
  have hβi : β.HasInjectiveRepresentative :=
    (hyperplaneInclusionGerm 2).hasInjectiveRepresentative_of_comp β (hfactor ▸ hfi)
  obtain ⟨v, hv⟩ : ∃ v : Source 2, g.differential v 0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hs
    rw [MapGerm.germDifferential_component]
    ext v
    exact h v
  have hvne : g.differential v ≠ 0 := by
    intro h
    exact hv (congrFun h 0)
  have hrange := range_eq_span_of_plane_minors_zero g.differential v hvne hc
  have hfdzero : f.differential = 0 := by
    have hfirst := congrArg Germ.differential hfzero
    rw [MapGerm.germDifferential_component, Germ.differential_zero] at hfirst
    apply ContinuousLinearMap.ext
    intro u
    have hfirstu : f.differential u 0 = 0 := congrArg (fun L : Source 1 →L[ℂ] ℂ => L u) hfirst
    have hfu : f.differential u = g.differential (γ.differential u) := by
      rw [show f = g.comp γ from rfl, differential_comp]
      rfl
    have hmemrange : f.differential u ∈ LinearMap.range g.differential.toLinearMap :=
      ⟨γ.differential u, hfu.symm⟩
    rw [hrange, Submodule.mem_span_singleton] at hmemrange
    obtain ⟨a, ha⟩ := hmemrange
    have ha0 : a = 0 := by
      have h := congrFun ha 0
      simp only [Pi.smul_apply, smul_eq_mul, hfirstu] at h
      exact (mul_eq_zero.mp h).resolve_right hv
    simpa only [ha0, zero_smul, zero_apply] using ha.symm
  refine ⟨e, β, he, hfactor, hβi, ?_⟩
  rw [show β = (hyperplaneTailGerm 2).comp f from rfl, differential_comp, hfdzero]
  exact ContinuousLinearMap.comp_zero _

end PointedMapGerm

end OnLeConjecture.Analytic
