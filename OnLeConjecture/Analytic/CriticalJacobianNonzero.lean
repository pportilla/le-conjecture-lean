/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericFiniteCompanion
public import OnLeConjecture.Analytic.FinitePlaneJacobian
public import OnLeConjecture.Analytic.JacobianLinearSpan
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness

/-!
# Nonzero coordinate minors of finite plane germs

A finite-colength pointed family admits two constant linear combinations
with finite intersection. Their Jacobian is nonzero, so the coordinate
Jacobians cannot all vanish. In particular, the common Jacobian divisor
of an injective plane germ is a nonzero germ.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- A finite-colength pointed family has a nonzero coordinate Jacobian. -/
theorem exists_jacobian_ne_zero_of_finite_colength
    {ι : Type*} [Finite ι] (F : ι → Germ 2)
    (hpointed : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    ∃ i j, jacobian (F i) (F j) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := exists_generator_not_dvd_of_finite_colength F hfinite 0
    (not_isUnit_zero)
  have hFi : F i ≠ 0 := by simpa only [zero_dvd_iff] using hi
  obtain ⟨V, _hVopen, ⟨q, hq⟩, _hVU, hV⟩ :=
    exists_open_finite_companion_linear_combinations
      (fun _ : Unit => F i) (fun _ => hFi) (fun _ => F) (fun _ => hfinite)
      Set.univ isOpen_univ Set.univ_nonempty
  have hJ := jacobian_ne_zero_of_hasFiniteIntersection (F i)
    (germLinearCombination F q) (hpointed i)
    (germLinearCombination_mem F (maximalIdeal 2) hpointed q) (hV q hq ())
  by_contra hall
  push Not at hall
  apply hJ
  apply zero_dvd_iff.mp
  apply dvd_jacobian_of_mem_linear_span F 0
    (fun j k => zero_dvd_iff.mpr (hall j k))
    (Submodule.subset_span (Set.mem_range_self i))
  change (∑ j, q j • F j) ∈ Submodule.span ℂ (Set.range F)
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j)))

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

/-- Finite coordinate fibre forces generic differential rank two. -/
theorem exists_jacobian_ne_zero_of_finiteCoordinateFiber
    {m : ℕ} (g : PointedMapGerm 2 m) (hfinite : g.HasFiniteCoordinateFiber) :
    ∃ i j, jacobian (g.1.component i) (g.1.component j) ≠ 0 := by
  apply exists_jacobian_ne_zero_of_finite_colength g.1.component
    (fun i => g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal i))
  have hI : g.1.coordinateIdeal = Ideal.span (Set.range g.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      exact fun i => Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact g.1.component_mem_coordinateIdeal i
  rw [← hI]
  exact hfinite

/-- A locally injective plane germ has a nonzero coordinate minor. -/
theorem exists_jacobian_ne_zero_of_injective
    {m : ℕ} (g : PointedMapGerm 2 m) (hinjective : g.HasInjectiveRepresentative) :
    ∃ i j, jacobian (g.1.component i) (g.1.component j) ≠ 0 :=
  g.exists_jacobian_ne_zero_of_finiteCoordinateFiber
    (g.coordinateQuotient_moduleFinite (g.injective_isFiniteAtOrigin_two hinjective))

end OnLeConjecture.Analytic.PointedMapGerm
