/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoordinateOrder
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.CoordinatePermutation
public import OnLeConjecture.Analytic.OrderTwoPreparation
public import OnLeConjecture.Analytic.Injectivity

/-!
# Coordinate order normalization

For a finite plane map germ, one component has order equal to the order of the
coordinate ideal. A linear source change makes that component regular in the
first source coordinate with the same order, and a linear target change moves
it to the first target coordinate.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Linear source and target changes make the first component regular with
order equal to the order of the coordinate ideal. -/
theorem exists_rightLeft_firstComponent_regularInCoordinateOrder
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin) :
    ∃ source : PointedEquivGerm 2,
      ∃ target : PointedEquivGerm (n + 1),
        Germ.IsRegularInFirstCoordinateOfOrder
          ((target.forward.comp
            (g.comp source.forward)).1.component 0)
          (g.coordinateOrder (by omega) hfinite) := by
  obtain ⟨i, hiNext⟩ :=
    g.exists_component_not_mem_maximalIdeal_pow_coordinateOrder_add_one
      (by omega) hfinite
  have hiOrder :=
    g.component_mem_maximalIdeal_pow_coordinateOrder
      (by omega) hfinite i
  obtain ⟨source, hregular⟩ :=
    Germ.exists_linear_equiv_regularInFirstCoordinateOfOrder
      hiOrder hiNext
  let target : PointedEquivGerm (n + 1) :=
    coordinateSwapPointedEquiv i
  refine ⟨source, target, ?_⟩
  have hinner :
      (g.comp source.forward).1.component i =
        source.forward.pullbackRingHom (g.1.component i) :=
    g.component_comp_general source.forward i
  have houter :
      (target.forward.comp (g.comp source.forward)).1.component 0 =
        (g.comp source.forward).1.component i := by
    exact coordinateSwap_comp_component_zero i
      (g.comp source.forward)
  rw [houter, hinner]
  exact hregular

/-- A finite plane map germ is right left equivalent to a finite germ whose
first component is regular with order equal to the original coordinate
order. -/
theorem exists_rightLeftEquivalent_firstComponent_regularInCoordinateOrder
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin) :
    ∃ h : PointedMapGerm 2 (n + 1),
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        Germ.IsRegularInFirstCoordinateOfOrder
          (h.1.component 0) (g.coordinateOrder (by omega) hfinite) := by
  obtain ⟨source, target, hregular⟩ :=
    g.exists_rightLeft_firstComponent_regularInCoordinateOrder hfinite
  let h : PointedMapGerm 2 (n + 1) :=
    target.forward.comp (g.comp source.forward)
  have hequivalent : g.RightLeftEquivalent h :=
    ⟨source, target, rfl⟩
  have hhfinite : h.IsFiniteAtOrigin :=
    hequivalent.isFiniteAtOrigin_iff.mpr hfinite
  exact ⟨h, hequivalent, hhfinite, hregular⟩

/-- If the coordinate ideal has order two, the first component can be made
regular of order two and admits analytic Weierstrass preparation. -/
theorem exists_rightLeftEquivalent_firstComponent_orderTwoPreparation
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by omega) hfinite = 2) :
    ∃ h : PointedMapGerm 2 (n + 1),
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        Germ.HasAnalyticWeierstrassFactorizationOfOrder
          (h.1.component 0) 2 := by
  obtain ⟨h, hequivalent, hhfinite, hregular⟩ :=
    g.exists_rightLeftEquivalent_firstComponent_regularInCoordinateOrder
      hfinite
  have hregularTwo : Germ.IsRegularInFirstCoordinateOfOrder
      (h.1.component 0) 2 := by
    simpa only [horder] using hregular
  exact ⟨h, hequivalent, hhfinite,
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_two hregularTwo⟩

/-- An injective germ with zero differential and coordinate order two can be
replaced by a right left equivalent germ with the same two properties and a
prepared first component of order two. -/
theorem exists_prepared_orderTwo_counterexample
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (hinjective : g.HasInjectiveRepresentative)
    (hdifferential : g.differential = 0)
    (horder : g.coordinateOrder (by omega) hfinite = 2) :
    ∃ h : PointedMapGerm 2 (n + 1),
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        h.HasInjectiveRepresentative ∧ h.differential = 0 ∧
          Germ.HasAnalyticWeierstrassFactorizationOfOrder
            (h.1.component 0) 2 := by
  obtain ⟨h, hequivalent, hhfinite, hprepared⟩ :=
    g.exists_rightLeftEquivalent_firstComponent_orderTwoPreparation
      hfinite horder
  have hhinjective : h.HasInjectiveRepresentative :=
    hequivalent.hasInjectiveRepresentative hinjective
  have hhdifferential : h.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff
      hequivalent).mpr hdifferential
  exact ⟨h, hequivalent, hhfinite, hhinjective, hhdifferential, hprepared⟩

end PointedMapGerm

end OnLeConjecture.Analytic
