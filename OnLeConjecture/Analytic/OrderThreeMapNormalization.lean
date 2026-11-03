/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoordinateOrderNormalization
public import OnLeConjecture.Analytic.OrderThreePreparation
public import OnLeConjecture.Analytic.RightLeftRelation

/-!
# Normalizing the first component in coordinate order three

A finite plane map germ whose coordinate ideal has order three is equivalent
to one whose first component is an analytic unit times a depressed monic cubic.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- A finite plane map germ of coordinate order three admits analytic
Weierstrass preparation in its first component. -/
theorem exists_rightLeftEquivalent_firstComponent_orderThreePreparation
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by omega) hfinite = 3) :
    ∃ h : PointedMapGerm 2 (n + 1),
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        Germ.HasAnalyticWeierstrassFactorizationOfOrder
          (h.1.component 0) 3 := by
  obtain ⟨h, hequivalent, hhfinite, hregular⟩ :=
    g.exists_rightLeftEquivalent_firstComponent_regularInCoordinateOrder
      hfinite
  have hregularThree : Germ.IsRegularInFirstCoordinateOfOrder
      (h.1.component 0) 3 := by
    simpa only [horder] using hregular
  exact ⟨h, hequivalent, hhfinite,
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_three hregularThree⟩

/-- A finite plane map germ of coordinate order three is equivalent to one
whose first component is a unit times a depressed cubic. -/
theorem exists_rightLeftEquivalent_firstComponent_depressedCubic
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (horder : g.coordinateOrder (by omega) hfinite = 3) :
    ∃ h : PointedMapGerm 2 (n + 1), ∃ a₁ a₀ : Germ 1, ∃ u : Germ 2,
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        a₁ ∈ Germ.maximalIdeal 1 ∧
        a₀ ∈ Germ.maximalIdeal 1 ∧
        IsUnit u ∧
        h.1.component 0 =
          (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.planeCoefficientExtension a₁ *
              Germ.coordinate (0 : Fin 2) +
            Germ.planeCoefficientExtension a₀) * u := by
  obtain ⟨g₀, hequivalent, hg₀Finite, hregular⟩ :=
    g.exists_rightLeftEquivalent_firstComponent_regularInCoordinateOrder
      hfinite
  have hregularThree : Germ.IsRegularInFirstCoordinateOfOrder
      (g₀.1.component 0) 3 := by
    simpa only [horder] using hregular
  obtain ⟨source, a₁, a₀, u, ha₁, ha₀, hu, hnormal,
      _hparameter⟩ :=
    Germ.exists_parameterPreserving_depressedCubicPreparation hregularThree
  let h : PointedMapGerm 2 (n + 1) := g₀.comp source.forward
  have hg₀h : g₀.RightLeftEquivalent h := by
    refine ⟨source, PointedEquivGerm.identity (n + 1), ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hequivalentFinal : g.RightLeftEquivalent h :=
    hequivalent.trans hg₀h
  have hhFinite : h.IsFiniteAtOrigin :=
    hequivalentFinal.isFiniteAtOrigin_iff.mpr hfinite
  have hcomponent : h.1.component 0 =
      (Germ.coordinate (0 : Fin 2) ^ 3 +
        Germ.planeCoefficientExtension a₁ *
          Germ.coordinate (0 : Fin 2) +
        Germ.planeCoefficientExtension a₀) * u := by
    calc
      h.1.component 0 =
          source.forward.pullbackRingHom (g₀.1.component 0) :=
        g₀.component_comp_general source.forward 0
      _ = source.pullbackAlgEquiv (g₀.1.component 0) := rfl
      _ = _ := hnormal
  exact ⟨h, a₁, a₀, u, hequivalentFinal, hhFinite,
    ha₁, ha₀, hu, hcomponent⟩

/-- An injective counterexample of coordinate order three can be replaced by
an injective equivalent germ with a prepared depressed cubic first component. -/
theorem exists_injective_firstComponent_depressedCubic
    {n : ℕ} (g : PointedMapGerm 2 (n + 1))
    (hfinite : g.IsFiniteAtOrigin)
    (hinjective : g.HasInjectiveRepresentative)
    (hdifferential : g.differential = 0)
    (horder : g.coordinateOrder (by omega) hfinite = 3) :
    ∃ h : PointedMapGerm 2 (n + 1), ∃ a₁ a₀ : Germ 1, ∃ u : Germ 2,
      g.RightLeftEquivalent h ∧ h.IsFiniteAtOrigin ∧
        h.HasInjectiveRepresentative ∧ h.differential = 0 ∧
        a₁ ∈ Germ.maximalIdeal 1 ∧
        a₀ ∈ Germ.maximalIdeal 1 ∧
        IsUnit u ∧
        h.1.component 0 =
          (Germ.coordinate (0 : Fin 2) ^ 3 +
            Germ.planeCoefficientExtension a₁ *
              Germ.coordinate (0 : Fin 2) +
            Germ.planeCoefficientExtension a₀) * u := by
  obtain ⟨h, a₁, a₀, u, hequivalent, hhFinite,
      ha₁, ha₀, hu, hcomponent⟩ :=
    g.exists_rightLeftEquivalent_firstComponent_depressedCubic hfinite horder
  exact ⟨h, a₁, a₀, u, hequivalent, hhFinite,
    hequivalent.hasInjectiveRepresentative hinjective,
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff
      hequivalent).mpr hdifferential,
    ha₁, ha₀, hu, hcomponent⟩

end PointedMapGerm

end OnLeConjecture.Analytic
