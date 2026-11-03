/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakTransformIdealData
public import OnLeConjecture.Analytic.CoordinateOrder

/-!
# Coordinate order from an actual weak point basis

The root weak ideal is the coordinate ideal when its generators are the
map's components. The recorded generic member proves that the root ideal
has exactly the recorded order, identifying it with coordinate order.
-/

public section

namespace OnLeConjecture.Analytic.WeakTransformIdealData

open OnLeConjecture.Analytic.Germ

theorem root_ideal_eq_coordinateIdeal
    {N m : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin m))
    (f : PointedMapGerm 2 m) (hgenerators : ∀ i, d.generators c.root i = f.1.component i) :
    d.ideal c.root = f.1.coordinateIdeal := by
  apply le_antisymm
  · rw [ideal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hgenerators]
    exact f.1.component_mem_coordinateIdeal i
  · rw [MapGerm.coordinateIdeal_le]
    intro i
    rw [← hgenerators]
    exact Ideal.subset_span (Set.mem_range_self i)

theorem coordinateOrder_eq_root_multiplicity
    {N m : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin m))
    (f : PointedMapGerm 2 m) (hfinite : f.IsFiniteAtOrigin)
    (hgenerators : ∀ i, d.generators c.root i = f.1.component i) :
    f.coordinateOrder (by decide) hfinite = c.multiplicity c.root := by
  have hideal := d.root_ideal_eq_coordinateIdeal f hgenerators
  have hle : f.1.coordinateIdeal ≤ maximalIdeal 2 ^ c.multiplicity c.root := by
    rw [← hideal]
    exact d.ideal_le_pow c.root
  have hnot : ¬ f.1.coordinateIdeal ≤ maximalIdeal 2 ^ (c.multiplicity c.root + 1) := by
    rw [← hideal]
    exact d.ideal_not_le_succ c.root
  apply le_antisymm
  · by_contra hn
    apply hnot
    exact (f.coordinateIdeal_le_maximalIdeal_pow_coordinateOrder (by decide) hfinite).trans
      (Ideal.pow_le_pow_right (by omega))
  · by_contra hn
    apply f.not_coordinateIdeal_le_maximalIdeal_pow_coordinateOrder_add_one (by decide) hfinite
    exact hle.trans (Ideal.pow_le_pow_right (by omega))

end OnLeConjecture.Analytic.WeakTransformIdealData
