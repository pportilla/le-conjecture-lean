/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LeConjectureReduction
public import OnLeConjecture.Analytic.CoordinateOrder

/-!
# Assembly of the three coordinate order exclusions

Once local finiteness, the upper bound four, and the exclusions in coordinate
orders two, three, and four are available, they imply Lê's conjecture.
-/

public section

namespace OnLeConjecture.Analytic

/-- Local finiteness, the coordinate order bound, and the three case
exclusions imply Lê's conjecture. -/
theorem leConjecture_of_finiteness_orderBound_and_caseExclusions
    (hfinite : ∀ g : PointedMapGerm 2 3,
      g.HasInjectiveRepresentative → g.IsFiniteAtOrigin)
    (hbound : ∀ (g : PointedMapGerm 2 3)
      (hf : g.IsFiniteAtOrigin),
      g.HasInjectiveRepresentative →
        g.differential = 0 → g.coordinateOrder (by omega) hf ≤ 4)
    (hexcludeTwo : ∀ (g : PointedMapGerm 2 3)
      (hf : g.IsFiniteAtOrigin),
      g.differential = 0 →
        g.coordinateOrder (by omega) hf = 2 →
          ¬ g.HasInjectiveRepresentative)
    (hexcludeThree : ∀ (g : PointedMapGerm 2 3)
      (hf : g.IsFiniteAtOrigin),
      g.differential = 0 →
        g.coordinateOrder (by omega) hf = 3 →
          ¬ g.HasInjectiveRepresentative)
    (hexcludeFour : ∀ (g : PointedMapGerm 2 3)
      (hf : g.IsFiniteAtOrigin),
      g.differential = 0 →
        g.coordinateOrder (by omega) hf = 4 →
          ¬ g.HasInjectiveRepresentative) :
    LeConjecture := by
  apply leConjecture_of_no_injective_zero_differential
  intro g hdifferential hinjective
  let hf : g.IsFiniteAtOrigin := hfinite g hinjective
  have hlower : 2 ≤ g.coordinateOrder (by omega) hf :=
    g.two_le_coordinateOrder_of_differential_eq_zero
      (by omega) hf hdifferential
  have hupper : g.coordinateOrder (by omega) hf ≤ 4 :=
    hbound g hf hinjective hdifferential
  have hcases : g.coordinateOrder (by omega) hf = 2 ∨
      g.coordinateOrder (by omega) hf = 3 ∨
      g.coordinateOrder (by omega) hf = 4 := by
    omega
  rcases hcases with htwo | hthree | hfour
  · exact hexcludeTwo g hf hdifferential htwo hinjective
  · exact hexcludeThree g hf hdifferential hthree hinjective
  · exact hexcludeFour g hf hdifferential hfour hinjective

end OnLeConjecture.Analytic
