/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LeConjectureAssembly
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness

/-!
# Assembly after plane finiteness

For plane map germs, local finiteness follows from injectivity. The remaining
inputs to Lê's conjecture are therefore the coordinate order bound and the
three order exclusions.
-/

public section

namespace OnLeConjecture.Analytic

/-- The coordinate order bound and the exclusions in orders two, three, and
four imply Lê's conjecture. -/
theorem leConjecture_of_orderBound_and_caseExclusions
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
  exact leConjecture_of_finiteness_orderBound_and_caseExclusions
    (fun g hinjective ↦
      PointedMapGerm.injective_isFiniteAtOrigin_two_three g hinjective)
    hbound hexcludeTwo hexcludeThree hexcludeFour

end OnLeConjecture.Analytic
