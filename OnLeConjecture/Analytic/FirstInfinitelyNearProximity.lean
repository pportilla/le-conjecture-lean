/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProximityTopOrderChain

/-!
# Proximity at the first infinitely near level

When generation records the blowup depth, a child of the root cannot
have a second proximity parent. The proof uses the actual rooted paths
and the decrease of generation along proximity relations.
-/

public section

namespace OnLeConjecture.Analytic

namespace AnalyticPointBasis

/-- The recorded generation cannot decrease along an ancestral path. -/
theorem generation_le_of_ancestor {N : ℕ} (c : AnalyticPointBasis N)
    {p q : Fin N} (h : c.Ancestor p q) : c.generation p ≤ c.generation q := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | @head q r hparent _hpath ih =>
      exact ih.trans (by
        have hdecrease := c.generation_decreases q hparent.1
        rw [hparent.2] at hdecrease
        omega)

/-- Every nonroot point has generation strictly above the root. -/
theorem root_generation_lt_of_ne {N : ℕ} (c : AnalyticPointBasis N)
    (q : Fin N) (hq : q ≠ c.root) : c.generation c.root < c.generation q := by
  have hpre := c.generation_le_of_ancestor (c.root_ancestor (c.predecessor q))
  exact hpre.trans_lt (c.generation_decreases q hq)

end AnalyticPointBasis

namespace AnalyticProximityData

/-- A point at the first blowup depth is proximate only to the root. -/
theorem parents_eq_root_of_first_depth {N : ℕ} {c : AnalyticPointBasis N}
    (d : AnalyticProximityData c) (q : Fin N)
    (hparent : c.ParentRelation q c.root)
    (hdepth : c.generation q = c.generation c.root + 1) :
    d.proximity.parents q = {c.root} := by
  apply Finset.Subset.antisymm
  · intro p hp
    apply Finset.mem_singleton.mpr
    by_contra hne
    have hbelow : c.generation p < c.generation q := d.generation_decreases hp
    have habove := c.root_generation_lt_of_ne p hne
    omega
  · intro p hp
    have hpRoot : p = c.root := Finset.mem_singleton.mp hp
    subst p
    exact d.analytic_parent_is_proximity_parent hparent

/-- In particular, a first-level point is not satellite. -/
theorem not_satellite_of_first_depth {N : ℕ} {c : AnalyticPointBasis N}
    (d : AnalyticProximityData c) (q : Fin N)
    (hparent : c.ParentRelation q c.root)
    (hdepth : c.generation q = c.generation c.root + 1) :
    q ∉ d.proximity.satellitePoints := by
  simp only [Numerical.ProximityCertificate.satellitePoints, Finset.mem_filter,
    Finset.mem_univ, true_and, d.parents_eq_root_of_first_depth q hparent hdepth,
    Finset.card_singleton]
  decide

end AnalyticProximityData

end OnLeConjecture.Analytic
