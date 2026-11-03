/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.SquareJetExtremeReduction
public import OnLeConjecture.DTwo.ExtremePreparedExclusion

/-!
# Analytic exclusion of the square-jet reduction

The proximity and intersection hypotheses first construct the numerical
alternatives and analytic preparation. The minimal alternative and the
extreme prepared form are both excluded by the proved analytic collision
theorems. No numerical alternative or prepared residual is assumed.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical PlaneCurve

theorem square_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hk : 3 ≤ k) (hfirst : F.1.component 0 = morseCurve k)
    (hreduced : Squarefree (F.1.component 0)) (hdifferential : F.differential = 0)
    (hbranches : c.branchCount = irreducibleBranchCount (F.1.component 0))
    (hvcritical : HasIsolatedCriticalPoint (F.1.component 0))
    (hgenus : 2 * c.multiplicityCount 2 + 1 =
      milnorNumber (F.1.component 0) hvcritical + c.branchCount)
    (h : Germ 2) (hh : h ∈ maximalIdeal 2)
    (hfiniteCritical : HasFiniteIntersection (F.1.component 0) h)
    (t : ℕ) (htransverse : c.totalMultiplicity ≤ t)
    (hpolar : intersectionMultiplicity (F.1.component 0) h hfiniteCritical * (t - 1) +
      c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity)
    (hminors : ∀ i : Fin 2, h ^ (t - 1) ∣ jacobian (F.1.component 0) (F.1.component i.succ))
    (selected : Fin 2)
    (hfinitePair : HasFiniteIntersection (F.1.component 0) (F.1.component selected.succ))
    (hpair : intersectionMultiplicity
      (F.1.component 0) (F.1.component selected.succ) hfinitePair = c.squareMultiplicity) :
    ¬ F.HasInjectiveRepresentative := by
  intro hinjective
  obtain ⟨heven, hk4, _, _, f, C₂, C₃, hFf, hf0, hf1, hf2, hfiniteMap, _⟩ :=
    exists_extreme_theta_form_of_square_jet_reduction F hinjective c generation hdecrease
      hroot hpositive k hk hfirst hreduced hdifferential hbranches hvcritical hgenus
      h hh hfiniteCritical t htransverse hpolar hminors selected hfinitePair hpair
  obtain ⟨a, hka⟩ := heven
  have hk2 : k = 2 * a := by omega
  have ha : 0 < a := by omega
  rw [hk2] at hf0 hf1 hf2
  have hfour : 2 * (2 * a) = 4 * a := by omega
  rw [hfour] at hf1 hf2
  exact extreme_prepared_not_hasInjectiveRepresentative f hfiniteMap a ha C₂ C₃ hf0 hf1 hf2
    (hFf.hasInjectiveRepresentative hinjective)

end OnLeConjecture.DTwo
