/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.SquareJetPreparedNumerics
public import OnLeConjecture.DTwo.ExtremeThetaPreparation

/-!
# The extreme theta form is the only surviving square-jet case

An actual target permutation puts the selected general member second.
The minimal numerical alternative is excluded by its actual intersection
number. The other alternative constructs the convergent theta form with
its finite first pair and intersection `3k`.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical PlaneCurve

/-- An actual target permutation places either selected last component
second, while retaining both last components as the same unordered pair. -/
theorem exists_target_selected_second (g : PointedMapGerm 2 3) (selected : Fin 2) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      f.1.component 0 = g.1.component 0 ∧
      f.1.component 1 = g.1.component selected.succ ∧
      ∀ i : Fin 2, ∃ j : Fin 2, f.1.component i.succ = g.1.component j.succ := by
  fin_cases selected
  · refine ⟨g, g.rightLeftEquivalent_refl, rfl, rfl, ?_⟩
    intro i
    exact ⟨i, rfl⟩
  · obtain ⟨f, hgf, hf0, hf1, hf2⟩ := exists_target_swap_last_two g
    refine ⟨f, hgf, hf0, hf1, ?_⟩
    intro i
    fin_cases i
    · exact ⟨1, hf1⟩
    · exact ⟨0, hf2⟩

/-- With the standing reduction identities, injectivity forces the
extreme numerical alternative and constructs its analytic theta form.
The initial power form is independent of the critical component. -/
theorem exists_extreme_theta_form_of_square_jet_reduction
    (F : PointedMapGerm 2 3) (hinjective : F.HasInjectiveRepresentative) {N : ℕ}
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
    Even k ∧ 4 ≤ k ∧ c.multiplicityCount 1 = k ∧ t = 2 * k ∧
      ∃ f : PointedMapGerm 2 3, ∃ C₂ C₃ : Germ 2,
        F.RightLeftEquivalent f ∧ f.1.component 0 = cyclicFirst k ∧
        f.1.component 1 = extremeTheta k + coordinate 1 ^ (2 * k) * C₂ ∧
        f.1.component 2 = coordinate 1 ^ (2 * k) * C₃ ∧ f.firstTwo.IsFiniteAtOrigin ∧
        ∃ hf : HasFiniteIntersection (f.1.component 0) (f.1.component 1),
          intersectionMultiplicity (f.1.component 0) (f.1.component 1) hf = 3 * k := by
  obtain ⟨G, hFG, hGdiff, hGfirst, hGminorsT, hGminorsK, heven, halternatives,
      hGfinite, hGpair⟩ := exists_square_jet_prepared_numerical_alternative
    F c generation hdecrease hroot hpositive k hk hfirst hreduced hdifferential hbranches
    hvcritical hgenus h hh hfiniteCritical t htransverse hpolar hminors selected hfinitePair hpair
  obtain ⟨g, hGg, hg0, hg1, hgothers⟩ := exists_target_selected_second G selected
  have hFg : F.RightLeftEquivalent g := hFG.trans hGg
  have hginjective := hFg.hasInjectiveRepresentative hinjective
  have hgdiff : g.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff hGg).mpr hGdiff
  have hgfirst : g.1.component 0 = cyclicFirst k := (hg0.trans hGfirst)
  have hderivative (i : Fin 3) : valueRingHom 2 (partialDerivative 0 (g.1.component i)) = 0 := by
    apply (differential_eq_zero_iff_partialDerivatives_vanish (g.1.component i)).mp
    rw [MapGerm.germDifferential_component]
    exact (MapGerm.differential_eq_zero_iff g.1).mp hgdiff i
  have hgminors (r : ℕ) (hdiv : ∀ i : Fin 2, coordinate (1 : Fin 2) ^ r ∣
      jacobian (G.1.component 0) (G.1.component i.succ)) (i : Fin 2) :
      coordinate (1 : Fin 2) ^ r ∣ jacobian (g.1.component 0) (g.1.component i.succ) := by
    obtain ⟨j, hj⟩ := hgothers i
    rw [hg0, hj]
    exact hdiv j
  have hgfinite : HasFiniteIntersection (g.1.component 0) (g.1.component 1) := by
    rw [hg0, hg1]
    exact hGfinite
  have hgpair : intersectionMultiplicity (g.1.component 0) (g.1.component 1) hgfinite =
      c.squareMultiplicity := by
    simpa only [hg0, hg1] using hGpair
  have hb : c.branchCount = 2 := by
    rw [hbranches, hfirst, irreducibleBranchCount_morseCurve k (by omega)]
    exact Nat.gcd_eq_left_iff_dvd.mpr heven.two_dvd
  have hmu : milnorNumber (F.1.component 0) hvcritical = k - 1 := by
    simpa only [hfirst] using milnorNumber_morseCurve k (by omega)
  have hcount : 2 * c.multiplicityCount 2 = k := by
    rw [hmu, hb] at hgenus
    omega
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : Fin N) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsquares := c.squareMultiplicity_eq_four_mul_count_two_add_count_one hpositive hbounded
  have hextreme : c.multiplicityCount 1 = k ∧ t = 2 * k := by
    rcases halternatives with hminimal | hextreme
    · have hsmall : intersectionMultiplicity (g.1.component 0) (g.1.component 1) hgfinite ≤
          2 * k := by omega
      exact (critical_axis_minimal_intersection_not_hasInjectiveRepresentative g k (by omega)
        hgfirst (hderivative 1) (hderivative 2)
        (hgminors (k - 1) hGminorsK 0) (hgminors (k - 1) hGminorsK 1)
        hgfinite hsmall hginjective).elim
    · exact hextreme
  have hgi : intersectionMultiplicity (g.1.component 0) (g.1.component 1) hgfinite = 3 * k := by
    omega
  have hgJT (i : Fin 2) : coordinate (1 : Fin 2) ^ (2 * k - 1) ∣
      jacobian (g.1.component 0) (g.1.component i.succ) := by
    simpa only [hextreme.2] using hgminors (t - 1) hGminorsT i
  obtain ⟨f, C₂, C₃, hgf, hf0, hf1, hf2, hfiniteMap, hf, hfi⟩ :=
    exists_extreme_theta_preparation_with_finite_pair g k (by omega) hgfirst
      (hgJT 0) (hgJT 1) hgfinite hgi
  have hk4 : 4 ≤ k := by obtain ⟨a, ha⟩ := heven; omega
  exact ⟨heven, hk4, hextreme.1, hextreme.2, f, C₂, C₃, hFg.trans hgf,
    hf0, hf1, hf2, hfiniteMap, hf, hfi⟩

end OnLeConjecture.DTwo
