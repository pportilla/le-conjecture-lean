/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.SquareJetAnalyticExclusion
public import OnLeConjecture.Analytic.SquareJetMemberNormalization
public import OnLeConjecture.DTwo.SquareQuadraticMemberNormalization

/-!
# Square-jet exclusion for the specified generic member

An analytic source equivalence constructs the quadratic power form of the
specified first member. Its branch count, Milnor number, selected pair
intersection and critical Jacobian divisibility are transported through
that equivalence. The critical equation need not be smooth in the input.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical PlaneCurve

theorem square_jet_reduction_not_hasInjectiveRepresentative_of_member_normalization
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hnormal : ∃ k : ℕ, 3 ≤ k ∧ ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom (F.1.component 0) = morseCurve k)
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
  obtain ⟨k, hk, e, he⟩ := hnormal
  let G := F.comp e.forward
  let h' := e.pullbackAlgEquiv h
  have hcomponent (i : Fin 3) : G.1.component i = e.pullbackAlgEquiv (F.1.component i) :=
    PointedMapGerm.component_comp_eq_pullback _ _ _
  have hFG : F.RightLeftEquivalent G := by
    refine ⟨e, PointedEquivGerm.identity 3, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp]
  have hGdiff : G.differential = 0 :=
    (PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff hFG).mpr hdifferential
  have hGfirst : G.1.component 0 = morseCurve k := (hcomponent 0).trans he
  have hGreduced : Squarefree (G.1.component 0) := by
    rw [hcomponent]
    exact e.squarefree_pullback _ hreduced
  have hGbranches : c.branchCount = irreducibleBranchCount (G.1.component 0) := by
    rw [hcomponent]
    exact hbranches.trans (irreducibleBranchCount_pullback e _)
  have hGcritical : HasIsolatedCriticalPoint (G.1.component 0) := by
    rw [hcomponent]
    exact (hasIsolatedCriticalPoint_pullback_iff e _).mpr hvcritical
  have hGgenus : 2 * c.multiplicityCount 2 + 1 =
      milnorNumber (G.1.component 0) hGcritical + c.branchCount := by
    simpa only [hcomponent, ← milnorNumber_pullback e _ hvcritical] using hgenus
  have hh' : h' ∈ maximalIdeal 2 := e.forward.pullback_mem_maximalIdeal hh
  have hGfiniteCritical : HasFiniteIntersection (G.1.component 0) h' := by
    rw [hcomponent]
    exact hfiniteCritical.pullback e
  have hGpolar : intersectionMultiplicity (G.1.component 0) h' hGfiniteCritical * (t - 1) +
      c.totalMultiplicity + c.branchCount ≤ 2 * c.squareMultiplicity := by
    simpa only [hcomponent, h', ← intersectionMultiplicity_pullback e hfiniteCritical] using hpolar
  have hGminors (i : Fin 2) : h' ^ (t - 1) ∣
      jacobian (G.1.component 0) (G.1.component i.succ) := by
    have hpull := map_dvd e.forward.pullbackRingHom (hminors i)
    rw [map_pow] at hpull
    rw [hcomponent, hcomponent]
    change h' ^ (t - 1) ∣ jacobian
      (e.forward.pullbackRingHom (F.1.component 0))
      (e.forward.pullbackRingHom (F.1.component i.succ))
    rw [show jacobian (e.forward.pullbackRingHom (F.1.component 0))
        (e.forward.pullbackRingHom (F.1.component i.succ)) =
        e.forward.pullbackRingHom (jacobian (F.1.component 0) (F.1.component i.succ)) *
          coordinateJacobian e.forward from
      jacobian_compPointed _ _ e.forward]
    exact dvd_mul_of_dvd_left hpull _
  have hGfinitePair : HasFiniteIntersection (G.1.component 0) (G.1.component selected.succ) := by
    rw [hcomponent, hcomponent]
    exact hfinitePair.pullback e
  have hGpair : intersectionMultiplicity
      (G.1.component 0) (G.1.component selected.succ) hGfinitePair = c.squareMultiplicity := by
    simp only [hcomponent]
    exact (intersectionMultiplicity_pullback e hfinitePair).symm.trans hpair
  intro hinjective
  exact square_jet_reduction_not_hasInjectiveRepresentative G c generation hdecrease
    hroot hpositive k hk hGfirst hGreduced hGdiff hGbranches hGcritical hGgenus
    h' hh' hGfiniteCritical t htransverse hGpolar hGminors selected hGfinitePair hGpair
    (hFG.hasInjectiveRepresentative hinjective)

theorem unprepared_square_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hfirst : F.1.component 0 - coordinate (0 : Fin 2) ^ 2 ∈ maximalIdeal 2 ^ 3)
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
  exact square_jet_reduction_not_hasInjectiveRepresentative_of_member_normalization
    F c generation hdecrease hroot hpositive
    (exists_square_jet_member_normalization _ hfirst hreduced)
    hreduced hdifferential hbranches hvcritical hgenus h hh hfiniteCritical t htransverse
    hpolar hminors selected hfinitePair hpair

theorem smooth_square_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (l : Germ 2) (hl : l ∈ maximalIdeal 2) (hdl : differential l ≠ 0)
    (hfirst : F.1.component 0 - l ^ 2 ∈ maximalIdeal 2 ^ 3)
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
  exact square_jet_reduction_not_hasInjectiveRepresentative_of_member_normalization
    F c generation hdecrease hroot hpositive
    (exists_smooth_square_jet_member_normalization _ l hl hdl hfirst hreduced)
    hreduced hdifferential hbranches hvcritical hgenus h hh hfiniteCritical t htransverse
    hpolar hminors selected hfinitePair hpair

theorem square_quadratic_jet_reduction_not_hasInjectiveRepresentative
    (F : PointedMapGerm 2 3) {N : ℕ}
    (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2) (hQne : Q ≠ 0)
    (hdisc : binaryQuadraticDiscriminant Q = 0)
    (hfirst : F.1.component 0 - coordinatePolynomialAlgHom 2 Q ∈ maximalIdeal 2 ^ 3)
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
  exact square_jet_reduction_not_hasInjectiveRepresentative_of_member_normalization
    F c generation hdecrease hroot hpositive
    (exists_square_quadratic_member_normalization _ Q hQ hQne hdisc hfirst hreduced)
    hreduced hdifferential hbranches hvcritical hgenus h hh hfiniteCritical t htransverse
    hpolar hminors selected hfinitePair hpair

end OnLeConjecture.DTwo
