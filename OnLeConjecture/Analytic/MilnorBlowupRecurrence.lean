/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularBlowupPolarRecurrence
public import OnLeConjecture.Analytic.TeissierPolarIdentity
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection
public import OnLeConjecture.PlaneCurve.MilnorBranchDefect

/-!
# The Milnor branch quantity under a point blowup

The coordinate polar identity and polar intersection recurrence give the
recurrence for Jacobian colength plus branch count minus one. Invariance
under units and analytic coordinates transports it to both original
projective charts.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- Multiplication by a unit preserves the Jacobian colength of a reduced
pointed equation. The proof uses the polar identity in transverse coordinates. -/
theorem jacobianColength_unit_mul_of_squarefree
    (f U : Germ 2) (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f) (hU : IsUnit U) :
    Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (U * f)) =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) := by
  obtain ⟨m, hm, hmnext⟩ := exists_exact_maximalIdeal_order_of_ne_zero f hsq.ne_zero
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hm hmnext
  let F := e.forward.pullbackRingHom f
  let V := e.forward.pullbackRingHom U
  have hF : F ∈ maximalIdeal 2 := e.forward.pullback_mem_maximalIdeal hf
  have hFsq : Squarefree F := e.squarefree_pullback f hsq
  have hV : IsUnit V := hU.map e.forward.pullbackRingHom
  have hVF : V * F ∈ maximalIdeal 2 := (maximalIdeal 2).mul_mem_left V hF
  have hVFsq : Squarefree (V * F) :=
    (associated_unit_mul_left F V hV).squarefree_iff.mpr hFsq
  have haxis : HasFiniteIntersection F (coordinate (1 : Fin 2)) :=
    (hasFiniteIntersection_comm _ _).mp
      (hasFiniteIntersection_secondCoordinate_of_regular F m he)
  have haxisV : HasFiniteIntersection (V * F) (coordinate (1 : Fin 2)) :=
    (hasFiniteIntersection_unit_mul_left_iff V F _ hV).mpr haxis
  obtain ⟨hpolar, _hfinite, hidentity⟩ := exists_first_partial_polar_identity F hF hFsq haxis
  obtain ⟨hpolarV, _hfiniteV, hidentityV⟩ :=
    exists_first_partial_polar_identity (V * F) hVF hVFsq haxisV
  have hpolarEq : intersectionMultiplicity (V * F) (partialDerivative 0 (V * F)) hpolarV =
      intersectionMultiplicity F (partialDerivative 0 F) hpolar := by
    change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [pairIdeal_unit_mul_polar V F hV]
  have haxisEq := intersectionMultiplicity_unit_mul_left V F _ hV haxisV haxis
  have hmu : Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (V * F)) =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal F) := by omega
  rw [jacobianColength_pullback e (U * f), jacobianColength_pullback e f, map_mul]
  exact hmu

/-- Associated reduced equations have the same Milnor branch quantity,
including the unit case. -/
theorem milnorBranchDefect_eq_of_associated
    {f g : Germ 2} (hsq : Squarefree f) (h : Associated f g) :
    milnorBranchDefect f = milnorBranchDefect g := by
  classical
  by_cases hfunit : IsUnit f
  · rw [milnorBranchDefect_eq_zero_of_isUnit f hfunit,
      milnorBranchDefect_eq_zero_of_isUnit g (h.isUnit_iff.mp hfunit)]
  · have hgunit : ¬ IsUnit g := h.isUnit_iff.not.mp hfunit
    have hf : f ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      by_contra hz
      exact hfunit (isUnit_of_valueRingHom_ne_zero hz)
    obtain ⟨U, hU⟩ := h
    have hg : g = (U : Germ 2) * f := by rw [← hU, mul_comm]
    have hbranch : irreducibleBranchCount f = irreducibleBranchCount g :=
      irreducibleBranchCount_eq_of_associated ⟨U, hU⟩
    rw [milnorBranchDefect, if_neg hfunit, milnorBranchDefect, if_neg hgunit,
      ← hbranch, hg, jacobianColength_unit_mul_of_squarefree f U hf hsq U.isUnit]

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open PlaneCurve
open scoped BigOperators

/-- Analytic chart lifts preserve the Milnor branch quantity of reduced
strict transforms. -/
theorem HasProjectiveBlowupLift.milnorBranchDefect_eq
    {e : PointedEquivGerm 2} {a b : Option ℂ} (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hsq : Squarefree (projectiveStrictTransform m (e.forward.pullbackRingHom f)
      (e.forward.pullback_mem_maximalIdeal_pow hf) a)) :
    milnorBranchDefect (projectiveStrictTransform m f hf b) =
      milnorBranchDefect (projectiveStrictTransform m (e.forward.pullbackRingHom f)
        (e.forward.pullback_mem_maximalIdeal_pow hf) a) := by
  obtain ⟨E, hE⟩ := h.strictTransform_associated m f hf
  have hsqE := E.squarefree_pullback _ hsq
  exact (milnorBranchDefect_eq_of_associated (hE.squarefree_iff.mpr hsqE) hE).trans
    (milnorBranchDefect_pullback E _).symm

/-- For a reduced equation transverse to the first axis, the Milnor
branch quantity is the sum of the child quantities and `m * (m - 1)`. -/
theorem exists_pointBlowup_milnorBranchDefect_recurrence_of_regular
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f) :
    ∃ s : Finset ℂ,
      (∀ c, c ∈ s ↔ ¬ IsUnit (pointBlowupTransform c m f hf)) ∧
      milnorBranchDefect f = m * (m - 1) +
        ∑ c ∈ s, milnorBranchDefect (pointBlowupTransform c m f hf) := by
  classical
  have hnext := not_mem_succ_maximalIdeal_pow_of_first_regular m f hregular
  have hfmem : f ∈ maximalIdeal 2 := by
    simpa only [pow_one] using Ideal.pow_le_pow_right hm hf
  have hfunit : ¬ IsUnit f := fun hu ↦
    valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp hfmem)
  obtain ⟨s, hpolar, hs, hlocal, hpolarSum⟩ :=
    exists_pointBlowup_polar_recurrence_of_squarefree_regular m hm f hf hregular hsq
  obtain ⟨_, _, _, hsqall, hinfinity⟩ :=
    exists_pointBlowupTransform_branchCount_sum_of_squarefree_regular m f hf hregular hsq
  let H (c : ℂ) := pointBlowupTransform c m f hf
  have haxis (c : ℂ) : HasFiniteIntersection (coordinate (1 : Fin 2)) (H c) := by
    apply hasFiniteIntersection_secondCoordinate_of_firstAxisRestriction_ne_zero
    have h := pointBlowupTransform_exceptionalRestriction_ne_zero c m f (H c) hf hnext
      (pointBlowupTransform_factor c m f hf)
    rwa [pointBlowupExceptionalLine_eq_lineGerm] at h
  let I (c : ℂ) := intersectionMultiplicity (H c) (partialDerivative 0 (H c)) (hlocal c)
  let A (c : ℂ) := intersectionMultiplicity (coordinate (1 : Fin 2)) (H c) (haxis c)
  let B (c : ℂ) := irreducibleBranchCount (H c)
  let D (c : ℂ) := milnorBranchDefect (H c)
  have hbranch : irreducibleBranchCount f = ∑ c ∈ s, B c :=
    pointBlowupTransform_branchCount_sum_of_finite_cover m f hf hregular hsq s
      (fun c hc ↦ (hs c).mpr hc)
  have hcover : ∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 →
      t ∈ s.image some := by
    intro t ht
    cases t with
    | none =>
      exact False.elim
        (valueRingHom_ne_zero_of_isUnit hinfinity (mem_maximalIdeal_iff.mp ht))
    | some c =>
      apply Finset.mem_image.mpr
      refine ⟨c, (hs c).mpr ?_, rfl⟩
      intro hu
      rw [projectiveStrictTransform_some] at ht
      exact valueRingHom_ne_zero_of_isUnit hu (mem_maximalIdeal_iff.mp ht)
  have haxisSum : ∑ c ∈ s, A c = m := by
    have h := sum_projective_exceptional_restriction_orders_eq m f hf hnext (s.image some) hcover
    rw [Finset.sum_image (fun _ _ _ _ h ↦ Option.some.inj h)] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro c _
    exact (intersectionMultiplicity_secondCoordinate_eq_exceptionalRestrictionOrder
      (H c) (haxis c)).trans (by rw [projectiveExceptionalIntersectionOrder,
        projectiveStrictTransform_some])
  have hparentAxis : HasFiniteIntersection f (coordinate (1 : Fin 2)) :=
    (hasFiniteIntersection_comm _ _).mp
      (hasFiniteIntersection_secondCoordinate_of_regular f m hregular)
  obtain ⟨hparentPolar, _, hparentTeissier⟩ :=
    exists_first_partial_polar_identity f hfmem hsq hparentAxis
  have hparentAxisEq : intersectionMultiplicity f (coordinate (1 : Fin 2)) hparentAxis = m := by
    rw [intersectionMultiplicity_comm]
    exact intersectionMultiplicity_secondCoordinate_of_regular f m hregular _
  rw [hparentAxisEq] at hparentTeissier
  have hparentDefect := milnorBranchDefect_add_one f hsq.ne_zero hfunit
  have hparent : intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar +
      irreducibleBranchCount f = milnorBranchDefect f + m := by omega
  have hchild (c : ℂ) (hc : c ∈ s) : I c + B c = D c + A c := by
    have hnonunit : ¬ IsUnit (H c) := (hs c).mp hc
    have hmem : H c ∈ maximalIdeal 2 := by
      rw [mem_maximalIdeal_iff]
      by_contra hz
      exact hnonunit (isUnit_of_valueRingHom_ne_zero hz)
    obtain ⟨hpol, _, hteissier⟩ := exists_first_partial_polar_identity (H c) hmem (hsqall c)
      ((hasFiniteIntersection_comm _ _).mp (haxis c))
    rw [intersectionMultiplicity_comm (H c) (coordinate (1 : Fin 2))] at hteissier
    have hdefect := milnorBranchDefect_add_one (H c) (hsqall c).ne_zero hnonunit
    change I c + 1 = _ + A c at hteissier
    change D c + 1 = _ + B c at hdefect
    omega
  have hsum : (∑ c ∈ s, I c) + (∑ c ∈ s, B c) =
      (∑ c ∈ s, D c) + ∑ c ∈ s, A c := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hchild
  refine ⟨s, hs, ?_⟩
  change intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hpolar =
    m * (m - 1) + ∑ c ∈ s, I c at hpolarSum
  change milnorBranchDefect f = m * (m - 1) + ∑ c ∈ s, D c
  omega

/-- The Milnor branch recurrence holds in both original projective charts
for every squarefree equation of positive exact ordinary order. -/
theorem exists_projectiveStrictTransform_milnorBranchDefect_recurrence
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (hsq : Squarefree f) :
    ∃ s : Finset (Option ℂ),
      (∀ t, t ∈ s ↔ ¬ IsUnit (projectiveStrictTransform m f hf t)) ∧
      milnorBranchDefect f = m * (m - 1) +
        ∑ t ∈ s, milnorBranchDefect (projectiveStrictTransform m f hf t) := by
  classical
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hf hnext
  let g := e.forward.pullbackRingHom f
  have hg : g ∈ maximalIdeal 2 ^ m := e.forward.pullback_mem_maximalIdeal_pow hf
  have hgsq : Squarefree g := e.squarefree_pullback f hsq
  obtain ⟨s, hs, hcount⟩ :=
    exists_pointBlowup_milnorBranchDefect_recurrence_of_regular m hm g hg he hgsq
  obtain ⟨_, _, _, hsqfinite, hinfinity⟩ :=
    exists_pointBlowupTransform_branchCount_sum_of_squarefree_regular m g hg he hgsq
  let S : Finset (Option ℂ) := s.image some
  have hS (a : Option ℂ) : a ∈ S ↔ ¬ IsUnit (projectiveStrictTransform m g hg a) := by
    cases a with
    | none =>
      have hinf : IsUnit (projectiveStrictTransform m g hg none) := hinfinity
      simp [S, hinf]
    | some c =>
      simpa only [S, Finset.mem_image, Option.some.injEq, exists_eq_right,
        projectiveStrictTransform_some] using hs c
  have hSsq (a : Option ℂ) : Squarefree (projectiveStrictTransform m g hg a) := by
    cases a with
    | none => exact hinfinity.squarefree
    | some c => simpa only [projectiveStrictTransform_some] using hsqfinite c
  have hScount : milnorBranchDefect g = m * (m - 1) +
      ∑ a ∈ S, milnorBranchDefect (projectiveStrictTransform m g hg a) := by
    rw [show S = s.image some from rfl, Finset.sum_image]
    · simpa only [projectiveStrictTransform_some] using hcount
    · exact fun _ _ _ _ h ↦ Option.some.inj h
  have hinj := (projectiveCenterMap_bijective e).1
  refine ⟨S.image (projectiveCenterMap e), ?_, ?_⟩
  · intro t
    obtain ⟨a, rfl⟩ := (projectiveCenterMap_bijective e).2 t
    rw [(projectiveCenterMap_hasLift e a).isUnit_iff m f hf, ← hS a]
    constructor
    · rintro h
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp h
      exact hinj hab ▸ hb
    · exact Finset.mem_image_of_mem _
  · have hparent : milnorBranchDefect f = milnorBranchDefect g :=
      milnorBranchDefect_pullback e f
    rw [hparent, hScount, Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
    congr 1
    exact Finset.sum_congr rfl (fun a _ ↦
      ((projectiveCenterMap_hasLift e a).milnorBranchDefect_eq m f hf (hSsq a)).symm)

/-- Any finite set containing every singular strict transform indexes the
Milnor branch recurrence. Smooth and unit transforms contribute zero. -/
theorem projectiveStrictTransform_milnorBranchDefect_recurrence_of_singular_cover
    (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (hsq : Squarefree f)
    (s : Finset (Option ℂ))
    (hcover : ∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 ^ 2 → t ∈ s) :
    milnorBranchDefect f = m * (m - 1) +
      ∑ t ∈ s, milnorBranchDefect (projectiveStrictTransform m f hf t) := by
  classical
  obtain ⟨r, hr, hcount⟩ :=
    exists_projectiveStrictTransform_milnorBranchDefect_recurrence m hm f hf hnext hsq
  let D (t : Option ℂ) := milnorBranchDefect (projectiveStrictTransform m f hf t)
  have hzeroR (t : Option ℂ) (ht : t ∉ r) : D t = 0 := by
    have hunit : IsUnit (projectiveStrictTransform m f hf t) := by
      by_contra hnot
      exact ht ((hr t).mpr hnot)
    exact milnorBranchDefect_eq_zero_of_isUnit _ hunit
  have hzeroS (t : Option ℂ) (ht : t ∉ s) : D t = 0 := by
    by_cases hunit : IsUnit (projectiveStrictTransform m f hf t)
    · exact milnorBranchDefect_eq_zero_of_isUnit _ hunit
    · have hmem : projectiveStrictTransform m f hf t ∈ maximalIdeal 2 := by
        rw [mem_maximalIdeal_iff]
        by_contra hz
        exact hunit (isUnit_of_valueRingHom_ne_zero hz)
      exact milnorBranchDefect_eq_zero_of_order_one _ hmem (fun h ↦ ht (hcover t h))
  have hsumR : (∑ t ∈ r, D t) = ∑ t ∈ r ∪ s, D t :=
    Finset.sum_subset Finset.subset_union_left (fun t _ ht ↦ hzeroR t ht)
  have hsumS : (∑ t ∈ s, D t) = ∑ t ∈ r ∪ s, D t :=
    Finset.sum_subset Finset.subset_union_right (fun t _ ht ↦ hzeroS t ht)
  change milnorBranchDefect f = m * (m - 1) + ∑ t ∈ s, D t
  change milnorBranchDefect f = m * (m - 1) + ∑ t ∈ r, D t at hcount
  rw [hcount, hsumR, hsumS]

/-- A separated list of exceptional points containing the singular strict
transforms may index the Milnor branch recurrence. -/
theorem projectiveStrictTransform_milnorBranchDefect_recurrence_of_indexed_singular_cover
    {κ : Type*} (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (hsq : Squarefree f)
    (s : Finset κ) (center : κ → Option ℂ) (hinj : Set.InjOn center s)
    (hcover : ∀ t, projectiveStrictTransform m f hf t ∈ maximalIdeal 2 ^ 2 →
      ∃ i ∈ s, center i = t) :
    milnorBranchDefect f = m * (m - 1) +
      ∑ i ∈ s, milnorBranchDefect (projectiveStrictTransform m f hf (center i)) := by
  classical
  rw [projectiveStrictTransform_milnorBranchDefect_recurrence_of_singular_cover
    m hm f hf hnext hsq (s.image center)
      (fun t ht ↦ Finset.mem_image.mpr (hcover t ht)), Finset.sum_image hinj]

end OnLeConjecture.Analytic.Germ
