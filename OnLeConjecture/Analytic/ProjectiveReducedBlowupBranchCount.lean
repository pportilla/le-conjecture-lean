/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionExact
public import OnLeConjecture.Analytic.ReducedBlowupBranchCount
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import OnLeConjecture.Analytic.ProjectivePointBasisCompleteness
public import OnLeConjecture.Analytic.TransverseSmoothPreparation

/-!
# Branch conservation in both projective blowup charts

An invertible source coordinate change induces a bijection of exceptional
points, with analytic equivalences between the corresponding chart germs.
Exact transverse coordinates therefore give branch conservation for every
squarefree plane equation of specified maximal-ideal order.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- The blowup map at a finite or complementary exceptional point. -/
@[expose] noncomputable def projectiveBlowupChart (t : Option ℂ) : PointedMapGerm 2 2 :=
  (projectiveChartSource t).forward.comp (pointBlowupChartGerm (projectiveChartCenter t))

/-- A lift of a source equivalence between specified exceptional points,
including its invertible factor on the exceptional coordinate. -/
@[expose] def HasProjectiveBlowupLift (e : PointedEquivGerm 2) (a b : Option ℂ) : Prop :=
  ∃ (E : PointedEquivGerm 2) (U : Germ 2), IsUnit U ∧
    E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
    e.forward.comp (projectiveBlowupChart a) = (projectiveBlowupChart b).comp E.forward

private theorem projectiveChart_tangent (t : Option ℂ) :
    (blowupTangentComponent (projectiveChartSource t) (projectiveChartCenter t) 0 =
      t.getD 1) ∧
    (blowupTangentComponent (projectiveChartSource t) (projectiveChartCenter t) 1 =
      if t.isSome then 1 else 0) := by
  cases t with
  | none =>
    have hx : (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
        (coordinate (0 : Fin 2)) = coordinate 1 := by
      rw [PointedMapGerm.pullback_coordinate]
      exact coordinateSwapPointedEquiv_component_zero 1
    have hy : (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
        (coordinate (1 : Fin 2)) = coordinate 0 := coordinateSwapPointedEquiv_pullback_second
    change (blowupTangentComponent (coordinateSwapPointedEquiv (1 : Fin 2)) 0 0 = 1) ∧
      (blowupTangentComponent (coordinateSwapPointedEquiv (1 : Fin 2)) 0 1 = 0)
    simp only [blowupTangentComponent, hx, hy]
    simp [partialDerivative_coordinate_same]
  | some c =>
    simp [projectiveChartSource, projectiveChartCenter, blowupTangentComponent,
      PointedMapGerm.pullbackRingHom_identity, partialDerivative_coordinate_same]

/-- Two lifts of the same chart map have the same target exceptional point. -/
theorem projective_centers_eq_of_same_chart_lifts
    (parent E F : PointedEquivGerm 2) (ζ : ℂ) (a b : Option ℂ) (U V : Germ 2)
    (hU : IsUnit U) (hV : IsUnit V)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hFy : F.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V)
    (hE : parent.forward.comp (pointBlowupChartGerm ζ) =
      (projectiveBlowupChart a).comp E.forward)
    (hF : parent.forward.comp (pointBlowupChartGerm ζ) =
      (projectiveBlowupChart b).comp F.forward) : a = b := by
  have h (i : Fin 2) :=
    (blowupTangentComponent_of_commuting_charts parent (projectiveChartSource a) E
      ζ (projectiveChartCenter a) U hEy
      (by simpa only [PointedEquivGerm.comp, projectiveBlowupChart,
        PointedMapGerm.comp_assoc] using hE) i).symm.trans
    (blowupTangentComponent_of_commuting_charts parent (projectiveChartSource b) F
      ζ (projectiveChartCenter b) V hFy
      (by simpa only [PointedEquivGerm.comp, projectiveBlowupChart,
        PointedMapGerm.comp_assoc] using hF) i)
  have h0 := h 0
  have h1 := h 1
  rw [(projectiveChart_tangent a).1, (projectiveChart_tangent b).1] at h0
  rw [(projectiveChart_tangent a).2, (projectiveChart_tangent b).2] at h1
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some c =>
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, mul_zero,
        Option.isSome_some, if_true, mul_one] at h1
      exact False.elim (valueRingHom_ne_zero_of_isUnit hV h1.symm)
  | some c =>
    cases b with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, mul_zero,
        Option.isSome_some, if_true, mul_one] at h1
      exact False.elim (valueRingHom_ne_zero_of_isUnit hU h1)
    | some d =>
      simp only [Option.isSome_some, if_true, mul_one] at h1
      simp only [Option.getD_some] at h0
      rw [← h1] at h0
      exact congrArg some (mul_left_cancel₀ (valueRingHom_ne_zero_of_isUnit hU) h0)

namespace HasProjectiveBlowupLift

/-- A source equivalence lifts at every exceptional point. -/
theorem exists_target (e : PointedEquivGerm 2) (a : Option ℂ) :
    ∃ b, HasProjectiveBlowupLift e a b := by
  obtain ⟨b, E, U, hU, hEy, hcomm⟩ :=
    exists_twoChart_blowup_lift (e.comp (projectiveChartSource a)) (projectiveChartCenter a)
  refine ⟨b, E, U, hU, hEy, ?_⟩
  simpa only [PointedEquivGerm.comp, projectiveBlowupChart, PointedMapGerm.comp_assoc] using hcomm

/-- The target point of a lift is unique. -/
theorem target_unique {e : PointedEquivGerm 2} {a b c : Option ℂ}
    (h : HasProjectiveBlowupLift e a b) (k : HasProjectiveBlowupLift e a c) : b = c := by
  obtain ⟨E, U, hU, hEy, hE⟩ := h
  obtain ⟨F, V, hV, hFy, hF⟩ := k
  exact projective_centers_eq_of_same_chart_lifts (e.comp (projectiveChartSource a)) E F
    (projectiveChartCenter a) b c U V hU hV hEy hFy
    (by simpa only [PointedEquivGerm.comp, projectiveBlowupChart,
        PointedMapGerm.comp_assoc] using hE)
    (by simpa only [PointedEquivGerm.comp, projectiveBlowupChart,
        PointedMapGerm.comp_assoc] using hF)

/-- Inverting a commuting chart square gives the inverse lift. -/
theorem symm {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b) : HasProjectiveBlowupLift e.symm b a := by
  obtain ⟨E, U, hU, hEy, hcomm⟩ := h
  obtain ⟨V, hV, hVy⟩ := exists_inverse_exceptional_unit E U hU hEy
  refine ⟨E.symm, V, hV, hVy, ?_⟩
  have h := congrArg (fun B : PointedMapGerm 2 2 ↦ e.inverse.comp (B.comp E.inverse)) hcomm
  simp only [PointedMapGerm.comp_assoc, E.forward_inverse,
    PointedMapGerm.comp_identity] at h
  have hleft : e.inverse.comp (e.forward.comp ((projectiveBlowupChart a).comp E.inverse)) =
      (projectiveBlowupChart a).comp E.inverse := by
    rw [← PointedMapGerm.comp_assoc, e.inverse_forward, PointedMapGerm.identity_comp]
  rw [hleft] at h
  exact h.symm

end HasProjectiveBlowupLift

/-- The action of a source equivalence on exceptional points, constructed
from analytic chart lifts. -/
@[expose] noncomputable def projectiveCenterMap (e : PointedEquivGerm 2) (a : Option ℂ) :
    Option ℂ := Classical.choose (HasProjectiveBlowupLift.exists_target e a)

theorem projectiveCenterMap_hasLift (e : PointedEquivGerm 2) (a : Option ℂ) :
    HasProjectiveBlowupLift e a (projectiveCenterMap e a) :=
  Classical.choose_spec (HasProjectiveBlowupLift.exists_target e a)

/-- The induced map on exceptional points is bijective. -/
theorem projectiveCenterMap_bijective (e : PointedEquivGerm 2) :
    Function.Bijective (projectiveCenterMap e) := by
  have hleft (a : Option ℂ) : projectiveCenterMap e.symm (projectiveCenterMap e a) = a :=
    (projectiveCenterMap_hasLift e.symm _).target_unique (projectiveCenterMap_hasLift e a).symm
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · simpa only [hleft] using congrArg (projectiveCenterMap e.symm) hab
  · refine ⟨projectiveCenterMap e.symm b, ?_⟩
    exact (projectiveCenterMap_hasLift e _).target_unique
      (projectiveCenterMap_hasLift e.symm b).symm

/-- A fixed analytic chart lift transports every strict transform using
the same inverse child coordinates and an invertible scalar factor. -/
theorem projectiveStrictTransform_associated_of_lift
    (e E : PointedEquivGerm 2) (a b : Option ℂ) (U : Germ 2)
    (hU : IsUnit U)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hcomm : e.forward.comp (projectiveBlowupChart a) =
      (projectiveBlowupChart b).comp E.forward)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    Associated (projectiveStrictTransform m f hf b)
      (E.inverse.pullbackRingHom
        (projectiveStrictTransform m (e.forward.pullbackRingHom f)
          (e.forward.pullback_mem_maximalIdeal_pow hf) a)) := by
  let g := projectiveStrictTransform m (e.forward.pullbackRingHom f)
    (e.forward.pullback_mem_maximalIdeal_pow hf) a
  have hfactor : (pointBlowupChartGerm (projectiveChartCenter a)).pullbackRingHom
      ((e.comp (projectiveChartSource a)).forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ m * g := by
    simpa only [PointedEquivGerm.comp, PointedMapGerm.pullbackRingHom_comp,
      RingHom.comp_apply, g, projectiveStrictTransform] using
      pointBlowupTransform_factor (projectiveChartCenter a) m
        ((projectiveChartSource a).forward.pullbackRingHom (e.forward.pullbackRingHom f))
        ((projectiveChartSource a).forward.pullback_mem_maximalIdeal_pow
          (e.forward.pullback_mem_maximalIdeal_pow hf))
  obtain ⟨F, W, hW, hF, hfactorF⟩ := exists_inverse_transform_of_unit_blowup
    (e.comp (projectiveChartSource a)) (projectiveChartSource b) E
    (projectiveChartCenter a) (projectiveChartCenter b) U hU hEy
    (by simpa only [PointedEquivGerm.comp, projectiveBlowupChart,
      PointedMapGerm.comp_assoc] using hcomm) f g m hfactor
  have htransform : projectiveStrictTransform m f hf b = F :=
    pointBlowupTransform_unique (projectiveChartCenter b) m
      ((projectiveChartSource b).forward.pullbackRingHom f) _ _
      (pointBlowupTransform_factor _ _ _ _) hfactorF
  rw [htransform, hF]
  exact associated_unit_mul_left _ _ hW

/-- Corresponding strict transforms differ by a unit and an invertible
analytic change of child coordinates. -/
theorem HasProjectiveBlowupLift.strictTransform_associated
    {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    ∃ E : PointedEquivGerm 2,
      Associated (projectiveStrictTransform m f hf b)
        (E.forward.pullbackRingHom
          (projectiveStrictTransform m (e.forward.pullbackRingHom f)
            (e.forward.pullback_mem_maximalIdeal_pow hf) a)) := by
  obtain ⟨E, U, hU, hEy, hcomm⟩ := h
  exact ⟨E.symm, projectiveStrictTransform_associated_of_lift e E a b U hU hEy hcomm m f hf⟩

/-- The analytic lift preserves the number of branches of a strict transform. -/
theorem HasProjectiveBlowupLift.branchCount_eq
    {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    PlaneCurve.irreducibleBranchCount (projectiveStrictTransform m f hf b) =
      PlaneCurve.irreducibleBranchCount
        (projectiveStrictTransform m (e.forward.pullbackRingHom f)
          (e.forward.pullback_mem_maximalIdeal_pow hf) a) := by
  obtain ⟨E, hE⟩ := h.strictTransform_associated m f hf
  exact (PlaneCurve.irreducibleBranchCount_eq_of_associated hE).trans
    (PlaneCurve.irreducibleBranchCount_pullback E _).symm

/-- The analytic lift preserves whether a strict transform is a unit. -/
theorem HasProjectiveBlowupLift.isUnit_iff
    {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    IsUnit (projectiveStrictTransform m f hf b) ↔
      IsUnit (projectiveStrictTransform m (e.forward.pullbackRingHom f)
        (e.forward.pullback_mem_maximalIdeal_pow hf) a) := by
  obtain ⟨E, hE⟩ := h.strictTransform_associated m f hf
  exact hE.isUnit_iff.trans (MulEquiv.isUnit_map E.pullbackRingEquiv)

/-- A squarefree transformed equation remains squarefree under the lift. -/
theorem HasProjectiveBlowupLift.squarefree
    {e : PointedEquivGerm 2} {a b : Option ℂ}
    (h : HasProjectiveBlowupLift e a b)
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hsq : Squarefree (projectiveStrictTransform m (e.forward.pullbackRingHom f)
      (e.forward.pullback_mem_maximalIdeal_pow hf) a)) :
    Squarefree (projectiveStrictTransform m f hf b) := by
  obtain ⟨E, hE⟩ := h.strictTransform_associated m f hf
  exact hE.squarefree_iff.mpr (E.squarefree_pullback _ hsq)

/-- Every squarefree equation of exact order has finitely many nonunit
strict transforms in the two projective charts. Their branch counts sum
to the original branch count, and every strict transform is squarefree. -/
theorem exists_projectiveStrictTransform_branchCount_sum
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (hsq : Squarefree f) :
    ∃ s : Finset (Option ℂ),
      (∀ t, t ∈ s ↔ ¬ IsUnit (projectiveStrictTransform m f hf t)) ∧
      PlaneCurve.irreducibleBranchCount f =
        ∑ t ∈ s, PlaneCurve.irreducibleBranchCount (projectiveStrictTransform m f hf t) ∧
      (∀ t, Squarefree (projectiveStrictTransform m f hf t)) := by
  classical
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hf hnext
  let g := e.forward.pullbackRingHom f
  have hg : g ∈ maximalIdeal 2 ^ m := e.forward.pullback_mem_maximalIdeal_pow hf
  obtain ⟨s, hs, hcount, hsqfinite, hinfinity⟩ :=
    exists_pointBlowupTransform_branchCount_sum_of_squarefree_regular m g hg he
      (e.squarefree_pullback f hsq)
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
  have hScount : PlaneCurve.irreducibleBranchCount g =
      ∑ a ∈ S, PlaneCurve.irreducibleBranchCount (projectiveStrictTransform m g hg a) := by
    rw [show S = s.image some from rfl, Finset.sum_image]
    · simpa only [projectiveStrictTransform_some] using hcount
    · exact fun _ _ _ _ h ↦ Option.some.inj h
  have hinj := (projectiveCenterMap_bijective e).1
  refine ⟨S.image (projectiveCenterMap e), ?_, ?_, ?_⟩
  · intro t
    obtain ⟨a, rfl⟩ := (projectiveCenterMap_bijective e).2 t
    rw [(projectiveCenterMap_hasLift e a).isUnit_iff m f hf, ← hS a]
    constructor
    · rintro h
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp h
      exact hinj hab ▸ hb
    · exact Finset.mem_image_of_mem _
  · calc
      PlaneCurve.irreducibleBranchCount f = PlaneCurve.irreducibleBranchCount g :=
        PlaneCurve.irreducibleBranchCount_pullback e f
      _ = ∑ a ∈ S, PlaneCurve.irreducibleBranchCount
          (projectiveStrictTransform m g hg a) := hScount
      _ = ∑ t ∈ S.image (projectiveCenterMap e), PlaneCurve.irreducibleBranchCount
          (projectiveStrictTransform m f hf t) := by
        rw [Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
        exact Finset.sum_congr rfl (fun a _ ↦
          ((projectiveCenterMap_hasLift e a).branchCount_eq m f hf).symm)
  · intro t
    obtain ⟨a, rfl⟩ := (projectiveCenterMap_bijective e).2 t
    exact (projectiveCenterMap_hasLift e a).squarefree m f hf (hSsq a)

/-- Any finite list containing the nonunit projective transforms may
index the branch sum. Unit transforms contribute zero. -/
theorem projectiveStrictTransform_branchCount_sum_of_finite_cover
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) (hsq : Squarefree f)
    (s : Finset (Option ℂ))
    (hcover : ∀ t, ¬ IsUnit (projectiveStrictTransform m f hf t) → t ∈ s) :
    PlaneCurve.irreducibleBranchCount f =
      ∑ t ∈ s, PlaneCurve.irreducibleBranchCount (projectiveStrictTransform m f hf t) := by
  classical
  obtain ⟨r, hr, hcount, _⟩ :=
    exists_projectiveStrictTransform_branchCount_sum m f hf hnext hsq
  rw [hcount]
  apply Finset.sum_subset
  · exact fun t ht ↦ hcover t ((hr t).mp ht)
  · intro t _ ht
    have hunit : IsUnit (projectiveStrictTransform m f hf t) := by
      by_contra hnot
      exact ht ((hr t).mpr hnot)
    exact PlaneCurve.irreducibleBranchCount_eq_zero_of_isUnit _ hunit

end OnLeConjecture.Analytic.Germ
