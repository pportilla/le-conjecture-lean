/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveReducedBlowupBranchCount
public import OnLeConjecture.Analytic.ProjectiveBlowupSquareFactor
public import OnLeConjecture.Analytic.PointBlowupIntersection

/-!
# The intersection recurrence in both projective blowup charts

A common transverse coordinate system is constructed from the product of
two equations. The bijection of exceptional points and the analytic chart
lifts transport the finite-chart intersection recurrence to the original
coordinates, including the complementary exceptional point.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic

/-- Replacing either equation by an associated equation preserves the
ideal defining the intersection algebra. -/
theorem pairIdeal_eq_of_associated {f g F G : Germ 2}
    (hf : Associated f F) (hg : Associated g G) : pairIdeal f g = pairIdeal F G := by
  obtain ⟨U, hU⟩ := hf
  obtain ⟨V, hV⟩ := hg
  rw [← hU, ← hV, mul_comm f (U : Germ 2), mul_comm g (V : Germ 2)]
  exact (pairIdeal_unit_mul_both _ _ _ _ U.isUnit V.isUnit).symm

/-- Associated defining equations have equal finite local intersections. -/
theorem intersectionMultiplicity_eq_of_associated {f g F G : Germ 2}
    (hf : Associated f F) (hg : Associated g G)
    (hfg : HasFiniteIntersection f g) (hFG : HasFiniteIntersection F G) :
    intersectionMultiplicity f g hfg = intersectionMultiplicity F G hFG := by
  change Module.finrank ℂ _ = Module.finrank ℂ _
  rw [pairIdeal_eq_of_associated hf hg]

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- Two nonzero equations admit one source coordinate system in which
both first-axis orders equal their specified ordinary orders. -/
theorem exists_linear_equiv_pair_regularInFirstCoordinateOfOrder
    (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfn : f ∉ maximalIdeal 2 ^ (m + 1)) (hgn : g ∉ maximalIdeal 2 ^ (n + 1)) :
    ∃ e : PointedEquivGerm 2,
      IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom f) m ∧
      IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom g) n := by
  obtain ⟨hfg, hfgn⟩ := exact_maximalIdeal_order_mul m n f g hf hfn hg hgn
  obtain ⟨e, he⟩ := exists_linear_equiv_regularInFirstCoordinateOfOrder hfg hfgn
  have hF := e.forward.pullback_mem_maximalIdeal_pow hf
  have hG := e.forward.pullback_mem_maximalIdeal_pow hg
  have hFn := (e.pullback_mem_maximalIdeal_pow_iff f).not.mpr hfn
  have hGn := (e.pullback_mem_maximalIdeal_pow_iff g).not.mpr hgn
  have hFne : e.forward.pullbackRingHom f ≠ 0 := by
    intro hz
    exact hFn (hz ▸ (maximalIdeal 2 ^ (m + 1)).zero_mem)
  have hGne : e.forward.pullbackRingHom g ≠ 0 := by
    intro hz
    exact hGn (hz ▸ (maximalIdeal 2 ^ (n + 1)).zero_mem)
  obtain ⟨k, hk, hkreg⟩ := exists_exact_regular_order_of_dvd (m + n)
    (e.forward.pullbackRingHom (f * g)) (e.forward.pullbackRingHom f)
    (e.forward.pullback_mem_maximalIdeal_pow hfg) he hFne
    (by rw [map_mul]; exact dvd_mul_right _ _)
  obtain ⟨l, hl, hlreg⟩ := exists_exact_regular_order_of_dvd (m + n)
    (e.forward.pullbackRingHom (f * g)) (e.forward.pullbackRingHom g)
    (e.forward.pullback_mem_maximalIdeal_pow hfg) he hGne
    (by rw [map_mul]; exact dvd_mul_left _ _)
  have hkm : k = m := exact_maximalIdeal_order_unique k m _ hk
    (not_mem_succ_maximalIdeal_pow_of_first_regular _ _ hkreg) hF hFn
  have hln : l = n := exact_maximalIdeal_order_unique l n _ hl
    (not_mem_succ_maximalIdeal_pow_of_first_regular _ _ hlreg) hG hGn
  exact ⟨e, hkm ▸ hkreg, hln ▸ hlreg⟩

/-- Exact first order and finite intersection ensure finite intersection
of strict transforms at every finite or complementary exceptional point. -/
theorem hasFiniteIntersection_projectiveStrictTransforms
    (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfn : f ∉ maximalIdeal 2 ^ (m + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g) (t : Option ℂ) :
    PlaneCurve.HasFiniteIntersection
      (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t) := by
  exact hasFiniteIntersection_pointBlowupTransforms (projectiveChartCenter t) m n
    ((projectiveChartSource t).forward.pullbackRingHom f)
    ((projectiveChartSource t).forward.pullbackRingHom g)
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hf)
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow hg)
    (((projectiveChartSource t).pullback_mem_maximalIdeal_pow_iff f).not.mpr hfn)
    (hfinite.pullback (projectiveChartSource t))

/-- A chart lift preserves the finite intersection of both strict transforms. -/
theorem HasProjectiveBlowupLift.intersectionMultiplicity_eq
    {e : PointedEquivGerm 2} {a b : Option ℂ} (h : HasProjectiveBlowupLift e a b)
    (m n : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hleft : PlaneCurve.HasFiniteIntersection
      (projectiveStrictTransform m f hf b) (projectiveStrictTransform n g hg b))
    (hright : PlaneCurve.HasFiniteIntersection
      (projectiveStrictTransform m (e.forward.pullbackRingHom f)
        (e.forward.pullback_mem_maximalIdeal_pow hf) a)
      (projectiveStrictTransform n (e.forward.pullbackRingHom g)
        (e.forward.pullback_mem_maximalIdeal_pow hg) a)) :
    PlaneCurve.intersectionMultiplicity
      (projectiveStrictTransform m f hf b) (projectiveStrictTransform n g hg b) hleft =
    PlaneCurve.intersectionMultiplicity
      (projectiveStrictTransform m (e.forward.pullbackRingHom f)
        (e.forward.pullback_mem_maximalIdeal_pow hf) a)
      (projectiveStrictTransform n (e.forward.pullbackRingHom g)
        (e.forward.pullback_mem_maximalIdeal_pow hg) a) hright := by
  obtain ⟨E, U, hU, hEy, hcomm⟩ := h
  have hF := projectiveStrictTransform_associated_of_lift e E a b U hU hEy hcomm m f hf
  have hG := projectiveStrictTransform_associated_of_lift e E a b U hU hEy hcomm n g hg
  exact (PlaneCurve.intersectionMultiplicity_eq_of_associated hF hG hleft
    (hright.pullback E.symm)).trans
    (PlaneCurve.intersectionMultiplicity_pullback E.symm hright).symm

/-- The complete intersection recurrence in the original projective
charts. Exact ordinary orders replace any first-axis regularity hypothesis. -/
theorem exists_projectiveBlowup_intersection_recurrence
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfn : f ∉ maximalIdeal 2 ^ (m + 1)) (hgn : g ∉ maximalIdeal 2 ^ (n + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g) :
    ∃ s : Finset (Option ℂ),
      (∀ t, t ∈ s ↔ ¬ IsUnit (projectiveStrictTransform m f hf t)) ∧
      ∃ hlocal : ∀ t, PlaneCurve.HasFiniteIntersection
        (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t),
        PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ t ∈ s,
          PlaneCurve.intersectionMultiplicity
            (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t)
            (hlocal t) := by
  classical
  obtain ⟨e, heF, heG⟩ :=
    exists_linear_equiv_pair_regularInFirstCoordinateOfOrder m n f g hf hg hfn hgn
  let F := e.forward.pullbackRingHom f
  let G := e.forward.pullbackRingHom g
  have hF : F ∈ maximalIdeal 2 ^ m := e.forward.pullback_mem_maximalIdeal_pow hf
  have hG : G ∈ maximalIdeal 2 ^ n := e.forward.pullback_mem_maximalIdeal_pow hg
  have hFn : F ∉ maximalIdeal 2 ^ (m + 1) :=
    (e.pullback_mem_maximalIdeal_pow_iff f).not.mpr hfn
  have hFG : PlaneCurve.HasFiniteIntersection F G := hfinite.pullback e
  obtain ⟨s, hs, hfiniteFG, hcount, hinfinity⟩ :=
    exists_pointBlowup_intersection_recurrence_of_regular m n hm hn F G hF hG heF heG hFG
  let S : Finset (Option ℂ) := s.image some
  have hS (a : Option ℂ) : a ∈ S ↔ ¬ IsUnit (projectiveStrictTransform m F hF a) := by
    cases a with
    | none =>
      have hinf : IsUnit (projectiveStrictTransform m F hF none) := hinfinity
      simp [S, hinf]
    | some c =>
      simpa only [S, Finset.mem_image, Option.some.injEq, exists_eq_right,
        projectiveStrictTransform_some] using hs c
  have hlocal := hasFiniteIntersection_projectiveStrictTransforms m n f g hf hg hfn hfinite
  have hnew := hasFiniteIntersection_projectiveStrictTransforms m n F G hF hG hFn hFG
  let I : Option ℂ → ℕ := fun t ↦ PlaneCurve.intersectionMultiplicity
    (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t) (hlocal t)
  let J : Option ℂ → ℕ := fun a ↦ PlaneCurve.intersectionMultiplicity
    (projectiveStrictTransform m F hF a) (projectiveStrictTransform n G hG a) (hnew a)
  have hJ (a : Option ℂ) : I (projectiveCenterMap e a) = J a :=
    (projectiveCenterMap_hasLift e a).intersectionMultiplicity_eq m n f g hf hg
      (hlocal _) (hnew a)
  have hScount : PlaneCurve.intersectionMultiplicity F G hFG = m * n + ∑ a ∈ S, J a := by
    rw [show S = s.image some from rfl, Finset.sum_image]
    · rw [Finset.sum_coe_sort s (fun c ↦ PlaneCurve.intersectionMultiplicity
        (pointBlowupTransform c m F hF) (pointBlowupTransform c n G hG) (hfiniteFG c))]
        at hcount
      simpa only [J, projectiveStrictTransform_some] using hcount
    · exact fun _ _ _ _ h ↦ Option.some.inj h
  have hinj := (projectiveCenterMap_bijective e).1
  refine ⟨S.image (projectiveCenterMap e), ?_, hlocal, ?_⟩
  · intro t
    obtain ⟨a, rfl⟩ := (projectiveCenterMap_bijective e).2 t
    rw [(projectiveCenterMap_hasLift e a).isUnit_iff m f hf, ← hS a]
    constructor
    · rintro h
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp h
      exact hinj hab ▸ hb
    · exact Finset.mem_image_of_mem _
  · change PlaneCurve.intersectionMultiplicity f g hfinite =
      m * n + ∑ t ∈ S.image (projectiveCenterMap e), I t
    have hparent : PlaneCurve.intersectionMultiplicity f g hfinite =
        PlaneCurve.intersectionMultiplicity F G hFG :=
      PlaneCurve.intersectionMultiplicity_pullback e hfinite
    rw [hparent, hScount, Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
    congr 1
    exact Finset.sum_congr rfl (fun a _ ↦ (hJ a).symm)

/-- A finite set containing the simultaneous nonunit projective transforms
indexes the intersection recurrence. -/
theorem projectiveBlowup_intersection_recurrence_of_common_zero_cover
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfn : f ∉ maximalIdeal 2 ^ (m + 1)) (hgn : g ∉ maximalIdeal 2 ^ (n + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g) (s : Finset (Option ℂ))
    (hcover : ∀ t, ¬ IsUnit (projectiveStrictTransform m f hf t) →
      ¬ IsUnit (projectiveStrictTransform n g hg t) → t ∈ s) :
    ∃ hlocal : ∀ t, PlaneCurve.HasFiniteIntersection
      (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t),
      PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ t ∈ s,
        PlaneCurve.intersectionMultiplicity
          (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t) (hlocal t) := by
  classical
  obtain ⟨r, hr, hlocal, hi⟩ :=
    exists_projectiveBlowup_intersection_recurrence m n hm hn f g hf hg hfn hgn hfinite
  let I : Option ℂ → ℕ := fun t ↦ PlaneCurve.intersectionMultiplicity
    (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t) (hlocal t)
  have hzeroR (t : Option ℂ) (ht : t ∉ r) : I t = 0 := by
    have hunit : IsUnit (projectiveStrictTransform m f hf t) := by
      by_contra hnot
      exact ht ((hr t).mpr hnot)
    exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hunit _
  have hzeroS (t : Option ℂ) (ht : t ∉ s) : I t = 0 := by
    by_cases hunit : IsUnit (projectiveStrictTransform m f hf t)
    · exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_left _ _ hunit _
    · have hgunit : IsUnit (projectiveStrictTransform n g hg t) := by
        by_contra hnot
        exact ht (hcover t hunit hnot)
      exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_right _ _ hgunit _
  have hsumR : (∑ t ∈ r, I t) = ∑ t ∈ r ∪ s, I t :=
    Finset.sum_subset Finset.subset_union_left (fun t _ ht ↦ hzeroR t ht)
  have hsumS : (∑ t ∈ s, I t) = ∑ t ∈ r ∪ s, I t :=
    Finset.sum_subset Finset.subset_union_right (fun t _ ht ↦ hzeroS t ht)
  refine ⟨hlocal, ?_⟩
  change PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ t ∈ s, I t
  change PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ t ∈ r, I t at hi
  rw [hi, hsumR, hsumS]

/-- A separated finite list of projective points containing all common
zeros may index the complete intersection recurrence. -/
theorem projectiveBlowup_intersection_recurrence_of_indexed_common_zero_cover
    {κ : Type*} (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ n)
    (hfn : f ∉ maximalIdeal 2 ^ (m + 1)) (hgn : g ∉ maximalIdeal 2 ^ (n + 1))
    (hfinite : PlaneCurve.HasFiniteIntersection f g) (s : Finset κ)
    (center : κ → Option ℂ) (hinj : Set.InjOn center s)
    (hcover : ∀ t, ¬ IsUnit (projectiveStrictTransform m f hf t) →
      ¬ IsUnit (projectiveStrictTransform n g hg t) → ∃ i ∈ s, center i = t) :
    ∃ hlocal : ∀ t, PlaneCurve.HasFiniteIntersection
      (projectiveStrictTransform m f hf t) (projectiveStrictTransform n g hg t),
      PlaneCurve.intersectionMultiplicity f g hfinite = m * n + ∑ i ∈ s,
        PlaneCurve.intersectionMultiplicity
          (projectiveStrictTransform m f hf (center i))
          (projectiveStrictTransform n g hg (center i)) (hlocal (center i)) := by
  classical
  obtain ⟨hlocal, hi⟩ := projectiveBlowup_intersection_recurrence_of_common_zero_cover
    m n hm hn f g hf hg hfn hgn hfinite (s.image center)
      (fun t ht hu ↦ Finset.mem_image.mpr (hcover t ht hu))
  refine ⟨hlocal, ?_⟩
  rw [hi, Finset.sum_image hinj]

end OnLeConjecture.Analytic.Germ
