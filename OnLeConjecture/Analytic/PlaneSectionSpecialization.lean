/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionNearbyPoints

/-!
# Specialization of the delta invariant of plane sections

Let `g : (ℂ², 0) → (ℂ³, 0)` be locally injective with an analytic
representative `G`, let `V_s = {G₀ = s}` and let `W_s = G(V_s)` be the image
of the level curve in the plane `{x₀ = s}`. Assume that `V₀` is reduced and
meets `{G₂ = 0}` finitely at the origin.

For every sufficiently small ball and every sufficiently small nonzero `s`,
the level curve `V_s` is smooth in the ball, the critical points of `G` on
it form a finite set `Z_s`, and

`δ(W₀) = δ(V₀) + ∑_{x ∈ Z_s} δ(W_s, G(x))`.

The proof applies the central polar identity at the origin and at every
point of `V_s` where the Jacobian `J(G₀, G₂)` or the pulled back surface
polar `∂₁F ∘ G` vanishes, and sums these identities using conservation of
intersection multiplicities along the level curves of `G₀`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric Set
open scoped Topology
open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

theorem fderiv_component_apply {G : Source 2 → Source 3} {x : Source 2}
    (hG : DifferentiableAt ℂ G x) (j : Fin 3) (z : Source 2) :
    fderiv ℂ (fun y => G y j) x z = fderiv ℂ G x z j := by
  have h := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j).hasFDerivAt.comp x
    hG.hasFDerivAt).fderiv
  change fderiv ℂ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j) ∘ G) x z = _
  rw [h]
  rfl

theorem eq_sum_coordinateVector (z : Source 2) :
    z = z 0 • coordinateVector (0 : Fin 2) + z 1 • coordinateVector (1 : Fin 2) := by
  funext i
  fin_cases i <;> simp [coordinateVector]

/-- At a critical point of `G` the section Jacobian vanishes. -/
theorem sectionJacobian_eq_zero_of_not_injective {G : Source 2 → Source 3} {x : Source 2}
    (hG : DifferentiableAt ℂ G x) (hni : ¬ Function.Injective (fderiv ℂ G x)) :
    sectionJacobian G x = 0 := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, fderiv ℂ G x a = fderiv ℂ G x b ∧ a ≠ b := by
    by_contra h
    push Not at h
    exact hni fun a b hab => h a b hab
  set z := a - b with hz
  have hz0 : z ≠ 0 := sub_ne_zero.mpr hne
  have hLz : fderiv ℂ G x z = 0 := by rw [hz, map_sub, hab, sub_self]
  have hcomp (j : Fin 3) : fderiv ℂ (fun y => G y j) x z = 0 := by
    rw [fderiv_component_apply hG, hLz]
    rfl
  have hexp (j : Fin 3) : z 0 * fderiv ℂ (fun y => G y j) x (coordinateVector 0) +
      z 1 * fderiv ℂ (fun y => G y j) x (coordinateVector 1) = 0 := by
    have h := hcomp j
    rw [eq_sum_coordinateVector z, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h
  have h0 := hexp 0
  have h2 := hexp 2
  unfold sectionJacobian
  set A := fderiv ℂ (fun y => G y 0) x (coordinateVector 0)
  set B := fderiv ℂ (fun y => G y 0) x (coordinateVector 1)
  set C := fderiv ℂ (fun y => G y 2) x (coordinateVector 0)
  set E := fderiv ℂ (fun y => G y 2) x (coordinateVector 1)
  have hz0' : (A * E - B * C) * z 0 = 0 := by linear_combination E * h0 - B * h2
  have hz1' : (A * E - B * C) * z 1 = 0 := by linear_combination A * h2 - C * h0
  by_contra hdet
  apply hz0
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp hz0').resolve_left hdet
  · exact (mul_eq_zero.mp hz1').resolve_left hdet

theorem analyticAt_sectionJacobian {G : Source 2 → Source 3} {x : Source 2}
    (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (sectionJacobian G) x :=
  (PointedMapGerm.jacobian_recenterOfFunction_components G x hG 0 2).choose

theorem PointedMapGerm.recenterOfFunction_zero (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0)
    (hG0 : G 0 = 0) :
    PointedMapGerm.recenterOfFunction G 0 hG = PointedMapGerm.ofFunction G hG hG0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with z
  simp [hG0]

theorem ofFunctionAt_of_eq_zero {n : ℕ} {F : Source n → ℂ} {p : Source n} (hp : p = 0)
    (h : AnalyticAt ℂ F p) (hF : AnalyticAt ℂ F 0) : ofFunctionAt F p h = ofFunction F hF := by
  subst hp
  exact (germAt_eq h).symm.trans (germAt_zero_eq hF)

theorem intersectionMultiplicity_congr {a a' b b' : Germ 2} (ha : a = a') (hb : b = b')
    (h : HasFiniteIntersection a b) (h' : HasFiniteIntersection a' b') :
    intersectionMultiplicity a b h = intersectionMultiplicity a' b' h' := by
  subst ha
  subst hb
  rfl

theorem sub_ne_zero_of_hasFiniteIntersection_germAt {f h : Source 2 → ℂ} {x : Source 2}
    (hf : AnalyticAt ℂ f x) (hfx : f x = 0)
    (hfin : HasFiniteIntersection (germAt f x) (germAt h x)) : germAt h x ≠ 0 := by
  intro h0
  rw [h0] at hfin
  have hu := isUnit_of_hasFiniteIntersection_zero_right _ hfin
  rw [germAt_eq hf, isUnit_ofFunctionAt_iff] at hu
  exact hu hfx

/-- At a point where `G` is an immersion, the local delta invariant of the
image of the level curve vanishes. -/
theorem localSectionDelta_eq_zero_of_injective (G : Source 2 → Source 3) (x : Source 2)
    (hG : AnalyticAt ℂ G x) (S : Set (Source 2)) (hS : S ∈ 𝓝 x) (hinj : InjOn G S)
    (hsmooth : ∃ z : Source 2, fderiv ℂ G x z 0 ≠ 0)
    (himm : Function.Injective (fderiv ℂ G x)) : localSectionDelta G x = 0 := by
  obtain ⟨D, hirr, -, -, hsm, -⟩ := exists_recentered_section_image_delta G x hG S hS hinj hsmooth
  rw [localSectionDelta_eq G x hG
    (PointedMapGerm.recenter_hasInjectiveRepresentative G x hG S hS hinj) D]
  exact deltaInvariant_eq_zero_of_order_one (irreducible_mem_maximalIdeal _ hirr) (hsm.mpr himm)

/-- **Specialization of the delta invariant of plane sections.** Let `g` be
a locally injective germ `(ℂ², 0) → (ℂ³, 0)` with analytic representative
`G`, reduced section `g₀` (encoded by the factorization `D`), and with `g₀`
meeting `g₂` finitely. For every sufficiently small radius `r` and every
sufficiently small nonzero `s`:
* the level curve `{G₀ = s}` is smooth in the ball of radius `r`.
* the critical points of `G` on it form a finite set `Z`.
* `δ(W₀) = δ(V₀) + ∑_{x ∈ Z} δ(W_s, G(x))`, where `δ(W_s, G(x))` is the
  delta invariant of the image germ of the level curve at `G(x)`. -/
theorem plane_section_delta_specialization
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (D : SectionImageFactorization g)
    (haxis : HasFiniteIntersection (g.1.component 0) (g.1.component 2))
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = PointedMapGerm.ofFunction G hG hG0) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 →
      ∃ Z : Finset (Source 2),
        (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ G x 0 = s ∧
          ¬ Function.Injective (fderiv ℂ G x))) ∧
        (∀ x ∈ ball (0 : Source 2) r, G x 0 = s → fderiv ℂ (fun y => G y 0) x ≠ 0) ∧
        deltaInvariant D.imageEquation =
          deltaInvariant (g.1.component 0) + ∑ x ∈ Z, localSectionDelta G x := by
  classical
  set v : Source 2 → ℂ := fun y => G y 0 with hvdef
  have hv : AnalyticAt ℂ v 0 := (analyticAt_pi_iff.mp hG) 0
  have hv0 : v 0 = 0 := by simp [hvdef, hG0]
  have hvg : ofFunction v hv = g.1.component 0 := by
    rw [hg]
    apply Subtype.ext
    exact (MapGerm.component_ofFunction G hG 0).symm
  have hsqv : Squarefree (ofFunction v hv) := hvg ▸ D.squarefree_component_zero
  have hf := g.injective_isFiniteAtOrigin_two hi
  obtain ⟨Φ, -, -, hker⟩ := g.exists_irreducible_generator_of_finite hf
  obtain ⟨F, hF, rfl⟩ := exists_analyticRepresentative_allOrders Φ
  obtain ⟨hJ0, hP0, heq0⟩ := D.two_mul_deltaInvariant_add_polar_eq hi _ hker haxis
  have hrec := (PointedMapGerm.recenterOfFunction_zero G hG hG0).trans hg.symm
  have hF0 : AnalyticAt ℂ F (G 0) := by rw [hG0]; exact hF
  have hJan : AnalyticAt ℂ (sectionJacobian G) 0 := analyticAt_sectionJacobian hG
  have hPan : AnalyticAt ℂ (surfacePolar F G) 0 := analyticAt_surfacePolar hG hF0
  have hJgerm : jacobian (g.1.component 0) (g.1.component 2) =
      ofFunction (sectionJacobian G) hJan := by
    rw [← hrec, recenter_jacobian_eq_germAt, germAt_zero_eq hJan]
  have hPgerm : g.pullbackRingHom (partialDerivative (1 : Fin 3) (ofFunction F hF)) =
      ofFunction (surfacePolar F G) hPan := by
    have h := recenter_pullback_partial_eq_germAt F G 0 hG hF0
    rw [hrec, ofFunctionAt_of_eq_zero hG0 hF0 hF, germAt_zero_eq hPan] at h
    exact h
  have hfinJ : HasFiniteIntersection (ofFunction v hv) (ofFunction (sectionJacobian G) hJan) := by
    rw [hvg, ← hJgerm]
    exact hJ0
  have hfinP : HasFiniteIntersection (ofFunction v hv) (ofFunction (surfacePolar F G) hPan) := by
    rw [hvg, ← hPgerm]
    exact hP0
  have heq0' : 2 * deltaInvariant D.imageEquation + intersectionMultiplicity _ _ hfinJ =
      2 * deltaInvariant (g.1.component 0) + intersectionMultiplicity _ _ hfinP := by
    rw [intersectionMultiplicity_congr hvg hJgerm.symm hfinJ hJ0,
      intersectionMultiplicity_congr hvg hPgerm.symm hfinP hP0]
    exact heq0
  obtain ⟨rJ, hrJ, hcJ⟩ := conservesAlongLevels v (sectionJacobian G) hv hJan hv0 hfinJ
  obtain ⟨rP, hrP, hcP⟩ := conservesAlongLevels v (surfacePolar F G) hv hPan hv0 hfinP
  -- an injective neighbourhood for `G`
  obtain ⟨G', hG', hG'0, hgG', S₀, hS₀, hinj₀⟩ := hi
  have hGG' : G =ᶠ[𝓝 0] G' :=
    Filter.Germ.coe_eq.mp (congrArg (fun p => p.1.1) (hg.symm.trans hgG'))
  have hS : S₀ ∩ {y | G y = G' y} ∩ {y | AnalyticAt ℂ G y} ∈ 𝓝 (0 : Source 2) :=
    inter_mem (inter_mem hS₀ hGG') hG.eventually_analyticAt
  obtain ⟨R, hR, hRS, hGan, -, hFG, hiff⟩ :=
    g.exists_closedBall_image_eq_zero_set_of_finite hf G hG hG0 hg F hF hker _ hS
  have hinjR : InjOn G (closedBall (0 : Source 2) R) := by
    intro a ha b hb hab
    have ha' := hRS ha
    have hb' := hRS hb
    apply hinj₀ ha'.1.1 hb'.1.1
    rw [← ha'.1.2, ← hb'.1.2, hab]
  obtain ⟨W, hWsub, hWo, hW0⟩ := _root_.mem_nhds_iff.mp (hiff.and hF.eventually_analyticAt)
  have hWG : G ⁻¹' W ∈ 𝓝 (0 : Source 2) :=
    hG.continuousAt.preimage_mem_nhds (hWo.mem_nhds (by rw [hG0]; exact hW0))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hWG (eventually_fderiv_ne_zero_of_squarefree_of_ne v hv hv0 hsqv))
  refine ⟨min (min rJ rP) (min ε R), lt_min (lt_min hrJ hrP) (lt_min hε hR),
    fun r hr hrle => ?_⟩
  have hrJ' : r ≤ rJ := hrle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrP' : r ≤ rP := hrle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrε : r ≤ ε := hrle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : r ≤ R := hrle.trans ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [hcJ r hr hrJ', hcP r hr hrP'] with s hsJ hsP hs0
  obtain ⟨ZJ, hZJ, hZJfin, hZJsum⟩ := hsJ hs0
  obtain ⟨ZP, hZP, hZPfin, hZPsum⟩ := hsP hs0
  -- data at the points of the ball
  have hballR : ∀ x ∈ ball (0 : Source 2) r, x ∈ ball (0 : Source 2) R :=
    fun x hx => ball_subset_ball hrR hx
  have hGx : ∀ x ∈ ball (0 : Source 2) r, AnalyticAt ℂ G x :=
    fun x hx => hGan x (ball_subset_closedBall (hballR x hx))
  have hεx : ∀ x ∈ ball (0 : Source 2) r, G x ∈ W ∧ (x ≠ 0 → fderiv ℂ v x ≠ 0) :=
    fun x hx => hεsub (ball_subset_ball hrε hx)
  have hinjx : ∀ x (hx : x ∈ ball (0 : Source 2) r),
      (PointedMapGerm.recenterOfFunction G x (hGx x hx)).HasInjectiveRepresentative :=
    fun x hx => PointedMapGerm.recenter_hasInjectiveRepresentative G x (hGx x hx) _
      (isOpen_ball.mem_nhds (hballR x hx)) (hinjR.mono ball_subset_closedBall)
  have hlevel : ∀ x ∈ ball (0 : Source 2) r, v x = s →
      x ≠ 0 ∧ fderiv ℂ v x ≠ 0 ∧ ∃ z : Source 2, fderiv ℂ G x z 0 ≠ 0 := by
    intro x hx hvx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hs0 (hvx.symm.trans hv0)
    have hd := (hεx x hx).2 hx0
    refine ⟨hx0, hd, ?_⟩
    by_contra hall
    push Not at hall
    apply hd
    ext z
    rw [hvdef, fderiv_component_apply (hGx x hx).differentiableAt]
    exact hall z
  -- the pointwise identity
  have hpoint : ∀ x ∈ ZJ ∪ ZP,
      2 * localSectionDelta G x + localIntersection (fun y => v y - s) (sectionJacobian G) x =
        localIntersection (fun y => v y - s) (surfacePolar F G) x := by
    intro x hxU
    have hxdata : x ∈ ball (0 : Source 2) r ∧ v x = s := by
      rcases Finset.mem_union.mp hxU with hx | hx
      · exact ⟨((hZJ x).mp hx).1, ((hZJ x).mp hx).2.1⟩
      · exact ⟨((hZP x).mp hx).1, ((hZP x).mp hx).2.1⟩
    obtain ⟨hx, hvx⟩ := hxdata
    obtain ⟨hx0, -, hsmooth⟩ := hlevel x hx hvx
    have hGx' := hGx x hx
    have hFx : AnalyticAt ℂ F (G x) := (hWsub (hεx x hx).1).2
    have hfun : (fun y => G y 0 - G x 0) = fun y => v y - s := by
      funext y
      rw [← hvx]
    have hvsan : AnalyticAt ℂ (fun y => v y - s) x :=
      ((analyticAt_pi_iff.mp hGx') 0).sub analyticAt_const
    have hvs0 : (fun y => v y - s) x = 0 := by simp [hvx]
    have hPne : germAt (surfacePolar F G) x ≠ 0 := by
      by_cases hxP : x ∈ ZP
      · exact sub_ne_zero_of_hasFiniteIntersection_germAt hvsan hvs0 (hZPfin x hxP)
      · have hPx : surfacePolar F G x ≠ 0 := fun h0 => hxP ((hZP x).mpr ⟨hx, hvx, h0⟩)
        exact (isUnit_germAt (analyticAt_surfacePolar hGx' hFx) hPx).ne_zero
    have hkerx := ker_recenter_eq_span_of_pullback_partial_ne_zero G F R
      (hGan.continuousOn) hinjR hFG W
      (fun y hy hFy => ((hWsub hy).1).mp hFy) x (hballR x hx) hGx'
      (hWo.mem_nhds (hεx x hx).1) hFx
      (by rw [recenter_pullback_partial_eq_germAt]; exact hPne)
    have hJfin : HasFiniteIntersection (germAt (fun y => v y - s) x)
        (germAt (sectionJacobian G) x) := by
      by_cases hxJ : x ∈ ZJ
      · exact hZJfin x hxJ
      · have hJx : sectionJacobian G x ≠ 0 := fun h0 => hxJ ((hZJ x).mpr ⟨hx, hvx, h0⟩)
        exact hasFiniteIntersection_of_isUnit_right
          (isUnit_germAt (analyticAt_sectionJacobian hGx') hJx)
    have hvn := recenter_component_zero_not_mem_sq G x hGx' hsmooth
    have hvmem : (PointedMapGerm.recenterOfFunction G x hGx').1.component 0 ∈ maximalIdeal 2 :=
      (PointedMapGerm.recenterOfFunction G x hGx').coordinateIdeal_le_maximalIdeal
        ((PointedMapGerm.recenterOfFunction G x hGx').1.component_mem_coordinateIdeal 0)
    have hvirr := (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _ hvmem hvn).2
    obtain ⟨Dx⟩ := (PointedMapGerm.recenterOfFunction G x hGx').exists_sectionImageFactorization
      (hinjx x hx) hvirr.squarefree
    have h0c := recenter_component_eq_germAt G x hGx' 0
    have h2c := recenter_component_eq_germAt G x hGx' 2
    have haxisx : HasFiniteIntersection (germAt (fun y => G y 0 - G x 0) x)
        (germAt (fun y => G y 2 - G x 2) x) := by
      rw [← h0c, ← h2c]
      apply hasFiniteIntersection_of_hasFiniteIntersection_jacobian hvirr.ne_zero
      rw [recenter_jacobian_eq_germAt, h0c, hfun]
      exact hJfin
    obtain ⟨-, -, hid⟩ := local_polar_identity G F x hGx' hFx (hinjx x hx) hkerx Dx haxisx
    rw [← h0c, deltaInvariant_eq_zero_of_order_one hvmem hvn, hfun] at hid
    rw [localSectionDelta_eq G x hGx' (hinjx x hx) Dx]
    simpa using hid
  -- summation
  have hsumJ : ∑ x ∈ ZJ ∪ ZP, localIntersection (fun y => v y - s) (sectionJacobian G) x =
      intersectionMultiplicity _ _ hfinJ := by
    rw [← hZJsum]
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro x hxU hxJ
    have hxd : x ∈ ball (0 : Source 2) r ∧ v x = s := by
      rcases Finset.mem_union.mp hxU with h | h
      · exact (hxJ h).elim
      · exact ⟨((hZP x).mp h).1, ((hZP x).mp h).2.1⟩
    have hJx : sectionJacobian G x ≠ 0 := fun h0 => hxJ ((hZJ x).mpr ⟨hxd.1, hxd.2, h0⟩)
    exact localIntersection_eq_zero_of_ne_zero (analyticAt_sectionJacobian (hGx x hxd.1)) hJx
  have hsumP : ∑ x ∈ ZJ ∪ ZP, localIntersection (fun y => v y - s) (surfacePolar F G) x =
      intersectionMultiplicity _ _ hfinP := by
    rw [← hZPsum]
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro x hxU hxP
    have hxd : x ∈ ball (0 : Source 2) r ∧ v x = s := by
      rcases Finset.mem_union.mp hxU with h | h
      · exact ⟨((hZJ x).mp h).1, ((hZJ x).mp h).2.1⟩
      · exact (hxP h).elim
    have hPx : surfacePolar F G x ≠ 0 := fun h0 => hxP ((hZP x).mpr ⟨hxd.1, hxd.2, h0⟩)
    have hFx : AnalyticAt ℂ F (G x) := (hWsub (hεx x hxd.1).1).2
    exact localIntersection_eq_zero_of_ne_zero (analyticAt_surfacePolar (hGx x hxd.1) hFx) hPx
  have htotal : 2 * ∑ x ∈ ZJ ∪ ZP, localSectionDelta G x + intersectionMultiplicity _ _ hfinJ =
      intersectionMultiplicity _ _ hfinP := by
    rw [← hsumJ, ← hsumP, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpoint
  -- restriction to the critical points
  let Z := (ZJ ∪ ZP).filter fun x => ¬ Function.Injective (fderiv ℂ G x)
  have hZsum : ∑ x ∈ Z, localSectionDelta G x = ∑ x ∈ ZJ ∪ ZP, localSectionDelta G x := by
    apply Finset.sum_filter_of_ne
    intro x hxU hne himm
    apply hne
    have hxd : x ∈ ball (0 : Source 2) r ∧ v x = s := by
      rcases Finset.mem_union.mp hxU with h | h
      · exact ⟨((hZJ x).mp h).1, ((hZJ x).mp h).2.1⟩
      · exact ⟨((hZP x).mp h).1, ((hZP x).mp h).2.1⟩
    exact localSectionDelta_eq_zero_of_injective G x (hGx x hxd.1) _
      (isOpen_ball.mem_nhds (hballR x hxd.1)) (hinjR.mono ball_subset_closedBall)
      (hlevel x hxd.1 hxd.2).2.2 himm
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro x
    simp only [Z, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hni⟩
      · exact ⟨((hZJ x).mp hx).1, ((hZJ x).mp hx).2.1, hni⟩
      · exact ⟨((hZP x).mp hx).1, ((hZP x).mp hx).2.1, hni⟩
    · rintro ⟨hx, hvx, hni⟩
      refine ⟨Or.inl ((hZJ x).mpr ⟨hx, hvx, ?_⟩), hni⟩
      exact sectionJacobian_eq_zero_of_not_injective (hGx x hx).differentiableAt hni
  · intro x hx hvx
    exact (hlevel x hx hvx).2.1
  · rw [hZsum]
    have h1 := htotal
    have h2 := heq0'
    omega

end OnLeConjecture.Analytic
