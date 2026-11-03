/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricRootCount
public import OnLeConjecture.Analytic.RebasedGerm
public import OnLeConjecture.Analytic.CurveNormalizationOrder
public import OnLeConjecture.Analytic.ReducedPlaneRegularLocus
public import OnLeConjecture.Analytic.CurveImage

/-!
# Conservation of intersection multiplicities along level curves

Let `v` and `h` be analytic near the origin of `ℂ²` with a finite
intersection multiplicity at the origin. For every sufficiently small
nonzero `s`, the common zeros of `v - s` and `h` in a fixed small ball form a
finite set, and the local intersection multiplicities of `v - s` and `h`
at these points add up to the intersection multiplicity of `v` and `h` at
the origin.

The proof decomposes `h` into irreducible branches with injective
parametrizations. The zero set of each branch is the image of its
parametrization near the origin. Along a branch, the equation `v = s`
becomes a one-variable analytic equation, whose zeros near the origin are
counted by conservation of zeros in analytic families.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped Topology
open OnLeConjecture.Analytic.Germ

/-- A complex number as a point of `Source 1`. -/
def oneVar (z : ℂ) : Source 1 := fun _ => z

theorem eq_oneVar (t : Source 1) : t = oneVar (t 0) := by
  funext i
  fin_cases i
  rfl

/-- The map `ℂ → Source 1`. -/
noncomputable def oneVarCLM : ℂ →L[ℂ] Source 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ

theorem oneVarCLM_apply (z : ℂ) : oneVarCLM z = oneVar z := rfl

theorem analyticAt_comp_oneVar {φ : Source 1 → ℂ} {t : Source 1} (h : AnalyticAt ℂ φ t) :
    AnalyticAt ℂ (fun z : ℂ => φ (oneVar z)) (t 0) := by
  have h' : AnalyticAt ℂ φ (oneVarCLM (t 0)) := by
    rw [oneVarCLM_apply, ← eq_oneVar]
    exact h
  exact h'.comp (oneVarCLM.analyticAt (t 0))

/-- The germ order of a one-variable function at a point is its analytic
order. -/
theorem vanishingOrder_ofFunctionAt (φ : Source 1 → ℂ) (t : Source 1) (hφ : AnalyticAt ℂ φ t) :
    vanishingOrder (ofFunctionAt φ t hφ) =
      analyticOrderAt (fun z : ℂ => φ (oneVar z)) (t 0) := by
  have hψ := analyticAt_comp_oneVar hφ
  have htend : Tendsto (fun z : Source 1 => t 0 + z 0) (𝓝 0) (𝓝 (t 0)) := by
    have hc : Continuous (fun z : Source 1 => t 0 + z 0) :=
      continuous_const.add (continuous_apply 0)
    simpa using hc.tendsto 0
  have hpt : ∀ z : Source 1, t + z = oneVar (t 0 + z 0) := by
    intro z
    funext i
    fin_cases i
    rfl
  cases hord : analyticOrderAt (fun z : ℂ => φ (oneVar z)) (t 0) using ENat.recTopCoe with
  | top =>
    rw [vanishingOrder_eq_top_iff]
    have hz := htend.eventually (analyticOrderAt_eq_top.mp hord)
    have : ofFunctionAt φ t hφ = ofFunction (fun _ => (0 : ℂ)) analyticAt_const := by
      apply ofFunction_eq_of_eventuallyEq
      filter_upwards [hz] with z hz
      rw [hpt z]
      exact hz
    rw [this]
    rfl
  | coe n =>
    obtain ⟨g, hg, hg0, hfg⟩ := (hψ.analyticOrderAt_eq_natCast).mp hord
    have hproj : AnalyticAt ℂ (fun z : Source 1 => z 0) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0
    have haff : AnalyticAt ℂ (fun z : Source 1 => t 0 + z 0) 0 := analyticAt_const.add hproj
    have hg' : AnalyticAt ℂ g ((fun z : Source 1 => t 0 + z 0) 0) := by
      change AnalyticAt ℂ g (t 0 + 0)
      rw [add_zero]
      exact hg
    have hgan : AnalyticAt ℂ (fun z : Source 1 => g (t 0 + z 0)) 0 :=
      AnalyticAt.comp (g := g) (f := fun z : Source 1 => t 0 + z 0) hg' haff
    let u : Germ 1 := ofFunction _ hgan
    have hu : IsUnit u := by
      apply isUnit_of_valueRingHom_ne_zero
      rw [valueRingHom_ofFunction]
      simpa using hg0
    apply vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu
    apply Subtype.ext
    change ((fun z => φ (t + z) : Source 1 → ℂ) : FunctionGerm 1) =
      ((fun z : Source 1 => z 0) : FunctionGerm 1) ^ n *
        ((fun z : Source 1 => g (t 0 + z 0)) : FunctionGerm 1)
    rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [htend.eventually hfg] with z hz
    rw [hpt z, hz, smul_eq_mul, add_sub_cancel_left]
    rfl

/-- Pullback along a recentred parametrization of a germ recentred at the
image point. -/
theorem recenter_pullback_ofFunctionAt {n m : ℕ} (E : Source n → Source m) (t : Source n)
    (hE : AnalyticAt ℂ E t) (Q : Source m → ℂ) (hQ : AnalyticAt ℂ Q (E t)) :
    (PointedMapGerm.recenterOfFunction E t hE).pullbackRingHom (ofFunctionAt Q (E t) hQ) =
      ofFunctionAt (Q ∘ E) t (hQ.comp hE) := by
  rw [PointedMapGerm.pullbackRingHom_apply, PointedMapGerm.recenterOfFunction, ofFunctionAt,
    compPointed_ofFunction]
  apply ofFunction_eq_of_eventuallyEq
  filter_upwards with z
  simp only [Function.comp_apply, add_sub_cancel]

/-- The germ at `x` of a function, or zero when the function is not
analytic at `x`. -/
noncomputable def germAt {n : ℕ} (F : Source n → ℂ) (x : Source n) : Germ n := by
  classical
  exact if hF : AnalyticAt ℂ F x then ofFunctionAt F x hF else 0

theorem germAt_eq {n : ℕ} {F : Source n → ℂ} {x : Source n} (hF : AnalyticAt ℂ F x) :
    germAt F x = ofFunctionAt F x hF := by
  classical
  unfold germAt
  rw [dif_pos hF]

theorem germAt_congr {n : ℕ} {F G : Source n → ℂ} {x : Source n} (hFG : F =ᶠ[𝓝 x] G)
    (hF : AnalyticAt ℂ F x) : germAt F x = germAt G x := by
  have hG : AnalyticAt ℂ G x := hF.congr hFG
  rw [germAt_eq hF, germAt_eq hG]
  apply ofFunction_eq_of_eventuallyEq
  have ht : Tendsto (fun z : Source n => x + z) (𝓝 0) (𝓝 x) := by
    have h : Continuous (fun z : Source n => x + z) := continuous_const.add continuous_id
    simpa using h.tendsto 0
  exact ht.eventually hFG

theorem germAt_mul {n : ℕ} {F G : Source n → ℂ} {x : Source n} (hF : AnalyticAt ℂ F x)
    (hG : AnalyticAt ℂ G x) : germAt (fun y => F y * G y) x = germAt F x * germAt G x := by
  have hFG : AnalyticAt ℂ (fun y => F y * G y) x := hF.mul hG
  rw [germAt_eq hFG, germAt_eq hF, germAt_eq hG]
  rfl

theorem isUnit_germAt {n : ℕ} {F : Source n → ℂ} {x : Source n} (hF : AnalyticAt ℂ F x)
    (hx : F x ≠ 0) : IsUnit (germAt F x) := by
  rw [germAt_eq hF, isUnit_ofFunctionAt_iff]
  exact hx

/-- The local intersection number at `x` of the zero sets of two functions. -/
noncomputable def localIntersection (f g : Source 2 → ℂ) (x : Source 2) : ℕ :=
  Module.finrank ℂ (Germ 2 ⧸ PlaneCurve.pairIdeal (germAt f x) (germAt g x))

theorem localIntersection_eq {f g : Source 2 → ℂ} {x : Source 2}
    (hfin : PlaneCurve.HasFiniteIntersection (germAt f x) (germAt g x)) :
    localIntersection f g x = PlaneCurve.intersectionMultiplicity _ _ hfin :=
  rfl

/-- A reduced plane equation is smooth, hence irreducible, at its nonzero
zeros near the origin. -/
theorem eventually_irreducible_ofFunctionAt_of_squarefree (P : Source 2 → ℂ)
    (hP : AnalyticAt ℂ P 0) (hP0 : P 0 = 0) (hsq : Squarefree (ofFunction P hP)) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → P x = 0 →
      ∃ hPx : AnalyticAt ℂ P x, Irreducible (ofFunctionAt P x hPx) := by
  filter_upwards [eventually_fderiv_ne_zero_of_squarefree P hP hP0 hsq,
    hP.eventually_analyticAt] with x hfd han hx hPx
  refine ⟨han, ?_⟩
  have hmem : ofFunctionAt P x han ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, valueRingHom_ofFunctionAt]
    exact hPx
  have hnot : ofFunctionAt P x han ∉ maximalIdeal 2 ^ 2 := by
    intro hsq2
    have hfirst := (mem_firstOrderIdeal_iff.mp ((maximalIdeal_sq_le_firstOrderIdeal 2) hsq2)).2
    rw [differential_ofFunctionAt] at hfirst
    exact hfd hx hfirst
  exact (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq _ hmem hnot).2

/-- Intersection multiplicity at a point of a parametrized irreducible germ,
computed along the recentred parametrization. -/
theorem localIntersection_eq_analyticOrderAt_of_parametrization
    (P Q : Source 2 → ℂ) (E : Source 1 → Source 2) (t : Source 1)
    (hE : AnalyticAt ℂ E t) (hP : AnalyticAt ℂ P (E t)) (hQ : AnalyticAt ℂ Q (E t))
    (hirr : Irreducible (ofFunctionAt P (E t) hP))
    (S : Set (Source 1)) (hS : S ∈ 𝓝 t) (hinj : Set.InjOn E S)
    (hPE : ∀ᶠ τ in 𝓝 t, P (E τ) = 0)
    (hord : analyticOrderAt (fun z : ℂ => Q (E (oneVar z))) (t 0) ≠ ⊤) :
    PlaneCurve.HasFiniteIntersection (germAt P (E t)) (germAt Q (E t)) ∧
      localIntersection P Q (E t) =
        (analyticOrderAt (fun z : ℂ => Q (E (oneVar z))) (t 0)).toNat := by
  let γ := PointedMapGerm.recenterOfFunction E t hE
  have hγ : γ.HasInjectiveRepresentative :=
    PointedMapGerm.recenter_hasInjectiveRepresentative E t hE S hS hinj
  have hγP : γ.pullbackRingHom (ofFunctionAt P (E t) hP) = 0 := by
    rw [recenter_pullback_ofFunctionAt]
    rw [show (0 : Germ 1) = ofFunction (fun _ => (0 : ℂ)) analyticAt_const from rfl]
    apply ofFunction_eq_of_eventuallyEq
    have ht : Tendsto (fun z : Source 1 => t + z) (𝓝 0) (𝓝 t) := by
      have h : Continuous (fun z : Source 1 => t + z) := continuous_const.add continuous_id
      simpa using h.tendsto 0
    filter_upwards [ht.eventually hPE] with z hz
    exact hz
  have hγQ : γ.pullbackRingHom (ofFunctionAt Q (E t) hQ) =
      ofFunctionAt (Q ∘ E) t (hQ.comp hE) := recenter_pullback_ofFunctionAt E t hE Q hQ
  have hvo : vanishingOrder (γ.pullbackRingHom (ofFunctionAt Q (E t) hQ)) =
      analyticOrderAt (fun z : ℂ => Q (E (oneVar z))) (t 0) := by
    rw [hγQ, vanishingOrder_ofFunctionAt]
    rfl
  have hne : γ.pullbackRingHom (ofFunctionAt Q (E t) hQ) ≠ 0 := by
    intro hz
    rw [hz, vanishingOrder_eq_top_iff.mpr rfl] at hvo
    exact hord hvo.symm
  have hfin : PlaneCurve.HasFiniteIntersection (ofFunctionAt P (E t) hP)
      (ofFunctionAt Q (E t) hQ) := by
    apply PlaneCurve.hasFiniteIntersection_of_irreducible_not_dvd _ _ hirr
    rintro ⟨c, hc⟩
    apply hne
    rw [hc, map_mul, hγP, zero_mul]
  rw [germAt_eq hP, germAt_eq hQ]
  refine ⟨hfin, ?_⟩
  rw [localIntersection_eq (by rw [germAt_eq hP, germAt_eq hQ]; exact hfin)]
  simp only [germAt_eq hP, germAt_eq hQ]
  rw [γ.intersectionMultiplicity_eq_pullback_order_of_injective_curve hγ _ hirr hγP _ hfin, hvo]

theorem localIntersection_comm (f g : Source 2 → ℂ) (x : Source 2) :
    localIntersection f g x = localIntersection g f x := by
  unfold localIntersection
  rw [PlaneCurve.pairIdeal_comm]

theorem vanishingOrder_ofFunction_eq_analyticOrderAt (φ : Source 1 → ℂ) (hφ : AnalyticAt ℂ φ 0) :
    vanishingOrder (ofFunction φ hφ) = analyticOrderAt (fun z : ℂ => φ (oneVar z)) 0 := by
  have h := vanishingOrder_ofFunctionAt φ 0 hφ
  have heq : ofFunctionAt φ 0 hφ = ofFunction φ hφ := by
    apply ofFunction_eq_of_eventuallyEq
    filter_upwards with z
    rw [zero_add]
  rw [heq] at h
  exact h

/-- Conservation of intersection numbers of `h` with the level curves of
`v`, with total `N`, in every sufficiently small ball. -/
def ConservesAlongLevels (v h : Source 2 → ℂ) (N : ℕ) : Prop :=
  ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 → ∃ Z : Finset (Source 2),
    (∀ x, x ∈ Z ↔ (x ∈ ball (0 : Source 2) r ∧ v x = s ∧ h x = 0)) ∧
    (∀ x ∈ Z, PlaneCurve.HasFiniteIntersection (germAt (fun y => v y - s) x) (germAt h x)) ∧
    ∑ x ∈ Z, localIntersection (fun y => v y - s) h x = N

theorem norm_oneVar (z : ℂ) : ‖oneVar z‖ = ‖z‖ := by
  change ‖(fun _ : Fin 1 => z)‖ = ‖z‖
  exact pi_norm_const z

/-- Conservation along the level curves of `v` for one irreducible branch. -/
theorem conservesAlongLevels_irreducible (v P : Source 2 → ℂ) (hv : AnalyticAt ℂ v 0)
    (hP : AnalyticAt ℂ P 0) (hv0 : v 0 = 0) (hirr : Irreducible (ofFunction P hP))
    (hfin : PlaneCurve.HasFiniteIntersection (ofFunction v hv) (ofFunction P hP)) :
    ConservesAlongLevels v P (PlaneCurve.intersectionMultiplicity _ _ hfin) := by
  classical
  obtain ⟨γ, hγinj, hγn, hγker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible _ hirr
  have hγinj' := hγinj
  obtain ⟨E, hE, hE0, hγE, S, hS, hinj⟩ := hγinj'
  subst hγE
  have hγP : (PointedMapGerm.ofFunction E hE hE0).pullbackRingHom (ofFunction P hP) = 0 :=
    (hγker _).mpr dvd_rfl
  have hfin' := (PlaneCurve.hasFiniteIntersection_comm _ _).mp hfin
  have hcomm := PlaneCurve.intersectionMultiplicity_comm _ _ hfin
  have hformula := PointedMapGerm.intersectionMultiplicity_eq_pullback_order_of_injective_curve
    (PointedMapGerm.ofFunction E hE hE0) hγinj _ hirr hγP _ hfin'
  have hvE : AnalyticAt ℂ (v ∘ E) 0 := by
    have : AnalyticAt ℂ v (E 0) := by rw [hE0]; exact hv
    exact this.comp hE
  have hpull : (PointedMapGerm.ofFunction E hE hE0).pullbackRingHom (ofFunction v hv) =
      ofFunction (v ∘ E) hvE := by
    rw [PointedMapGerm.pullbackRingHom_apply, compPointed_ofFunction]
  have hne : (PointedMapGerm.ofFunction E hE hE0).pullbackRingHom (ofFunction v hv) ≠ 0 := by
    intro hz
    have hdvd : ofFunction P hP ∣ ofFunction v hv := (hγker _).mp hz
    exact hirr.not_isUnit (hfin.isUnit_of_common_divisor _ hdvd dvd_rfl)
  set e := PlaneCurve.intersectionMultiplicity _ _ hfin with he
  have hord : analyticOrderAt (fun z : ℂ => v (E (oneVar z))) 0 = e := by
    have hb := vanishingOrder_ofFunction_eq_analyticOrderAt (v ∘ E) hvE
    rw [show (fun z : ℂ => v (E (oneVar z))) = fun z => (v ∘ E) (oneVar z) from rfl, ← hb,
      ← hpull]
    have hfinite : vanishingOrder ((PointedMapGerm.ofFunction E hE hE0).pullbackRingHom
        (ofFunction v hv)) ≠ ⊤ := fun htop => hne (vanishingOrder_eq_top_iff.mp htop)
    rw [hcomm, hformula, ENat.natCast_toNat hfinite]
  -- the analytic family along the branch
  let Φ : (Fin 1 → ℂ) × ℂ → ℂ := fun q => v (E (oneVar q.2)) - q.1 0
  have hEan0 : AnalyticAt ℂ (fun z : ℂ => E (oneVar z)) 0 := by
    have : AnalyticAt ℂ E (oneVarCLM 0) := by
      rw [map_zero]
      exact hE
    exact this.comp (oneVarCLM.analyticAt 0)
  have hΦ : AnalyticAt ℂ Φ (0, 0) := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => v (E (oneVar z))) 0 := by
      have : AnalyticAt ℂ v (E (oneVar 0)) := by
        rw [show oneVar 0 = (0 : Source 1) from rfl, hE0]
        exact hv
      exact AnalyticAt.comp (g := v) (f := fun z : ℂ => E (oneVar z)) this hEan0
    have h2 : AnalyticAt ℂ (fun q : (Fin 1 → ℂ) × ℂ => v (E (oneVar q.2))) (0, 0) :=
      AnalyticAt.comp (g := fun z : ℂ => v (E (oneVar z)))
        (f := fun q : (Fin 1 → ℂ) × ℂ => q.2) h1 analyticAt_snd
    have h3 : AnalyticAt ℂ (fun q : (Fin 1 → ℂ) × ℂ => q.1 0) (0, 0) :=
      AnalyticAt.comp (g := fun y : Fin 1 → ℂ => y 0) (f := fun q : (Fin 1 → ℂ) × ℂ => q.1)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)
        analyticAt_fst
    exact h2.sub h3
  have hcentral : (fun z => Φ (0, z)) = fun z : ℂ => v (E (oneVar z)) := by
    funext z
    simp [Φ]
  have hordΦ : analyticOrderAt (fun z => Φ (0, z)) 0 = e := by
    rw [hcentral]
    exact hord
  -- neighbourhoods
  have hPE : ∀ᶠ t in 𝓝 (0 : Source 1), P (E t) = 0 := by
    have h := congrArg Subtype.val (show ofFunction (P ∘ E) _ = (0 : Germ 1) from by
      rw [← compPointed_ofFunction P hP E hE hE0, ← PointedMapGerm.pullbackRingHom_apply]
      exact hγP)
    exact Filter.Germ.coe_eq.mp h
  have hEnear : ∀ᶠ t in 𝓝 (0 : Source 1), AnalyticAt ℂ E t := hE.eventually_analyticAt
  obtain ⟨ρS, hρS, hρSball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hS (inter_mem hPE hEnear))
  obtain ⟨ρ, hρ, hρlt, hcount, hshrink⟩ :=
    exists_local_root_count_shrink Φ 0 0 hΦ e hordΦ ρS hρS
  obtain ⟨rE, hrE, hrEsub, -, -, -, hzero⟩ := exists_curve_closedBall_image_eq_zero_set E hE hE0
    hγn P hP hγker (S ∩ ball 0 ρ) (inter_mem hS (ball_mem_nhds 0 hρ))
    (hinj.mono Set.inter_subset_left)
  have hP0 : P 0 = 0 := by
    have hmem := irreducible_mem_maximalIdeal _ hirr
    rw [mem_maximalIdeal_iff, valueRingHom_ofFunction] at hmem
    exact hmem
  have hsmooth := eventually_irreducible_ofFunctionAt_of_squarefree P hP hP0 hirr.squarefree
  obtain ⟨r₀, hr₀, hr₀ball⟩ := Metric.mem_nhds_iff.mp
    (hzero.and (hsmooth.and (hv.eventually_analyticAt.and hP.eventually_analyticAt)))
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  obtain ⟨ρ', hρ', hρ'r⟩ := Metric.continuousAt_iff.mp hEan0.continuousAt r hr
  have htend : Tendsto (fun s : ℂ => (fun _ : Fin 1 => s)) (𝓝 0) (𝓝 (0 : Fin 1 → ℂ)) := by
    have hc : Continuous (fun s : ℂ => (fun _ : Fin 1 => s)) := continuous_pi fun _ => continuous_id
    exact hc.tendsto 0
  filter_upwards [htend.eventually hcount, htend.eventually (hshrink ρ' hρ')] with s hcs hshs hs0
  obtain ⟨T, hT, hTb, hTan, hTfin, hTsum⟩ := hcs
  let f : ℂ → Source 2 := fun τ => E (oneVar τ)
  have hball_oneVar : ∀ τ : ℂ, ‖τ‖ < ρS → oneVar τ ∈ ball (0 : Source 1) ρS := by
    intro τ hτ
    rw [mem_ball_zero_iff, norm_oneVar]
    exact hτ
  have hτdata : ∀ τ ∈ T, oneVar τ ∈ ball (0 : Source 1) ρS ∧ v (f τ) = s ∧
      P (f τ) = 0 ∧ f τ ∈ ball (0 : Source 2) r := by
    intro τ hτ
    have hτb := hTb τ hτ
    have hτc : τ ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hτb
    have hΦ0 : Φ ((fun _ => s), τ) = 0 := (hT τ hτc).mpr hτ
    have hτρS : oneVar τ ∈ ball (0 : Source 1) ρS := by
      apply hball_oneVar
      rw [← mem_ball_zero_iff]
      exact ball_subset_ball hρlt.le hτb
    refine ⟨hτρS, ?_, (hρSball hτρS).2.1, ?_⟩
    · exact sub_eq_zero.mp hΦ0
    · have hτρ' := hshs τ hτc hΦ0
      have h := hρ'r (show dist τ 0 < ρ' from mem_ball.mp hτρ')
      rw [show oneVar 0 = (0 : Source 1) from rfl, hE0] at h
      exact h
  refine ⟨T.image f, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨-, hv', hP', hr'⟩ := hτdata τ hτ
      exact ⟨hr', hv', hP'⟩
    · rintro ⟨hxr, hvx, hPx⟩
      have hx₀ := hr₀ball (ball_subset_ball hrr₀ hxr)
      obtain ⟨t, ht, htx⟩ := hx₀.1.mp hPx
      have htρ : t ∈ ball (0 : Source 1) ρ := (hrEsub ht).2
      have hτc : t 0 ∈ closedBall (0 : ℂ) ρ := by
        rw [mem_closedBall_zero_iff, ← norm_oneVar, ← eq_oneVar]
        exact (mem_ball_zero_iff.mp htρ).le
      apply Finset.mem_image.mpr
      refine ⟨t 0, (hT (t 0) hτc).mp ?_, ?_⟩
      · change v (E (oneVar (t 0))) - s = 0
        rw [← eq_oneVar, htx, hvx, sub_self]
      · change E (oneVar (t 0)) = x
        rw [← eq_oneVar, htx]
  · intro x hx
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hτρS, hv', hP', hr'⟩ := hτdata τ hτ
    have hx₀ := hr₀ball (ball_subset_ball hrr₀ hr')
    have hxne : f τ ≠ 0 := by
      intro h
      rw [h, hv0] at hv'
      exact hs0 hv'.symm
    obtain ⟨hPx, hirrx⟩ := hx₀.2.1 hxne hP'
    have hQx : AnalyticAt ℂ (fun y => v y - s) (f τ) := hx₀.2.2.1.sub analyticAt_const
    have hPE' : ∀ᶠ t' in 𝓝 (oneVar τ), P (E t') = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hτρS] with t' ht'
      exact (hρSball ht').2.1
    have hres := localIntersection_eq_analyticOrderAt_of_parametrization P (fun y => v y - s) E
      (oneVar τ) (hρSball hτρS).2.2 hPx hQx hirrx (ball 0 ρS) (isOpen_ball.mem_nhds hτρS)
      (hinj.mono fun t' ht' => (hρSball ht').1) hPE' (hTfin τ hτ)
    exact (PlaneCurve.hasFiniteIntersection_comm _ _).mp hres.1
  · rw [Finset.sum_image]
    · rw [← hTsum]
      apply Finset.sum_congr rfl
      intro τ hτ
      obtain ⟨hτρS, hv', hP', hr'⟩ := hτdata τ hτ
      have hx₀ := hr₀ball (ball_subset_ball hrr₀ hr')
      have hxne : f τ ≠ 0 := by
        intro h
        rw [h, hv0] at hv'
        exact hs0 hv'.symm
      obtain ⟨hPx, hirrx⟩ := hx₀.2.1 hxne hP'
      have hQx : AnalyticAt ℂ (fun y => v y - s) (f τ) := hx₀.2.2.1.sub analyticAt_const
      have hPE' : ∀ᶠ t' in 𝓝 (oneVar τ), P (E t') = 0 := by
        filter_upwards [isOpen_ball.mem_nhds hτρS] with t' ht'
        exact (hρSball ht').2.1
      have hres := localIntersection_eq_analyticOrderAt_of_parametrization P (fun y => v y - s) E
        (oneVar τ) (hρSball hτρS).2.2 hPx hQx hirrx (ball 0 ρS) (isOpen_ball.mem_nhds hτρS)
        (hinj.mono fun t' ht' => (hρSball ht').1) hPE' (hTfin τ hτ)
      rw [localIntersection_comm]
      exact hres.2
    · intro τ₁ hτ₁ τ₂ hτ₂ heq
      have h1 := (hρSball (hτdata τ₁ hτ₁).1).1
      have h2 := (hρSball (hτdata τ₂ hτ₂).1).1
      have := hinj h1 h2 heq
      exact congrFun this 0

theorem hasFiniteIntersection_of_isUnit_right {f u : Germ 2} (hu : IsUnit u) :
    PlaneCurve.HasFiniteIntersection f u := by
  apply (PlaneCurve.hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f u).mpr
  refine ⟨0, ?_⟩
  rw [pow_zero, Ideal.one_eq_top, top_le_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu

theorem localIntersection_eq_zero_of_ne_zero {f h : Source 2 → ℂ} {x : Source 2}
    (hh : AnalyticAt ℂ h x) (hx : h x ≠ 0) : localIntersection f h x = 0 := by
  have hu := isUnit_germAt hh hx
  rw [localIntersection_eq (hasFiniteIntersection_of_isUnit_right hu)]
  exact PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_right _ _ hu _

theorem germAt_eq_of_eventuallyEq {n : ℕ} {F G : Source n → ℂ} {x : Source n}
    (hFG : F =ᶠ[𝓝 x] G) : germAt F x = germAt G x := by
  by_cases hF : AnalyticAt ℂ F x
  · exact germAt_congr hFG hF
  · have hG : ¬ AnalyticAt ℂ G x := fun h => hF (h.congr hFG.symm)
    classical
    unfold germAt
    rw [dif_neg hF, dif_neg hG]

/-- Conservation is unchanged when the second function is replaced by a
function agreeing with it near the origin. -/
theorem ConservesAlongLevels.congr {v h h' : Source 2 → ℂ} {N : ℕ}
    (hc : ConservesAlongLevels v h N) (hhh : h =ᶠ[𝓝 0] h') :
    ConservesAlongLevels v h' N := by
  obtain ⟨r₀, hr₀, hcons⟩ := hc
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hhh
  refine ⟨min r₀ (ε / 2), lt_min hr₀ (half_pos hε), fun r hr hrle => ?_⟩
  have hrr₀ : r ≤ r₀ := hrle.trans (min_le_left _ _)
  have hrε : r < ε := lt_of_le_of_lt (hrle.trans (min_le_right _ _)) (half_lt_self hε)
  filter_upwards [hcons r hr hrr₀] with s hs hs0
  obtain ⟨Z, hZ, hZfin, hZsum⟩ := hs hs0
  have hball : ∀ x ∈ ball (0 : Source 2) r, x ∈ ball (0 : Source 2) ε :=
    fun x hx => ball_subset_ball hrε.le hx
  have hgerm : ∀ x ∈ ball (0 : Source 2) r, germAt h x = germAt h' x := by
    intro x hx
    apply germAt_eq_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (hball x hx)] with y hy using hεsub hy
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro x
    rw [hZ x]
    constructor
    · rintro ⟨hx, hvx, hhx⟩
      exact ⟨hx, hvx, (hεsub (hball x hx)) ▸ hhx⟩
    · rintro ⟨hx, hvx, hhx⟩
      exact ⟨hx, hvx, (hεsub (hball x hx)).symm ▸ hhx⟩
  · intro x hx
    rw [← hgerm x ((hZ x).mp hx).1]
    exact hZfin x hx
  · rw [← hZsum]
    apply Finset.sum_congr rfl
    intro x hx
    unfold localIntersection
    rw [hgerm x ((hZ x).mp hx).1]

/-- A function not vanishing at the origin has no zeros on nearby level
curves, with total intersection zero. -/
theorem conservesAlongLevels_of_ne_zero {v h : Source 2 → ℂ} (hh : AnalyticAt ℂ h 0)
    (h0 : h 0 ≠ 0) : ConservesAlongLevels v h 0 := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hh.continuousAt.eventually_ne h0)
  refine ⟨ε, hε, fun r _ hrle => ?_⟩
  filter_upwards with s _
  refine ⟨∅, ?_, by simp, by simp⟩
  intro x
  simp only [Finset.notMem_empty, false_iff, not_and]
  intro hx _
  exact hεsub (ball_subset_ball hrle hx)

/-- Conservation is additive for products. -/
theorem ConservesAlongLevels.mul {v h₁ h₂ : Source 2 → ℂ} {N₁ N₂ : ℕ}
    (hv : AnalyticAt ℂ v 0) (h₁an : AnalyticAt ℂ h₁ 0) (h₂an : AnalyticAt ℂ h₂ 0)
    (c₁ : ConservesAlongLevels v h₁ N₁) (c₂ : ConservesAlongLevels v h₂ N₂) :
    ConservesAlongLevels v (fun y => h₁ y * h₂ y) (N₁ + N₂) := by
  classical
  obtain ⟨r₁, hr₁, hc₁⟩ := c₁
  obtain ⟨r₂, hr₂, hc₂⟩ := c₂
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((hv.eventually_analyticAt.and h₁an.eventually_analyticAt).and h₂an.eventually_analyticAt)
  refine ⟨min (min r₁ r₂) (ε / 2), lt_min (lt_min hr₁ hr₂) (half_pos hε), fun r hr hrle => ?_⟩
  have hrr₁ : r ≤ r₁ := hrle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₂ : r ≤ r₂ := hrle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrε : r < ε := lt_of_le_of_lt (hrle.trans (min_le_right _ _)) (half_lt_self hε)
  have han : ∀ x ∈ ball (0 : Source 2) r,
      (AnalyticAt ℂ v x ∧ AnalyticAt ℂ h₁ x) ∧ AnalyticAt ℂ h₂ x :=
    fun x hx => hεsub (ball_subset_ball hrε.le hx)
  filter_upwards [hc₁ r hr hrr₁, hc₂ r hr hrr₂] with s hs₁ hs₂ hs0
  obtain ⟨Z₁, hZ₁, hZ₁fin, hZ₁sum⟩ := hs₁ hs0
  obtain ⟨Z₂, hZ₂, hZ₂fin, hZ₂sum⟩ := hs₂ hs0
  have hmem : ∀ x, x ∈ Z₁ ∪ Z₂ ↔
      (x ∈ ball (0 : Source 2) r ∧ v x = s ∧ h₁ x * h₂ x = 0) := by
    intro x
    rw [Finset.mem_union, hZ₁ x, hZ₂ x, mul_eq_zero]
    tauto
  have hfin₁ : ∀ x ∈ Z₁ ∪ Z₂,
      PlaneCurve.HasFiniteIntersection (germAt (fun y => v y - s) x) (germAt h₁ x) := by
    intro x hx
    by_cases hx₁ : x ∈ Z₁
    · exact hZ₁fin x hx₁
    · have hxr := ((hmem x).mp hx).1
      have hne : h₁ x ≠ 0 := fun h0 => hx₁ ((hZ₁ x).mpr ⟨hxr, ((hmem x).mp hx).2.1, h0⟩)
      exact hasFiniteIntersection_of_isUnit_right (isUnit_germAt (han x hxr).1.2 hne)
  have hfin₂ : ∀ x ∈ Z₁ ∪ Z₂,
      PlaneCurve.HasFiniteIntersection (germAt (fun y => v y - s) x) (germAt h₂ x) := by
    intro x hx
    by_cases hx₂ : x ∈ Z₂
    · exact hZ₂fin x hx₂
    · have hxr := ((hmem x).mp hx).1
      have hne : h₂ x ≠ 0 := fun h0 => hx₂ ((hZ₂ x).mpr ⟨hxr, ((hmem x).mp hx).2.1, h0⟩)
      exact hasFiniteIntersection_of_isUnit_right (isUnit_germAt (han x hxr).2 hne)
  have hgerm : ∀ x ∈ Z₁ ∪ Z₂, germAt (fun y => h₁ y * h₂ y) x = germAt h₁ x * germAt h₂ x :=
    fun x hx => germAt_mul (han x ((hmem x).mp hx).1).1.2 (han x ((hmem x).mp hx).1).2
  refine ⟨Z₁ ∪ Z₂, hmem, ?_, ?_⟩
  · intro x hx
    rw [hgerm x hx]
    exact (PlaneCurve.hasFiniteIntersection_mul_right_iff _ _ _).mpr ⟨hfin₁ x hx, hfin₂ x hx⟩
  · have hsplit : ∀ x ∈ Z₁ ∪ Z₂, localIntersection (fun y => v y - s) (fun y => h₁ y * h₂ y) x =
        localIntersection (fun y => v y - s) h₁ x + localIntersection (fun y => v y - s) h₂ x := by
      intro x hx
      have hprod : PlaneCurve.HasFiniteIntersection (germAt (fun y => v y - s) x)
          (germAt h₁ x * germAt h₂ x) :=
        (PlaneCurve.hasFiniteIntersection_mul_right_iff _ _ _).mpr ⟨hfin₁ x hx, hfin₂ x hx⟩
      unfold localIntersection
      rw [hgerm x hx]
      exact PlaneCurve.intersectionMultiplicity_mul_right _ _ _ (hfin₁ x hx) (hfin₂ x hx) hprod
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← hZ₁sum, ← hZ₂sum]
    congr 1
    · symm
      apply Finset.sum_subset Finset.subset_union_left
      intro x hx hx₁
      have hxr := ((hmem x).mp hx).1
      have hne : h₁ x ≠ 0 := fun h0 => hx₁ ((hZ₁ x).mpr ⟨hxr, ((hmem x).mp hx).2.1, h0⟩)
      exact localIntersection_eq_zero_of_ne_zero (han x hxr).1.2 hne
    · symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x hx hx₂
      have hxr := ((hmem x).mp hx).1
      have hne : h₂ x ≠ 0 := fun h0 => hx₂ ((hZ₂ x).mpr ⟨hxr, ((hmem x).mp hx).2.1, h0⟩)
      exact localIntersection_eq_zero_of_ne_zero (han x hxr).2 hne

/-- **Conservation along level curves.** If `v` vanishes at the origin and
meets `h` finitely there, then for every small ball and every small nonzero
`s`, the intersection multiplicities of `v - s` and `h` at the points of the
ball add up to the intersection multiplicity of `v` and `h` at the origin. -/
theorem conservesAlongLevels (v h : Source 2 → ℂ) (hv : AnalyticAt ℂ v 0)
    (hh : AnalyticAt ℂ h 0) (hv0 : v 0 = 0)
    (hfin : PlaneCurve.HasFiniteIntersection (ofFunction v hv) (ofFunction h hh)) :
    ConservesAlongLevels v h (PlaneCurve.intersectionMultiplicity _ _ hfin) := by
  suffices H : ∀ q : Germ 2, ∀ (Q : Source 2 → ℂ) (hQ : AnalyticAt ℂ Q 0),
      ofFunction Q hQ = q → ∀ hq : PlaneCurve.HasFiniteIntersection (ofFunction v hv) q,
        ConservesAlongLevels v Q (PlaneCurve.intersectionMultiplicity _ _ hq) from
    H _ h hh rfl hfin
  intro q
  induction q using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro Q hQ _ hq
      have hu := PlaneCurve.isUnit_of_hasFiniteIntersection_zero_right _ hq
      rw [isUnit_iff_valueRingHom_ne_zero, valueRingHom_ofFunction] at hu
      exact (hu hv0).elim
  | h₂ a ha =>
      intro Q hQ hQa hq
      rw [PlaneCurve.intersectionMultiplicity_eq_zero_of_isUnit_right _ _ ha hq]
      apply conservesAlongLevels_of_ne_zero hQ
      rw [← hQa, isUnit_iff_valueRingHom_ne_zero, valueRingHom_ofFunction] at ha
      exact ha
  | h₃ a p _ hp ih =>
      intro Q hQ hQpa hq
      obtain ⟨P, hP, rfl⟩ := exists_analyticRepresentative_allOrders p
      obtain ⟨A, hA, rfl⟩ := exists_analyticRepresentative_allOrders a
      obtain ⟨hqP, hqA⟩ := (PlaneCurve.hasFiniteIntersection_mul_right_iff _ _ _).mp hq
      have cP := conservesAlongLevels_irreducible v P hv hP hv0 hp.irreducible hqP
      have cA := ih A hA rfl hqA
      have cPA := cP.mul hv hP hA cA
      rw [PlaneCurve.intersectionMultiplicity_mul_right _ _ _ hqP hqA hq]
      apply cPA.congr
      have hgerm : ofFunction (fun y => P y * A y) (hP.mul hA) = ofFunction Q hQ := by
        rw [hQpa]
        rfl
      exact (Filter.Germ.coe_eq.mp (congrArg Subtype.val hgerm))

end OnLeConjecture.Analytic
