/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupDirections
public import OnLeConjecture.Analytic.PlaneMilnorLevelChart
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Holomorphic charts of smooth level curves

* `exists_levelCurve`: let `f : ℂ² → ℂ` be analytic at `x` with nonzero differential. Inside any
  prescribed neighbourhood of `x` there are an open neighbourhood `N` of `x` and a holomorphic
  injective curve `γ` on a disc `B(0, r)` with `γ 0 = x`, whose image is exactly
  `N ∩ {f = f x}`, with nonzero velocity tangent to the level curve. It is obtained from the
  inverse function theorem for `z ↦ (ℓ z, f z)`, for a coordinate `ℓ` transverse to the kernel
  of `df(x)`.
* `deriv_ne_zero_of_injOn`: a holomorphic function of one variable that is injective on a
  neighbourhood of a point has nonzero derivative there. If the derivative vanished, the
  function would be the `k`-th power of a local coordinate with `k ≥ 2`
  (`exists_pow_openPartialHomeomorph`), and two points whose coordinates differ by a primitive
  `k`-th root of unity would have the same
  image.
* `eventually_injective_fderiv`: injectivity of the differential of an analytic map
  `ℂ² → ℂ × ℂ` is an open condition.
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- Injectivity of the differential of an analytic map `ℂ² → ℂ × ℂ` is an open condition. -/
theorem eventually_injective_fderiv {Θ : Source 2 → ℂ × ℂ} {x : Source 2}
    (hΘ : AnalyticAt ℂ Θ x) (hinj : Injective (fderiv ℂ Θ x)) :
    ∀ᶠ y in 𝓝 x, Injective (fderiv ℂ Θ y) := by
  have hcont : ContinuousAt (fderiv ℂ Θ) x := hΘ.fderiv.continuousAt
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective _ hinj
  have hmem : range ((↑) : (Source 2 ≃L[ℂ] ℂ × ℂ) → Source 2 →L[ℂ] ℂ × ℂ) ∈
      𝓝 (fderiv ℂ Θ x) := ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩
  filter_upwards [hcont.preimage_mem_nhds hmem] with y hy
  obtain ⟨e', he'⟩ := hy
  rw [← he']
  exact e'.injective

/-- At a point where an analytic map `ℂ² → ℂ × ℂ` has injective differential, it is strictly
differentiable with an invertible derivative. -/
theorem exists_hasStrictFDerivAt_equiv {Θ : Source 2 → ℂ × ℂ} {x : Source 2}
    (hΘ : AnalyticAt ℂ Θ x) (hinj : Injective (fderiv ℂ Θ x)) :
    ∃ e : Source 2 ≃L[ℂ] ℂ × ℂ, (e : Source 2 →L[ℂ] ℂ × ℂ) = fderiv ℂ Θ x ∧
      HasStrictFDerivAt Θ (e : Source 2 →L[ℂ] ℂ × ℂ) x := by
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective _ hinj
  refine ⟨e, he, ?_⟩
  rw [he]
  exact hΘ.hasStrictFDerivAt

/-- **A holomorphic chart of a smooth level curve**, for a coordinate `ℓ` transverse to the
kernel of `df(x)`. -/
theorem exists_levelCurve_of_transverse {f : Source 2 → ℂ} {x : Source 2} (hf : AnalyticAt ℂ f x)
    (ℓ : Source 2 →L[ℂ] ℂ) (hℓ : ∀ a, ℓ a = 0 → fderiv ℂ f x a = 0 → a = 0)
    {S : Set (Source 2)} (hS : S ∈ 𝓝 x) :
    ∃ (γ : ℂ → Source 2) (r : ℝ) (N : Set (Source 2)), 0 < r ∧ IsOpen N ∧ x ∈ N ∧ N ⊆ S ∧
      γ 0 = x ∧ (∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ γ t) ∧
      (∀ t ∈ ball (0 : ℂ) r, γ t ∈ N ∧ f (γ t) = f x) ∧ InjOn γ (ball 0 r) ∧
      (∃ κ : Source 2 →L[ℂ] ℂ, ∀ z ∈ N, f z = f x → κ (z - x) ∈ ball (0 : ℂ) r ∧
        γ (κ (z - x)) = z) ∧
      (∀ t ∈ ball (0 : ℂ) r, deriv γ t ≠ 0 ∧ fderiv ℂ f (γ t) (deriv γ t) = 0) ∧
      ∀ a, fderiv ℂ f x a = 0 → ∃ c : ℂ, a = c • deriv γ 0 := by
  set Θ : Source 2 → ℂ × ℂ := fun z => (ℓ z, f z) with hΘdef
  have hΘan : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ Θ z := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    exact (ℓ.analyticAt z).prod hz
  have hfderiv : ∀ z, AnalyticAt ℂ f z →
      fderiv ℂ Θ z = ℓ.prod (fderiv ℂ f z) := fun z hz =>
    (ℓ.hasFDerivAt.prodMk hz.differentiableAt.hasFDerivAt).fderiv
  have hinj : Injective (fderiv ℂ Θ x) := by
    rw [hfderiv x hf, injective_iff_map_eq_zero]
    intro a ha
    exact hℓ a (congrArg Prod.fst ha) (congrArg Prod.snd ha)
  obtain ⟨E, hE, hEs⟩ := exists_hasStrictFDerivAt_equiv hΘan.self_of_nhds hinj
  set e := hEs.toOpenPartialHomeomorph Θ with hedef
  have hecoe : ∀ z, e z = Θ z := fun z => rfl
  -- the good open neighbourhood
  have hgood : ∀ᶠ z in 𝓝 x, z ∈ S ∧ AnalyticAt ℂ f z ∧ Injective (fderiv ℂ Θ z) :=
    (show ∀ᶠ z in 𝓝 x, z ∈ S from hS).and
      (hf.eventually_analyticAt.and (eventually_injective_fderiv hΘan.self_of_nhds hinj))
  obtain ⟨N₀, hN₀good, hN₀o, hxN₀⟩ := _root_.eventually_nhds_iff.mp hgood
  set N₁ : Set (Source 2) := e.source ∩ N₀ with hN₁def
  have hN₁o : IsOpen N₁ := e.open_source.inter hN₀o
  have hxN₁ : x ∈ N₁ := ⟨hEs.mem_toOpenPartialHomeomorph_source, hxN₀⟩
  set T : Set (ℂ × ℂ) := e.target ∩ e.symm ⁻¹' N₁ with hTdef
  have hTo : IsOpen T := e.continuousOn_symm.isOpen_inter_preimage e.open_target hN₁o
  have hΘx : Θ x ∈ T := by
    refine ⟨e.map_source hxN₁.1, ?_⟩
    change e.symm (e x) ∈ N₁
    rw [e.left_inv hxN₁.1]
    exact hxN₁
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hTo _ hΘx
  set L : ℂ → ℂ × ℂ := fun t => (ℓ x + t, f x) with hLdef
  have hLball : ∀ t ∈ ball (0 : ℂ) r, L t ∈ ball (Θ x) r := by
    intro t ht
    rw [mem_ball, Prod.dist_eq]
    simp only [L, Θ, dist_self]
    rw [dist_eq_norm, add_sub_cancel_left]
    exact max_lt (by simpa using ht) hr
  have hLT : ∀ t ∈ ball (0 : ℂ) r, L t ∈ T := fun t ht => hrT (hLball t ht)
  set γ : ℂ → Source 2 := fun t => e.symm (L t) with hγdef
  set N : Set (Source 2) := N₁ ∩ Θ ⁻¹' (ball (Θ x) r) with hNdef
  have hΘcont : ContinuousOn Θ N₁ := fun z hz =>
    ((ℓ.continuous.continuousAt).prodMk (hN₀good z hz.2).2.1.continuousAt).continuousWithinAt
  have hNo : IsOpen N := hΘcont.isOpen_inter_preimage hN₁o isOpen_ball
  have hγT : ∀ t ∈ ball (0 : ℂ) r, L t ∈ e.target ∧ γ t ∈ N₁ := fun t ht => hLT t ht
  have hΘγ : ∀ t ∈ ball (0 : ℂ) r, Θ (γ t) = L t := fun t ht => by
    rw [← hecoe]
    exact e.right_inv (hγT t ht).1
  have hγ0 : γ 0 = x := by
    change e.symm (L 0) = x
    have hL0 : L 0 = e x := by simp [L, hecoe, Θ]
    rw [hL0]
    exact e.left_inv hxN₁.1
  -- differentiability of the curve
  have hγdiff : ∀ t ∈ ball (0 : ℂ) r, DifferentiableAt ℂ γ t := by
    intro t ht
    obtain ⟨htarget, hγN₁⟩ := hγT t ht
    have hgood' := hN₀good _ hγN₁.2
    have hΘan' : AnalyticAt ℂ Θ (γ t) := (ℓ.analyticAt _).prod hgood'.2.1
    obtain ⟨E', -, hE'⟩ := exists_hasStrictFDerivAt_equiv hΘan' hgood'.2.2
    have hsymm := e.hasFDerivAt_symm htarget hE'.hasFDerivAt
    have hL : DifferentiableAt ℂ L t :=
      ((differentiableAt_const _).add differentiableAt_id).prodMk (differentiableAt_const _)
    exact hsymm.differentiableAt.comp t hL
  have hderγ : ∀ t ∈ ball (0 : ℂ) r, ℓ (deriv γ t) = 1 ∧ fderiv ℂ f (γ t) (deriv γ t) = 0 := by
    intro t ht
    have hγN₁ := (hγT t ht).2
    have hfan : AnalyticAt ℂ f (γ t) := (hN₀good _ hγN₁.2).2.1
    have hd1 : HasDerivAt (fun t' => Θ (γ t')) (fderiv ℂ Θ (γ t) (deriv γ t)) t :=
      ((ℓ.analyticAt _).prod hfan).differentiableAt.hasFDerivAt.comp_hasDerivAt t
        (hγdiff t ht).hasDerivAt
    have hd2 : HasDerivAt L ((1 : ℂ), (0 : ℂ)) t := by
      have h1 : HasDerivAt (fun t' : ℂ => ℓ x + t') 1 t := (hasDerivAt_id t).const_add _
      have h2 : HasDerivAt (fun _ : ℂ => f x) 0 t := hasDerivAt_const t _
      exact h1.prodMk h2
    have heq : (fun t' => Θ (γ t')) =ᶠ[𝓝 t] L := by
      filter_upwards [isOpen_ball.mem_nhds ht] with t' ht'
      exact hΘγ t' ht'
    have hval := hd1.unique (hd2.congr_of_eventuallyEq heq)
    rw [hfderiv _ hfan] at hval
    have hv1 := congrArg Prod.fst hval
    have hv2 := congrArg Prod.snd hval
    simp only [ContinuousLinearMap.prod_apply] at hv1 hv2
    exact ⟨hv1, hv2⟩
  refine ⟨γ, r, N, hr, hNo, ⟨hxN₁, ?_⟩, fun z hz => (hN₀good z hz.1.2).1, hγ0, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · change Θ x ∈ ball (Θ x) r
    exact mem_ball_self hr
  · intro t ht
    refine DifferentiableOn.analyticAt (fun t' ht' => (hγdiff t' ht').differentiableWithinAt) ?_
    exact isOpen_ball.mem_nhds ht
  · intro t ht
    refine ⟨⟨(hγT t ht).2, ?_⟩, ?_⟩
    · change Θ (γ t) ∈ ball (Θ x) r
      rw [hΘγ t ht]
      exact hLball t ht
    · have h := congrArg Prod.snd (hΘγ t ht)
      exact h
  · intro t₁ ht₁ t₂ ht₂ h12
    have h := congrArg Prod.fst ((hΘγ t₁ ht₁).symm.trans ((congrArg Θ h12).trans (hΘγ t₂ ht₂)))
    simpa [L] using h
  · refine ⟨ℓ, fun z hz hfz => ?_⟩
    rw [map_sub]
    refine ⟨?_, ?_⟩
    · have h := hz.2
      rw [mem_preimage, mem_ball, Prod.dist_eq] at h
      have h1 := (le_max_left _ _).trans_lt h
      rw [mem_ball, dist_zero_right]
      simpa [Θ, dist_eq_norm] using h1
    · change e.symm (L (ℓ z - ℓ x)) = z
      have hLz : L (ℓ z - ℓ x) = e z := by simp [L, hecoe, Θ, hfz]
      rw [hLz]
      exact e.left_inv hz.1.1
  · intro t ht
    obtain ⟨h1, h2⟩ := hderγ t ht
    refine ⟨fun h0 => ?_, h2⟩
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  · intro a ha
    have h0 := hderγ 0 (mem_ball_self hr)
    rw [hγ0] at h0
    refine ⟨ℓ a, ?_⟩
    have hb := hℓ (a - ℓ a • deriv γ 0) (by rw [map_sub, map_smul, h0.1, smul_eq_mul, mul_one,
      sub_self]) (by rw [map_sub, map_smul, h0.2, ha, smul_zero, sub_zero])
    exact sub_eq_zero.mp hb

/-- **A holomorphic chart of a smooth level curve.** -/
theorem exists_levelCurve {f : Source 2 → ℂ} {x : Source 2} (hf : AnalyticAt ℂ f x)
    (hdf : fderiv ℂ f x ≠ 0) {S : Set (Source 2)} (hS : S ∈ 𝓝 x) :
    ∃ (γ : ℂ → Source 2) (r : ℝ) (N : Set (Source 2)), 0 < r ∧ IsOpen N ∧ x ∈ N ∧ N ⊆ S ∧
      γ 0 = x ∧ (∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ γ t) ∧
      (∀ t ∈ ball (0 : ℂ) r, γ t ∈ N ∧ f (γ t) = f x) ∧ InjOn γ (ball 0 r) ∧
      (∃ κ : Source 2 →L[ℂ] ℂ, ∀ z ∈ N, f z = f x → κ (z - x) ∈ ball (0 : ℂ) r ∧
        γ (κ (z - x)) = z) ∧
      (∀ t ∈ ball (0 : ℂ) r, deriv γ t ≠ 0 ∧ fderiv ℂ f (γ t) (deriv γ t) = 0) ∧
      ∀ a, fderiv ℂ f x a = 0 → ∃ c : ℂ, a = c • deriv γ 0 := by
  have hpart : ∀ a : Source 2, fderiv ℂ f x a =
      a 0 * fderiv ℂ f x (Pi.single 0 1) + a 1 * fderiv ℂ f x (Pi.single 1 1) := by
    intro a
    have ha : a = a 0 • (Pi.single 0 1 : Source 2) + a 1 • (Pi.single 1 1 : Source 2) := by
      funext i
      fin_cases i <;> simp
    conv_lhs => rw [ha]
    simp only [map_add, map_smul, smul_eq_mul]
  by_cases h1 : fderiv ℂ f x (Pi.single 1 1) ≠ 0
  · refine exists_levelCurve_of_transverse hf (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 => ℂ) 0) (fun a ha0 hfa => ?_) hS
    change a 0 = 0 at ha0
    rw [hpart, ha0, zero_mul, zero_add] at hfa
    have ha1 : a 1 = 0 := (mul_eq_zero.mp hfa).resolve_right h1
    funext i
    fin_cases i
    · exact ha0
    · exact ha1
  · push Not at h1
    have h0 : fderiv ℂ f x (Pi.single 0 1) ≠ 0 := by
      intro h0
      apply hdf
      ext1 a
      rw [hpart, h0, h1]
      simp
    refine exists_levelCurve_of_transverse hf (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 => ℂ) 1) (fun a ha1 hfa => ?_) hS
    change a 1 = 0 at ha1
    rw [hpart, ha1, zero_mul, add_zero] at hfa
    have ha0 : a 0 = 0 := (mul_eq_zero.mp hfa).resolve_right h0
    funext i
    fin_cases i
    · exact ha0
    · exact ha1

/-- **Injective holomorphic functions have nonzero derivative.** -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {U : Set ℂ}
    (hU : U ∈ 𝓝 a) (hinj : InjOn f U) : deriv f a ≠ 0 := by
  set g : ℂ → ℂ := fun t => f t - f a with hgdef
  have hg : AnalyticAt ℂ g a := hf.sub analyticAt_const
  have hga : g a = 0 := sub_self _
  have hderiv : deriv g a = deriv f a := by
    simp only [g]
    exact deriv_sub_const (f a)
  have hne : ¬∀ᶠ y in 𝓝 a, g y = 0 := by
    intro hev
    obtain ⟨y, hy, hya⟩ := ((hev.and hU).filter_mono nhdsWithin_le_nhds |>.and
      self_mem_nhdsWithin).exists (f := 𝓝[≠] a)
    exact hya (hinj hy.2 (mem_of_mem_nhds hU) (sub_eq_zero.mp hy.1))
  obtain ⟨k, hk, hk1, τ, haτ, hτa, hgτ⟩ := exists_pow_openPartialHomeomorph hg hga hne
  intro hfa
  have hk2 : 1 < k := by
    rcases Nat.lt_or_ge 1 k with h | h
    · exact h
    · have : k = 1 := le_antisymm h hk
      exact absurd (hderiv.trans hfa) (hk1 this)
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hω
  have hprim := Complex.isPrimitiveRoot_exp k (by omega)
  have hω1 : ω ≠ 1 := hprim.ne_one hk2
  have hωk : ω ^ k = 1 := hprim.pow_eq_one
  have hτ0 : τ.symm 0 = a := by
    rw [← hτa]
    exact τ.left_inv haτ
  have h0T : (0 : ℂ) ∈ τ.target := by
    rw [← hτa]
    exact τ.map_source haτ
  -- the conditions near `0`
  have hU' : U ∩ τ.source ∈ 𝓝 a := inter_mem hU (τ.open_source.mem_nhds haτ)
  have hc1 : ∀ᶠ σ in 𝓝 (0 : ℂ), σ ∈ τ.target ∧ τ.symm σ ∈ U ∩ τ.source :=
    (show ∀ᶠ σ in 𝓝 (0 : ℂ), σ ∈ τ.target from τ.open_target.mem_nhds h0T).and
      ((τ.continuousAt_symm h0T).preimage_mem_nhds (by rw [hτ0]; exact hU'))
  have hωc : Tendsto (fun σ : ℂ => ω * σ) (𝓝 0) (𝓝 0) := by
    have h := (continuous_const_mul ω).tendsto (0 : ℂ)
    rwa [mul_zero] at h
  have hc2 : ∀ᶠ σ in 𝓝 (0 : ℂ), ω * σ ∈ τ.target ∧ τ.symm (ω * σ) ∈ U ∩ τ.source :=
    hωc.eventually hc1
  obtain ⟨σ, ⟨h1, h2⟩, hσ0⟩ := ((hc1.and hc2).filter_mono nhdsWithin_le_nhds |>.and
    self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℂ))
  have hσ0' : σ ≠ 0 := hσ0
  have hne' : τ.symm σ ≠ τ.symm (ω * σ) := by
    intro heq
    have := congrArg τ heq
    rw [τ.right_inv h1.1, τ.right_inv h2.1] at this
    apply hω1
    have h' : (ω - 1) * σ = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hσ0')
  apply hne'
  apply hinj h1.2.1 h2.2.1
  have e1 := hgτ _ h1.2.2
  have e2 := hgτ _ h2.2.2
  rw [τ.right_inv h1.1] at e1
  rw [τ.right_inv h2.1, mul_pow, hωk, one_mul] at e2
  have : g (τ.symm σ) = g (τ.symm (ω * σ)) := e1.trans e2.symm
  simpa [g] using this

end OnLeConjecture.Analytic
