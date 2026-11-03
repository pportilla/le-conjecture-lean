/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorPolydisc
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local charts on a level set of a plane function

Let `H : Source 2 → ℂ` be analytic at `w` with nonzero differential, and suppose that the
restriction of `H - H w` to the vertical line through `w` has a zero of finite order at `w 0`.
Near `w`, the level set `{H = H w}` is a holomorphic disc on which the base projection
`z ↦ z 1` reads `w 1 + τ ^ k` in a suitable coordinate `τ`, where `k ≥ 1`, and `k = 1`
exactly when `fibrePartial H w ≠ 0`.

## Main results

* `exists_levelChart`: the local chart of the level set `{H = H w}` described above.
* `starConvex_pow_preimage`: in such a chart, a base set that is star-shaped about `w 1`
  pulls back to a star-shaped subset of the chart disc.

## Proof

If `fibrePartial H w ≠ 0`, the map `z ↦ (z 1 - w 1, H z - H w)` is a local chart at `w` by
the inverse function theorem, and `k = 1`. Otherwise `basePartial H w ≠ 0`, and the inverse
function theorem for `Ψ z = (z 0, H z - H w)` exhibits the level set near `w` as the graph of
an analytic function `g` of the fibre coordinate with `g (w 0) = w 1`. The finite order
hypothesis shows that `g` is not constant near `w 0`, so `g y - w 1 = (y - w 0) ^ k * u y` with
`u (w 0) ≠ 0`. A `k`-th root of `u` gives a local coordinate `τ` with `g y - w 1 = τ y ^ k`.
Differentiating `H (y, g y) = H w` shows `deriv g (w 0) = 0`, hence `k ≥ 2`.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace OnLeConjecture.Analytic

/-- The differential of `H` at `w` in terms of the two partial derivatives. -/
theorem fderiv_apply_eq_partials (H : Source 2 → ℂ) (w v : Source 2) :
    fderiv ℂ H w v = v 0 * fibrePartial H w + v 1 * basePartial H w := by
  have hv : v = v 0 • (Pi.single 0 1 : Source 2) + v 1 • (Pi.single 1 1 : Source 2) := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul, fibrePartial, basePartial]

/-- An injective continuous linear map `Source 2 → ℂ × ℂ` is a continuous linear
equivalence. -/
theorem exists_continuousLinearEquiv_of_injective (L : Source 2 →L[ℂ] ℂ × ℂ)
    (hL : Injective L) : ∃ e : Source 2 ≃L[ℂ] ℂ × ℂ, (e : Source 2 →L[ℂ] ℂ × ℂ) = L := by
  have hdim : Module.finrank ℂ (Source 2) = Module.finrank ℂ (ℂ × ℂ) := by simp
  refine ⟨((L : Source 2 →ₗ[ℂ] ℂ × ℂ).linearEquivOfInjective hL
    hdim).toContinuousLinearEquiv, ?_⟩
  ext v <;> rfl

/-- A chart `Θ` at `w` whose second coordinate is `H - H w`, and whose first coordinate `t`
satisfies `z 1 = w 1 + t ^ k` on the level set `{H = H w}`, restricts to a chart of the level
set onto a disc. -/
theorem levelChart_of_openPartialHomeomorph (H : Source 2 → ℂ) {w : Source 2} {k : ℕ}
    (Θ : OpenPartialHomeomorph (Source 2) (ℂ × ℂ)) (hw : w ∈ Θ.source) (hΘw : Θ w = 0)
    (hsnd : ∀ z ∈ Θ.source, (Θ z).2 = H z - H w)
    (hfst : ∀ z ∈ Θ.source, H z = H w → z 1 = w 1 + (Θ z).1 ^ k) :
    ∀ r₀ > 0, ∃ N : Set (Source 2), IsOpen N ∧ w ∈ N ∧ N ⊆ Metric.ball w r₀ ∧
      ∃ r > 0, ∃ τ : ↥(N ∩ {z | H z = H w}) ≃ₜ ↥(Metric.ball (0 : ℂ) r),
        ∀ z : ↥(N ∩ {z | H z = H w}), (z : Source 2) 1 = w 1 + ((τ z : ℂ)) ^ k := by
  intro r₀ hr₀
  have h0 : (0 : ℂ × ℂ) ∈ Θ.target := hΘw ▸ Θ.map_source hw
  have hT : Θ.target ∩ Θ.symm ⁻¹' ball w r₀ ∈ 𝓝 (0 : ℂ × ℂ) := by
    refine inter_mem (Θ.open_target.mem_nhds h0) ?_
    apply (Θ.continuousAt_symm h0).preimage_mem_nhds
    rw [← hΘw, Θ.left_inv hw]
    exact ball_mem_nhds w hr₀
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨Θ.source ∩ Θ ⁻¹' ball 0 r, Θ.isOpen_inter_preimage isOpen_ball,
    ⟨hw, by simp [hΘw, hr]⟩, ?_, r, hr, ?_⟩
  · intro z hz
    have hz' := (hrT hz.2).2
    rwa [mem_preimage, Θ.left_inv hz.1] at hz'
  have hmk : ∀ t : ℂ, t ∈ ball (0 : ℂ) r → ((t, 0) : ℂ × ℂ) ∈ ball (0 : ℂ × ℂ) r := by
    intro t ht
    simpa [Prod.norm_def] using ht
  have hsymm : ∀ t : ℂ, t ∈ ball (0 : ℂ) r →
      Θ.symm (t, 0) ∈ (Θ.source ∩ Θ ⁻¹' ball 0 r) ∩ {z | H z = H w} := by
    intro t ht
    have htT : ((t, 0) : ℂ × ℂ) ∈ Θ.target := (hrT (hmk t ht)).1
    have hsrc : Θ.symm (t, 0) ∈ Θ.source := Θ.map_target htT
    have hval : Θ (Θ.symm (t, 0)) = (t, 0) := Θ.right_inv htT
    refine ⟨⟨hsrc, ?_⟩, ?_⟩
    · rw [mem_preimage, hval]
      exact hmk t ht
    · have h2 := hsnd _ hsrc
      rw [hval] at h2
      exact sub_eq_zero.mp h2.symm
  let e : ↥((Θ.source ∩ Θ ⁻¹' ball 0 r) ∩ {z | H z = H w}) ≃ₜ ↥(ball (0 : ℂ) r) :=
    { toFun := fun z => ⟨(Θ z).1, by
        have hz := z.2.1.2
        rw [mem_preimage, mem_ball_zero_iff] at hz
        rw [mem_ball_zero_iff]
        exact (norm_fst_le _).trans_lt hz⟩
      invFun := fun t => ⟨Θ.symm (t, 0), hsymm t t.2⟩
      left_inv := by
        rintro ⟨z, ⟨hzs, hzb⟩, hzH⟩
        apply Subtype.ext
        have h2 : (Θ z).2 = 0 := by
          rw [hsnd z hzs, sub_eq_zero]
          exact hzH
        change Θ.symm ((Θ z).1, 0) = z
        rw [← h2, Prod.mk.eta, Θ.left_inv hzs]
      right_inv := by
        rintro ⟨t, ht⟩
        apply Subtype.ext
        change (Θ (Θ.symm (t, 0))).1 = t
        rw [Θ.right_inv (hrT (hmk t ht)).1]
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        refine continuous_fst.comp ?_
        exact Θ.continuousOn.comp_continuous continuous_subtype_val fun z => z.2.1.1
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        refine Θ.continuousOn_symm.comp_continuous ?_ fun t => (hrT (hmk t t.2)).1
        exact continuous_subtype_val.prodMk continuous_const }
  exact ⟨e, fun z => hfst z z.2.1.1 z.2.2⟩

/-- Near a zero `a` of an analytic function `f` of one variable that does not vanish identically
near `a`, the function `f` is the `k`-th power of a local coordinate, where `k ≥ 1`, and
`deriv f a ≠ 0` when `k = 1`. -/
theorem exists_pow_openPartialHomeomorph {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfa : f a = 0) (hne : ¬∀ᶠ y in 𝓝 a, f y = 0) :
    ∃ k : ℕ, 0 < k ∧ (k = 1 → deriv f a ≠ 0) ∧
      ∃ τ : OpenPartialHomeomorph ℂ ℂ, a ∈ τ.source ∧ τ a = 0 ∧
        ∀ y ∈ τ.source, f y = τ y ^ k := by
  obtain ⟨n, u, hu, hu0, hfu⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hn : n ≠ 0 := by
    rintro rfl
    have h := hfu.self_of_nhds
    rw [hfa, pow_zero, one_smul] at h
    exact hu0 h.symm
  let v : ℂ → ℂ := fun y => u a ^ ((n : ℂ)⁻¹) * (u y / u a) ^ ((n : ℂ)⁻¹)
  have hv : ∀ y, v y ^ n = u y := by
    intro y
    simp only [v, mul_pow, Complex.cpow_nat_inv_pow _ hn]
    field_simp
  have hvan : AnalyticAt ℂ v a := by
    refine analyticAt_const.mul ((hu.div analyticAt_const hu0).cpow analyticAt_const ?_)
    simp [hu0]
  have hva : v a ≠ 0 := by
    intro h
    apply hu0
    rw [← hv a, h, zero_pow hn]
  let τ₀ : ℂ → ℂ := fun y => (y - a) * v y
  have hτan : AnalyticAt ℂ τ₀ a := (analyticAt_id.sub analyticAt_const).mul hvan
  have hτd : HasDerivAt τ₀ (v a) a :=
    (((hasDerivAt_id a).sub_const a).mul hvan.differentiableAt.hasDerivAt).congr_deriv
      (by simp)
  have hτs : HasStrictDerivAt τ₀ (v a) a := by
    have h := hτan.hasStrictDerivAt
    rwa [hτd.deriv] at h
  have hfτ : ∀ᶠ y in 𝓝 a, f y = τ₀ y ^ n := by
    filter_upwards [hfu] with y hy
    rw [hy, smul_eq_mul, mul_pow, hv]
  obtain ⟨V, hVf, hVo, haV⟩ := _root_.eventually_nhds_iff.mp hfτ
  let T := (hτs.hasStrictFDerivAt_equiv hva).toOpenPartialHomeomorph τ₀
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_, T.restrOpen V hVo, ?_, ?_, ?_⟩
  · rintro rfl
    have h : f =ᶠ[𝓝 a] τ₀ := hfτ.mono fun y hy => by simpa using hy
    rw [h.deriv_eq, hτd.deriv]
    exact hva
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨(hτs.hasStrictFDerivAt_equiv hva).mem_toOpenPartialHomeomorph_source, haV⟩
  · simp [T, τ₀]
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    simpa [T] using hVf y hy.2

/-- If `fibrePartial H w ≠ 0`, then `z ↦ (z 1 - w 1, H z - H w)` is a chart at `w`. -/
theorem exists_chart_of_fibrePartial_ne_zero (H : Source 2 → ℂ) {w : Source 2}
    (han : AnalyticAt ℂ H w) (hfib : fibrePartial H w ≠ 0) :
    ∃ Θ : OpenPartialHomeomorph (Source 2) (ℂ × ℂ), w ∈ Θ.source ∧ Θ w = 0 ∧
      (∀ z ∈ Θ.source, (Θ z).2 = H z - H w) ∧
      ∀ z ∈ Θ.source, H z = H w → z 1 = w 1 + (Θ z).1 ^ 1 := by
  let L : Source 2 →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.proj 1).prod (fderiv ℂ H w)
  have hL : Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : v 1 = 0 := congrArg Prod.fst hv
    have h2 : fderiv ℂ H w v = 0 := congrArg Prod.snd hv
    rw [fderiv_apply_eq_partials, h1, zero_mul, add_zero] at h2
    have h0 : v 0 = 0 := (mul_eq_zero.mp h2).resolve_right hfib
    funext i
    fin_cases i
    · exact h0
    · exact h1
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective L hL
  have hΨ : HasStrictFDerivAt (fun z : Source 2 => (z 1 - w 1, H z - H w))
      (e : Source 2 →L[ℂ] ℂ × ℂ) w := by
    rw [he]
    exact ((hasStrictFDerivAt_apply 1 w).sub_const (w 1)).prodMk
      (han.hasStrictFDerivAt.sub_const (H w))
  refine ⟨hΨ.toOpenPartialHomeomorph _, hΨ.mem_toOpenPartialHomeomorph_source, ?_, ?_, ?_⟩
  · simp
  · intro z _
    simp
  · intro z _ _
    simp

/-- If `basePartial H w ≠ 0` and `fibrePartial H w = 0`, and the restriction of `H - H w` to
the vertical line through `w` has a zero of finite order at `w 0`, then there is a chart at `w`
whose second coordinate is `H - H w` and whose first coordinate `t` satisfies
`z 1 = w 1 + t ^ k` on the level set, for some `k ≥ 2`. -/
theorem exists_chart_of_basePartial_ne_zero (H : Source 2 → ℂ) {w : Source 2}
    (han : AnalyticAt ℂ H w) (hbase : basePartial H w ≠ 0) (hfib : fibrePartial H w = 0)
    (hfin : analyticOrderAt (fun t : ℂ => H (Function.update w 0 t) - H w) (w 0) ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ k ≠ 1 ∧ ∃ Θ : OpenPartialHomeomorph (Source 2) (ℂ × ℂ),
      w ∈ Θ.source ∧ Θ w = 0 ∧ (∀ z ∈ Θ.source, (Θ z).2 = H z - H w) ∧
      ∀ z ∈ Θ.source, H z = H w → z 1 = w 1 + (Θ z).1 ^ k := by
  let L : Source 2 →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.proj 0).prod (fderiv ℂ H w)
  have hL : Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : v 0 = 0 := congrArg Prod.fst hv
    have h2 : fderiv ℂ H w v = 0 := congrArg Prod.snd hv
    rw [fderiv_apply_eq_partials, h0, zero_mul, zero_add] at h2
    have h1 : v 1 = 0 := (mul_eq_zero.mp h2).resolve_right hbase
    funext i
    fin_cases i
    · exact h0
    · exact h1
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective L hL
  let Ψ : Source 2 → ℂ × ℂ := fun z => (z 0, H z - H w)
  have hΨ : HasStrictFDerivAt Ψ (e : Source 2 →L[ℂ] ℂ × ℂ) w := by
    rw [he]
    exact (hasStrictFDerivAt_apply 0 w).prodMk (han.hasStrictFDerivAt.sub_const (H w))
  let Φ := hΨ.toOpenPartialHomeomorph Ψ
  have hΦcoe : (Φ : Source 2 → ℂ × ℂ) = Ψ := hΨ.toOpenPartialHomeomorph_coe
  have hwS : w ∈ Φ.source := hΨ.mem_toOpenPartialHomeomorph_source
  have hΨw : Ψ w = (w 0, 0) := by simp [Ψ]
  have hwT : ((w 0, 0) : ℂ × ℂ) ∈ Φ.target :=
    hΨw ▸ hΨ.image_mem_toOpenPartialHomeomorph_target
  have hΦw : Φ.symm (w 0, 0) = w := by
    rw [← hΨw, ← hΦcoe, Φ.left_inv hwS]
  have hΨan : AnalyticAt ℂ Ψ w :=
    ((ContinuousLinearMap.proj 0).analyticAt w).prod (han.sub analyticAt_const)
  have hsymm_an : AnalyticAt ℂ Φ.symm (w 0, 0) := by
    have h := Φ.analyticAt_symm' (i := e) hwS (hΦcoe ▸ hΨan)
      (by rw [hΦcoe]; exact hΨ.hasFDerivAt.fderiv)
    rwa [hΦcoe, hΨw] at h
  have hsymm_d : HasFDerivAt Φ.symm (e.symm : ℂ × ℂ →L[ℂ] Source 2) (w 0, 0) :=
    Φ.hasFDerivAt_symm hwT (by rw [hΦw, hΦcoe]; exact hΨ.hasFDerivAt)
  let γ : ℂ → Source 2 := fun y => Φ.symm (y, 0)
  let g : ℂ → ℂ := fun y => γ y 1 - w 1
  have hγT : ∀ᶠ y in 𝓝 (w 0), ((y, 0) : ℂ × ℂ) ∈ Φ.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds hwT)
  have hγ : ∀ y, ((y, 0) : ℂ × ℂ) ∈ Φ.target → γ y 0 = y ∧ H (γ y) = H w := by
    intro y hy
    have h := Φ.right_inv hy
    rw [hΦcoe] at h
    simp only [Ψ, Prod.mk.injEq] at h
    exact ⟨h.1, sub_eq_zero.mp h.2⟩
  have hgan : AnalyticAt ℂ g (w 0) := by
    have h1 : AnalyticAt ℂ γ (w 0) :=
      hsymm_an.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    exact (((ContinuousLinearMap.proj 1).analyticAt _).comp h1).sub analyticAt_const
  have hg0 : g (w 0) = 0 := by simp [g, γ, hΦw]
  have hgne : ¬∀ᶠ y in 𝓝 (w 0), g y = 0 := by
    intro hg
    apply hfin
    rw [analyticOrderAt_eq_top]
    filter_upwards [hg, hγT] with y hy hyT
    obtain ⟨h0, hH⟩ := hγ y hyT
    have hupd : γ y = Function.update w 0 y := by
      funext i
      fin_cases i
      · simpa using h0
      · simpa [g, sub_eq_zero] using hy
    rw [← hupd, hH, sub_self]
  have hgd : deriv g (w 0) = 0 := by
    have hγd : HasDerivAt γ (e.symm (1, 0)) (w 0) :=
      hsymm_d.comp_hasDerivAt_of_eq (w 0)
        (HasDerivAt.prodMk (hasDerivAt_id (w 0)) (hasDerivAt_const (w 0) (0 : ℂ))) rfl
    have hgd' : HasDerivAt g (e.symm (1, 0) 1) (w 0) :=
      ((hasDerivAt_pi.mp hγd) 1).sub_const (w 1)
    rw [hgd'.deriv]
    have hev : L (e.symm (1, 0)) = (1, 0) := by
      rw [← he]
      exact e.apply_symm_apply (1, 0)
    have h2 : fderiv ℂ H w (e.symm (1, 0)) = 0 := congrArg Prod.snd hev
    rw [fderiv_apply_eq_partials, hfib, mul_zero, zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_right hbase
  obtain ⟨k, hk, hk1, τ, haτ, hτa, hgτ⟩ := exists_pow_openPartialHomeomorph hgan hg0 hgne
  refine ⟨k, hk, fun h => hk1 h hgd, Φ.trans (τ.prod (OpenPartialHomeomorph.refl ℂ)),
    ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hwS, ?_⟩
    simp [hΦcoe, Ψ, haτ]
  · simp [hΦcoe, Ψ, hτa]
  · intro z _
    simp [hΦcoe, Ψ]
  · intro z hz hzH
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzS, hzτ⟩ := hz
    have hΨz : Ψ z = (z 0, 0) := by simp [Ψ, hzH]
    have hz0 : z 0 ∈ τ.source := by
      simpa [hΦcoe, hΨz, OpenPartialHomeomorph.prod_source] using hzτ
    have hzγ : γ (z 0) = z := by
      change Φ.symm (z 0, 0) = z
      rw [← hΨz, ← hΦcoe, Φ.left_inv hzS]
    have h := hgτ (z 0) hz0
    simp only [g, hzγ] at h
    simp only [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.prod_apply, hΦcoe, Ψ,
      OpenPartialHomeomorph.refl_apply]
    linear_combination h

/-- **Local chart on a level set.** Let `H` be analytic at `w` with nonzero differential, and
suppose that `t ↦ H (update w 0 t) - H w` has a zero of finite order at `w 0`. Then there is
`k ≥ 1`, with `k = 1` exactly when `fibrePartial H w ≠ 0`, such that every ball around `w`
contains an open neighbourhood `N` of `w` whose intersection with the level set `{H = H w}` is
homeomorphic to a disc `ball 0 r` by a coordinate `τ` with `z 1 = w 1 + τ z ^ k`. -/
theorem exists_levelChart (H : Source 2 → ℂ) {w : Source 2} (han : AnalyticAt ℂ H w)
    (hgrad : fderiv ℂ H w ≠ 0)
    (hfin : analyticOrderAt (fun t : ℂ => H (Function.update w 0 t) - H w) (w 0) ≠ ⊤) :
    ∃ k : ℕ, 0 < k ∧ (k = 1 ↔ fibrePartial H w ≠ 0) ∧
      ∀ r₀ > 0, ∃ N : Set (Source 2), IsOpen N ∧ w ∈ N ∧ N ⊆ Metric.ball w r₀ ∧
        ∃ r > 0, ∃ τ : ↥(N ∩ {z | H z = H w}) ≃ₜ ↥(Metric.ball (0 : ℂ) r),
          ∀ z : ↥(N ∩ {z | H z = H w}), (z : Source 2) 1 = w 1 + ((τ z : ℂ)) ^ k := by
  by_cases hfib : fibrePartial H w ≠ 0
  · obtain ⟨Θ, hw, hΘw, hsnd, hfst⟩ := exists_chart_of_fibrePartial_ne_zero H han hfib
    exact ⟨1, one_pos, iff_of_true rfl hfib,
      levelChart_of_openPartialHomeomorph H Θ hw hΘw hsnd hfst⟩
  · rw [not_not] at hfib
    have hbase : basePartial H w ≠ 0 := by
      intro hb
      apply hgrad
      ext1 v
      rw [fderiv_apply_eq_partials, hfib, hb]
      simp
    obtain ⟨k, hk, hk1, Θ, hw, hΘw, hsnd, hfst⟩ :=
      exists_chart_of_basePartial_ne_zero H han hbase hfib hfin
    exact ⟨k, hk, iff_of_false hk1 (not_not.mpr hfib),
      levelChart_of_openPartialHomeomorph H Θ hw hΘw hsnd hfst⟩

/-- In a chart where the base coordinate reads `b + τ ^ k`, a base set `M` that is star-shaped
about `b` pulls back to a star-shaped subset of the chart disc `ball 0 r`. -/
theorem starConvex_pow_preimage (k : ℕ) (r : ℝ) {b : ℂ} {M : Set ℂ}
    (hM : StarConvex ℝ b M) :
    StarConvex ℝ (0 : ℂ) {τ : ℂ | τ ∈ Metric.ball (0 : ℂ) r ∧ b + τ ^ k ∈ M} := by
  rintro τ ⟨hτr, hτM⟩ a s ha hs has
  have hs1 : s ≤ 1 := by linarith
  rw [smul_zero, zero_add]
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff] at hτr ⊢
    rw [norm_smul, Real.norm_of_nonneg hs]
    exact (mul_le_of_le_one_left (norm_nonneg τ) hs1).trans_lt hτr
  · have h := hM hτM (sub_nonneg.mpr (pow_le_one₀ hs hs1)) (pow_nonneg hs k) (by ring)
    convert h using 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
      mul_pow]
    ring

/-- If a base set `M` lies in the disc of radius `r ^ k` about `b`, where `k ≥ 1` and
`r ≥ 0`, then every `τ` with `b + τ ^ k ∈ M` lies in the chart disc `ball 0 r`. -/
theorem mem_ball_of_pow_mem {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 ≤ r) {b : ℂ} {M : Set ℂ}
    (hMr : M ⊆ Metric.ball b (r ^ k)) {τ : ℂ} (hτ : b + τ ^ k ∈ M) :
    τ ∈ Metric.ball (0 : ℂ) r := by
  have h := hMr hτ
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_pow] at h
  rw [mem_ball_zero_iff]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg τ) hr hk.ne').mp h

end OnLeConjecture.Analytic
