/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibre
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Oriented charts with boundary on the Milnor fibre

Let `H : Source 2 → ℂ` be analytic at the origin with `H 0 = 0` and squarefree germ, and let
`E = euclideanEquation H` be the equation on the Euclidean model of `ℂ²`. For every sufficiently
small radius `ε` there is `δ > 0` such that for `0 < |s| < δ` every point `z` of the Milnor fibre
`F = {w : ‖w‖ ≤ ε, E w = s}` carries a chart `MilnorFibreChart H ε s z`. Such a chart is a real
analytic immersion `φ` of an open set `W ⊆ ℂ`, with real coordinates `t = u + i v`, such that
* the restriction of `φ` to the model set, which is `W` for an interior chart and
  `W ∩ {Im t ≥ 0}` for a boundary chart, is a homeomorphism onto a neighbourhood of `z` in `F`;
* a point `t` of the model set is sent to the boundary `{‖w‖ = ε, E w = s}` exactly when the
  chart is a boundary chart and `Im t = 0`;
* `∂ᵥφ = c • ∂ᵤφ` with `Im c > 0`, so that `φ` preserves the complex orientation of `F`.

## Main results

* `exists_levelParametrization`: a holomorphic parametrization `ψ` of the level of a function
  with nonzero complex differential, together with a linear left inverse `w ↦ ℓ (w - z)`.
* `nonempty_milnorFibreChart_of_interior`: interior charts at points with `‖z‖ < ε`.
* `nonempty_milnorFibreChart_of_boundary`: boundary charts at points with `‖z‖ = ε` where the
  equation together with the squared norm is a submersion.
* `exists_milnorFibreCharts`: every point of a Milnor fibre of small radius over a small nonzero
  level has a chart.
* `MilnorFibreChart.homeomorph`: the homeomorphism of the model set onto the image of a chart.

## Proof

At a point `z` where the complex differential `dE` does not vanish, choose a coordinate `ℓ`
of `ℂ²` such that `(ℓ, dE)` is invertible. The holomorphic inverse function theorem applied to
`w ↦ (ℓ (w - z), E w - E z)` gives a holomorphic parametrization `ψ` of the level `{E = E z}`
near `z`, with `ψ 0 = z` and `ℓ (ψ t - z) = t`. In the interior, `ψ` restricted to a small disc
is the chart, and complex linearity of its differential gives `c = i`.

On the boundary sphere, the function `r u = ‖ψ u‖ ^ 2` has nonzero real differential `β` at `0`,
by surjectivity of the real differential of `z ↦ (E z, ‖z‖ ^ 2)`. For
`μ = -β i - (β 1) i`, the real analytic map `T u = Re (μ u) + i (ε ^ 2 - r u)` has differential
equal to multiplication by `μ` at `0`. By the real inverse function theorem `T` has a real
analytic local inverse `g`, and the boundary chart is `φ = ψ ∘ g`. The function
`χ w = Re (μ ℓ (w - z)) + i (ε ^ 2 - ‖w‖ ^ 2)` is a left inverse of `φ`, so that
`Im t = ε ^ 2 - ‖φ t‖ ^ 2`. Since `dg 0` is multiplication by `μ⁻¹`, the quantity
`Im (dg t i · conj (dg t 1))` is positive near `0`, and `∂ᵥφ = c • ∂ᵤφ` with
`c = dg t i / dg t 1`.

## Implementation notes

The flag `boundaryChart` of a chart is a `Bool`, so that the `if` defining the model set needs
no decidability instance. The smoothness condition `ContDiffOn ℝ ⊤ φ W` uses `⊤ = ω`, so it
states that `φ` is real analytic on `W`.
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-! ### Inverse function theorem with analytic inverse -/

/-- **Analytic local inverse.** If `f` is analytic near `a` and its derivative at `a` is a
continuous linear equivalence, then `f` restricts to an open partial homeomorphism whose source
contains `a` and whose inverse is analytic at every point of its target. -/
theorem exists_openPartialHomeomorph_contDiffAt_symm {𝕂 : Type*} [RCLike 𝕂]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕂 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕂 Y]
    {f : X → Y} {a : X} {f' : X ≃L[𝕂] Y}
    (hf : ∀ᶠ x in 𝓝 a, ContDiffAt 𝕂 ω f x) (hfa : HasFDerivAt f (f' : X →L[𝕂] Y) a) :
    ∃ Φ : OpenPartialHomeomorph X Y, (Φ : X → Y) = f ∧ a ∈ Φ.source ∧
      ∀ y ∈ Φ.target, ContDiffAt 𝕂 ω Φ.symm y := by
  have hstrict : HasStrictFDerivAt f (f' : X →L[𝕂] Y) a := by
    have h := hf.self_of_nhds.hasStrictFDerivAt (by simp)
    rwa [hfa.fderiv] at h
  have hS : {x | ContDiffAt 𝕂 ω f x ∧ ∃ e : X ≃L[𝕂] Y, (e : X →L[𝕂] Y) = fderiv 𝕂 f x}
      ∈ 𝓝 a := by
    have hcont : ContinuousAt (fderiv 𝕂 f) a :=
      (hf.self_of_nhds.fderiv_right (m := 0) (by simp)).continuousAt
    have h2 : {x | ∃ e : X ≃L[𝕂] Y, (e : X →L[𝕂] Y) = fderiv 𝕂 f x} ∈ 𝓝 a := by
      have h3 := f'.nhds
      rw [← hfa.fderiv] at h3
      exact hcont.preimage_mem_nhds h3
    filter_upwards [hf, h2] with x h1 h2 using ⟨h1, h2⟩
  obtain ⟨V, hVS, hVo, haV⟩ := _root_.mem_nhds_iff.mp hS
  refine ⟨(hstrict.toOpenPartialHomeomorph f).restrOpen V hVo, rfl,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, haV⟩, fun y hy => ?_⟩
  set Φ := (hstrict.toOpenPartialHomeomorph f).restrOpen V hVo
  have hx : Φ.symm y ∈ Φ.source := Φ.map_target hy
  obtain ⟨hc, e, he⟩ := hVS hx.2
  refine Φ.contDiffAt_symm (f₀' := e) hy ?_ hc
  rw [he]
  exact (hc.differentiableAt (by simp)).hasFDerivAt

/-! ### Holomorphic parametrization of a level -/

/-- A nonzero complex linear form on `ℂ²` does not vanish on some standard basis vector. -/
theorem exists_euclidean_single_ne_zero {D : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ} (hD : D ≠ 0) :
    ∃ j : Fin 2, D (EuclideanSpace.single j 1) ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.ext
  intro i
  simpa using h i

/-- If a complex linear form `D` on `ℂ²` does not vanish on the basis vector `e_j` and `i ≠ j`,
then `v ↦ (v i, D v)` is injective. -/
theorem injective_euclideanProj_prod {D : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ} {i j : Fin 2}
    (hij : i ≠ j) (hj : D (EuclideanSpace.single j 1) ≠ 0) :
    Injective ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).prod D) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hi : v i = 0 := congrArg Prod.fst hv
  have hD : D v = 0 := congrArg Prod.snd hv
  have hv' : v = v j • EuclideanSpace.single j (1 : ℂ) := by
    ext m
    by_cases hm : m = j
    · subst hm
      simp
    · have hmi : m = i := by
        fin_cases m <;> fin_cases i <;> fin_cases j <;> simp_all
      subst hmi
      simp [hi, hm]
  rw [hv', map_smul, smul_eq_mul, mul_eq_zero] at hD
  rcases hD with h | h
  · rw [hv', h, zero_smul]
  · exact absurd h hj

/-- An injective continuous linear map `ℂ² → ℂ × ℂ` is a continuous linear equivalence. -/
theorem exists_continuousLinearEquiv_of_injective_euclidean
    (L : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ × ℂ) (hL : Injective L) :
    ∃ e : EuclideanSpace ℂ (Fin 2) ≃L[ℂ] ℂ × ℂ,
      (e : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ × ℂ) = L := by
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = Module.finrank ℂ (ℂ × ℂ) := by
    simp
  refine ⟨((L : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ × ℂ).linearEquivOfInjective hL
    hdim).toContinuousLinearEquiv, ?_⟩
  ext v <;> rfl

/-- **Holomorphic parametrization of a level.** Let `F : ℂ² → ℂ` be analytic at `z` with
nonzero complex differential. There are a complex linear form `ℓ`, open sets `U ∋ 0` in `ℂ` and
`N ∋ z` in `ℂ²`, and a map `ψ : ℂ → ℂ²` analytic on `U` with `ψ 0 = z`, such that `ψ` maps `U`
into the level `{F = F z}`, the map `w ↦ ℓ (w - z)` is a left inverse of `ψ` on `U`, every point
of the level in `N` is `ψ (ℓ (w - z))`, and every vector `h` in the kernel of the complex
differential of `F` at `z` equals `ℓ h • deriv ψ 0`. -/
theorem exists_levelParametrization (F : EuclideanSpace ℂ (Fin 2) → ℂ)
    {z : EuclideanSpace ℂ (Fin 2)} (hF : AnalyticAt ℂ F z) (hd : fderiv ℂ F z ≠ 0) :
    ∃ (ℓ : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ) (ψ : ℂ → EuclideanSpace ℂ (Fin 2)) (U : Set ℂ)
      (N : Set (EuclideanSpace ℂ (Fin 2))),
      IsOpen U ∧ (0 : ℂ) ∈ U ∧ IsOpen N ∧ z ∈ N ∧ ψ 0 = z ∧
      (∀ t ∈ U, AnalyticAt ℂ ψ t) ∧ (∀ t ∈ U, F (ψ t) = F z) ∧
      (∀ t ∈ U, ℓ (ψ t - z) = t) ∧
      (∀ w ∈ N, F w = F z → ℓ (w - z) ∈ U ∧ ψ (ℓ (w - z)) = w) ∧
      (∀ h, fderiv ℂ F z h = 0 → h = ℓ h • deriv ψ 0) := by
  obtain ⟨j, hj⟩ := exists_euclidean_single_ne_zero hd
  obtain ⟨i, hij⟩ : ∃ i : Fin 2, i ≠ j := by
    fin_cases j
    exacts [⟨1, by decide⟩, ⟨0, by decide⟩]
  set ℓ : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ := EuclideanSpace.proj i with hℓ
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_of_injective_euclidean _
    (injective_euclideanProj_prod (D := fderiv ℂ F z) hij hj)
  set Ψ : EuclideanSpace ℂ (Fin 2) → ℂ × ℂ := fun w => (ℓ (w - z), F w - F z) with hΨ
  have hℓd : HasFDerivAt (fun w => ℓ (w - z)) ℓ z := by
    simpa using ℓ.hasFDerivAt
  have hΨd : HasFDerivAt Ψ (e : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ × ℂ) z := by
    rw [he]
    exact hℓd.prodMk (hF.differentiableAt.hasFDerivAt.sub_const (F z))
  have hΨc : ∀ᶠ w in 𝓝 z, ContDiffAt ℂ ω Ψ w := by
    filter_upwards [hF.eventually_analyticAt] with w hw
    exact ((ℓ.analyticAt _).comp ((analyticAt_id).sub analyticAt_const)).prod
      (hw.sub analyticAt_const) |>.contDiffAt
  obtain ⟨Φ, hΦ, hzΦ, hsymm⟩ := exists_openPartialHomeomorph_contDiffAt_symm hΨc hΨd
  have hΦz : Φ z = (0, 0) := by simp [hΦ, Ψ]
  have hΨz : Φ.symm (0, 0) = z := by rw [← hΦz, Φ.left_inv hzΦ]
  have h0T : ((0 : ℂ), (0 : ℂ)) ∈ Φ.target := hΦz ▸ Φ.map_source hzΦ
  have hR : ∀ t : ℂ, (t, (0 : ℂ)) ∈ Φ.target → Ψ (Φ.symm (t, 0)) = (t, 0) := by
    intro t ht
    rw [← hΦ]
    exact Φ.right_inv ht
  refine ⟨ℓ, fun t => Φ.symm (t, 0), (fun t : ℂ => (t, (0 : ℂ))) ⁻¹' Φ.target, Φ.source,
    Φ.open_target.preimage (continuous_id.prodMk continuous_const), h0T, Φ.open_source, hzΦ,
    hΨz, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hsymm _ ht).analyticAt.comp (f := fun t : ℂ => (t, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const)
  · intro t ht
    have h := congrArg Prod.snd (hR t ht)
    exact sub_eq_zero.mp h
  · intro t ht
    exact congrArg Prod.fst (hR t ht)
  · intro w hw hFw
    have hΦw : Φ w = (ℓ (w - z), 0) := by simp [hΦ, Ψ, hFw]
    refine ⟨?_, ?_⟩
    · change (ℓ (w - z), (0 : ℂ)) ∈ Φ.target
      rw [← hΦw]
      exact Φ.map_source hw
    · change Φ.symm (ℓ (w - z), 0) = w
      rw [← hΦw, Φ.left_inv hw]
  · intro h hh
    have hsd : HasFDerivAt Φ.symm (e.symm : ℂ × ℂ →L[ℂ] EuclideanSpace ℂ (Fin 2)) (0, 0) :=
      Φ.hasFDerivAt_symm h0T (by rw [hΨz, hΦ]; exact hΨd)
    have hψd : HasDerivAt (fun t : ℂ => Φ.symm (t, 0)) (e.symm (1, 0)) 0 :=
      hsd.comp_hasDerivAt_of_eq 0
        (HasDerivAt.prodMk (hasDerivAt_id 0) (hasDerivAt_const 0 (0 : ℂ))) rfl
    rw [hψd.deriv]
    apply e.injective
    have h1 : e h = (ℓ h, 0) := by
      rw [← ContinuousLinearEquiv.coe_coe, he]
      simp [hh, hℓ]
    rw [h1, map_smul, e.apply_symm_apply]
    simp

/-! ### Orientation-preserving real local inverses -/

/-- Multiplication by a nonzero complex number, as a real continuous linear equivalence of
`ℂ`. -/
def mulRealEquiv (μ : ℂ) (hμ : μ ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 μ hμ)

@[simp] theorem mulRealEquiv_apply (μ : ℂ) (hμ : μ ≠ 0) (v : ℂ) :
    mulRealEquiv μ hμ v = μ * v := rfl

@[simp] theorem mulRealEquiv_symm_apply (μ : ℂ) (hμ : μ ≠ 0) (v : ℂ) :
    (mulRealEquiv μ hμ).symm v = μ⁻¹ * v := rfl

/-- For `a ≠ 0`, the real linear map `t ↦ a t` has positive orientation:
`Im (a i · conj a) = |a| ^ 2 > 0`. -/
theorem im_mul_I_mul_conj_pos {a : ℂ} (ha : a ≠ 0) : 0 < (a * Complex.I * conj a).im := by
  have h : (a * Complex.I * conj a).im = Complex.normSq a := by
    simp [Complex.normSq_apply, Complex.mul_im, Complex.mul_re]
    ring
  rw [h]
  exact Complex.normSq_pos.mpr ha

/-- **Orientation-preserving real local inverse.** Let `T : ℂ → ℂ` be real analytic near `0`
with `T 0 = 0`, whose real differential at `0` is multiplication by `μ ≠ 0`. Then `T` restricts
to an open partial homeomorphism `G` with `0` in its source and real analytic inverse, and the
differential of the inverse is orientation preserving near `0`, in the sense that
`Im (d(G⁻¹) i · conj (d(G⁻¹) 1)) > 0`. -/
theorem exists_orientedLocalInverse {T : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (hT : ∀ᶠ u in 𝓝 0, ContDiffAt ℝ ω T u) (hT0 : T 0 = 0)
    (hTd : HasFDerivAt T ((mulRealEquiv μ hμ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 0) :
    ∃ G : OpenPartialHomeomorph ℂ ℂ, (G : ℂ → ℂ) = T ∧ (0 : ℂ) ∈ G.source ∧
      (∀ t ∈ G.target, ContDiffAt ℝ ω G.symm t) ∧
      ∀ᶠ t in 𝓝 0, 0 < (fderiv ℝ G.symm t Complex.I * conj (fderiv ℝ G.symm t 1)).im := by
  obtain ⟨G, hG, h0G, hsymm⟩ := exists_openPartialHomeomorph_contDiffAt_symm hT hTd
  have hG0 : G 0 = 0 := by rw [hG, hT0]
  have h0T : (0 : ℂ) ∈ G.target := hG0 ▸ G.map_source h0G
  have hGs0 : G.symm 0 = 0 := by
    have h := G.left_inv h0G
    rwa [hG0] at h
  have hsd : HasFDerivAt G.symm ((mulRealEquiv μ hμ).symm : ℂ →L[ℝ] ℂ) 0 :=
    G.hasFDerivAt_symm h0T (by rw [hGs0, hG]; exact hTd)
  have hcont : ContinuousAt (fderiv ℝ G.symm) 0 :=
    ((hsymm 0 h0T).fderiv_right (m := 0) (by simp)).continuousAt
  have hq : ContinuousAt
      (fun t => (fderiv ℝ G.symm t Complex.I * conj (fderiv ℝ G.symm t 1)).im) 0 := by
    refine Complex.continuous_im.continuousAt.comp ?_
    refine (hcont.clm_apply continuousAt_const).mul ?_
    exact Complex.continuous_conj.continuousAt.comp (hcont.clm_apply continuousAt_const)
  refine ⟨G, hG, h0G, hsymm, continuousAt_const.eventually_lt hq ?_⟩
  rw [hsd.fderiv]
  simpa using im_mul_I_mul_conj_pos (inv_ne_zero hμ)

/-! ### Charts -/

/-- An oriented chart with boundary of the Milnor fibre `F = milnorFibre H ε s` at `z`: a real
analytic immersion `φ` of an open set `W ⊆ ℂ`, with real coordinates `t = u + i v`, whose
restriction to the model set (`W` itself for interior charts, `W ∩ {Im t ≥ 0}` for boundary
charts) is a homeomorphism onto a neighbourhood of `z` in `F`, sending exactly the points with
`Im t = 0` of a boundary chart to the boundary, and compatible with the complex orientation:
`∂ᵥφ = c • ∂ᵤφ` with `Im c > 0`. Here `ContDiffOn ℝ ⊤` with `⊤ = ω` means real analytic. -/
structure MilnorFibreChart (H : Source 2 → ℂ) (ε : ℝ) (s : ℂ) (z : EuclideanSpace ℂ (Fin 2))
    where
  /-- The open domain of the chart. -/
  W : Set ℂ
  isOpen_W : IsOpen W
  /-- Whether the chart is a boundary chart. -/
  boundaryChart : Bool
  /-- The model set: `W` for interior charts and `W ∩ {Im t ≥ 0}` for boundary charts. -/
  model : Set ℂ
  model_eq : model = if boundaryChart then W ∩ {t | 0 ≤ t.im} else W
  /-- The parametrization. -/
  φ : ℂ → EuclideanSpace ℂ (Fin 2)
  zero_mem : (0 : ℂ) ∈ model
  φ_zero : φ 0 = z
  smooth : ContDiffOn ℝ ⊤ φ W
  immersion : ∀ t ∈ W, Function.Injective (fderiv ℝ φ t)
  oriented : ∀ t ∈ W, ∃ c : ℂ, 0 < c.im ∧ fderiv ℝ φ t Complex.I = c • fderiv ℝ φ t 1
  mapsTo : Set.MapsTo φ model (milnorFibre H ε s)
  injOn : Set.InjOn φ model
  isOpenMap : ∀ U, IsOpen U →
    ∃ V, IsOpen V ∧ φ '' (U ∩ model) = V ∩ milnorFibre H ε s ∩ φ '' model
  nhds : φ '' model ∈ nhdsWithin z (milnorFibre H ε s)
  boundary_iff : ∀ t ∈ model, φ t ∈ milnorFibreBoundary H ε s ↔ (boundaryChart ∧ t.im = 0)

/-- A map `φ : ℂ → F` with a differentiable left inverse near `t` has injective differential
at `t`. -/
theorem injective_fderiv_of_leftInverse {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → F} {χ : F → ℂ} {t : ℂ}
    (hφ : DifferentiableAt ℝ φ t) (hχ : DifferentiableAt ℝ χ (φ t))
    (h : ∀ᶠ u in 𝓝 t, χ (φ u) = u) : Injective (fderiv ℝ φ t) := by
  have h1 : HasFDerivAt (χ ∘ φ) ((fderiv ℝ χ (φ t)).comp (fderiv ℝ φ t)) t :=
    hχ.hasFDerivAt.comp t hφ.hasFDerivAt
  have h2 : HasFDerivAt (χ ∘ φ) (ContinuousLinearMap.id ℝ ℂ) t :=
    (hasFDerivAt_id t).congr_of_eventuallyEq h
  have h3 := h1.unique h2
  intro a b hab
  have ha := DFunLike.congr_fun h3 a
  have hb := DFunLike.congr_fun h3 b
  simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_id', id_eq]
    at ha hb
  rw [← ha, ← hb, hab]

/-- Assemble a chart of the Milnor fibre from a real analytic map `φ` on an open set `W` that
has a differentiable left inverse `χ` on `W`, maps the model set into the fibre, satisfies the
orientation condition and the boundary correspondence, and such that `φ ∘ χ` is the identity on
the points of the fibre near `z`, with `χ` taking values in the model set there. -/
def MilnorFibreChart.ofLeftInverse {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (W : Set ℂ) (hW : IsOpen W) (b : Bool) (model : Set ℂ)
    (hmodel : model = if b then W ∩ {t | 0 ≤ t.im} else W)
    (φ : ℂ → EuclideanSpace ℂ (Fin 2)) (χ : EuclideanSpace ℂ (Fin 2) → ℂ)
    (h0 : (0 : ℂ) ∈ model) (hφ0 : φ 0 = z) (hsmooth : ContDiffOn ℝ ⊤ φ W)
    (hχ : Differentiable ℝ χ) (hleft : ∀ t ∈ W, χ (φ t) = t)
    (horient : ∀ t ∈ W, ∃ c : ℂ, 0 < c.im ∧ fderiv ℝ φ t Complex.I = c • fderiv ℝ φ t 1)
    (hmaps : MapsTo φ model (milnorFibre H ε s))
    (hnhds : ∀ᶠ w in 𝓝[milnorFibre H ε s] z, χ w ∈ model ∧ φ (χ w) = w)
    (hbdry : ∀ t ∈ model, φ t ∈ milnorFibreBoundary H ε s ↔ (b ∧ t.im = 0)) :
    MilnorFibreChart H ε s z where
  W := W
  isOpen_W := hW
  boundaryChart := b
  model := model
  model_eq := hmodel
  φ := φ
  zero_mem := h0
  φ_zero := hφ0
  smooth := hsmooth
  immersion t ht := by
    have hφd : DifferentiableAt ℝ φ t :=
      (hsmooth.contDiffAt (hW.mem_nhds ht)).differentiableAt (by simp)
    refine injective_fderiv_of_leftInverse hφd (hχ _) ?_
    filter_upwards [hW.mem_nhds ht] with u hu using hleft u hu
  oriented := horient
  mapsTo := hmaps
  injOn := by
    have hMW : model ⊆ W := by
      rw [hmodel]
      cases b
      · exact subset_rfl
      · exact inter_subset_left
    intro t ht u hu htu
    rw [← hleft t (hMW ht), ← hleft u (hMW hu), htu]
  isOpenMap U hU := by
    have hMW : model ⊆ W := by
      rw [hmodel]
      cases b
      · exact subset_rfl
      · exact inter_subset_left
    refine ⟨χ ⁻¹' U, hU.preimage hχ.continuous, ?_⟩
    ext w
    constructor
    · rintro ⟨t, ⟨htU, htM⟩, rfl⟩
      refine ⟨⟨?_, hmaps htM⟩, t, htM, rfl⟩
      rw [mem_preimage, hleft t (hMW htM)]
      exact htU
    · rintro ⟨⟨hwU, -⟩, t, htM, rfl⟩
      refine ⟨t, ⟨?_, htM⟩, rfl⟩
      rwa [mem_preimage, hleft t (hMW htM)] at hwU
  nhds := by
    filter_upwards [hnhds] with w hw
    exact ⟨χ w, hw.1, hw.2⟩
  boundary_iff := hbdry

/-- A complex differentiable function whose real differential is surjective has nonzero complex
differential. -/
theorem fderiv_ne_zero_of_real_surjective {F : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hF : DifferentiableAt ℂ F z)
    (hsurj : Surjective (fderiv ℝ F z)) : fderiv ℂ F z ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := hsurj 1
  rw [hF.fderiv_restrictScalars ℝ, h0] at hv
  simp at hv

/-- **Interior charts.** At a point `z` with `‖z‖ < ε` and `E z = s`, where the equation `E` is
analytic with surjective real differential, the Milnor fibre has an interior chart. -/
theorem nonempty_milnorFibreChart_of_interior {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hzε : ‖z‖ < ε) (hzs : euclideanEquation H z = s)
    (han : AnalyticAt ℂ (euclideanEquation H) z)
    (hsurj : Surjective (fderiv ℝ (euclideanEquation H) z)) :
    Nonempty (MilnorFibreChart H ε s z) := by
  obtain ⟨ℓ, ψ, U, N, hU, h0U, hN, hzN, hψ0, hψan, hψF, hψℓ, hloc, -⟩ :=
    exists_levelParametrization (euclideanEquation H) han
      (fderiv_ne_zero_of_real_surjective han.differentiableAt hsurj)
  have hψc : ContinuousOn ψ U := fun t ht => (hψan t ht).continuousAt.continuousWithinAt
  set W := U ∩ ψ ⁻¹' ball 0 ε with hWdef
  have hW : IsOpen W := hψc.isOpen_inter_preimage hU isOpen_ball
  have h0W : (0 : ℂ) ∈ W := ⟨h0U, by rw [mem_preimage, hψ0]; exact mem_ball_zero_iff.mpr hzε⟩
  refine ⟨MilnorFibreChart.ofLeftInverse W hW false W (by simp) ψ (fun w => ℓ (w - z)) h0W hψ0
    ?_ ?_ (fun t ht => hψℓ t ht.1) ?_ ?_ ?_ ?_⟩
  · exact fun t ht => ((hψan t ht.1).restrictScalars (𝕜 := ℝ)).contDiffAt.contDiffWithinAt
  · exact (ℓ.restrictScalars ℝ).differentiable.comp (differentiable_id.sub_const z)
  · intro t ht
    refine ⟨Complex.I, by simp, ?_⟩
    rw [(hψan t ht.1).differentiableAt.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars']
    rw [← map_smul, smul_eq_mul, mul_one]
  · intro t ht
    exact ⟨(mem_ball_zero_iff.mp ht.2).le, (hψF t ht.1).trans hzs⟩
  · refine mem_nhdsWithin.mpr ⟨N ∩ ball 0 ε, hN.inter isOpen_ball,
      ⟨hzN, mem_ball_zero_iff.mpr hzε⟩, ?_⟩
    rintro w ⟨⟨hwN, hwb⟩, hwF⟩
    obtain ⟨h1, h2⟩ := hloc w hwN (hwF.2.trans hzs.symm)
    refine ⟨⟨h1, ?_⟩, h2⟩
    rw [mem_preimage, h2]
    exact hwb
  · intro t ht
    simp only [Bool.false_eq_true, false_and, iff_false]
    rintro ⟨h, -⟩
    exact (mem_ball_zero_iff.mp ht.2).ne h

/-- A real linear form on `ℂ` in terms of its values at `1` and `i`. -/
theorem realLinearForm_apply_eq (β : ℂ →L[ℝ] ℝ) (v : ℂ) :
    β v = v.re * β 1 + v.im * β Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The real differential of a complex differentiable map `ψ : ℂ → F` is `v ↦ v • ψ'`. -/
theorem fderiv_real_apply_eq_smul_deriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {ψ : ℂ → F} {u : ℂ} (hψ : DifferentiableAt ℂ ψ u) (v : ℂ) :
    fderiv ℝ ψ u v = v • deriv ψ u := by
  rw [(hψ.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp

/-- If `Im (a · conj b) > 0`, then `Im (a / b) > 0`. -/
theorem im_div_pos_of_im_mul_conj_pos {a b : ℂ} (h : 0 < (a * conj b).im) :
    0 < (a / b).im := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  have h' : (a / b).im = (a * conj b).im / Complex.normSq b := by
    rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h']
  exact div_pos h (Complex.normSq_pos.mpr hb)

/-- **Boundary charts.** At a point `z` with `‖z‖ = ε` and `E z = s`, where the equation `E` is
analytic with surjective real differential and the equation together with the squared norm has
surjective real differential, the Milnor fibre has a boundary chart. -/
theorem nonempty_milnorFibreChart_of_boundary {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hzε : ‖z‖ = ε) (hzs : euclideanEquation H z = s)
    (han : AnalyticAt ℂ (euclideanEquation H) z)
    (hsurj : Surjective (fderiv ℝ (euclideanEquation H) z))
    (hrad : Surjective (fderiv ℝ (radialPair H) z)) :
    Nonempty (MilnorFibreChart H ε s z) := by
  have hε0 : 0 ≤ ε := hzε ▸ norm_nonneg z
  obtain ⟨ℓ, ψ, U, N, hU, h0U, hN, hzN, hψ0, hψan, hψF, hψℓ, hloc, hker⟩ :=
    exists_levelParametrization (euclideanEquation H) han
      (fderiv_ne_zero_of_real_surjective han.differentiableAt hsurj)
  set k := deriv ψ 0 with hk
  set n2 : EuclideanSpace ℂ (Fin 2) → ℝ := fun x => ‖x‖ ^ 2 with hn2
  set ρ : ℂ → ℝ := fun u => ‖ψ u‖ ^ 2 with hρdef
  have hNd : ∀ w, DifferentiableAt ℝ n2 w :=
    fun w => ((contDiff_norm_sq ℝ (n := 1)).differentiable (by simp)) w
  have hψR : ∀ u ∈ U, ContDiffAt ℝ ω ψ u := fun u hu =>
    ((hψan u hu).restrictScalars (𝕜 := ℝ)).contDiffAt
  -- the differential `β` of the squared norm along the parametrization
  set β : ℂ →L[ℝ] ℝ := (fderiv ℝ n2 z).comp (fderiv ℝ ψ 0) with hβdef
  have hρd : HasFDerivAt ρ β 0 := by
    have h1 : HasFDerivAt n2 (fderiv ℝ n2 z) (ψ 0) := by
      rw [hψ0]
      exact (hNd z).hasFDerivAt
    exact h1.comp 0 ((hψan 0 h0U).differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hβ : ∀ v, β v = fderiv ℝ n2 z (v • k) := by
    intro v
    simp only [hβdef, ContinuousLinearMap.coe_comp, comp_apply]
    rw [fderiv_real_apply_eq_smul_deriv (hψan 0 h0U).differentiableAt]
  -- transversality to the sphere: `β ≠ 0`
  obtain ⟨h, hh⟩ := hrad (0, 1)
  have hradd : fderiv ℝ (radialPair H) z =
      (fderiv ℝ (euclideanEquation H) z).prod (fderiv ℝ n2 z) :=
    ((han.differentiableAt.restrictScalars ℝ).hasFDerivAt.prodMk (hNd z).hasFDerivAt).fderiv
  rw [hradd] at hh
  have hh1 : fderiv ℝ (euclideanEquation H) z h = 0 := congrArg Prod.fst hh
  have hh2 : fderiv ℝ n2 z h = 1 := congrArg Prod.snd hh
  have hhk : h = ℓ h • k := by
    apply hker
    rw [han.differentiableAt.fderiv_restrictScalars ℝ] at hh1
    exact hh1
  have hβ1 : β (ℓ h) = 1 := by rw [hβ, ← hhk, hh2]
  set μ : ℂ := -(β Complex.I : ℂ) - (β 1 : ℂ) * Complex.I with hμdef
  have hμ : μ ≠ 0 := by
    intro h0
    have hre : β Complex.I = 0 := by
      have := congrArg Complex.re h0
      simpa [hμdef] using this
    have him : β 1 = 0 := by
      have := congrArg Complex.im h0
      simpa [hμdef] using this
    have := realLinearForm_apply_eq β (ℓ h)
    rw [hβ1, hre, him] at this
    simp at this
  -- the real map `T` and its local inverse
  set T : ℂ → ℂ := fun u => ((μ * u).re : ℂ) + (ε ^ 2 - ρ u) • Complex.I with hTdef
  have hT0 : T 0 = 0 := by simp [hTdef, hρdef, hψ0, hzε]
  set A : ℂ →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (Complex.reCLM.comp (mulRealEquiv μ hμ : ℂ →L[ℝ] ℂ)) with hAdef
  have hTd : HasFDerivAt T ((mulRealEquiv μ hμ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 0 := by
    have h2 : HasFDerivAt T (A + (0 - β).smulRight Complex.I) 0 :=
      A.hasFDerivAt.add (((hasFDerivAt_const (𝕜 := ℝ) (ε ^ 2) (0 : ℂ)).sub hρd).smul_const
        Complex.I)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    apply Complex.ext
    · simp [hAdef]
    · have hAv : (A v).im = 0 := by simp [hAdef]
      have h3 : ((A + (0 - β).smulRight Complex.I) v).im = -β v := by simp [hAv]
      rw [h3, realLinearForm_apply_eq β v]
      simp [hμdef]
      ring
  have hTc : ∀ u ∈ U, ContDiffAt ℝ ω T u := by
    intro u hu
    have hρc : ContDiffAt ℝ ω ρ u := (contDiff_norm_sq ℝ).contDiffAt.comp u (hψR u hu)
    exact A.contDiff.contDiffAt.add ((contDiffAt_const.sub hρc).smul contDiffAt_const)
  obtain ⟨G, hG, h0G, hGs, hq⟩ := exists_orientedLocalInverse hμ
    (by filter_upwards [hU.mem_nhds h0U] with u hu using hTc u hu) hT0 hTd
  obtain ⟨O, hOq, hO, h0O⟩ := _root_.eventually_nhds_iff.mp hq
  have hG0 : G 0 = 0 := by rw [hG, hT0]
  have h0T : (0 : ℂ) ∈ G.target := hG0 ▸ G.map_source h0G
  have hGs0 : G.symm 0 = 0 := by
    have h := G.left_inv h0G
    rwa [hG0] at h
  -- the chart `φ = ψ ∘ G⁻¹` and its left inverse `χ`
  set W := G.target ∩ G.symm ⁻¹' U ∩ O with hWdef
  have hW : IsOpen W := (G.isOpen_inter_preimage_symm hU).inter hO
  have h0W : (0 : ℂ) ∈ W := ⟨⟨h0T, by rw [mem_preimage, hGs0]; exact h0U⟩, h0O⟩
  set φ : ℂ → EuclideanSpace ℂ (Fin 2) := fun t => ψ (G.symm t) with hφdef
  set χ : EuclideanSpace ℂ (Fin 2) → ℂ :=
    fun w => ((μ * ℓ (w - z)).re : ℂ) + (ε ^ 2 - ‖w‖ ^ 2) • Complex.I with hχdef
  have hχT : ∀ u ∈ U, χ (ψ u) = T u := by
    intro u hu
    simp only [hχdef, hTdef, hρdef, hψℓ u hu]
  have hχim : ∀ w, (χ w).im = ε ^ 2 - ‖w‖ ^ 2 := by
    intro w
    simp only [hχdef, Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
      smul_eq_mul, mul_one, zero_add]
  have hleft : ∀ t ∈ W, χ (φ t) = t := by
    intro t ht
    rw [hφdef, hχT _ ht.1.2, ← hG]
    exact G.right_inv ht.1.1
  have hχd : Differentiable ℝ χ := by
    have hA : Differentiable ℝ
        (fun w : EuclideanSpace ℂ (Fin 2) => ((μ * ℓ (w - z)).re : ℂ)) :=
      (A.comp (ℓ.restrictScalars ℝ)).differentiable.comp (differentiable_id.sub_const z)
    exact hA.add (((differentiable_const _).sub (fun w => hNd w)).smul_const Complex.I)
  have hsmooth : ContDiffOn ℝ ⊤ φ W := fun t ht =>
    ((hψR _ ht.1.2).comp t (hGs t ht.1.1)).contDiffWithinAt
  have horient : ∀ t ∈ W,
      ∃ c : ℂ, 0 < c.im ∧ fderiv ℝ φ t Complex.I = c • fderiv ℝ φ t 1 := by
    intro t ht
    have hgd : DifferentiableAt ℝ G.symm t := (hGs t ht.1.1).differentiableAt (by simp)
    have hψd : DifferentiableAt ℂ ψ (G.symm t) := (hψan _ ht.1.2).differentiableAt
    have hφd : fderiv ℝ φ t = (fderiv ℝ ψ (G.symm t)).comp (fderiv ℝ G.symm t) :=
      fderiv_fun_comp t (hψd.restrictScalars ℝ) hgd
    have hab := hOq t ht.2
    refine ⟨fderiv ℝ G.symm t Complex.I / fderiv ℝ G.symm t 1,
      im_div_pos_of_im_mul_conj_pos hab, ?_⟩
    have hb : fderiv ℝ G.symm t 1 ≠ 0 := by
      intro hb0
      rw [hb0] at hab
      simp at hab
    rw [hφd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      fderiv_real_apply_eq_smul_deriv hψd, fderiv_real_apply_eq_smul_deriv hψd,
      smul_smul, div_mul_cancel₀ _ hb]
  have hmaps : MapsTo φ (W ∩ {t | 0 ≤ t.im}) (milnorFibre H ε s) := by
    rintro t ⟨htW, ht0⟩
    have him := hχim (φ t)
    rw [hleft t htW] at him
    rw [mem_ofPred_eq] at ht0
    refine ⟨?_, (hψF _ htW.1.2).trans hzs⟩
    have h2 : ‖φ t‖ ^ 2 ≤ ε ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε0 two_ne_zero).mp h2
  have hnhds : ∀ᶠ w in 𝓝[milnorFibre H ε s] z,
      χ w ∈ W ∩ {t | 0 ≤ t.im} ∧ φ (χ w) = w := by
    refine mem_nhdsWithin.mpr ⟨N ∩ (fun w => ℓ (w - z)) ⁻¹' G.source ∩ χ ⁻¹' W, ?_, ?_, ?_⟩
    · exact (hN.inter (G.open_source.preimage
        (ℓ.continuous.comp (continuous_id.sub continuous_const)))).inter
        (hW.preimage hχd.continuous)
    · refine ⟨⟨hzN, ?_⟩, ?_⟩
      · simp [h0G]
      · have hχz : χ z = 0 := by simp [hχdef, hzε]
        rw [mem_preimage, hχz]
        exact h0W
    · rintro w ⟨⟨⟨hwN, hwG⟩, hwW⟩, hwF⟩
      obtain ⟨hu, hψu⟩ := hloc w hwN (hwF.2.trans hzs.symm)
      have hχw : χ w = G (ℓ (w - z)) := by
        conv_lhs => rw [← hψu]
        rw [hχT _ hu, hG]
      have hgχ : G.symm (χ w) = ℓ (w - z) := by rw [hχw, G.left_inv hwG]
      refine ⟨⟨hwW, ?_⟩, ?_⟩
      · rw [mem_ofPred_eq, hχim]
        have := pow_le_pow_left₀ (norm_nonneg w) hwF.1 2
        linarith
      · rw [hφdef]
        simp only
        rw [hgχ, hψu]
  have hbdry : ∀ t ∈ W ∩ {t | 0 ≤ t.im},
      φ t ∈ milnorFibreBoundary H ε s ↔ (true ∧ t.im = 0) := by
    rintro t ⟨htW, -⟩
    have him := hχim (φ t)
    rw [hleft t htW] at him
    have hF : euclideanEquation H (φ t) = s := (hψF _ htW.1.2).trans hzs
    simp only [milnorFibreBoundary, mem_ofPred_eq, hF, and_true, true_and]
    rw [← pow_left_inj₀ (norm_nonneg _) hε0 two_ne_zero]
    constructor <;> intro h2 <;> linarith
  have hφ0 : φ 0 = z := by simp [hφdef, hGs0, hψ0]
  exact ⟨MilnorFibreChart.ofLeftInverse W hW true (W ∩ {t | 0 ≤ t.im}) (by simp) φ χ
    ⟨h0W, by simp⟩ hφ0 hsmooth hχd hleft horient hmaps hnhds hbdry⟩

namespace MilnorFibreChart

variable {H : Source 2 → ℂ} {ε : ℝ} {s : ℂ} {z : EuclideanSpace ℂ (Fin 2)}

/-- The model set of a chart is contained in its domain. -/
theorem model_subset (c : MilnorFibreChart H ε s z) : c.model ⊆ c.W := by
  rw [c.model_eq]
  split_ifs
  exacts [inter_subset_left, subset_rfl]

/-- A chart is continuous on its model set. -/
theorem continuousOn (c : MilnorFibreChart H ε s z) : ContinuousOn c.φ c.model :=
  c.smooth.continuousOn.mono c.model_subset

/-- A chart restricts to a homeomorphism of its model set onto its image, which is a
neighbourhood of `z` in the Milnor fibre by `MilnorFibreChart.nhds`. -/
def homeomorph (c : MilnorFibreChart H ε s z) : c.model ≃ₜ c.φ '' c.model :=
  (Equiv.Set.imageOfInjOn c.φ c.model c.injOn).toHomeomorphOfContinuousOpen
    (c.continuousOn.domRestrict.subtype_mk _) (by
      intro O hO
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hO
      obtain ⟨V, hV, hVeq⟩ := c.isOpenMap U hU
      refine isOpen_induced_iff.mpr ⟨V, hV, ?_⟩
      ext ⟨y, hy⟩
      constructor
      · intro hyV
        have hy' : y ∈ c.φ '' (U ∩ c.model) := by
          rw [hVeq]
          obtain ⟨t, ht, rfl⟩ := hy
          exact ⟨⟨hyV, c.mapsTo ht⟩, t, ht, rfl⟩
        obtain ⟨t, ⟨htU, htM⟩, rfl⟩ := hy'
        exact ⟨⟨t, htM⟩, htU, rfl⟩
      · rintro ⟨⟨t, htM⟩, htU, hty⟩
        have hty' : c.φ t = y := congrArg Subtype.val hty
        have hmem : y ∈ c.φ '' (U ∩ c.model) := ⟨t, ⟨htU, htM⟩, hty'⟩
        rw [hVeq] at hmem
        exact hmem.1.1)

@[simp] theorem homeomorph_apply (c : MilnorFibreChart H ε s z) (t : c.model) :
    (c.homeomorph t : EuclideanSpace ℂ (Fin 2)) = c.φ t := rfl

end MilnorFibreChart

/-- **Charts of the Milnor fibre.** For every sufficiently small radius `ε` there is `δ > 0` such
that for `0 < |s| < δ` every point of the Milnor fibre `{‖z‖ ≤ ε, H z = s}` has an oriented
chart with boundary. -/
theorem exists_milnorFibreCharts (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < δ →
      ∀ z ∈ milnorFibre H ε s, Nonempty (MilnorFibreChart H ε s z) := by
  obtain ⟨ε₀, hε₀, hradii⟩ := exists_milnorFibre_radii H hH hH0 hsq
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨δ, hδ, hδs⟩ := hradii ε hε hεε₀ ε hε le_rfl
  refine ⟨δ, hδ, fun s hs0 hsδ z hz => ?_⟩
  obtain ⟨-, -, hsub, htr⟩ := hδs s hs0 hsδ
  obtain ⟨han, hsurj⟩ := hsub z hz
  rcases hz.1.lt_or_eq with hlt | heq
  · exact nonempty_milnorFibreChart_of_interior hlt hz.2 han hsurj
  · exact nonempty_milnorFibreChart_of_boundary heq hz.2 han hsurj (htr z hz heq.ge)

end OnLeConjecture.Analytic
