/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupChart
public import OnLeConjecture.Analytic.LevelOuterCentral
public import OnLeConjecture.Analytic.AllOrdersPreparation

/-!
# The central curve is unramified over a punctured disc

Let `G : ℂ² → ℂ` represent a reduced germ that is regular of order `S ≥ 1` in the first
coordinate `ζ` and lies in `𝔪^S`. This is the image equation `W` in coordinates `(ζ, h)` for a
base coordinate `h` transverse to `W`.

* `eventually_eq_zero_of_zero_of_snd_eq_zero`: near the origin, the only zero of `G` on the axis
  `{h = 0}` is the origin.
* `eventually_fibreDeriv_ne_zero`: near the origin, at every zero of `G` off the axis `{h = 0}`,
  the partial derivative of `G` in `ζ` is nonzero.

Both follow from Weierstrass preparation `G = P u` with `P` monic of degree `S` in `ζ` and
coefficients vanishing at `0`: over a nonzero base value, the `S` distinct strands of job J14 are
roots of the specialization of `P`, hence all its roots, and they are simple
(`derivative_eval_ne_zero_of_distinct_roots`).

The main result is `exists_central_unramified`, the analytic part of
`LevelProjectionSetup.OuterAdmissible` that concerns the central curve `{v = 0}`: for every
sufficiently small radius `R`, the map `H` is analytic on `B̄_R` and injective on `B_R`, the only
common zero of `v` and `h ∘ H` on `B̄_R` is the origin, and there is `δ > 0` such that the
differential of `x ↦ (v x, h (H x))` is injective at every point of the central curve in `B_R`
over `0 < |h| < δ`. This is the step "The transverse Puiseux calculation now gives
`dh₀|_{ker dv} ≠ 0`, so `d(v, h₀)` is invertible" of the subsection "A proper representative with
the correct number of sheets" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`). The proof: near such a point `x`, the central curve is a
holomorphic disc `γ` (`exists_levelCurve`, using `dv(x) ≠ 0`). The image of `γ` lies in the zero
set of `G`, which is a graph over `h` near `(ζ (H x), h (H x))` because `∂_ζ G ≠ 0` there; hence
`h ∘ H ∘ γ` is injective, by injectivity of `H`, and its derivative is nonzero
(`deriv_ne_zero_of_injOn`).
-/

@[expose] public noncomputable section

open Set Function Metric Filter Polynomial
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A nonzero polynomial of degree at most `S` with `S` distinct roots has nonzero derivative
at each of them. -/
theorem derivative_eval_ne_zero_of_distinct_roots {S : ℕ} {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ S) {f : Fin S → ℂ} (hf : Injective f) (hroots : ∀ k, Q.eval (f k) = 0)
    (j : Fin S) : (derivative Q).eval (f j) ≠ 0 := by
  classical
  have hsub : Finset.univ.image f ⊆ Q.roots.toFinset := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr (hroots k))
  have hcardim : (Finset.univ.image f).card = S := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hle1 : S ≤ Q.roots.toFinset.card := hcardim ▸ Finset.card_le_card hsub
  have hle2 : Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le _
  have hle3 : Q.roots.card ≤ S := (Polynomial.card_roots' Q).trans hdeg
  have hnodup : Q.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    omega
  have hmem : f j ∈ Q.roots := (Polynomial.mem_roots hQ).mpr (hroots j)
  have hmult : Q.rootMultiplicity (f j) = 1 := by
    rw [← Polynomial.count_roots]
    exact Multiset.count_eq_one_of_mem hnodup hmem
  have hdmult := Polynomial.derivative_rootMultiplicity_of_root (p := Q) (hroots j)
  rw [hmult] at hdmult
  have hdeg1 : 1 ≤ Q.natDegree := by
    have := Polynomial.card_roots' Q
    have h1 : 1 ≤ Q.roots.card := Multiset.card_pos_iff_exists_mem.mpr ⟨_, hmem⟩
    omega
  have hder : derivative Q ≠ 0 := by
    intro h0
    have := Polynomial.derivative_eq_zero.mp h0
    omega
  intro hzero
  have hpos := (Polynomial.rootMultiplicity_pos hder).mpr hzero
  omega

/-- **Weierstrass preparation as a function identity.** -/
theorem exists_weierstrass_function_identity (G : Source 2 → ℂ) (hG : AnalyticAt ℂ G 0)
    {S : ℕ} (hS : 0 < S) (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction G hG) S) :
    ∃ (A : ℕ → Source 1 → ℂ) (U : Source 2 → ℂ),
      (∀ k < S, A k 0 = 0) ∧
      ∀ᶠ z in 𝓝 (0 : Source 2), AnalyticAt ℂ U z ∧ U z ≠ 0 ∧
        G z = (specializedPolynomial S A (curveParameterEquiv.symm (z 1))).eval (z 0) * U z := by
  obtain ⟨P, u, hPm, hPdeg, hPcoeff, hu, hfac⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_of_pos hS hreg
  have hrep : ∀ k, ∃ (Ak : Source 1 → ℂ) (hAk : AnalyticAt ℂ Ak 0), P.coeff k = ofFunction Ak hAk :=
    fun k => Germ.exists_ofFunction (P.coeff k)
  choose A hA hAeq using hrep
  obtain ⟨Uu, hUu, huU⟩ := Germ.exists_ofFunction u
  refine ⟨A, Uu, fun k hk => ?_, ?_⟩
  · have h := hPcoeff k hk
    rw [hAeq k, mem_maximalIdeal_iff, valueRingHom_ofFunction] at h
    exact h
  subst hPdeg
  let A' : Fin P.natDegree → Source 1 → ℂ := fun i => A i
  have hA' : ∀ i : Fin P.natDegree, AnalyticAt ℂ (A' i) 0 := fun i => hA i
  have hAeq' : ∀ i : Fin P.natDegree, P.coeff i.1 = ofFunction (A' i) (hA' i) :=
    fun i => hAeq i
  have hPgerm := coe_firstCoordinatePolynomialEvaluation_monic P hPm A' hA' hAeq'
  let Pf : Source 2 → ℂ := fun z =>
    z 0 ^ P.natDegree + ∑ i : Fin P.natDegree, A' i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1
  have hgerm : ((ofFunction G hG : Germ 2) : FunctionGerm 2) =
      ((fun z => Pf z * Uu z : Source 2 → ℂ) : FunctionGerm 2) := by
    rw [hfac]
    change ((firstCoordinatePolynomialEvaluation P : Germ 2) : FunctionGerm 2) *
      ((u : Germ 2) : FunctionGerm 2) = _
    rw [hPgerm, huU]
    rfl
  have hev := Filter.Germ.coe_eq.mp hgerm
  have hU0 : Uu 0 ≠ 0 := by
    have h := valueRingHom_ne_zero_of_isUnit hu
    rwa [huU, valueRingHom_ofFunction] at h
  filter_upwards [hev, hUu.continuousAt.eventually_ne hU0, hUu.eventually_analyticAt]
    with z hz hUz hUan
  refine ⟨hUan, hUz, ?_⟩
  change G z = _ at hz
  rw [hz]
  congr 1
  have htail : Germ.hyperplaneTail 1 z = curveParameterEquiv.symm (z 1) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Germ.hyperplaneTail_apply]
  simp only [specializedPolynomial, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C]
  rw [← Fin.sum_univ_eq_sum_range (fun k => A k (curveParameterEquiv.symm (z 1)) * z 0 ^ k)]
  simp only [Pf, A', htail]

variable (G : Source 2 → ℂ) (hG : AnalyticAt ℂ G 0)

/-- Near the origin, the only zero of a transverse germ on the axis `{h = 0}` is the origin. -/
theorem eventually_eq_zero_of_zero_of_snd_eq_zero {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction G hG) S) :
    ∀ᶠ z in 𝓝 (0 : Source 2), G z = 0 → z 1 = 0 → z 0 = 0 := by
  obtain ⟨A, U, hA0, hev⟩ := exists_weierstrass_function_identity G hG hS hreg
  filter_upwards [hev] with z hzz hz hz1
  obtain ⟨-, hUz, hGz⟩ := hzz
  rw [hz, hz1, map_zero] at hGz
  have hP : (specializedPolynomial S A 0).eval (z 0) = 0 :=
    (mul_eq_zero.mp hGz.symm).resolve_right hUz
  have hspec : specializedPolynomial S A 0 = X ^ S := by
    rw [specializedPolynomial, add_eq_left]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hA0 k (Finset.mem_range.mp hk), map_zero, zero_mul]
  rw [hspec, eval_pow, eval_X] at hP
  exact pow_eq_zero_iff hS.ne' |>.mp hP

/-- Near the origin, at every zero of a transverse reduced germ off the axis `{h = 0}`, the
partial derivative in the first coordinate is nonzero. -/
theorem eventually_fibreDeriv_ne_zero (hsq : Squarefree (ofFunction G hG)) {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction G hG) S)
    (hmult : ofFunction G hG ∈ maximalIdeal 2 ^ S) :
    ∀ᶠ z in 𝓝 (0 : Source 2), G z = 0 → z 1 ≠ 0 →
      fderiv ℂ G z (Pi.single 0 1) ≠ 0 := by
  obtain ⟨A, U, -, hev⟩ := exists_weierstrass_function_identity G hG hS hreg
  obtain ⟨c, τ, w, q, r₀, y, z, hc, hq, hr₀, -, -, -, -, htend, hmain⟩ :=
    Germ.exists_transverse_fullTwist_positive_word G hG hsq hreg hmult
  -- a ball on which the function identity holds
  obtain ⟨r₁, hr₁, hr₁ball⟩ := Metric.eventually_nhds_iff_ball.mp (hev.and hG.eventually_analyticAt)
  obtain ⟨r₂, hr₂, hr₂N⟩ := htend (ball 0 r₁) (ball_mem_nhds 0 hr₁)
  set ρ : ℝ := min r₀ r₂ with hρdef
  have hρ : 0 < ρ := lt_min hr₀ hr₂
  have hball : ball (0 : Source 2) (min r₁ (ρ ^ q)) ∈ 𝓝 (0 : Source 2) :=
    ball_mem_nhds 0 (lt_min hr₁ (pow_pos hρ q))
  filter_upwards [hball] with p hp hGp hp1
  have hpr₁ : p ∈ ball (0 : Source 2) r₁ := ball_subset_ball (min_le_left _ _) hp
  obtain ⟨⟨hUan, hUp, hGid⟩, hGan⟩ := hr₁ball p hpr₁
  -- write the base value on a circle
  have hp1ρ : ‖p 1‖ < ρ ^ q := by
    have h1 : ‖p 1‖ ≤ ‖p‖ := norm_le_pi_norm p 1
    have h2 : ‖p‖ < min r₁ (ρ ^ q) := mem_ball_zero_iff.mp hp
    linarith [min_le_right r₁ (ρ ^ q)]
  set r : ℝ := ‖p 1‖ ^ ((q : ℝ)⁻¹) with hrdef
  have hnp : 0 < ‖p 1‖ := norm_pos_iff.mpr hp1
  have hrpos : 0 < r := Real.rpow_pos_of_pos hnp _
  have hrq : r ^ q = ‖p 1‖ := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul hnp.le, inv_mul_cancel₀ (by
      exact_mod_cast hq.ne'), Real.rpow_one]
  have hrρ : r < ρ := by
    by_contra hcon
    have h := pow_le_pow_left₀ hρ.le (not_lt.mp hcon) q
    rw [hrq] at h
    linarith
  set θ : ℝ := Complex.arg (p 1) with hθ
  have hcirc : circlePath (r ^ q) θ = p 1 := by
    rw [circlePath, hrq, hθ]
    exact Complex.norm_mul_exp_arg_mul_I (p 1)
  obtain ⟨-, -, -, hyzero, -⟩ := hmain r hrpos (lt_of_lt_of_le hrρ (min_le_left _ _))
  have hperY := (hmain r hrpos (lt_of_lt_of_le hrρ (min_le_left _ _))).1
  -- the strands are roots of the specialized polynomial
  set Q : Polynomial ℂ := specializedPolynomial S A (curveParameterEquiv.symm (p 1)) with hQdef
  have hQ0 : Q ≠ 0 := (specializedPolynomial_monic S A _).ne_zero
  have hQdeg : Q.natDegree ≤ S := (specializedPolynomial_natDegree S A _).le
  have hroots : ∀ k, Q.eval (y r k θ) = 0 := by
    intro k
    have hmemN := hr₂N r hrpos (lt_of_lt_of_le hrρ (min_le_right _ _)) k θ
    obtain ⟨⟨-, hUk, hGk⟩, -⟩ := hr₁ball _ hmemN
    have hzk := hyzero k θ
    rw [hGk] at hzk
    have h := (mul_eq_zero.mp hzk).resolve_right hUk
    simpa [hcirc, hQdef] using h
  have hpQ : Q.eval (p 0) = 0 := by
    rw [hGid] at hGp
    exact (mul_eq_zero.mp hGp).resolve_right hUp
  obtain ⟨j, hj⟩ := mem_range_of_eval_eq_zero hQ0 hQdeg (hperY.injective θ) hroots hpQ
  have hder : (derivative Q).eval (p 0) ≠ 0 := by
    rw [← hj]
    exact derivative_eval_ne_zero_of_distinct_roots hQ0 hQdeg (hperY.injective θ) hroots j
  -- the partial derivative in the first coordinate
  set e₀ : Source 2 := Pi.single 0 1 with he₀
  have hℓ : HasDerivAt (fun t : ℂ => p + t • e₀) e₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e₀).const_add p
  have hℓ0 : p + (0 : ℂ) • e₀ = p := by simp
  have hcont : Tendsto (fun t : ℂ => p + t • e₀) (𝓝 0) (𝓝 p) := by
    have h := hℓ.continuousAt.tendsto
    rwa [hℓ0] at h
  have hline : (fun t : ℂ => G (p + t • e₀)) =ᶠ[𝓝 0]
      fun t => Q.eval (p 0 + t) * U (p + t • e₀) := by
    filter_upwards [hcont.eventually (isOpen_ball.mem_nhds hpr₁)] with t ht
    obtain ⟨⟨-, -, hGt⟩, -⟩ := hr₁ball _ ht
    rw [hGt]
    simp [hQdef, he₀]
  have hd1 : HasDerivAt (fun t : ℂ => G (p + t • e₀)) (fderiv ℂ G p e₀) 0 :=
    hGan.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hℓ hℓ0.symm
  have hQd : HasDerivAt (fun t : ℂ => Q.eval (p 0 + t)) ((derivative Q).eval (p 0)) 0 := by
    have h : HasDerivAt (fun x => Q.eval x) ((derivative Q).eval (p 0)) (p 0 + 0) := by
      rw [add_zero]
      exact Q.hasDerivAt (p 0)
    exact h.comp_const_add (p 0) 0
  have hUd : HasDerivAt (fun t : ℂ => U (p + t • e₀)) (fderiv ℂ U p e₀) 0 :=
    hUan.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hℓ hℓ0.symm
  have hd2 := (hQd.mul hUd).congr_of_eventuallyEq hline
  have heq := hd1.unique hd2
  have hU0' : U (p + (0 : ℂ) • e₀) = U p := by rw [hℓ0]
  simp only [add_zero, hpQ, zero_mul] at heq
  rw [heq, hU0']
  exact mul_ne_zero hder hUp

/-! ### The central curve in the source -/

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace ResolutionSectionAssembly

variable (A : ResolutionSectionAssembly g hd hi)

/-- `H` is injective on the ball of radius `A.radius`. -/
theorem injOn_ball_radius : InjOn A.H (ball (0 : Source 2) A.radius) := by
  obtain ⟨L, hL⟩ := A.exists_level_at_radius A.radius A.radius_pos le_rfl
  rw [← hL]
  exact L.injective

theorem analyticAt_levelFunction : AnalyticAt ℂ (fun x => A.H x 0) 0 :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp
    A.H_analytic

/-- The germ of `v = H₀` is the reduced source equation. -/
theorem ofFunction_levelFunction :
    ofFunction (fun x => A.H x 0) A.analyticAt_levelFunction = A.sourceEquation := by
  rw [← A.sourceEquation_component]
  apply Subtype.ext
  exact (MapGerm.component_ofFunction A.H A.H_analytic 0).symm

/-- Near the origin, `dv` vanishes only at the origin. -/
theorem eventually_fderiv_levelFunction_ne_zero :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → fderiv ℂ (fun y => A.H y 0) x ≠ 0 := by
  have hsq : Squarefree (ofFunction (fun x => A.H x 0) A.analyticAt_levelFunction) := by
    rw [A.ofFunction_levelFunction]
    exact A.sourceEquation_squarefree
  exact eventually_fderiv_ne_zero_of_squarefree_of_ne _ _ (by simp [A.H_zero]) hsq

end ResolutionSectionAssembly

/-- The derivative of `x ↦ (v x, h (H x))`. -/
theorem fderiv_levelBaseMap_apply (A : ResolutionSectionAssembly g hd hi)
    (baseCoord : Source 3 →L[ℂ] ℂ) {x : Source 2} (hx : AnalyticAt ℂ A.H x) (a : Source 2) :
    fderiv ℂ (levelBaseMap A baseCoord) x a =
      (fderiv ℂ (fun y => A.H y 0) x a, fderiv ℂ (fun y => baseCoord (A.H y)) x a) := by
  have h0 : AnalyticAt ℂ (fun y => A.H y 0) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp hx
  have h1 : AnalyticAt ℂ (fun y => baseCoord (A.H y)) x := (baseCoord.analyticAt _).comp hx
  have h := h0.differentiableAt.hasFDerivAt.prodMk h1.differentiableAt.hasFDerivAt
  rw [show levelBaseMap A baseCoord = fun y => (A.H y 0, baseCoord (A.H y)) from rfl, h.fderiv]
  rfl

/-- **The central curve is unramified.** For linear coordinates `(z₀, h, ζ)` of the target
with `h` transverse to the image curve `W`, for every sufficiently small radius `R`: `H` is
analytic on `B̄_R` and injective on `B_R`, the origin is the only common zero of `v` and `h ∘ H`
on `B̄_R`, and the differential of `x ↦ (v x, h (H x))` is injective at every point of the
central curve in `B_R` off `h ∘ H = 0`. -/
theorem exists_central_unramified (A : ResolutionSectionAssembly g hd hi)
    {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y))
    (htr : ∃ u : Source 2, baseCoord (hyperplaneInclusion 2 u) = 0 ∧
      fibreCoord (hyperplaneInclusion 2 u) = 1 ∧
      vanishingOrder (lineRestriction u A.imageEquation) = (A.squareSum : ℕ∞)) :
    ∃ R₀ > 0, ∀ R, 0 < R → R ≤ R₀ →
      (∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) ∧
      InjOn A.H (ball (0 : Source 2) R) ∧
      (∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → baseCoord (A.H x) = 0 → x = 0) ∧
      ∀ x ∈ ball (0 : Source 2) R, A.H x 0 = 0 → baseCoord (A.H x) ≠ 0 →
        Injective (fderiv ℂ (levelBaseMap A baseCoord) x) := by
  obtain ⟨u, hu0, hu1, hord⟩ := htr
  set T := planeCoordsEquiv hcoord with hTdef
  obtain ⟨Wf, hWf, hWeq⟩ := Germ.exists_ofFunction A.imageEquation
  set G : Source 2 → ℂ := Wf ∘ T.symm with hGdef
  have hG : AnalyticAt ℂ G 0 := by
    have h : AnalyticAt ℂ Wf (T.symm 0) := by simpa using hWf
    exact h.comp (T.symm.analyticAt 0)
  set e := pointedEquivGermOfContinuousLinearEquiv T.symm with hedef
  have hGe : ofFunction G hG = e.forward.pullbackRingHom A.imageEquation := by
    rw [hWeq]
    change _ = Germ.compPointed (ofFunction Wf hWf)
      (PointedMapGerm.ofFunction T.symm (T.symm.analyticAt 0) (map_zero T.symm))
    rw [compPointed_ofFunction]
  have hS2 := A.two_le_squareSum
  have hS : 0 < A.squareSum := by omega
  have hsq : Squarefree (ofFunction G hG) := by
    rw [hGe]
    exact e.squarefree_pullback _ A.imageEquation_squarefree
  have hmult : ofFunction G hG ∈ maximalIdeal 2 ^ A.squareSum := by
    rw [hGe]
    exact e.forward.pullback_mem_maximalIdeal_pow A.imageEquation_mem
  have hTu : T.symm (firstCoordinateVector 1) = u := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    ext i
    fin_cases i
    · simp [hTdef, hu1, firstCoordinateVector]
    · simp [hTdef, hu0, firstCoordinateVector]
  have hreg : IsRegularInFirstCoordinateOfOrder (ofFunction G hG) A.squareSum := by
    unfold IsRegularInFirstCoordinateOfOrder
    rw [lineRestriction_ofFunction, ← hord, hWeq, lineRestriction_ofFunction]
    congr 1
    apply ofFunction_congr_fun
    funext z
    simp only [hGdef, comp_apply, lineMap_apply, map_smul, hTu]
  -- the good neighbourhood of the origin in the plane coordinates `(ζ, h)`
  have hax := eventually_eq_zero_of_zero_of_snd_eq_zero G hG hS hreg
  have hfib := eventually_fibreDeriv_ne_zero G hG hsq hS hreg hmult
  obtain ⟨rG, hrG, hrGball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hax.and hfib).and hG.eventually_analyticAt)
  -- the analyticity, injectivity and regularity radii in the source
  obtain ⟨ran, hran, hranball⟩ := Metric.eventually_nhds_iff_ball.mp
    (A.H_analytic.eventually_analyticAt.and A.eventually_fderiv_levelFunction_ne_zero)
  set rU := min ran A.radius with hrU
  have hrUpos : 0 < rU := lt_min hran A.radius_pos
  -- the zero set of the image equation near the origin
  obtain ⟨ρ', hρ', hρ'U, hzs⟩ :=
    A.imageEquation_zero_set Wf hWf hWeq (ball 0 rU) (ball_mem_nhds 0 hrUpos)
  have hTt : Tendsto T (𝓝 0) (𝓝 0) := by
    have h := T.continuous.tendsto 0
    rwa [map_zero] at h
  set Np : Set (Source 2) := {p | (Wf p = 0 ↔ ∃ x ∈ closedBall (0 : Source 2) ρ',
    A.H x = hyperplaneInclusion 2 p) ∧ T p ∈ ball (0 : Source 2) rG} with hNpdef
  have hNp : Np ∈ 𝓝 (0 : Source 2) := hzs.and (hTt.eventually (ball_mem_nhds 0 hrG))
  have hHt : Tendsto (fun x => hyperplaneTail 2 (A.H x)) (𝓝 0) (𝓝 0) := by
    have h := ((hyperplaneTail 2).continuous.tendsto (A.H 0)).comp
      A.H_analytic.continuousAt.tendsto
    rwa [A.H_zero, map_zero] at h
  obtain ⟨ε₁, hε₁, hε₁N⟩ := Metric.mem_nhds_iff.mp (hHt hNp)
  set R₀ := min (min ε₁ ρ') rU / 2 with hR₀def
  have hR₀pos : 0 < R₀ := half_pos (lt_min (lt_min hε₁ hρ') hrUpos)
  have hR₀lt : R₀ < min (min ε₁ ρ') rU := half_lt_self (lt_min (lt_min hε₁ hρ') hrUpos)
  refine ⟨R₀, hR₀pos, fun R hR hRR₀ => ?_⟩
  have hsmall : ∀ x ∈ closedBall (0 : Source 2) R,
      x ∈ ball (0 : Source 2) ε₁ ∧ x ∈ closedBall (0 : Source 2) ρ' ∧
        x ∈ ball (0 : Source 2) ran ∧ x ∈ ball (0 : Source 2) A.radius := by
    intro x hx
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    have h1 : ‖x‖ < min (min ε₁ ρ') rU := hxR.trans_lt (hRR₀.trans_lt hR₀lt)
    refine ⟨mem_ball_zero_iff.mpr (h1.trans_le ((min_le_left _ _).trans (min_le_left _ _))),
      mem_closedBall_zero_iff.mpr (h1.le.trans ((min_le_left _ _).trans (min_le_right _ _))),
      mem_ball_zero_iff.mpr (h1.trans_le ((min_le_right _ _).trans (min_le_left _ _))),
      mem_ball_zero_iff.mpr (h1.trans_le ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hinjR : InjOn A.H (ball (0 : Source 2) R) := A.injOn_ball_radius.mono fun x hx =>
    (hsmall x (ball_subset_closedBall hx)).2.2.2
  -- the plane point of a point of the central curve
  have hplane : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 →
      G (T (hyperplaneTail 2 (A.H x))) = 0 ∧ T (hyperplaneTail 2 (A.H x)) ∈ ball 0 rG ∧
      T (hyperplaneTail 2 (A.H x)) 0 = fibreCoord (A.H x) ∧
      T (hyperplaneTail 2 (A.H x)) 1 = baseCoord (A.H x) := by
    intro x hx hx0
    obtain ⟨hxε₁, hxρ', -, -⟩ := hsmall x hx
    have hpN := hε₁N hxε₁
    have hι : hyperplaneInclusion 2 (hyperplaneTail 2 (A.H x)) = A.H x :=
      hyperplaneInclusion_tail_of_zero hx0
    refine ⟨?_, hpN.2, ?_, ?_⟩
    · simp only [hGdef, comp_apply, T.symm_apply_apply]
      exact hpN.1.mpr ⟨x, hxρ', hι.symm⟩
    · rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_zero, hι]
    · rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_one, hι]
  -- injectivity of the coordinates on the central curve
  have hHeq : ∀ x ∈ ball (0 : Source 2) R, ∀ y ∈ ball (0 : Source 2) R, A.H x 0 = 0 →
      A.H y 0 = 0 → baseCoord (A.H x) = baseCoord (A.H y) →
      fibreCoord (A.H x) = fibreCoord (A.H y) → x = y := by
    intro x hx y hy hx0 hy0 hb hf
    apply hinjR hx hy
    apply hcoord
    simp only [hx0, hy0, hb, hf]
  refine ⟨fun x hx => hranball _ (hsmall x hx).2.2.1 |>.1, hinjR, ?_, ?_⟩
  · -- the only common zero is the origin
    intro x hx hx0 hxb
    obtain ⟨hGz, hzG, hz0, hz1⟩ := hplane x hx hx0
    have h := (hrGball _ hzG).1.1 hGz (by rw [hz1, hxb])
    rw [hz0] at h
    have hH0 : A.H x = A.H 0 := by
      apply hcoord
      simp only [A.H_zero, hx0, hxb, h, map_zero, Pi.zero_apply]
    have hx' := (hsmall x hx).2.2.2
    exact A.injOn_ball_radius hx' (mem_ball_self A.radius_pos) hH0
  · -- the central curve is unramified off `h ∘ H = 0`
    intro x hx hx0 hxb
    have hxc := ball_subset_closedBall hx
    have hxne : x ≠ 0 := by
      rintro rfl
      apply hxb
      rw [A.H_zero, map_zero]
    obtain ⟨hHan, hdv⟩ := hranball _ (hsmall x hxc).2.2.1
    have hdv' := hdv hxne
    have hvan : AnalyticAt ℂ (fun y => A.H y 0) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp hHan
    -- the plane point and local injectivity of `(G, h)` there
    obtain ⟨hGz, hzG, hz0, hz1⟩ := hplane x hxc hx0
    set z₀ := T (hyperplaneTail 2 (A.H x)) with hz₀
    obtain ⟨⟨-, hfibz⟩, hGanz⟩ := hrGball _ hzG
    have hdz := hfibz hGz (by rw [hz1]; exact hxb)
    set Ψ : Source 2 → ℂ × ℂ := fun z => (G z, z 1) with hΨ
    have hΨan : AnalyticAt ℂ Ψ z₀ :=
      hGanz.prod ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _)
    have hΨinj : Injective (fderiv ℂ Ψ z₀) := by
      have hfd : fderiv ℂ Ψ z₀ = (fderiv ℂ G z₀).prod
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1) :=
        (hGanz.differentiableAt.hasFDerivAt.prodMk
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).hasFDerivAt).fderiv
      rw [hfd, injective_iff_map_eq_zero]
      intro a ha
      have ha1 : a 1 = 0 := congrArg Prod.snd ha
      have hae : a = a 0 • (Pi.single 0 1 : Source 2) := by
        funext i
        fin_cases i
        · simp
        · simp [ha1]
      have ha0 := congrArg Prod.fst ha
      simp only [ContinuousLinearMap.prod_apply, Prod.fst_zero] at ha0
      rw [hae, map_smul, smul_eq_mul] at ha0
      have : a 0 = 0 := (mul_eq_zero.mp ha0).resolve_right hdz
      rw [hae, this, zero_smul]
    obtain ⟨E, -, hE⟩ := exists_hasStrictFDerivAt_equiv hΨan hΨinj
    set eΨ := hE.toOpenPartialHomeomorph Ψ with heΨ
    set V := eΨ.source with hVdef
    have hz₀V : z₀ ∈ V := hE.mem_toOpenPartialHomeomorph_source
    -- the chart of the central curve at `x`
    obtain ⟨γ, r, N, hr, -, -, hNball, hγ0, hγan, hγmem, hγinj, -, -, hker⟩ :=
      exists_levelCurve hvan hdv' (isOpen_ball.mem_nhds hx)
    -- the plane points of the chart near `0`
    have hγc : ContinuousAt γ 0 := (hγan 0 (mem_ball_self hr)).continuousAt
    have hcomp : ContinuousAt (fun t => T (hyperplaneTail 2 (A.H (γ t)))) 0 := by
      have h1 : ContinuousAt A.H (γ 0) := by rw [hγ0]; exact hHan.continuousAt
      exact (T.continuous.continuousAt.comp ((hyperplaneTail 2).continuous.continuousAt.comp
        (h1.comp hγc)))
    have hVt : ∀ᶠ t in 𝓝 (0 : ℂ), T (hyperplaneTail 2 (A.H (γ t))) ∈ V :=
      hcomp.preimage_mem_nhds (by rw [hγ0]; exact eΨ.open_source.mem_nhds hz₀V)
    obtain ⟨r', hr', hr'V⟩ := Metric.eventually_nhds_iff_ball.mp hVt
    set f : ℂ → ℂ := fun t => baseCoord (A.H (γ t)) with hfdef
    have hfan : AnalyticAt ℂ f 0 := by
      have h1 : AnalyticAt ℂ A.H (γ 0) := by rw [hγ0]; exact hHan
      exact (baseCoord.analyticAt _).comp (h1.comp (hγan 0 (mem_ball_self hr)))
    have hfinj : InjOn f (ball 0 (min r r')) := by
      intro t₁ ht₁ t₂ ht₂ h12
      have ht₁r : t₁ ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) ht₁
      have ht₂r : t₂ ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) ht₂
      obtain ⟨hγ₁N, hγ₁v⟩ := hγmem t₁ ht₁r
      obtain ⟨hγ₂N, hγ₂v⟩ := hγmem t₂ ht₂r
      have hγ₁B : γ t₁ ∈ ball (0 : Source 2) R := hNball hγ₁N
      have hγ₂B : γ t₂ ∈ ball (0 : Source 2) R := hNball hγ₂N
      rw [hx0] at hγ₁v hγ₂v
      obtain ⟨hG₁, -, h₁0, h₁1⟩ := hplane _ (ball_subset_closedBall hγ₁B) hγ₁v
      obtain ⟨hG₂, -, h₂0, h₂1⟩ := hplane _ (ball_subset_closedBall hγ₂B) hγ₂v
      have hΨeq : Ψ (T (hyperplaneTail 2 (A.H (γ t₁)))) =
          Ψ (T (hyperplaneTail 2 (A.H (γ t₂)))) := by
        simp only [hΨ, hG₁, hG₂, h₁1, h₂1]
        exact congrArg _ h12
      have hzz := eΨ.injOn (hr'V _ (ball_subset_ball (min_le_right _ _) ht₁))
        (hr'V _ (ball_subset_ball (min_le_right _ _) ht₂)) hΨeq
      have hζ : fibreCoord (A.H (γ t₁)) = fibreCoord (A.H (γ t₂)) := by
        rw [← h₁0, ← h₂0, hzz]
      exact hγinj ht₁r ht₂r (hHeq _ hγ₁B _ hγ₂B hγ₁v hγ₂v h12 hζ)
    have hfd : deriv f 0 ≠ 0 :=
      deriv_ne_zero_of_injOn hfan (ball_mem_nhds 0 (lt_min hr hr')) hfinj
    -- the differential
    have hφan : AnalyticAt ℂ (fun y => baseCoord (A.H y)) x := (baseCoord.analyticAt _).comp hHan
    have hderf : deriv f 0 = fderiv ℂ (fun y => baseCoord (A.H y)) x (deriv γ 0) := by
      have h1 : HasFDerivAt (fun y => baseCoord (A.H y))
          (fderiv ℂ (fun y => baseCoord (A.H y)) x) (γ 0) := by
        rw [hγ0]
        exact hφan.differentiableAt.hasFDerivAt
      exact (h1.comp_hasDerivAt 0 (hγan 0 (mem_ball_self hr)).differentiableAt.hasDerivAt).deriv
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [fderiv_levelBaseMap_apply A baseCoord hHan] at ha
    have hav := congrArg Prod.fst ha
    have haφ := congrArg Prod.snd ha
    simp only [Prod.fst_zero, Prod.snd_zero] at hav haφ
    obtain ⟨c, rfl⟩ := hker a hav
    rw [map_smul, smul_eq_mul, ← hderf] at haφ
    rw [(mul_eq_zero.mp haφ).resolve_right hfd, zero_smul]

end OnLeConjecture.Analytic
