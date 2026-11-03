/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelOuterAdmissible
public import OnLeConjecture.Analytic.BraidMonodromyLocalFactors
public import OnLeConjecture.Analytic.BraidMonodromyModel

/-!
# The roots of the central section over small circles

This module identifies the roots of the central level `v = 0` over small circles around `0` with
the transverse root braid of the image curve `W` (Theorem `J14:thm:transverse-germ`), for linear
coordinates `h, ζ` of the target in which `h` is transverse to `W`. It is the step "The central
branch construction supplied in the question then compares this outer word with `d_S w`" of the
subsection "Global factorization, exponent count, and transitivity" of Section 3 of the written
proof of Statement E (`statement-E-complete-proof.tex`), at a small radius.

* `planeCoordsEquiv`: the linear coordinates `p ↦ (ζ (ι p), h (ι p))` of the target plane
  `{z₀ = 0}`, an isomorphism since `(z₀, h, ζ)` are coordinates of the target.
* `exists_transverse_fullTwist_strands`: the J14 word `w` of a transverse reduced germ with its
  cycle and length identities, the J14 strands with their convergence to the origin, and a monic
  polynomial of degree `S` in the first coordinate whose roots contain the zeros of a
  representative near the origin (Weierstrass preparation).
* `mem_range_of_eval_eq_zero`: `S` distinct roots of a nonzero polynomial of degree at most `S`
  are all its roots.
* `exists_pos_le_norm_baseCoord`: away from the origin, the central curve in `B̄_R` stays away from
  `h ∘ H = 0`, when the origin is the only common zero of `v` and `h ∘ H`.
* `exists_centralRootBraid`: there is an image word `w` with the identities of `NativeRouteChoice`
  such that over arbitrarily small circles `|c| = r` the roots of the central level are labelled
  by strands represented, through closed braids, by `d_S w`.
-/

@[expose] public noncomputable section

open Set Function Filter Metric Real Polynomial
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve OnLeConjecture.Analytic.Germ

/-! ### Plane coordinates -/

/-- The linear map `p ↦ (ζ (ι p), h (ι p))` of the target plane `{z₀ = 0}`. -/
def planeCoords (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) : Source 2 →L[ℂ] Source 2 :=
  ContinuousLinearMap.pi
    (Fin.cases (fibreCoord.comp (hyperplaneInclusion 2))
      (fun _ => baseCoord.comp (hyperplaneInclusion 2)))

@[simp]
theorem planeCoords_apply_zero (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) (p : Source 2) :
    planeCoords baseCoord fibreCoord p 0 = fibreCoord (hyperplaneInclusion 2 p) := rfl

@[simp]
theorem planeCoords_apply_one (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) (p : Source 2) :
    planeCoords baseCoord fibreCoord p 1 = baseCoord (hyperplaneInclusion 2 p) := rfl

theorem hyperplaneInclusion_tail_of_zero {v : Source 3} (hv : v 0 = 0) :
    hyperplaneInclusion 2 (hyperplaneTail 2 v) = v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [hyperplaneInclusion_apply_zero, hv]
  · rw [hyperplaneInclusion_apply_succ, hyperplaneTail_apply]

theorem planeCoords_injective {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)) :
    Injective (planeCoords baseCoord fibreCoord) := by
  intro p p' hpp'
  have h0 := congrFun hpp' 0
  have h1 := congrFun hpp' 1
  rw [planeCoords_apply_zero, planeCoords_apply_zero] at h0
  rw [planeCoords_apply_one, planeCoords_apply_one] at h1
  have hι : hyperplaneInclusion 2 p = hyperplaneInclusion 2 p' := hcoord (by
    simp only [hyperplaneInclusion_apply_zero, h0, h1])
  have := congrArg (hyperplaneTail 2) hι
  simpa using this

/-- The linear coordinates `p ↦ (ζ (ι p), h (ι p))` of the target plane. -/
def planeCoordsEquiv {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)) :
    Source 2 ≃L[ℂ] Source 2 :=
  (LinearEquiv.ofInjectiveEndo (planeCoords baseCoord fibreCoord : Source 2 →ₗ[ℂ] Source 2)
    (planeCoords_injective hcoord)).toContinuousLinearEquiv

@[simp]
theorem planeCoordsEquiv_apply {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)) (p : Source 2) :
    planeCoordsEquiv hcoord p = planeCoords baseCoord fibreCoord p := rfl

/-! ### The J14 strands and the Weierstrass polynomial -/

theorem ofFunction_congr_fun {n : ℕ} {F F' : Source n → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF' : AnalyticAt ℂ F' 0) (h : F = F') : ofFunction F hF = ofFunction F' hF' := by
  subst h
  rfl

/-- **The J14 strands.** For a transverse reduced germ of multiplicity `S ≥ 1`: the J14 word `w`
with its cycle and length identities; strands `y r` of zeros of `G` over the circles
`ξ = r^q e^{iθ}`, converging to the origin as `r → 0`, pairwise distinct, and represented through
closed braids by `d_S w`; and monic polynomials `Q c` of degree `S` whose roots contain the first
coordinates of the zeros of `G` near the origin over `ξ = c`. -/
theorem exists_transverse_fullTwist_strands (G : Source 2 → ℂ) (hG : AnalyticAt ℂ G 0)
    (hsq : Squarefree (ofFunction G hG)) {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction G hG) S)
    (hmult : ofFunction G hG ∈ maximalIdeal 2 ^ S) :
    ∃ (w : PositiveAdjacentWord S) (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin S → ℝ → ℂ),
      (PositiveAdjacentWord.toSigned w).cycleCount = irreducibleBranchCount (ofFunction G hG) ∧
      w.length + S ^ 2 + irreducibleBranchCount (ofFunction G hG) =
        2 * deltaInvariant (ofFunction G hG) + 2 * S ∧
      0 < q ∧ 0 < r₀ ∧
      (∀ N ∈ 𝓝 (0 : Source 2), ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r, 0 < r → r < r₁ → ∀ k θ,
        ![y r k θ, circlePath (r ^ q) θ] ∈ N) ∧
      (∀ r, 0 < r → r < r₀ → (∀ k, Continuous (y r k)) ∧ (∀ θ, Injective fun k => y r k θ) ∧
        (∀ k θ, G ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
        ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * π) (fullTwistWord S ++ w)) ∧
      ∃ Q : ℂ → Polynomial ℂ, (∀ c, Q c ≠ 0 ∧ (Q c).natDegree = S) ∧
        ∀ᶠ z in 𝓝 (0 : Source 2), G z = 0 → (Q (z 1)).eval (z 0) = 0 := by
  have hf : ofFunction G hG ∈ maximalIdeal 2 := by
    have h := Ideal.pow_le_pow_right (I := maximalIdeal 2)
      (Nat.one_le_iff_ne_zero.mpr hS.ne') hmult
    simpa using h
  obtain ⟨P, u, A, hPm, hPdeg, -, hu, hfac, hA, himp⟩ :=
    exists_weierstrass_data_fullTwistWord_append_length (ofFunction G hG) hf hsq hS hreg
  obtain ⟨c, τ, w, q, r₀, y, z, hc, hq, hr₀, -, hcw, -, -, htend, hmain⟩ :=
    Germ.exists_transverse_fullTwist_positive_word G hG hsq hreg hmult
  have hW := eventually_specializedPolynomial_eval_eq_zero G hG P u hPm hPdeg hu hfac A
    (fun k _ => hA k)
  have hword : ∀ r₀' : ℝ, 0 < r₀' → ∃ r : ℝ, 0 < r ∧ r < r₀' ∧
      ∃ (b : ℝ) (y' : Fin S → ℝ → ℂ),
        (∀ k, ContinuousOn (y' k) (Icc b (b + 2 * π))) ∧
        (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial S A
          (curveParameterEquiv.symm (circlePath r θ))).eval (y' k θ) = 0) ∧
        (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y' k θ) ∧
        ∃ (c : ℂ), c ≠ 0 ∧ ∃ D : SheetCrossingData S y' b c,
          SignedAdjacentWord.exponentSum
            (PositiveAdjacentWord.toSigned (fullTwistWord S ++ w)) = D.signedCount := by
    intro r₀' hr₀'
    obtain ⟨r₁, hr₁, hr₁spec⟩ := htend _ hW
    set ρ := min (min r₀ r₁) (min 1 r₀') / 2 with hρdef
    have hm : 0 < min (min r₀ r₁) (min 1 r₀') := lt_min (lt_min hr₀ hr₁) (lt_min one_pos hr₀')
    have hρpos : 0 < ρ := half_pos hm
    have hρlt : ρ < min (min r₀ r₁) (min 1 r₀') := half_lt_self hm
    have hρr₀ : ρ < r₀ := lt_of_lt_of_le hρlt ((min_le_left _ _).trans (min_le_left _ _))
    have hρr₁ : ρ < r₁ := lt_of_lt_of_le hρlt ((min_le_left _ _).trans (min_le_right _ _))
    have hρ1 : ρ < 1 := lt_of_lt_of_le hρlt ((min_le_right _ _).trans (min_le_left _ _))
    have hρr₀' : ρ < r₀' := lt_of_lt_of_le hρlt ((min_le_right _ _).trans (min_le_right _ _))
    have hrpos : 0 < ρ ^ q := pow_pos hρpos q
    have hrlt : ρ ^ q < r₀' :=
      lt_of_le_of_lt (pow_le_of_le_one hρpos.le hρ1.le hq.ne') hρr₀'
    obtain ⟨hperY, -, -, hzero, -, -, -, hfinY, hcross⟩ := hmain ρ hρpos hρr₀
    obtain ⟨b, hbmem, hb⟩ := (Set.Ioo_infinite (zero_lt_one' ℝ)).exists_notMem_finset
      (hfinY 0 (2 * π)).toFinset
    have hbreg : ∀ k l, k ≠ l → (c * y ρ k b).re ≠ (c * y ρ l b).re := by
      intro k l hkl heq
      apply hb
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨hbmem.1.le, by linarith [hbmem.2, Real.two_le_pi]⟩, k, l, hkl, heq⟩
    obtain ⟨D, -, hD⟩ := hcross b hbreg
    refine ⟨ρ ^ q, hrpos, hrlt, b, y ρ, fun k => (hperY.continuous k).continuousOn, ?_,
      fun θ _ => hperY.injective θ, c, hc, D, hD.symm⟩
    intro θ _ k
    have h := hr₁spec ρ hρpos hρr₁ k θ (hzero k θ)
    simpa using h
  obtain ⟨-, hlen⟩ := himp w hword
  refine ⟨w, q, r₀, y, hcw, hlen, hq, hr₀, htend, fun r hr hrr => ?_,
    fun c => specializedPolynomial S A (curveParameterEquiv.symm c),
    fun c => ⟨(specializedPolynomial_monic _ _ _).ne_zero, specializedPolynomial_natDegree _ _ _⟩,
    ?_⟩
  · obtain ⟨hperY, -, -, hzero, -, -, hrep, -, -⟩ := hmain r hr hrr
    exact ⟨hperY.continuous, hperY.injective, hzero, hrep⟩
  · filter_upwards [hW] with z hz hGz
    exact hz hGz

/-- `S` distinct roots of a nonzero polynomial of degree at most `S` are all its roots. -/
theorem mem_range_of_eval_eq_zero {S : ℕ} {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ S) {f : Fin S → ℂ} (hf : Injective f) (hroots : ∀ k, Q.eval (f k) = 0)
    {a : ℂ} (ha : Q.eval a = 0) : a ∈ range f := by
  classical
  have hsub : Finset.univ.image f ⊆ Q.roots.toFinset := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr (hroots k))
  have hcard : Q.roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' Q).trans hdeg)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have ha' : a ∈ Q.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr ha)
  rw [← heq] at ha'
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp ha'
  exact ⟨k, hk⟩

/-! ### The central curve away from the origin -/

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- **The central curve away from the origin.** If the origin is the only common zero of `v` and
`h ∘ H` on `B̄_R`, then for every `ε > 0` the values of `|h ∘ H|` on the points of the central curve
in `B̄_R` with `|x| ≥ ε` are bounded below by a positive number. -/
theorem exists_pos_le_norm_baseCoord (A : ResolutionSectionAssembly g hd hi) {R ε : ℝ}
    (hε : 0 < ε) {baseCoord : Source 3 →L[ℂ] ℂ} (hHc : ContinuousOn A.H (closedBall 0 R))
    (hiso : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → baseCoord (A.H x) = 0 → x = 0) :
    ∃ m > 0, ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → ε ≤ ‖x‖ →
      m ≤ ‖baseCoord (A.H x)‖ := by
  set K : Set (Source 2) :=
    (closedBall (0 : Source 2) R ∩ (fun x => A.H x 0) ⁻¹' {0}) ∩ {x | ε ≤ ‖x‖} with hK
  have hv : ContinuousOn (fun x => A.H x 0) (closedBall (0 : Source 2) R) :=
    (continuous_apply 0).comp_continuousOn hHc
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : Source 2) R).of_isClosed_subset
      ((hv.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton).inter
        (isClosed_le continuous_const continuous_norm))
      (inter_subset_left.trans inter_subset_left)
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · refine ⟨1, one_pos, fun x hx hx0 hxε => ?_⟩
    have : x ∈ K := ⟨⟨hx, hx0⟩, hxε⟩
    rw [hKe] at this
    exact this.elim
  have hf : ContinuousOn (fun x => ‖baseCoord (A.H x)‖) K :=
    (continuous_norm.comp baseCoord.continuous).comp_continuousOn
      (hHc.mono (inter_subset_left.trans inter_subset_left))
  obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hKn hf
  refine ⟨‖baseCoord (A.H x₀)‖, ?_, fun x hx hx0 hxε => hmin ⟨⟨hx, hx0⟩, hxε⟩⟩
  refine norm_pos_iff.mpr fun h0 => ?_
  have h00 := hiso x₀ hx₀.1.1 hx₀.1.2 h0
  have : ε ≤ ‖x₀‖ := hx₀.2
  rw [h00, norm_zero] at this
  exact absurd this (not_le.mpr hε)

/-! ### The central root braid -/

/-- **The central root braid over small circles.** For linear coordinates `(z₀, h, ζ)` of the
target in which `h` is transverse to the image curve, with `H` continuous on `B̄_R` and the origin
the only common zero of `v` and `h ∘ H` on `B̄_R`, there is a positive word `w` with the image word
identities such that over arbitrarily small circles `|c| = r` the roots of the central level
`v = 0` in `B_R` are labelled by strands represented through closed braids by `d_S w`. -/
theorem exists_centralRootBraid (A : ResolutionSectionAssembly g hd hi) {R : ℝ} (hR : 0 < R)
    {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y))
    (hHc : ContinuousOn A.H (closedBall 0 R))
    (htr : ∃ u : Source 2, baseCoord (hyperplaneInclusion 2 u) = 0 ∧
      fibreCoord (hyperplaneInclusion 2 u) = 1 ∧
      vanishingOrder (lineRestriction u A.imageEquation) = (A.squareSum : ℕ∞))
    (hiso : ∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → baseCoord (A.H x) = 0 → x = 0) :
    ∃ w : PositiveAdjacentWord A.squareSum,
      w.toSigned.cycleCount = irreducibleBranchCount A.imageEquation ∧
      w.length + A.squareSum * (A.squareSum - 1) + irreducibleBranchCount A.imageEquation =
        2 * deltaInvariant A.imageEquation + A.squareSum ∧
      ∀ ε > 0, ∃ r, 0 < r ∧ r < ε ∧ ∃ y : Fin A.squareSum → ℝ → ℂ,
        IsRootLabellingOn (levelRootsAt A R baseCoord fibreCoord 0) (circlePath r) univ y ∧
        ∀ b : ℝ, IsRepresentedByPositiveWord y b (b + 2 * π) (fullTwistWord A.squareSum ++ w) := by
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
  obtain ⟨w, q, r₀, y, hcyc, hlen, hq, hr₀, htend, hstr, Q, hQ, hQz⟩ :=
    exists_transverse_fullTwist_strands G hG hsq (by omega) hreg hmult
  have hb : irreducibleBranchCount (ofFunction G hG) = irreducibleBranchCount A.imageEquation := by
    rw [hGe, ← irreducibleBranchCount_pullback]
  have hf2 : A.imageEquation ∈ maximalIdeal 2 ^ 2 :=
    Ideal.pow_le_pow_right hS2 A.imageEquation_mem
  have hδ : deltaInvariant (ofFunction G hG) = deltaInvariant A.imageEquation := by
    rw [hGe, deltaInvariant_pullback e A.imageEquation_squarefree hf2]
  refine ⟨w, hcyc.trans hb, ?_, ?_⟩
  · rw [hb, hδ] at hlen
    have hsq' : A.squareSum * (A.squareSum - 1) + A.squareSum = A.squareSum ^ 2 := by
      obtain ⟨m, hm⟩ : ∃ m, A.squareSum = m + 1 := ⟨A.squareSum - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]; ring
    omega
  intro ε hε
  -- the zero set of the image equation near the origin
  obtain ⟨ρ', hρ', hρ'R, hzs⟩ :=
    A.imageEquation_zero_set Wf hWf hWeq (ball 0 R) (ball_mem_nhds 0 hR)
  have hTt : Tendsto T (𝓝 0) (𝓝 0) := by
    have h := T.continuous.tendsto 0
    rwa [map_zero] at h
  have hTst : Tendsto T.symm (𝓝 0) (𝓝 0) := by
    have h := T.symm.continuous.tendsto 0
    rwa [map_zero] at h
  set N : Set (Source 2) := {p | (Wf p = 0 ↔ ∃ x ∈ closedBall (0 : Source 2) ρ',
    A.H x = hyperplaneInclusion 2 p) ∧ (G (T p) = 0 → (Q (T p 1)).eval (T p 0) = 0)} with hNdef
  have hN : N ∈ 𝓝 (0 : Source 2) := hzs.and (hTt.eventually hQz)
  -- the source points near the origin
  have hHt : Tendsto (fun x => hyperplaneTail 2 (A.H x)) (𝓝 0) (𝓝 0) := by
    have h := ((hyperplaneTail 2).continuous.tendsto (A.H 0)).comp
      A.H_analytic.continuousAt.tendsto
    rwa [A.H_zero, map_zero] at h
  obtain ⟨ε₁, hε₁, hε₁N⟩ := Metric.mem_nhds_iff.mp (hHt hN)
  set ε₀ := min ε₁ ρ' with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε₁ hρ'
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_norm_baseCoord A hε₀pos hHc hiso
  -- the J14 strands near the origin
  obtain ⟨r₁, hr₁, hr₁N⟩ := htend (T.symm ⁻¹' N) (hTst hN)
  set ρ := min (min r₀ r₁) (min 1 (min m ε)) / 2 with hρdef
  have hmin : 0 < min (min r₀ r₁) (min 1 (min m ε)) :=
    lt_min (lt_min hr₀ hr₁) (lt_min one_pos (lt_min hm hε))
  have hρpos : 0 < ρ := half_pos hmin
  have hρlt : ρ < min (min r₀ r₁) (min 1 (min m ε)) := half_lt_self hmin
  have hρr₀ : ρ < r₀ := lt_of_lt_of_le hρlt ((min_le_left _ _).trans (min_le_left _ _))
  have hρr₁ : ρ < r₁ := lt_of_lt_of_le hρlt ((min_le_left _ _).trans (min_le_right _ _))
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρlt ((min_le_right _ _).trans (min_le_left _ _))
  have hρm : ρ < m := lt_of_lt_of_le hρlt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρε : ρ < ε := lt_of_lt_of_le hρlt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpow : ρ ^ q ≤ ρ := pow_le_of_le_one hρpos.le hρ1.le hq.ne'
  have hrpos : 0 < ρ ^ q := pow_pos hρpos q
  obtain ⟨hyc, hyinj, hyzero, hyrep⟩ := hstr ρ hρpos hρr₀
  refine ⟨ρ ^ q, hrpos, hpow.trans_lt hρε, y ρ, ⟨fun k => (hyc k).continuousOn,
    fun θ _ => hyinj θ, fun θ _ => ?_⟩, hyrep⟩
  -- the strands are roots of the central level, and roots of `Q`
  have hstrand : ∀ k, ∃ x ∈ ball (0 : Source 2) R, A.H x 0 = 0 ∧
      baseCoord (A.H x) = circlePath (ρ ^ q) θ ∧ fibreCoord (A.H x) = y ρ k θ := by
    intro k
    set z : Source 2 := ![y ρ k θ, circlePath (ρ ^ q) θ] with hz
    have hzN : T.symm z ∈ N := hr₁N ρ hρpos hρr₁ k θ
    have hWz : Wf (T.symm z) = 0 := hyzero k θ
    obtain ⟨x, hx, hHx⟩ := hzN.1.mp hWz
    have hTz : T (T.symm z) = z := T.apply_symm_apply z
    refine ⟨x, hρ'R hx, ?_, ?_, ?_⟩
    · rw [hHx, hyperplaneInclusion_apply_zero]
    · have h1 := congrFun hTz 1
      rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_one] at h1
      rw [hHx, h1]
      rfl
    · have h0 := congrFun hTz 0
      rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_zero] at h0
      rw [hHx, h0]
      rfl
  have hroot : ∀ k, (Q (circlePath (ρ ^ q) θ)).eval (y ρ k θ) = 0 := by
    intro k
    set z : Source 2 := ![y ρ k θ, circlePath (ρ ^ q) θ] with hz
    have hzN : T.symm z ∈ N := hr₁N ρ hρpos hρr₁ k θ
    have hTz : T (T.symm z) = z := T.apply_symm_apply z
    have h := hzN.2 (by rw [hTz]; exact hyzero k θ)
    rw [hTz] at h
    simpa [hz] using h
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx, hx0, hxc, hxy⟩ := hstrand k
    exact ⟨x, ⟨hx, hx0, hxc⟩, hxy⟩
  · rintro ⟨x, ⟨hxb, hx0, hxc⟩, rfl⟩
    have hxsmall : ‖x‖ < ε₀ := by
      by_contra hcon
      have h := hmK x (ball_subset_closedBall hxb) hx0 (not_lt.mp hcon)
      rw [hxc, norm_circlePath hrpos.le] at h
      linarith
    set p := hyperplaneTail 2 (A.H x) with hp
    have hpN : p ∈ N := hε₁N (mem_ball_zero_iff.mpr (hxsmall.trans_le (min_le_left _ _)))
    have hι : hyperplaneInclusion 2 p = A.H x := hyperplaneInclusion_tail_of_zero hx0
    have hWp : Wf p = 0 := hpN.1.mpr ⟨x, mem_closedBall_zero_iff.mpr
      (hxsmall.le.trans (min_le_right _ _)), hι.symm⟩
    have hGp : G (T p) = 0 := by
      simp only [hGdef, comp_apply, T.symm_apply_apply]
      exact hWp
    have h := hpN.2 hGp
    have hT0 : T p 0 = fibreCoord (A.H x) := by
      rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_zero, hι]
    have hT1 : T p 1 = circlePath (ρ ^ q) θ := by
      rw [hTdef, planeCoordsEquiv_apply, planeCoords_apply_one, hι, hxc]
    rw [hT0, hT1] at h
    exact mem_range_of_eval_eq_zero (hQ _).1 (hQ _).2.le (hyinj θ) hroot h

end OnLeConjecture.Analytic
