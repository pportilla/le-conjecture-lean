/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveFullTwistGerm
public import OnLeConjecture.Analytic.PlaneCurveBraidLengthReduced
public import OnLeConjecture.Analytic.PlaneIsolatedFiberElimination

/-!
# The full-twist factorization of the root braid of a transverse reduced germ

This module proves the word-level content of Theorem `J14:thm:transverse-germ` of the written
proof (records M405, M406 and M1153 of the dependency audit), under the corrected hypotheses
of the written proof: the germ `f = ofFunction H hH` is reduced, regular of order `S` in the
first coordinate `ζ`, and lies in `𝔪^S`. Together the last two hypotheses say that `f` has
multiplicity exactly `S` and that the projection to the second coordinate `ξ` is transverse,
`f_S(1, 0) ≠ 0`. The displayed API of M405, with regularity alone, is false (Proposition
`J14:prop:false`: `ζ² - ξ`), so the hypothesis `hmult` is an intended deviation.

`Germ.exists_transverse_fullTwist_positive_word`: there are a fibre rotation `c ≠ 0`, a
permutation `τ` with `irreducibleBranchCount f` cycles, and a positive word `w` (the positive
event word of the strict-transform sheets read through `Re (c ·)` at a reference radius) such
that, for every sufficiently small source radius `r`, the closed braid `y` of zeros of `H` over
the base circle `ξ = r^q e^{iθ}` and its strict transform `z = y / ξ` satisfy:

* `y` and `z` are periodic closed braids with monodromy `τ`;
* every projected crossing of `c z` is positive;
* `z` is represented, through closed braids, by `w`, and `y` by `fullTwistWord S ++ w`;
* `w` and `fullTwistWord S ++ w` have `irreducibleBranchCount f` permutation cycles;
* at every regular base angle, the projected crossing data of `y` (J15's `SheetCrossingData`)
  have only positive crossings and signed crossing count equal to the length of
  `fullTwistWord S ++ w`.

`Germ.exists_fullTwist_rootBraid_hword` derives from this exactly the hypothesis `hword` of the
J15 theorem `fullTwistWord_append_length_of_rootBraid`, for any Weierstrass data of `f`, and
`Germ.exists_transverse_fullTwist_word_length` combines both into the unconditional length
identities `length (fullTwistWord S ++ w) + 1 = μ(f) + S` and
`length w + S² + b = 2 δ(f) + 2 S`.
-/

@[expose] public noncomputable section

open Set Filter Metric Real Polynomial
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve KnotTheory

/-- **Full-twist factorization of the root braid of a transverse reduced germ**
(Theorem `J14:thm:transverse-germ`, word level). For every source radius `r < r₀`, `y r` is a
closed braid of zeros of `H` over the base circle `ξ = r^q e^{iθ}`, and `z r = y r / ξ` is its
strict transform. The word `w` is the positive event word of `c z r₁` at a reference radius. -/
theorem Germ.exists_transverse_fullTwist_positive_word (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hsq : Squarefree (ofFunction H hH)) {S : ℕ}
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S)
    (hmult : ofFunction H hH ∈ maximalIdeal 2 ^ S) :
    ∃ (c : ℂ) (τ : Equiv.Perm (Fin S)) (w : PositiveAdjacentWord S) (q : ℕ) (r₀ : ℝ)
      (y z : ℝ → Fin S → ℝ → ℂ),
      c ≠ 0 ∧ 0 < q ∧ 0 < r₀ ∧
      permCycleCount τ = irreducibleBranchCount (ofFunction H hH) ∧
      (PositiveAdjacentWord.toSigned w).cycleCount = irreducibleBranchCount (ofFunction H hH) ∧
      (PositiveAdjacentWord.toSigned (fullTwistWord S ++ w)).cycleCount =
        irreducibleBranchCount (ofFunction H hH) ∧
      (∃ (r₁ b₁ : ℝ) (E : Finset ℝ) (N : ℕ) (event left right : Fin N → ℝ)
          (σ : Fin (N + 1) → Equiv.Perm (Fin S)) (ww : Fin N → PositiveAdjacentWord S),
          0 < r₁ ∧ r₁ < r₀ ∧ w = (List.ofFn ww).flatten ∧
          (∀ t, t ∈ E ↔ t ∈ Icc b₁ (b₁ + 2 * π) ∧
            ∃ k l : Fin S, k ≠ l ∧ (c * z r₁ k t).re = (c * z r₁ l t).re) ∧
          b₁ ∉ E ∧ b₁ + 2 * π ∉ E ∧ List.ofFn event = E.sort (· ≤ ·) ∧
          (∀ j : Fin N, b₁ < left j ∧ left j < event j ∧ event j < right j ∧
            right j < b₁ + 2 * π ∧
            (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
            IsPositiveBraidEventWord (fun k θ => c * z r₁ k θ) (event j) (σ j.castSucc)
              (σ j.succ) (ww j)) ∧
          (σ (Fin.last N)).trans τ = σ 0) ∧
      (∀ N ∈ 𝓝 (0 : Source 2), ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r, 0 < r → r < r₁ → ∀ k θ,
        ![y r k θ, circlePath (r ^ q) θ] ∈ N) ∧
      ∀ r, 0 < r → r < r₀ →
        IsPeriodicStrandBraid (y r) τ ∧ IsPeriodicStrandBraid (z r) τ ∧
        (∀ k θ, y r k θ = circlePath (r ^ q) θ * z r k θ) ∧
        (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
        (∀ θ k l, k ≠ l → (c * z r k θ).re = (c * z r l θ).re →
          0 < -deriv (fun t => (c * z r k t - c * z r l t).re) θ *
            (c * z r k θ - c * z r l θ).im) ∧
        (∀ b : ℝ, IsRepresentedByPositiveWord (z r) b (b + 2 * π) w) ∧
        (∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * π) (fullTwistWord S ++ w)) ∧
        (∀ u v : ℝ, {θ | θ ∈ Icc u v ∧
          ∃ k l, k ≠ l ∧ (c * y r k θ).re = (c * y r l θ).re}.Finite) ∧
        ∀ b : ℝ, (∀ k l, k ≠ l → (c * y r k b).re ≠ (c * y r l b).re) →
          ∃ D : SheetCrossingData S (y r) b c,
            (∀ k l, k < l → ∀ θ ∈ D.crossings k l, D.crossingSign k l θ = 1) ∧
            D.signedCount = SignedAdjacentWord.exponentSum
              (PositiveAdjacentWord.toSigned (fullTwistWord S ++ w)) := by
  obtain ⟨D, hcyc, hzero, htend⟩ := exists_transverse_multiSheetData H hH hsq hreg hmult
  obtain ⟨c, hc, hproj⟩ := D.exists_projection
  obtain ⟨r₀, hr₀, hr₀R, hper, hfin, hall⟩ := D.exists_fullTwist_factorization hc hproj
  have hr₁ : 0 < r₀ / 2 := half_pos hr₀
  have hr₁r : r₀ / 2 < r₀ := half_lt_self hr₀
  obtain ⟨b₁, E, N, event, left, right, σ, ww, hE, hbE, hdE, -, henum, -, hblocks, -, hσ, -,
    hrep, hcycw, hcycd, hcross⟩ := hall (r₀ / 2) hr₁ hr₁r
  have hKeq : ∀ r k θ, D.strict c r k θ = c * D.strict 1 r k θ :=
    fun r k θ => MultiSheetData.multiSheetStrands_eq_mul c D.U D.q r k θ
  have hYeq : ∀ r k θ, D.root c r k θ = c * D.root 1 r k θ :=
    fun r k θ => MultiSheetData.multiSheetStrands_eq_mul c D.rootSheet D.q r k θ
  have hfunK : ∀ r, (fun k θ => c * D.strict 1 r k θ) = D.strict c r :=
    fun r => funext fun k => funext fun θ => (hKeq r k θ).symm
  refine ⟨c, D.τ, (List.ofFn ww).flatten, D.q, r₀, fun r => D.root 1 r, fun r => D.strict 1 r,
    hc, D.q_pos, hr₀, hcyc, hcycw.trans hcyc, hcycd.trans hcyc, ?_, htend, ?_⟩
  · refine ⟨r₀ / 2, b₁, E, N, event, left, right, σ, ww, hr₁, hr₁r, rfl, fun t => ?_, hbE, hdE,
      henum, fun j => ?_, hσ⟩
    · rw [hE t]
      simp only [hKeq]
    · obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := hblocks j
      exact ⟨h1, h2, h3, h4, h7, by rw [hfunK]; exact h8⟩
  · intro r hr hrr
    obtain ⟨hperK, hperY, hpos⟩ := hper r hr hrr
    have hrR : r < D.R := lt_of_lt_of_le hrr hr₀R
    have hperZ : IsPeriodicStrandBraid (D.strict 1 r) D.τ :=
      ⟨fun k => multiSheetStrands_continuous D.analytic D.q hr.le hrR k,
        fun t k l hkl => hperK.injective t (by
          change D.strict c r k t = D.strict c r l t
          rw [hKeq, hKeq]
          exact congrArg _ hkl),
        fun k t => D.strict_add_two_pi 1 hr.le hrR k t⟩
    refine ⟨hperY, hperZ, fun k θ => D.root_eq 1 r k θ, fun k θ => hzero r hr hrR k θ,
      fun θ k l hkl heq => ?_, fun b => ?_, fun b => (hrep r hr hrr b).2, fun u v => ?_,
      fun b hb => ?_⟩
    · have h := hpos θ k l hkl (by rw [hKeq, hKeq]; exact heq)
      simpa only [← hfunK] using h
    · have h := (hrep r hr hrr b).1.const_mul (hperK.isClosedStrandBraid b) (inv_ne_zero hc)
      refine h.congr_fun (funext fun k => funext fun θ => ?_)
      rw [hKeq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · simpa only [hYeq] using (hfin r hr hrr u v).2
    · exact hcross r hr hrr b (fun k l hkl => by rw [hYeq, hYeq]; exact hb k l hkl)

/-! ### The root braid and the Weierstrass polynomial -/

/-- Near the origin, every zero of `H` is a root of every Weierstrass polynomial of its germ,
specialized at the second coordinate. -/
theorem eventually_specializedPolynomial_eval_eq_zero (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) {S : ℕ} (P : Polynomial (Germ 1)) (u : Germ 2) (hPm : P.Monic)
    (hPdeg : P.natDegree = S) (hu : IsUnit u)
    (hfac : ofFunction H hH = firstCoordinatePolynomialEvaluation P * u)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < S, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    ∀ᶠ z in 𝓝 (0 : Source 2), H z = 0 →
      (specializedPolynomial S A (curveParameterEquiv.symm (z 1))).eval (z 0) = 0 := by
  subst hPdeg
  let A' : Fin P.natDegree → Source 1 → ℂ := fun i => A i
  have hA' : ∀ i : Fin P.natDegree, AnalyticAt ℂ (A' i) 0 := fun i => (hA i i.isLt).choose
  have hAeq : ∀ i : Fin P.natDegree, P.coeff i.1 = ofFunction (A' i) (hA' i) :=
    fun i => (hA i i.isLt).choose_spec
  have hPgerm := coe_firstCoordinatePolynomialEvaluation_monic P hPm A' hA' hAeq
  obtain ⟨Uu, hUu, huU⟩ := exists_ofFunction u
  let Pf : Source 2 → ℂ := fun z =>
    z 0 ^ P.natDegree + ∑ i : Fin P.natDegree, A' i (Germ.hyperplaneTail 1 z) * z 0 ^ i.1
  have hgerm : ((ofFunction H hH : Germ 2) : FunctionGerm 2) =
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
  filter_upwards [hev, hUu.continuousAt.eventually_ne hU0] with z hz hUz hH0
  rw [hH0] at hz
  have hPf : Pf z = 0 := (mul_eq_zero.mp hz.symm).resolve_right hUz
  have htail : Germ.hyperplaneTail 1 z = curveParameterEquiv.symm (z 1) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Germ.hyperplaneTail_apply]
  simp only [specializedPolynomial, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C]
  rw [← Fin.sum_univ_eq_sum_range (fun k => A k (curveParameterEquiv.symm (z 1)) * z 0 ^ k)]
  rw [← hPf]
  simp only [Pf, A', htail]

/-- **The hypothesis `hword` of J15(b) for the J14 word.** For any Weierstrass data
`f = P u` of a transverse reduced germ, with analytic representatives `A` of the lower
coefficients of `P`, the word `w` of `Germ.exists_transverse_fullTwist_positive_word` satisfies
the hypothesis `hword` of `fullTwistWord_append_length_of_rootBraid`: over arbitrarily small
circles there are a labelled root family of `P`, a projection direction and crossing data whose
signed crossing count is the exponent sum of `fullTwistWord S ++ w`. The same word represents
the root braid of `f`, and its number of permutation cycles is the number of branches. -/
theorem Germ.exists_fullTwist_rootBraid_hword (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) {S : ℕ}
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S)
    (hmult : ofFunction H hH ∈ maximalIdeal 2 ^ S)
    (P : Polynomial (Germ 1)) (u : Germ 2) (hPm : P.Monic) (hPdeg : P.natDegree = S)
    (hu : IsUnit u) (hfac : ofFunction H hH = firstCoordinatePolynomialEvaluation P * u)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < S, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    ∃ w : PositiveAdjacentWord S,
      (PositiveAdjacentWord.toSigned w).cycleCount = irreducibleBranchCount (ofFunction H hH) ∧
      (∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin S → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * π) (fullTwistWord S ++ w)) ∧
      ∀ r₀ : ℝ, 0 < r₀ → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
        ∃ (b : ℝ) (y : Fin S → ℝ → ℂ),
          (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) ∧
          (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial S A
            (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) ∧
          (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) ∧
          ∃ (c : ℂ), c ≠ 0 ∧ ∃ D : SheetCrossingData S y b c,
            SignedAdjacentWord.exponentSum
              (PositiveAdjacentWord.toSigned (fullTwistWord S ++ w)) = D.signedCount := by
  obtain ⟨c, τ, w, q, r₀, y, z, hc, hq, hr₀, -, hcw, -, -, htend, hmain⟩ :=
    Germ.exists_transverse_fullTwist_positive_word H hH hsq hreg hmult
  have hW := eventually_specializedPolynomial_eval_eq_zero H hH P u hPm hPdeg hu hfac A hA
  refine ⟨w, hcw, ⟨q, r₀, y, hq, hr₀, fun r hr hrr =>
    ⟨(hmain r hr hrr).2.2.2.1, (hmain r hr hrr).2.2.2.2.2.2.1⟩⟩, ?_⟩
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

/-- **Length of the J14 word** (J15(b) made unconditional). For a transverse reduced germ of
multiplicity `S ≥ 1`, the positive word `w` of the full-twist factorization satisfies
`length (fullTwistWord S ++ w) + 1 = μ(f) + S` and `length w + S² + b = 2 δ(f) + 2 S`, where
`b` is the number of branches, which is also the number of permutation cycles of `w`. The
same word represents the root braid of `f` over every sufficiently small circle. -/
theorem Germ.exists_transverse_fullTwist_word_length (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hsq : Squarefree (ofFunction H hH)) {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S)
    (hmult : ofFunction H hH ∈ maximalIdeal 2 ^ S) :
    ∃ w : PositiveAdjacentWord S,
      (PositiveAdjacentWord.toSigned w).cycleCount = irreducibleBranchCount (ofFunction H hH) ∧
      (∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin S → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * π) (fullTwistWord S ++ w)) ∧
      (fullTwistWord S ++ w).length + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) + S ∧
      w.length + S ^ 2 + irreducibleBranchCount (ofFunction H hH) =
        2 * deltaInvariant (ofFunction H hH) + 2 * S := by
  have hf : ofFunction H hH ∈ maximalIdeal 2 := by
    have h := Ideal.pow_le_pow_right (I := maximalIdeal 2) (Nat.one_le_iff_ne_zero.mpr hS.ne')
      hmult
    simpa using h
  obtain ⟨P, u, A, hPm, hPdeg, -, hu, hfac, hA, himp⟩ :=
    exists_weierstrass_data_fullTwistWord_append_length (ofFunction H hH) hf hsq hS hreg
  obtain ⟨w, hcw, hrep, hword⟩ := Germ.exists_fullTwist_rootBraid_hword H hH hsq hreg hmult
    P u hPm hPdeg hu hfac A (fun k _ => hA k)
  obtain ⟨hlen, htail⟩ := himp w hword
  exact ⟨w, hcw, hrep, hlen, htail⟩

end OnLeConjecture.Analytic
