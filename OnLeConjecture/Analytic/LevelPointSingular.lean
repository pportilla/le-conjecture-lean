/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootRegularCluster
public import OnLeConjecture.Analytic.LevelOuterBraid
public import OnLeConjecture.Analytic.BraidMonodromyHomotopy
public import OnLeConjecture.Analytic.BraidMonodromyLocalFactors

/-!
# The cluster at a singular point of a fibre

This module proves the pointwise cluster data (`LevelRootCriticalStrips.lean`) at a singular point
`Q_j = L.point j` of the level, for a setup `P` with `SetupProperties`
(`LevelSetupInterface.lean`). It is the second paragraph of the subsection "Local factors, without
a generic-Morse projection" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`): in the transverse coordinates `(ζ, h)` of the target plane the
branch-word construction of job J14 gives the positive word `β_j = d_{a_j} w_j` on `a_j` sheets.

Write `x = Q_j`, `c = h (H x)`, `ζ_x = ζ (H x)`, `f` for the local image equation
`localSectionEquation A.H x` and `T = P.planeChart`, so that `T u` is the point of the target plane
with `ζ`-coordinate `u 0` and `h`-coordinate `u 1`.

* `IsPathWord.signedBraidEquiv_const_add`: a translation of all strands by a constant does not
  change the path word, up to `SignedBraidEquiv` (homotopy `s ↦ s c + K`, along which the
  lexicographic order at the two endpoints does not change).
* `LevelProjectionSetup.localClusterAt_of_strands`: if, near `0`, the zero set of a function `W`
  is the image of the level near `x` in the plane coordinates centered at `H x` (the image
  description of `SingularSectionPointData`), and the J14 strands `y r` of `W ∘ T` over the
  circles of radius `r^q` are represented by a positive word `V`, and the zeros of `W ∘ T` near `0`
  are roots of monic polynomials of degree `S` in the first coordinate, then the cluster at `x`
  has degree `S` and word `V`. Over `c + r e^{iθ}` the local roots are the translates
  `ζ_x + y (r^{1/q}) k θ` of the strands: a strand gives a point of the level near `x` by the
  image description on a small closed ball, and a point of the level near `x` gives a zero of
  `W ∘ T`, hence a root of the polynomial, hence one of the `S` distinct strands.
* `LevelProjectionSetup.pointClusterData_of_singular`: the cluster data at `L.point j`, with
  degree the exact multiplicity `a_j` of `f`, kind `some j`, and word `d_{a_j} w_j`, where `w_j`
  is the J14 word of `T^* f` (`exists_transverse_fullTwist_strands`, applicable by the field
  `point_transverse` of `SetupProperties`). The factor-word identities follow as in
  `ResolutionSectionLevel.exists_factorWord`, since `f` is irreducible and the delta invariant
  and the number of branches are invariant under `T`.
* `pointClusterStatement_of_smooth`: `PointClusterStatement` from the cluster data at the critical
  points of the level that are not singular points.
-/

@[expose] public noncomputable section

open Set Function Filter Metric Real
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord OnLeConjecture.Analytic.Germ

/-! ### Translation of strand families -/

theorem lexKey_const_add_lt_iff (c z w : ℂ) :
    lexKey (c + z) < lexKey (c + w) ↔ lexKey z < lexKey w := by
  rw [lexKey_lt_iff, lexKey_lt_iff]
  simp only [Complex.add_re, Complex.add_im, add_lt_add_iff_left, add_right_inj]

/-- A translation does not change the lexicographic order of a configuration. -/
theorem configSort_const_add {S : ℕ} (c : ℂ) {x : Fin S → ℂ} (hx : Injective x) :
    configSort (fun k => c + x k) = configSort x := by
  symm
  apply eq_configSort ((add_right_injective c).comp hx)
  intro i j hij
  exact (lexKey_const_add_lt_iff c _ _).mpr (configSort_strictMono hx hij)

/-- **Translation does not change path words.** For a strand family `K`, continuous on `[u, v]`
with pairwise distinct points, the path words of `K` and of its translate `c + K` are
equivalent. -/
theorem IsPathWord.signedBraidEquiv_const_add {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    (huv : u < v) (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (c : ℂ) {W W' : SignedAdjacentWord S}
    (hW : IsPathWord K u v W) (hW' : IsPathWord (fun k t => c + K k t) u v W') :
    SignedBraidEquiv W W' := by
  have hcont' : ∀ k, ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) * c + K k p.2)
      (Icc 0 1 ×ˢ Icc u v) := by
    intro k
    refine ContinuousOn.add ?_ ?_
    · exact ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).continuousOn
    · exact (hcont k).comp continuousOn_snd fun p hp => hp.2
  have hinj' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, Injective fun k => (s : ℂ) * c + K k t :=
    fun s _ t ht k l hkl => hinj t ht (add_left_cancel hkl)
  have h₀ : IsPathWord (fun k t => ((0 : ℝ) : ℂ) * c + K k t) u v W :=
    hW.of_eqOn fun k t _ => by simp
  have h₁ : IsPathWord (fun k t => ((1 : ℝ) : ℂ) * c + K k t) u v W' :=
    hW'.of_eqOn fun k t _ => by simp
  have hside : ∀ t₀ ∈ Icc u v, IsPathWord (fun k (s : ℝ) => (s : ℂ) * c + K k t₀) 0 1 [] :=
    fun t₀ ht₀ => IsPathWord.of_configSort_const fun s _ => configSort_const_add _ (hinj t₀ ht₀)
  have h := isPathWord_homotopy (H := fun s k t => (s : ℂ) * c + K k t) huv hcont' hinj' h₀ h₁
    (hside u (left_mem_Icc.mpr huv.le)) (hside v (right_mem_Icc.mpr huv.le))
  simpa using h

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (P : LevelProjectionSetup A L)

theorem planeChart_symm_apply_zero (p : Source 2) :
    P.planeChart.symm p 0 = P.fibreCoord (hyperplaneInclusion 2 p) := by
  have h := P.fibreCoord_planeChart (P.planeChart.symm p)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem planeChart_symm_apply_one (p : Source 2) :
    P.planeChart.symm p 1 = P.baseCoord (hyperplaneInclusion 2 p) := by
  have h := P.baseCoord_planeChart (P.planeChart.symm p)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The cluster at a point from transverse strands.** Let `x` be a point of the level at which
`H` is continuous. Assume that near `0` the zero set of `W` is the image of the level near `x`
under `y ↦ H y - H x`, in the sense of the image description of `SingularSectionPointData`, that
the strands `y r` of zeros of `W ∘ T` over the circles `ξ = r^q e^{iθ}`, `r < r₀`, converge to `0`,
are continuous and pairwise distinct and are represented through closed braids by `V`, and that
near `0` the first coordinates of the zeros of `W ∘ T` over `ξ` are roots of a nonzero polynomial
`Q ξ` of degree `S`. Then the cluster at `x` over the circles around `c = h (H x)` has `S` strands
and word `V`. -/
theorem localClusterAt_of_strands {x : Source 2} (hxR : x ∈ ball (0 : Source 2) L.radius)
    (hxs : A.H x 0 = L.parameter) (hHx : ContinuousAt A.H x) {Wf : Source 2 → ℂ}
    (hzs : ∀ U ∈ 𝓝 (0 : Source 2), ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : Source 2) ρ ⊆ U ∧
      ∀ᶠ p in 𝓝 (0 : Source 2), Wf p = 0 ↔
        ∃ z ∈ closedBall (0 : Source 2) ρ, A.H (x + z) - A.H x = hyperplaneInclusion 2 p)
    {S : ℕ} {V : PositiveAdjacentWord S} {q : ℕ} {r₀ : ℝ} {y : ℝ → Fin S → ℝ → ℂ}
    (hq : 0 < q) (hr₀ : 0 < r₀)
    (htend : ∀ N ∈ 𝓝 (0 : Source 2), ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r, 0 < r → r < r₁ → ∀ k θ,
      ![y r k θ, circlePath (r ^ q) θ] ∈ N)
    (hstr : ∀ r, 0 < r → r < r₀ → (∀ k, Continuous (y r k)) ∧
      (∀ θ, Injective fun k => y r k θ) ∧
      (∀ k θ, Wf (P.planeChart ![y r k θ, circlePath (r ^ q) θ]) = 0) ∧
      ∀ b : ℝ, IsRepresentedByPositiveWord (y r) b (b + 2 * π) V)
    {Q : ℂ → Polynomial ℂ} (hQ : ∀ c, Q c ≠ 0 ∧ (Q c).natDegree = S)
    (hQz : ∀ᶠ u in 𝓝 (0 : Source 2), Wf (P.planeChart u) = 0 → (Q (u 1)).eval (u 0) = 0) :
    P.LocalClusterAt (P.baseCoord (A.H x)) x S V := by
  intro δ hδ
  set T := P.planeChart with hTdef
  set ζx := P.fibreCoord (A.H x) with hζx
  set c := P.baseCoord (A.H x) with hc
  -- The ball `B(x, ε₁)` in `B_R` on which `ζ ∘ H` stays within `δ` of `ζ (H x)`.
  have hζc : ContinuousAt (fun y => P.fibreCoord (A.H y)) x :=
    P.fibreCoord.continuous.continuousAt.comp hHx
  have hN₁ : ball (0 : Source 2) L.radius ∩ {y | ‖P.fibreCoord (A.H y) - ζx‖ < δ} ∈ 𝓝 x := by
    refine inter_mem (isOpen_ball.mem_nhds hxR) ?_
    filter_upwards [hζc.preimage_mem_nhds (ball_mem_nhds (P.fibreCoord (A.H x)) hδ)] with y hy
    simpa [dist_eq_norm] using hy
  obtain ⟨ε₁, hε₁, hε₁N⟩ := Metric.mem_nhds_iff.mp hN₁
  -- The image description on a closed ball of radius `ρ₁` inside `B(0, ε₁)`.
  obtain ⟨ρ₁, hρ₁, hρ₁U, hzs₁⟩ := hzs (ball 0 ε₁) (ball_mem_nhds 0 hε₁)
  -- The polynomials `Q` in the plane coordinates.
  have hTt : Tendsto T (𝓝 0) (𝓝 0) := by
    have h := T.continuous.tendsto 0
    rwa [map_zero] at h
  have hTst : Tendsto T.symm (𝓝 0) (𝓝 0) := by
    have h := T.symm.continuous.tendsto 0
    rwa [map_zero] at h
  have hQp : ∀ᶠ p in 𝓝 (0 : Source 2), Wf p = 0 → (Q (T.symm p 1)).eval (T.symm p 0) = 0 := by
    filter_upwards [hTst.eventually hQz] with p hp hWp
    exact hp (by rw [ContinuousLinearEquiv.apply_symm_apply]; exact hWp)
  -- The ball `B(x, ε)`, on which `H y - H x` lies in the neighbourhoods above.
  have hHt : Tendsto (fun y => hyperplaneTail 2 (A.H y - A.H x)) (𝓝 x) (𝓝 0) := by
    have h := ((hyperplaneTail 2).continuous.tendsto (A.H x - A.H x)).comp
      (hHx.sub continuousAt_const).tendsto
    rwa [sub_self, map_zero] at h
  obtain ⟨ε₂, hε₂, hε₂N⟩ := Metric.mem_nhds_iff.mp (hHt (hzs₁.and hQp))
  set ε := min ε₂ ρ₁ with hεdef
  have hε : 0 < ε := lt_min hε₂ hρ₁
  have hερ₁ : ∀ y ∈ ball x ε, y - x ∈ closedBall (0 : Source 2) ρ₁ := by
    intro y hy
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact (mem_ball.mp hy).le.trans (min_le_right _ _)
  have hεball : ∀ y ∈ ball x ε, y ∈ ball x ε₁ := by
    intro y hy
    have h2 := hρ₁U (hερ₁ y hy)
    rwa [mem_ball_zero_iff, ← dist_eq_norm] at h2
  -- The image description on a closed ball of radius `ρ₂` inside `B(0, ε)`.
  obtain ⟨ρ₂, hρ₂, hρ₂U, hzs₂⟩ := hzs (ball 0 ε) (ball_mem_nhds 0 hε)
  -- The strands near the origin.
  obtain ⟨r₁, hr₁, hr₁N⟩ := htend (T ⁻¹' {p | (Wf p = 0 ↔ ∃ z ∈ closedBall (0 : Source 2) ρ₂,
      A.H (x + z) - A.H x = hyperplaneInclusion 2 p) ∧
      (Wf p = 0 → (Q (T.symm p 1)).eval (T.symm p 0) = 0)}) (hTt (hzs₂.and hQp))
  set m := min r₀ r₁ with hmdef
  have hm : 0 < m := lt_min hr₀ hr₁
  refine ⟨ε, hε, m ^ q, pow_pos hm q, fun r hr hrm => ?_⟩
  -- The circle of radius `r` is the base circle of the strands of index `ρ = r^{1/q}`.
  obtain ⟨ρ, hρ, rfl, hρm⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ q = r ∧ ρ < m := by
    refine ⟨r ^ ((q : ℝ)⁻¹), Real.rpow_pos_of_pos hr _, Real.rpow_inv_natCast_pow hr.le hq.ne',
      ?_⟩
    have h := Real.rpow_lt_rpow hr.le hrm (inv_pos.mpr (Nat.cast_pos.mpr hq))
    rwa [Real.pow_rpow_inv_natCast hm.le hq.ne'] at h
  have hρr₀ : ρ < r₀ := hρm.trans_le (min_le_left _ _)
  have hρr₁ : ρ < r₁ := hρm.trans_le (min_le_right _ _)
  obtain ⟨hyc, hyinj, hyzero, hyrep⟩ := hstr ρ hρ hρr₀
  have hstrN : ∀ k θ, (Wf (T ![y ρ k θ, circlePath (ρ ^ q) θ]) = 0 ↔
      ∃ z ∈ closedBall (0 : Source 2) ρ₂,
        A.H (x + z) - A.H x = hyperplaneInclusion 2 (T ![y ρ k θ, circlePath (ρ ^ q) θ])) ∧
      (Wf (T ![y ρ k θ, circlePath (ρ ^ q) θ]) = 0 →
        (Q (circlePath (ρ ^ q) θ)).eval (y ρ k θ) = 0) := by
    intro k θ
    have h := hr₁N ρ hρ hρr₁ k θ
    simp only [mem_preimage, Set.mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply] at h
    simpa using h
  -- The strands are roots of `Q`.
  have hroot : ∀ θ k, (Q (circlePath (ρ ^ q) θ)).eval (y ρ k θ) = 0 :=
    fun θ k => (hstrN k θ).2 (hyzero k θ)
  -- The local roots are the translated strands.
  have hclaim : ∀ θ : ℝ, P.localRoots x ε (c + circlePath (ρ ^ q) θ) =
      range fun k => ζx + y ρ k θ := by
    intro θ
    ext z
    constructor
    · rintro ⟨y', ⟨⟨hy'R, hy's, hy'c⟩, hy'x⟩, rfl⟩
      have hy'ε₂ : y' ∈ ball x ε₂ :=
        mem_ball.mpr ((mem_ball.mp hy'x).trans_le (min_le_left _ _))
      obtain ⟨hpN, hpQ⟩ := hε₂N hy'ε₂
      have hι : hyperplaneInclusion 2 (hyperplaneTail 2 (A.H y' - A.H x)) = A.H y' - A.H x :=
        hyperplaneInclusion_tail_of_zero (by rw [Pi.sub_apply, hy's, hxs, sub_self])
      have hWp : Wf (hyperplaneTail 2 (A.H y' - A.H x)) = 0 :=
        hpN.mpr ⟨y' - x, hερ₁ y' hy'x, by rw [add_sub_cancel, hι]⟩
      have h := hpQ hWp
      have hT0 : T.symm (hyperplaneTail 2 (A.H y' - A.H x)) 0 =
          P.fibreCoord (A.H y') - ζx := by
        rw [hTdef, P.planeChart_symm_apply_zero, hι, map_sub]
      have hT1 : T.symm (hyperplaneTail 2 (A.H y' - A.H x)) 1 = circlePath (ρ ^ q) θ := by
        rw [hTdef, P.planeChart_symm_apply_one, hι, map_sub, hy'c, hc, add_sub_cancel_left]
      rw [hT0, hT1] at h
      obtain ⟨k, hk⟩ := mem_range_of_eval_eq_zero (hQ _).1 (hQ _).2.le (hyinj θ) (hroot θ) h
      refine ⟨k, ?_⟩
      have hk' : y ρ k θ = P.fibreCoord (A.H y') - ζx := hk
      change ζx + y ρ k θ = P.fibreCoord (A.H y')
      rw [hk']
      ring
    · rintro ⟨k, rfl⟩
      obtain ⟨z, hz, hHz⟩ := (hstrN k θ).1.mp (hyzero k θ)
      have hzε : z ∈ ball (0 : Source 2) ε := hρ₂U hz
      have hball : x + z ∈ ball x ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        rwa [mem_ball_zero_iff] at hzε
      have hHxz : A.H (x + z) =
          A.H x + hyperplaneInclusion 2 (T ![y ρ k θ, circlePath (ρ ^ q) θ]) :=
        sub_eq_iff_eq_add'.mp hHz
      refine ⟨x + z, ⟨⟨(hε₁N (hεball _ hball)).1, ?_, ?_⟩, hball⟩, ?_⟩
      · rw [hHxz, Pi.add_apply, hyperplaneInclusion_apply_zero, add_zero, hxs]
      · rw [hHxz, map_add, hTdef, P.baseCoord_planeChart]
        simp [hc]
      · change P.fibreCoord (A.H (x + z)) = ζx + y ρ k θ
        rw [hHxz, map_add, hTdef, P.fibreCoord_planeChart]
        simp [hζx]
  refine ⟨fun θ => ?_, fun θ y' hy' => (hε₁N (hεball _ hy'.2)).2, fun b K hK W hW => ?_⟩
  · rw [hclaim θ]
    exact ncard_range_fin ((add_right_injective ζx).comp (hyinj θ))
  · -- The translated strands label the local roots.
    have hY : IsRootLabellingOn (P.localRoots x ε) (fun θ => c + circlePath (ρ ^ q) θ)
        (Icc b (b + 2 * π)) fun k θ => ζx + y ρ k θ :=
      ⟨fun k => (continuous_const.add (hyc k)).continuousOn,
        fun θ _ => (add_right_injective ζx).comp (hyinj θ), fun θ _ => (hclaim θ).symm⟩
    obtain ⟨τ, hτ⟩ := hY.exists_perm isPreconnected_Icc hK
    have hWY : IsPathWord (fun k θ => ζx + y ρ k θ) b (b + 2 * π) W :=
      (IsPathWord.relabel hY.injective τ).mp (hW.of_eqOn fun k θ hθ => hτ k θ hθ)
    have hb : b < b + 2 * π := by linarith [Real.pi_pos]
    obtain ⟨W₀, hW₀⟩ := exists_isPathWord hb (fun k => (hyc k).continuousOn)
      (fun θ _ => hyinj θ)
    have hE := IsPathWord.signedBraidEquiv_const_add hb (fun k => (hyc k).continuousOn)
      (fun θ _ => hyinj θ) ζx hW₀ hWY
    exact hE.symm.toConj.trans ((hyrep b).signedBraidConj hW₀)

/-- **The cluster data at a singular point.** At `x = L.point j`, with `c = h (H x)`, the cluster
has degree the exact multiplicity `a_j` of the local image equation, kind `some j`, and the word
`d_{a_j} w_j`, where `w_j` is the J14 word of the local image equation in the coordinates
`(ζ, h)`. -/
theorem pointClusterData_of_singular (hP : P.SetupProperties) (j : Fin L.points.card) :
    Nonempty (P.PointClusterData (P.baseCoord (A.H (L.point j))) (L.point j)) := by
  have hQj : L.point j ∈ L.points := Finset.coe_mem _
  obtain ⟨hxR, hxs, -⟩ := (L.points_iff _).mp hQj
  obtain ⟨hHx, -, -, -, a, -, hirr, hmem, hnot, ha2, ham, -, -, -, -, hzs⟩ :=
    L.singular (L.point j) hQj
  obtain ⟨Wf, hWf, hWeq⟩ := Germ.exists_ofFunction (localSectionEquation A.H (L.point j))
  have hG : AnalyticAt ℂ (Wf ∘ P.planeChart) 0 := by
    have h : AnalyticAt ℂ Wf (P.planeChart 0) := by simpa using hWf
    exact h.comp (P.planeChart.analyticAt 0)
  set e := pointedEquivGermOfContinuousLinearEquiv P.planeChart with hedef
  have hGe : ofFunction (Wf ∘ P.planeChart) hG =
      e.forward.pullbackRingHom (localSectionEquation A.H (L.point j)) := by
    rw [hWeq]
    change _ = Germ.compPointed (ofFunction Wf hWf)
      (PointedMapGerm.ofFunction P.planeChart (P.planeChart.analyticAt 0)
        (map_zero P.planeChart))
    rw [compPointed_ofFunction]
  have hsq : Squarefree (ofFunction (Wf ∘ P.planeChart) hG) := by
    rw [hGe]
    exact e.squarefree_pullback _ hirr.squarefree
  have hreg : IsRegularInFirstCoordinateOfOrder (ofFunction (Wf ∘ P.planeChart) hG) a := by
    rw [hGe]
    exact hP.point_transverse j a hmem hnot
  have hmult : ofFunction (Wf ∘ P.planeChart) hG ∈ maximalIdeal 2 ^ a := by
    rw [hGe]
    exact e.forward.pullback_mem_maximalIdeal_pow hmem
  obtain ⟨w, q, r₀, y, hcyc, hlen, hq, hr₀, htend, hstr, Q, hQ, hQz⟩ :=
    exists_transverse_fullTwist_strands _ hG hsq (by omega) hreg hmult
  have hb1 : irreducibleBranchCount (ofFunction (Wf ∘ P.planeChart) hG) = 1 := by
    rw [hGe, ← irreducibleBranchCount_pullback]
    exact irreducibleBranchCount_eq_one_of_irreducible _ hirr
  have hf2 : localSectionEquation A.H (L.point j) ∈ maximalIdeal 2 ^ 2 :=
    Ideal.pow_le_pow_right ha2 hmem
  have hδ : deltaInvariant (ofFunction (Wf ∘ P.planeChart) hG) =
      deltaInvariant (localSectionEquation A.H (L.point j)) := by
    rw [hGe, deltaInvariant_pullback e hirr.squarefree hf2]
  have hholds : P.LocalClusterAt (P.baseCoord (A.H (L.point j))) (L.point j) a
      (fullTwistWord a ++ w) :=
    P.localClusterAt_of_strands hxR hxs hHx.continuousAt (hzs Wf hWf hWeq) hq hr₀ htend
      (fun r hr hrr => hstr r hr hrr) hQ hQz
  refine ⟨{ degree := a
            word := fullTwistWord a ++ w
            kind := some j
            holds := hholds
            kind_singular := fun j' hj' => ?_
            kind_none := fun h => absurd h (Option.some_ne_none j)
            point_kind := fun j' hj' => ?_
            critical := fun _ => Or.inl (Option.some_ne_none j) }⟩
  · obtain rfl := Option.some.inj hj'
    refine ⟨rfl, ha2, ham, ?_, generatorIndices_fullTwistWord_append w, ?_⟩
    · rw [cycleCount_fullTwist_append, hcyc, hb1]
    · rw [List.length_append, length_fullTwistWord]
      rw [hb1, hδ] at hlen
      have hsq' : a * (a - 1) + a = a ^ 2 := by
        obtain ⟨m, hm⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel]; ring
      omega
  · have h : L.points.equivFin.symm j = L.points.equivFin.symm j' := Subtype.ext hj'
    rw [L.points.equivFin.symm.injective h]

end LevelProjectionSetup

/-- **The pointwise cluster statement from the smooth critical points.** The regular points are
treated by `pointClusterData_of_regular` and the singular points by
`pointClusterData_of_singular`. The remaining hypothesis is the cluster data at the critical
points of the level that are not singular points. -/
theorem pointClusterStatement_of_smooth
    (hSmooth : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ {c : ℂ} {x : Source 2}, c ∈ P.critical → x ∈ P.levelFibre c →
        ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) → (∀ j, x ≠ L.point j) →
          Nonempty (P.PointClusterData c x)) :
    PointClusterStatement :=
  pointClusterStatement_of_cases hSmooth fun P hP j => P.pointClusterData_of_singular hP j

end OnLeConjecture.Analytic
