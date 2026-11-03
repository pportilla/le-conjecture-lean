/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreCover

/-!
# Roots of nearby levels over a small circle

Let `H` be a reduced equation meeting the axis `x = 0` finitely. Away from the
origin, the curve `H = 0` meets the polar curve `∂₀H = 0` nowhere near the
origin: at such a common point, conservation of intersection numbers would
produce ramification points of nearby nonzero levels away from the origin,
which the ramification count excludes. Hence over every base point `x ≠ 0`
near the origin the roots of `H(·, x) = 0` are simple.

By compactness of a circle `|x| = r` and conservation of zeros, the roots of
`H(·, x) = s` over that circle are uniformly separated for all small levels
`s`.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- Finite intersection of a level with the fibre derivative at a regular point. -/
theorem hasFiniteIntersection_fibreDerivative (H : Source 2 → ℂ) {z : Source 2} {s : ℂ}
    (han : AnalyticAt ℂ H z) (hz : H z = s) (hgrad : fderiv ℂ H z ≠ 0)
    (hfin : rootOrder H s (z 0) (z 1) ≠ ⊤) :
    HasFiniteIntersection (germAt (fun w => H w - s) z) (germAt (fibreDerivative H) z) := by
  set F : Source 2 → ℂ := fun w => H w - s with hFdef
  have hF : AnalyticAt ℂ F z := han.sub analyticAt_const
  set f := ofFunctionAt F z hF with hfdef
  have hdF : ∀ w, fderiv ℂ F w = fderiv ℂ H w := fun w => fderiv_sub_const s
  have hmem : f ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, hfdef, valueRingHom_ofFunctionAt]
    simp [F, hz]
  have hdiff : differential f ≠ 0 := by
    rw [hfdef, differential_ofFunctionAt, hdF]
    exact hgrad
  have hnot : f ∉ maximalIdeal 2 ^ 2 := by
    intro hsq2
    have hfirst := (mem_firstOrderIdeal_iff.mp ((maximalIdeal_sq_le_firstOrderIdeal 2) hsq2)).2
    exact hdiff hfirst
  have hsq : Squarefree f :=
    (smooth_irreducible_of_mem_maximalIdeal_not_mem_sq f hmem hnot).2.squarefree
  have hline : analyticOrderAt (fun t : ℂ => F (z + t • coordinateVector (0 : Fin 2))) 0 =
      rootOrder H s (z 0) (z 1) := analyticOrderAt_line_eq_rootOrder H s z
  obtain ⟨haxis, -⟩ := axis_intersection_ofFunctionAt F z hF (hline ▸ hfin)
  obtain ⟨hpolar, -, -⟩ := exists_first_partial_polar_identity f hmem hsq haxis
  have hD : AnalyticAt ℂ (fibreDerivative H) z := analyticAt_fibreDerivative han
  have hpd : partialDerivative (0 : Fin 2) f = germAt (fibreDerivative H) z := by
    rw [hfdef, partialDerivative_ofFunctionAt, germAt_eq hD]
    congr 1
    funext w
    rw [hdF]
    rfl
  rw [germAt_eq hF, ← hfdef, ← hpd]
  exact hpolar

/-- **No polar points on the curve away from the origin.** Under the
conclusions of the ramification count, a zero `w ≠ 0` of `H` inside the ball
of radius `ρ` where the fibre root has finite order is not a zero of `∂₀H`. -/
theorem fibreDerivative_ne_zero_of_curve {H : Source 2 → ℂ} {r₁ ρ : ℝ}
    (hreg : ∀ z : Source 2, ‖z‖ < r₁ → AnalyticAt ℂ H z ∧ (z ≠ 0 → fderiv ℂ H z ≠ 0))
    (hρ : ρ < r₁)
    (hram : ∀ r > 0, ∃ c > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < c → ∃ R : Finset (Source 2),
      (∀ z, z ∈ R ↔ (‖z‖ ≤ ρ ∧ H z = s ∧ fibreDerivative H z = 0)) ∧ (∀ z ∈ R, ‖z‖ < r))
    {w : Source 2} (hw : ‖w‖ < ρ) (hw0 : w ≠ 0) (hHw : H w = 0)
    (hfin : rootOrder H 0 (w 0) (w 1) ≠ ⊤) :
    fibreDerivative H w ≠ 0 := by
  intro hd
  have hwr₁ : ‖w‖ < r₁ := hw.trans hρ
  have han := (hreg w hwr₁).1
  have hgrad := (hreg w hwr₁).2 hw0
  have hsub0 : (fun y => H y - 0) = H := funext fun y => sub_zero _
  have hfinI := hasFiniteIntersection_fibreDerivative H han hHw hgrad hfin
  rw [hsub0] at hfinI
  have hD : AnalyticAt ℂ (fibreDerivative H) w := analyticAt_fibreDerivative han
  have hpos : 0 < localIntersection H (fibreDerivative H) w :=
    localIntersection_pos han hD hHw hd hfinI
  -- translate to the origin
  set v : Source 2 → ℂ := fun z => H (w + z) with hv
  set h : Source 2 → ℂ := fun z => fibreDerivative H (w + z) with hh
  have hva : AnalyticAt ℂ v 0 := han.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero w)
  have hha : AnalyticAt ℂ h 0 := hD.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero w)
  have hv0 : v 0 = 0 := by simp [v, hHw]
  have hgv : germAt H w = ofFunction v hva := by rw [germAt_eq han]; rfl
  have hgh : germAt (fibreDerivative H) w = ofFunction h hha := by rw [germAt_eq hD]; rfl
  have hfin' : HasFiniteIntersection (ofFunction v hva) (ofFunction h hha) := by
    rw [← hgv, ← hgh]
    exact hfinI
  have hN : intersectionMultiplicity _ _ hfin' = localIntersection H (fibreDerivative H) w := by
    unfold localIntersection
    rw [hgv, hgh]
    rfl
  obtain ⟨r₀, hr₀, hcons⟩ := conservesAlongLevels v h hva hha hv0 hfin'
  set r' := min r₀ (min (ρ - ‖w‖) (‖w‖ / 2)) with hr'
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hr'pos : 0 < r' := lt_min hr₀ (lt_min (by linarith) (by linarith))
  obtain ⟨c₀, hc₀, hR⟩ := hram (‖w‖ / 2) (half_pos hwpos)
  obtain ⟨ε', hε', hsub⟩ := Metric.eventually_nhds_iff.mp (hcons r' hr'pos (min_le_left _ _))
  set t : ℝ := min ε' c₀ / 2 with ht
  have htpos : 0 < t := by positivity
  have hs0 : ((t : ℂ)) ≠ 0 := by exact_mod_cast htpos.ne'
  have hsn : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_of_nonneg htpos.le]
  have hsd : dist (t : ℂ) 0 < ε' := by
    rw [dist_zero_right, hsn]
    have := min_le_left ε' c₀
    linarith
  obtain ⟨Z, hZ, -, hZsum⟩ := hsub hsd hs0
  have hZne : Z.Nonempty := by
    by_contra hZe
    rw [Finset.not_nonempty_iff_eq_empty] at hZe
    rw [hZe, Finset.sum_empty, hN] at hZsum
    omega
  obtain ⟨z, hz⟩ := hZne
  obtain ⟨hzb, hzs, hzd⟩ := (hZ z).mp hz
  have hzr' : ‖z‖ < r' := mem_ball_zero_iff.mp hzb
  have hz1 : ‖z‖ < ρ - ‖w‖ := hzr'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hz2 : ‖z‖ < ‖w‖ / 2 := hzr'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨R, hRmem, hRsmall⟩ := hR (t : ℂ) hs0 (by
    rw [hsn]
    have := min_le_right ε' c₀
    linarith)
  have hwz : ‖w + z‖ ≤ ρ := by
    have := norm_add_le w z
    linarith
  have hmem : w + z ∈ R := (hRmem (w + z)).mpr ⟨hwz, hzs, hzd⟩
  have hsmall := hRsmall _ hmem
  have hlow : ‖w‖ - ‖z‖ ≤ ‖w + z‖ := by
    have := norm_sub_norm_le w (-z)
    simpa [sub_neg_eq_add] using this
  linarith

theorem analyticAt_rootFamily {H : Source 2 → ℂ} {p : Fin 2 → ℂ} {y : ℂ}
    (hH : AnalyticAt ℂ H (planePoint y (p 0))) : AnalyticAt ℂ (rootFamily H) (p, y) := by
  have hlin : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × ℂ => planePoint q.2 (q.1 0)) (p, y) := by
    have h : (fun q : (Fin 2 → ℂ) × ℂ => planePoint q.2 (q.1 0)) =
        fun q => q.2 • coordinateVector (0 : Fin 2) + q.1 0 • coordinateVector (1 : Fin 2) := by
      funext q
      exact planePoint_eq_affine q.2 (q.1 0)
    rw [h]
    have h1 : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × ℂ => q.1 0) (p, y) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp
        analyticAt_fst
    exact (analyticAt_snd.smul analyticAt_const).add (h1.smul analyticAt_const)
  have h2 : AnalyticAt ℂ (fun q : (Fin 2 → ℂ) × ℂ => q.1 1) (p, y) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt _).comp
      analyticAt_fst
  exact (AnalyticAt.comp (g := H) (f := fun q : (Fin 2 → ℂ) × ℂ => planePoint q.2 (q.1 0))
    hH hlin).sub h2

/-- **Uniform separation over a circle.** For a circle `|x| = r` of small
radius and all sufficiently small levels `s`, distinct roots of
`H(·, x) = s` in the disc of radius `ρ` are at distance at least `κ`. -/
theorem exists_circle_root_separation {H : Source 2 → ℂ} {r₁ ρ η : ℝ} {d : ℕ}
    (hreg : ∀ z : Source 2, ‖z‖ < r₁ → AnalyticAt ℂ H z ∧ (z ≠ 0 → fderiv ℂ H z ≠ 0))
    (hρ : ρ < r₁)
    (hram : ∀ r > 0, ∃ c > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ < c → ∃ R : Finset (Source 2),
      (∀ z, z ∈ R ↔ (‖z‖ ≤ ρ ∧ H z = s ∧ fibreDerivative H z = 0)) ∧ (∀ z ∈ R, ‖z‖ < r))
    (hroots : ∀ x : ℂ, ‖x‖ < η → ∀ s : ℂ, ‖s‖ < η → ∃ Z : Finset ℂ,
      (∀ y : ℂ, ‖y‖ ≤ ρ → (H (planePoint y x) = s ↔ y ∈ Z)) ∧ (∀ y ∈ Z, ‖y‖ < ρ / 2) ∧
      (∀ y ∈ Z, rootOrder H s y x ≠ ⊤) ∧ ∑ y ∈ Z, (rootOrder H s y x).toNat = d)
    {r : ℝ} (hr : 0 < r) (hrη : r < η) (hrρ : r < ρ) :
    ∃ κ > 0, ∃ c > 0, ∀ x : ℂ, ‖x‖ = r → ∀ s : ℂ, ‖s‖ < c → ∀ y y' : ℂ, ‖y‖ ≤ ρ →
      ‖y'‖ ≤ ρ → H (planePoint y x) = s → H (planePoint y' x) = s → y ≠ y' →
        κ ≤ ‖y - y'‖ := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ x : ℂ, ‖x‖ = r ∧ ∃ s : ℂ, ‖s‖ < 1 / ((n : ℝ) + 1) ∧ ∃ y y' : ℂ,
      ‖y‖ ≤ ρ ∧ ‖y'‖ ≤ ρ ∧ H (planePoint y x) = s ∧ H (planePoint y' x) = s ∧ y ≠ y' ∧
        ‖y - y'‖ < 1 / ((n : ℝ) + 1) := fun n => hcon _ (by positivity) _ (by positivity)
  choose x hx s hs y y' hy hy' hys hy's hne hdist using hseq
  set K : Set (ℂ × ℂ) := Metric.sphere (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) ρ with hK
  have hKc : IsCompact K := (isCompact_sphere 0 r).prod (isCompact_closedBall 0 ρ)
  have hmemK : ∀ n, (x n, y n) ∈ K := fun n =>
    ⟨mem_sphere_zero_iff_norm.mpr (hx n), mem_closedBall_zero_iff.mpr (hy n)⟩
  obtain ⟨p, hpK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmemK
  set xs := p.1 with hxsdef
  set ys := p.2 with hysdef
  have hxs_norm : ‖xs‖ = r := mem_sphere_zero_iff_norm.mp hpK.1
  have hys_norm : ‖ys‖ ≤ ρ := mem_closedBall_zero_iff.mp hpK.2
  have hxlim : Tendsto (fun n => x (φ n)) atTop (𝓝 xs) := (continuous_fst.tendsto p).comp hlim
  have hylim : Tendsto (fun n => y (φ n)) atTop (𝓝 ys) := (continuous_snd.tendsto p).comp hlim
  have hinv : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop
  have hslim : Tendsto (fun n => s (φ n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hs (φ n)).le) hinv
  have hy'lim : Tendsto (fun n => y' (φ n)) atTop (𝓝 ys) := by
    have hd : Tendsto (fun n => y' (φ n) - y (φ n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hinv
      rw [norm_sub_rev]
      exact (hdist (φ n)).le
    simpa using hd.add hylim
  -- the limit point is a root of the curve
  have hwlt : ‖planePoint ys xs‖ < r₁ := by
    rw [norm_planePoint]
    exact max_lt (hys_norm.trans_lt hρ) (hxs_norm ▸ hrρ.trans hρ)
  have hanw := (hreg _ hwlt).1
  have hcontw : ContinuousAt (fun q : ℂ × ℂ => H (planePoint q.1 q.2)) (ys, xs) :=
    ContinuousAt.comp (g := H) (f := fun q : ℂ × ℂ => planePoint q.1 q.2) hanw.continuousAt
      continuous_planePoint.continuousAt
  have hHlim : Tendsto (fun n => H (planePoint (y (φ n)) (x (φ n)))) atTop
      (𝓝 (H (planePoint ys xs))) :=
    hcontw.tendsto.comp (hylim.prodMk_nhds hxlim)
  have hroot : H (planePoint ys xs) = 0 := by
    have h2 : Tendsto (fun n => H (planePoint (y (φ n)) (x (φ n)))) atTop (𝓝 0) := by
      have hfun : (fun n => H (planePoint (y (φ n)) (x (φ n)))) = fun n => s (φ n) :=
        funext fun n => hys (φ n)
      rw [hfun]
      exact hslim
    exact tendsto_nhds_unique hHlim h2
  -- the limit root is simple
  obtain ⟨Z₀, hZ₀, hZ₀r, hZ₀fin, -⟩ := hroots xs (hxs_norm ▸ hrη) 0 (by rw [norm_zero]; linarith)
  have hys0 : ys ∈ Z₀ := (hZ₀ ys hys_norm).mp hroot
  have hysρ : ‖ys‖ < ρ / 2 := hZ₀r ys hys0
  have hρpos : 0 < ρ := hr.trans hrρ
  have hw0 : planePoint ys xs ≠ 0 := by
    intro h
    have h1 : xs = 0 := by simpa [planePoint] using congrFun h 1
    rw [h1, norm_zero] at hxs_norm
    linarith
  have hwρ : ‖planePoint ys xs‖ < ρ := by
    rw [norm_planePoint]
    exact max_lt (by linarith) (by rw [hxs_norm]; exact hrρ)
  have hfd := fibreDerivative_ne_zero_of_curve hreg hρ hram hwρ hw0 hroot
    (by simpa using hZ₀fin ys hys0)
  have hord1 : rootOrder H 0 ys xs = 1 :=
    rootOrder_eq_one_of_fibreDerivative_ne_zero hanw hroot hfd
  have hΦ : AnalyticAt ℂ (rootFamily H) (![xs, 0], ys) :=
    analyticAt_rootFamily (by simpa using hanw)
  have hord : analyticOrderAt (fun z => rootFamily H (![xs, 0], z)) ys = ((1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_one, ← hord1]
    rfl
  obtain ⟨ρ', hρ', -, hev⟩ := exists_local_root_count (rootFamily H) ![xs, 0] ys hΦ 1 hord 1
    one_pos
  have hqlim : Tendsto (fun n => (![x (φ n), s (φ n)] : Fin 2 → ℂ)) atTop (𝓝 ![xs, 0]) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simpa using hxlim
    · simpa using hslim
  have hball1 : ∀ᶠ n in atTop, y (φ n) ∈ closedBall ys ρ' := hylim (closedBall_mem_nhds ys hρ')
  have hball2 : ∀ᶠ n in atTop, y' (φ n) ∈ closedBall ys ρ' :=
    hy'lim (closedBall_mem_nhds ys hρ')
  obtain ⟨n, hn1, hn2, hn3⟩ := ((hqlim.eventually hev).and (hball1.and hball2)).exists
  obtain ⟨Z, hZ, -, hZan, hZfin, hZsum⟩ := hn1
  set q : Fin 2 → ℂ := ![x (φ n), s (φ n)] with hq
  have hrootq : ∀ w : ℂ, H (planePoint w (x (φ n))) = s (φ n) → rootFamily H (q, w) = 0 := by
    intro w hw
    rw [hq, rootFamily_apply, hw, sub_self]
  have hyZ : y (φ n) ∈ Z := (hZ _ hn2).mp (hrootq _ (hys (φ n)))
  have hy'Z : y' (φ n) ∈ Z := (hZ _ hn3).mp (hrootq _ (hy's (φ n)))
  have hge : ∀ w, w ∈ closedBall ys ρ' → rootFamily H (q, w) = 0 → w ∈ Z →
      1 ≤ (analyticOrderAt (fun v => rootFamily H (q, v)) w).toNat := by
    intro w hwb hw0' hwZ
    have hne0 : analyticOrderAt (fun v => rootFamily H (q, v)) w ≠ 0 := by
      rw [analyticOrderAt_ne_zero]
      exact ⟨hZan w hwb, hw0'⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [ENat.toNat_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hne0 h0
    · exact hZfin w hwZ h0
  have h1 := hge _ hn2 (hrootq _ (hys (φ n))) hyZ
  have h2 := hge _ hn3 (hrootq _ (hy's (φ n))) hy'Z
  have hpair : ({y (φ n), y' (φ n)} : Finset ℂ) ⊆ Z := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hyZ
    · rw [Finset.mem_singleton.mp hw]
      exact hy'Z
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun z => (analyticOrderAt (fun v => rootFamily H (q, v)) z).toNat) hpair
  rw [Finset.sum_pair (hne (φ n)), hZsum] at hsum
  omega

end OnLeConjecture.Analytic
