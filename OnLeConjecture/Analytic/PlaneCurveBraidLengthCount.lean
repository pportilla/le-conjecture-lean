/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WindingNumberArgument
public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingFinite
public import OnLeConjecture.Analytic.PlaneBranchBraidMonodromy

/-!
# Counting projected branch crossings by vanishing orders

Let `F` be an analytic branch representative with `F z i = z ^ a` on a disc of
radius `R`, and suppose every nontrivial sheet difference
`h_ζ(z) = F(ζ z)_{i.rev} - F(z)_{i.rev}` has positive angular logarithmic
derivative on the punctured disc. On a source circle of radius `r < R`, a
projected coincidence of the ordered sheets `l + m` and `l` at base angle `t`
is a zero of the real part of `c h_ζ` at the source angle `t + 2π l`, where
`ζ = ω^m` and `ω = e^{2πi/a}`. As `l` runs over all sheets and `t` over one base
period, the source angle runs once over the whole source circle.

On the whole source circle, the continuous argument of `c h_ζ` is strictly
increasing and increases by `2π` times the winding number. Therefore the real
part vanishes exactly twice the winding number times. The local argument
principle identifies that winding number with the vanishing order of `h_ζ`.

Counting each unordered coincident pair once over the ordered events of one base
period gives
`∑ events #(coincident unordered pairs) = ∑_{m ≠ 0} ord₀ h_{ω^m}`.
This is the exact length formula of the canonical positive event words, so no
event resolution or general-position argument is needed.
-/

@[expose] public noncomputable section

open Set Filter Topology Real Metric

namespace OnLeConjecture.Analytic

/-! ### Elementary identities for the source circle -/

theorem planeBranchAngularParameter_add_two_pi_mul {a : ℕ} (ha : 0 < a) (r θ : ℝ) :
    planeBranchAngularParameter a r (θ + 2 * π * a) = planeBranchAngularParameter a r θ := by
  unfold planeBranchAngularParameter
  congr 1
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [show (((θ + 2 * π * a : ℝ) : ℂ) / (a : ℂ)) * Complex.I =
      ((θ : ℂ) / a) * Complex.I + 2 * π * Complex.I by
    push_cast
    field_simp]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem planeBranchAngularParameter_eq_circlePath (a : ℕ) (r θ : ℝ) :
    planeBranchAngularParameter a r θ = circlePath r (θ / a) := by
  simp only [planeBranchAngularParameter, circlePath]
  push_cast
  ring_nf

theorem planeBranchBraidRoot_add {a : ℕ} (ha : 0 < a) [NeZero a] (l m : Fin a) :
    planeBranchBraidRoot a (l + m) = planeBranchBraidRoot a l * planeBranchBraidRoot a m := by
  have hω := (Complex.isPrimitiveRoot_exp a ha.ne').pow_eq_one
  unfold planeBranchBraidRoot
  rw [Fin.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (l.val + m.val) a, pow_add, pow_mul, hω, one_pow, mul_one]

theorem planeBranchBraidRoot_pow_eq_one {a : ℕ} (ha : 0 < a) (m : Fin a) :
    planeBranchBraidRoot a m ^ a = 1 :=
  planeBranchBraidRoot_pow ha m

theorem planeBranchBraidRoot_ne_one {a : ℕ} [NeZero a] {m : Fin a} (hm : m ≠ 0) :
    planeBranchBraidRoot a m ≠ 1 := by
  intro h
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have h0 : planeBranchBraidRoot a 0 = 1 := by
    simp [planeBranchBraidRoot]
  exact hm (planeBranchBraidRoot_injective ha (h.trans h0.symm))

/-! ### The zero count of one sheet difference on the whole source circle -/

/-- On the whole source circle the projected real part of one nontrivial
sheet difference vanishes exactly twice its vanishing order times. -/
theorem planeBranchAngularDifference_re_zero_finite_ncard
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hrot : ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ z ∈ ball (0 : ℂ) R, z ≠ 0 →
      planeBranchSheetDifference F i ζ z ≠ 0 ∧
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) {ζ : ℂ} (hζ : ζ ^ a = 1) (hζ1 : ζ ≠ 1)
    {c : ℂ} (hc : c ≠ 0) (b : ℝ) :
    ({s | s ∈ Ico b (b + 2 * π * a) ∧
        (c * planeBranchAngularDifference F i ζ a r s).re = 0} : Set ℝ).Finite ∧
    ({s | s ∈ Ico b (b + 2 * π * a) ∧
        (c * planeBranchAngularDifference F i ζ a r s).re = 0} : Set ℝ).ncard =
      2 * analyticOrderNatAt (planeBranchSheetDifference F i ζ) 0 := by
  set h := planeBranchSheetDifference F i ζ with hh
  set p := planeBranchAngularParameter a r with hp
  have hpnorm : ∀ s, ‖p s‖ = r := fun s => by
    simp only [hp, planeBranchAngularParameter_norm, abs_of_pos hr]
  have hpball : ∀ s, p s ∈ ball (0 : ℂ) R := fun s => by
    rw [mem_ball, dist_zero_right, hpnorm]
    exact hrR
  have hpne : ∀ s, p s ≠ 0 := fun s h0 => by
    have := hpnorm s
    rw [h0, norm_zero] at this
    exact hr.ne this
  have hhan : ∀ z ∈ ball (0 : ℂ) R, AnalyticAt ℂ h z := fun z hz =>
    planeBranchSheetDifference_analyticAt_of_mem_ball hF i ha hζ hz
  let γ : ℝ → ℂ := fun s => c * planeBranchAngularDifference F i ζ a r s
  have hγeq : ∀ s, γ s = c * h (p s) := fun s => rfl
  have hDd : ∀ s, HasDerivAt (fun t => h (p t)) (deriv (fun t => h (p t)) s) s := fun s =>
    ((hhan _ (hpball s)).differentiableAt.hasDerivAt.comp s
      (planeBranchAngularParameter_hasDerivAt a r s)).differentiableAt.hasDerivAt
  have hγd : ∀ s, HasDerivAt γ (c * deriv (fun t => h (p t)) s) s := fun s =>
    (hDd s).const_mul c
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγd s).continuousAt
  have hγne : ∀ s, γ s ≠ 0 := fun s =>
    mul_ne_zero hc (hrot ζ hζ hζ1 _ (hpball s) (hpne s)).1
  have hpos : ∀ s, 0 < ((c * deriv (fun t => h (p t)) s) / γ s).im := by
    intro s
    rw [hγeq, mul_div_mul_left _ _ hc]
    have him := im_logDeriv_comp_planeBranchAngularParameter (d := h) a r s
      (hhan _ (hpball s)).differentiableAt
    rw [him]
    exact div_pos (hrot ζ hζ hζ1 _ (hpball s) (hpne s)).2 (by exact_mod_cast ha)
  have hb : b ≤ b + 2 * π * a := by
    have : 0 ≤ 2 * π * a := by positivity
    linarith
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn (u := b) (v := b + 2 * π * a)
    hγcont.continuousOn (fun s _ => hγne s)
  have hmono := hL.strictMonoOn_im (fun s _ => ⟨_, hγd s, hpos s⟩)
  have hloop : γ b = γ (b + 2 * π * a) := by
    simp only [γ, planeBranchAngularDifference, planeBranchAngularParameter_add_two_pi_mul ha]
  obtain ⟨_, hfin, hcard⟩ := hL.ncard_re_eq_zero hb hmono hloop
  refine ⟨hfin, ?_⟩
  rw [hcard]
  have hcomp : (fun s => h (p s)) = (fun θ => h (circlePath r θ)) ∘ (fun s => s / (a : ℝ)) :=
    funext fun s => by
      simp only [Function.comp_apply, hp, planeBranchAngularParameter_eq_circlePath]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hcircle_ball : ∀ θ, circlePath r θ ∈ ball (0 : ℂ) R := by
    intro θ
    rw [mem_ball, dist_zero_right, norm_circlePath hr.le]
    exact hrR
  have hcircle_ne : ∀ θ, circlePath r θ ≠ 0 := by
    intro θ h0
    have := norm_circlePath hr.le θ
    rw [h0, norm_zero] at this
    exact hr.ne this
  have hγcirc : Continuous (fun θ => h (circlePath r θ)) :=
    ContinuousOn.comp_continuous (fun z hz => (hhan z hz).continuousAt.continuousWithinAt)
      (continuous_circlePath r) hcircle_ball
  have hwind_hp : windingNumber (fun s => h (p s)) b (b + 2 * π * a) =
      windingNumber (fun θ => h (circlePath r θ)) (b / a) (b / a + 2 * π) := by
    unfold windingNumber
    rw [hcomp, argChange_comp (u := b / a) (v := b / a + 2 * π) (u' := b)
      (v' := b + 2 * π * a) (φ := fun s => s / (a : ℝ))
      (by linarith [Real.pi_pos]) hγcirc.continuousOn
      (fun θ _ => (hrot ζ hζ hζ1 _ (hcircle_ball θ) (hcircle_ne θ)).1) hb
      (by fun_prop)]
    · intro s hs
      constructor
      · exact div_le_div_of_nonneg_right hs.1 ha'.le
      · rw [show b / a + 2 * π = (b + 2 * π * a) / a by field_simp]
        exact div_le_div_of_nonneg_right hs.2 ha'.le
    · rfl
    · field_simp
  have hcont_hp : ContinuousOn (fun s => h (p s)) (Icc b (b + 2 * π * a)) :=
    (continuous_iff_continuousAt.mpr fun s => (hDd s).continuousAt).continuousOn
  have hne_hp : ∀ s ∈ Icc b (b + 2 * π * a), h (p s) ≠ 0 :=
    fun s _ => (hrot ζ hζ hζ1 _ (hpball s) (hpne s)).1
  have hloop_hp : h (p b) = h (p (b + 2 * π * a)) := by
    rw [hp, planeBranchAngularParameter_add_two_pi_mul ha]
  have hwind : windingNumber γ b (b + 2 * π * a) = analyticOrderNatAt h 0 := by
    calc windingNumber γ b (b + 2 * π * a)
        = windingNumber (fun s => c * h (p s)) b (b + 2 * π * a) := rfl
      _ = windingNumber (fun s => h (p s)) b (b + 2 * π * a) :=
          windingNumber_const_mul hb hcont_hp hne_hp hloop_hp hc
      _ = windingNumber (fun θ => h (circlePath r θ)) (b / a) (b / a + 2 * π) := hwind_hp
      _ = analyticOrderNatAt h 0 :=
          windingNumber_circlePath_eq_analyticOrderNatAt (fun z hz => hhan z hz)
            (fun z hz hz0 => (hrot ζ hζ hζ1 z hz hz0).1) hr hrR (b / a)
  rw [hwind]
  simp

/-! ### Reorganizing the coincident pairs of the events -/

/-- Every unordered pair of distinct labels is counted twice among ordered
pairs. Relabelling by a permutation does not change the count. -/
theorem two_mul_card_filter_lt_perm {a : ℕ} (Q : Fin a → Fin a → Prop) [DecidableRel Q]
    (hQ : ∀ k l, Q k l → Q l k) (σ : Equiv.Perm (Fin a)) :
    2 * (Finset.univ.filter fun p : Fin a × Fin a => p.1 < p.2 ∧ Q (σ p.1) (σ p.2)).card =
      (Finset.univ.filter fun p : Fin a × Fin a => p.1 ≠ p.2 ∧ Q p.1 p.2).card := by
  classical
  set A := Finset.univ.filter fun p : Fin a × Fin a => p.1 < p.2 ∧ Q (σ p.1) (σ p.2)
  set B := Finset.univ.filter fun p : Fin a × Fin a => p.2 < p.1 ∧ Q (σ p.1) (σ p.2)
  have hAB : A.card = B.card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · intro p hp
      simp only [A, B, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨hp.1, hQ _ _ hp.2⟩
    · intro p hp
      simp only [A, B, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨hp.1, hQ _ _ hp.2⟩
    · intro p _
      simp
    · intro p _
      simp
  have hunion : (Finset.univ.filter fun p : Fin a × Fin a =>
      p.1 ≠ p.2 ∧ Q (σ p.1) (σ p.2)) = A ∪ B := by
    ext p
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hne, hq⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, hq⟩
      · exact Or.inr ⟨h, hq⟩
    · rintro (⟨h, hq⟩ | ⟨h, hq⟩)
      · exact ⟨h.ne, hq⟩
      · exact ⟨h.ne', hq⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1.1 h2.1
  have hσ : (Finset.univ.filter fun p : Fin a × Fin a =>
      p.1 ≠ p.2 ∧ Q (σ p.1) (σ p.2)).card =
      (Finset.univ.filter fun p : Fin a × Fin a => p.1 ≠ p.2 ∧ Q p.1 p.2).card := by
    apply Finset.card_nbij' (fun p => (σ p.1, σ p.2)) (fun p => (σ.symm p.1, σ.symm p.2))
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨fun h => hp.1 (σ.injective h), hp.2⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Equiv.apply_symm_apply] at hp ⊢
      exact ⟨fun h => hp.1 (σ.symm.injective h), hp.2⟩
    · intro p _
      simp
    · intro p _
      simp
  rw [← hσ, hunion, Finset.card_union_of_disjoint hdisj, ← hAB]
  ring

/-- A sum over an enumeration of a finite set by its sorted list. -/
theorem sum_fin_eq_sum_finset_of_ofFn_eq_sort {N : ℕ} {event : Fin N → ℝ} {E : Finset ℝ}
    (henum : List.ofFn event = E.sort (· ≤ ·)) (g : ℝ → ℕ) :
    ∑ j : Fin N, g (event j) = ∑ t ∈ E, g t := by
  have h1 : ∑ j : Fin N, g (event j) = ((List.ofFn event).map g).sum := by
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  rw [h1, henum, Finset.sum_eq_multiset_sum, ← Finset.sort_eq E (· ≤ ·), Multiset.map_coe,
    Multiset.sum_coe]

/-- A projected coincidence of the sheets `l + m` and `l` is a zero of the
projected sheet difference for `ω^m` at the source angle `t + 2π l`. -/
theorem planeBranch_sheet_re_eq_iff (F : ℂ → Source 2) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    [NeZero a] (r : ℝ) (c : ℂ) (l m : Fin a) (t : ℝ) :
    (c * planeBranchBraidSheet F i a r (l + m) t).re =
        (c * planeBranchBraidSheet F i a r l t).re ↔
      (c * planeBranchAngularDifference F i (planeBranchBraidRoot a m) a r
        (t + 2 * π * l.val)).re = 0 := by
  have hpair := planeBranchBraidPairDifference_eq_angularDifference F i a r (l + m) l t
  rw [planeBranchBraidRoot_add ha,
    mul_div_cancel_left₀ _ (planeBranchBraidRoot_ne_zero a l)] at hpair
  rw [← hpair, planeBranchBraidPairDifference, mul_sub, Complex.sub_re, sub_eq_zero]

/-- The coincident pairs of all events of one base period, counted twice,
are the zeros of the projected sheet differences on the whole source circle. -/
theorem two_mul_sum_event_pair_card_eq
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} [NeZero a] (ha : 0 < a) {r : ℝ} {c : ℂ} {b : ℝ}
    {E : Finset ℝ}
    (hE : ∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c b (b + 2 * π))
    (hdE : b + 2 * π ∉ E)
    {N : ℕ} {event : Fin N → ℝ} (henum : List.ofFn event = E.sort (· ≤ ·))
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) :
    2 * ∑ j : Fin N, (Finset.univ.filter fun p : Fin a × Fin a =>
        p.1 < p.2 ∧ (c * planeBranchBraidSheet F i a r (σ j.succ p.1) (event j)).re =
          (c * planeBranchBraidSheet F i a r (σ j.succ p.2) (event j)).re).card =
      ∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0),
        ({s | s ∈ Ico b (b + 2 * π * a) ∧
          (c * planeBranchAngularDifference F i (planeBranchBraidRoot a m) a r s).re = 0} :
            Set ℝ).ncard := by
  classical
  let K : Fin a → ℝ → ℂ := fun k t => c * planeBranchBraidSheet F i a r k t
  let O : ℝ → ℕ := fun t => (Finset.univ.filter fun p : Fin a × Fin a =>
    p.1 ≠ p.2 ∧ (K p.1 t).re = (K p.2 t).re).card
  have h1 : 2 * ∑ j : Fin N, (Finset.univ.filter fun p : Fin a × Fin a =>
        p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re = (K (σ j.succ p.2) (event j)).re).card =
      ∑ j : Fin N, O (event j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    convert two_mul_card_filter_lt_perm (fun k l => (K k (event j)).re = (K l (event j)).re)
      (fun k l h => h.symm) (σ j.succ)
  change 2 * ∑ j : Fin N, (Finset.univ.filter fun p : Fin a × Fin a =>
        p.1 < p.2 ∧ (K (σ j.succ p.1) (event j)).re = (K (σ j.succ p.2) (event j)).re).card = _
  rw [h1, sum_fin_eq_sum_finset_of_ofFn_eq_sort henum O]
  have h2 : ∑ t ∈ E, O t = ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin a => p.1 ≠ p.2),
      (E.filter fun t => (K p.1 t).re = (K p.2 t).re).card := by
    simp only [O, Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.1 ≠ p.2
    · simp [hp]
    · simp [hp]
  rw [h2]
  have h3 : ∑ p ∈ Finset.univ.filter (fun p : Fin a × Fin a => p.1 ≠ p.2),
      (E.filter fun t => (K p.1 t).re = (K p.2 t).re).card =
      ∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0), ∑ l : Fin a,
        (E.filter fun t => (K (l + m) t).re = (K l t).re).card := by
    rw [← Finset.sum_product']
    apply Finset.sum_nbij' (fun p => (p.1 - p.2, p.2)) (fun x => (x.2 + x.1, x.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hp ⊢
      exact sub_ne_zero.mpr hp
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hx ⊢
      intro h
      exact hx (by simpa using h)
    · intro p _
      simp
    · intro x _
      simp
    · intro p _
      simp
  rw [h3]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hpos : 0 < 2 * π := by positivity
  rw [← Finset.card_sigma, ← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun x _ => x.2 + 2 * π * x.1.val)
  · rintro x hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_filter, Set.mem_ofPred_eq] at hx
    obtain ⟨hxE, hxQ⟩ := hx
    have hIcc := ((hE x.2).mp hxE).1
    have hne : x.2 ≠ b + 2 * π := fun h => hdE (h ▸ hxE)
    have hl : (x.1.val : ℝ) + 1 ≤ a := by exact_mod_cast x.1.isLt
    refine ⟨⟨?_, ?_⟩, (planeBranch_sheet_re_eq_iff F i ha r c x.1 m x.2).mp hxQ⟩
    · have : 0 ≤ 2 * π * (x.1.val : ℝ) := by positivity
      linarith [hIcc.1]
    · have hlt : x.2 < b + 2 * π := lt_of_le_of_ne hIcc.2 hne
      nlinarith [Real.pi_pos]
  · rintro x y hx hy hxy
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    have hxI := ((hE x.2).mp hx.1).1
    have hyI := ((hE y.2).mp hy.1).1
    have hxlt : x.2 < b + 2 * π := lt_of_le_of_ne hxI.2 (fun h => hdE (h ▸ hx.1))
    have hylt : y.2 < b + 2 * π := lt_of_le_of_ne hyI.2 (fun h => hdE (h ▸ hy.1))
    have h1' : (x.1.val : ℝ) < y.1.val + 1 := by
      by_contra hc
      push Not at hc
      nlinarith [hyI.1, hxI.1, Real.pi_pos]
    have h2' : (y.1.val : ℝ) < x.1.val + 1 := by
      by_contra hc
      push Not at hc
      nlinarith [hyI.1, hxI.1, Real.pi_pos]
    have hn1 : x.1.val < y.1.val + 1 := by exact_mod_cast h1'
    have hn2 : y.1.val < x.1.val + 1 := by exact_mod_cast h2'
    have hidx : x.1 = y.1 := Fin.ext (by omega)
    have hsnd : x.2 = y.2 := by
      have : (x.1.val : ℝ) = y.1.val := by rw [hidx]
      rw [this] at hxy
      linarith
    exact Sigma.ext hidx (heq_of_eq hsnd)
  · rintro s ⟨hs, hzero⟩
    set n := ⌊(s - b) / (2 * π)⌋₊ with hn
    have hq : 0 ≤ (s - b) / (2 * π) := div_nonneg (by linarith [hs.1]) hpos.le
    have hfl := Nat.floor_le hq
    have hfl' := Nat.lt_floor_add_one ((s - b) / (2 * π))
    have hqa : (s - b) / (2 * π) < a := by
      rw [div_lt_iff₀ hpos]
      nlinarith [hs.2]
    have hna : n < a := by
      have : (n : ℝ) < a := lt_of_le_of_lt hfl hqa
      exact_mod_cast this
    let l : Fin a := ⟨n, hna⟩
    let t := s - 2 * π * n
    have hfl2 : 2 * π * (n : ℝ) ≤ s - b := by
      rw [le_div_iff₀ hpos] at hfl
      linarith
    have hfl3 : s - b < 2 * π * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hpos] at hfl'
      linarith
    have ht : t + 2 * π * (l.val : ℝ) = s := by
      simp only [t, l]
      ring
    have htQ : (K (l + m) t).re = (K l t).re := by
      apply (planeBranch_sheet_re_eq_iff F i ha r c l m t).mpr
      rw [ht]
      exact hzero
    have htE : t ∈ E := by
      rw [hE, mem_planeBranchProjectedCrossingTimes_iff]
      refine ⟨⟨by simp only [t]; linarith, by simp only [t]; linarith⟩, l + m, l, ?_, htQ⟩
      intro h
      exact hm0 (by simpa using h)
    refine ⟨⟨l, t⟩, ?_, ht⟩
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, true_and,
      Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨htE, htQ⟩

/-- The exact length of the canonical event words of a branch: the number of
coincident unordered pairs over all events of one base period equals the sum of
the vanishing orders of the nontrivial sheet differences. -/
theorem sum_event_pair_card_eq_sum_analyticOrderNatAt
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} [NeZero a] (ha : 0 < a) {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hrot : ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ z ∈ ball (0 : ℂ) R, z ≠ 0 →
      planeBranchSheetDifference F i ζ z ≠ 0 ∧
      0 < (z * deriv (planeBranchSheetDifference F i ζ) z /
        planeBranchSheetDifference F i ζ z).re)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℂ} (hc : c ≠ 0) {b : ℝ} {E : Finset ℝ}
    (hE : ∀ t, t ∈ E ↔ t ∈ planeBranchProjectedCrossingTimes F i a r c b (b + 2 * π))
    (hdE : b + 2 * π ∉ E)
    {N : ℕ} {event : Fin N → ℝ} (henum : List.ofFn event = E.sort (· ≤ ·))
    (σ : Fin (N + 1) → Equiv.Perm (Fin a)) :
    ∑ j : Fin N, (Finset.univ.filter fun p : Fin a × Fin a =>
        p.1 < p.2 ∧ (c * planeBranchBraidSheet F i a r (σ j.succ p.1) (event j)).re =
          (c * planeBranchBraidSheet F i a r (σ j.succ p.2) (event j)).re).card =
      ∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0),
        analyticOrderNatAt (planeBranchSheetDifference F i (planeBranchBraidRoot a m)) 0 := by
  have hB := two_mul_sum_event_pair_card_eq ha hE hdE henum σ
  rw [Finset.sum_congr rfl fun m hm => (planeBranchAngularDifference_re_zero_finite_ncard ha hF
    hrot hr hrR (planeBranchBraidRoot_pow ha m)
    (planeBranchBraidRoot_ne_one (Finset.mem_filter.mp hm).2) hc b).2, ← Finset.mul_sum] at hB
  omega

end OnLeConjecture.Analytic
