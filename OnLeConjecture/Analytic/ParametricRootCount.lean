/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.OpenAIMath.HolomorphicAlgebraicity.WeierstrassPreparation

/-!
# Conservation of zeros in analytic families of one variable

Let `Φ(y, z)` be analytic near `(x, c)` and suppose that `z ↦ Φ(x, z)` has a
zero of finite order `e` at `c`. For every sufficiently small disc around
`c` and every parameter `y` near `x`, the zeros of `z ↦ Φ(y, z)` in the
closed disc form a finite set contained in the open disc, and their orders
add up to `e`.

The proof uses the polynomial preparation of holomorphic families vendored
from openai/math: near `x`, each fibre is a monic polynomial of fixed degree
times a nonvanishing analytic function on the closed disc.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open Filter Metric _root_.Polynomial
open scoped Topology
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.WeierstrassPreparation

/-- The analytic order of a polynomial times a nonvanishing analytic
function is the root multiplicity. -/
theorem analyticOrderAt_polynomial_mul {P : ℂ[X]} (hP : P ≠ 0) {u : ℂ → ℂ} {z : ℂ}
    (hu : AnalyticAt ℂ u z) (huz : u z ≠ 0) :
    analyticOrderAt (fun w => P.eval w * u w) z = P.rootMultiplicity z := by
  have hfactor := pow_mul_divByMonic_rootMultiplicity_eq P z
  have hR := eval_divByMonic_pow_rootMultiplicity_ne_zero z hP
  set R := P /ₘ (X - C z) ^ P.rootMultiplicity z
  have hanP : AnalyticAt ℂ (fun w => P.eval w) z :=
    AnalyticOnNhd.eval_polynomial P z (Set.mem_univ z)
  have hanR : AnalyticAt ℂ (fun w => R.eval w) z :=
    AnalyticOnNhd.eval_polynomial R z (Set.mem_univ z)
  have han : AnalyticAt ℂ (fun w => P.eval w * u w) z := hanP.mul hu
  rw [han.analyticOrderAt_eq_natCast]
  refine ⟨fun w => R.eval w * u w, hanR.mul hu, mul_ne_zero hR huz, ?_⟩
  filter_upwards with w
  have h := congrArg (fun Q : ℂ[X] => Q.eval w) hfactor
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
  rw [smul_eq_mul, ← h]
  ring

theorem sum_rootMultiplicity_roots_toFinset (P : ℂ[X]) :
    ∑ c ∈ P.roots.toFinset, P.rootMultiplicity c = P.natDegree := by
  classical
  simp_rw [← count_roots]
  rw [Multiset.sum_count_eq_card (fun c hc => Multiset.mem_toFinset.mpr hc)]
  exact IsAlgClosed.card_roots_eq_natDegree

/-- **Conservation of zeros in a one-variable analytic family.** -/
theorem exists_local_root_count {n : ℕ} (Φ : (Fin n → ℂ) × ℂ → ℂ) (x : Fin n → ℂ) (c : ℂ)
    (hΦ : AnalyticAt ℂ Φ (x, c)) (e : ℕ)
    (hord : analyticOrderAt (fun z => Φ (x, z)) c = e) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧ ∀ᶠ y in 𝓝 x, ∃ Z : Finset ℂ,
      (∀ z ∈ closedBall c ρ, Φ (y, z) = 0 ↔ z ∈ Z) ∧ (∀ z ∈ Z, z ∈ ball c ρ) ∧
      (∀ z ∈ closedBall c ρ, AnalyticAt ℂ (fun w => Φ (y, w)) z) ∧
      (∀ z ∈ Z, analyticOrderAt (fun w => Φ (y, w)) z ≠ ⊤) ∧
      ∑ z ∈ Z, (analyticOrderAt (fun w => Φ (y, w)) z).toNat = e := by
  classical
  -- a product neighbourhood on which `Φ` is analytic
  have hopen := isOpen_analyticAt ℂ Φ
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hopen (x, c) hΦ
  -- isolated zero of the central fibre
  have hslice : AnalyticAt ℂ (fun z => Φ (x, z)) c :=
    hΦ.comp (analyticAt_const.prod analyticAt_id)
  have hnz : ∀ᶠ z in 𝓝[≠] c, Φ (x, z) ≠ 0 := by
    rcases hslice.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have htop := analyticOrderAt_eq_top.mpr h
      rw [hord] at htop
      exact ENat.natCast_ne_top e htop
    · exact h
  obtain ⟨r₂, hr₂, hr₂ne⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnz)
  set ρ := min (ρ₀ / 2) (min (r₁ / 2) (r₂ / 2)) with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρ₀ : ρ < ρ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρ₁ : ρ < r₁ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hρ₂ : ρ < r₂ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  let W : Set ((Fin n → ℂ) × ℂ) := ball x r₁ ×ˢ ball c r₁
  have hWo : IsOpen W := isOpen_ball.prod isOpen_ball
  have hWan : ∀ p ∈ W, AnalyticAt ℂ Φ p := fun p hp => hball (by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt hp.1 hp.2)
  have hdiff : DifferentiableOn ℂ Φ W := fun p hp =>
    (hWan p hp).differentiableAt.differentiableWithinAt
  have hbase : ∀ z ∈ closedBall c ρ, (x, z) ∈ W := fun z hz =>
    ⟨mem_ball_self hr₁, lt_of_le_of_lt (mem_closedBall.mp hz) hρ₁⟩
  have hsphere : ∀ z ∈ sphere c ρ, Φ (x, z) ≠ 0 := by
    intro z hz
    apply hr₂ne
    · rw [mem_sphere] at hz
      rw [hz]
      exact hρ₂
    · intro hzc
      rw [Set.mem_singleton_iff] at hzc
      rw [mem_sphere, hzc, dist_self] at hz
      exact hρpos.ne hz
  obtain ⟨d, U, P, hU, hxU, hUW, -, hdata⟩ :=
    Constructions.Preparation.exists_polynomial_preparation hWo hdiff hρpos hbase hsphere
  -- the central fibre determines the degree
  have hde : d = e := by
    obtain ⟨hmon, hdeg, hroots, u, hu, hun, hfu⟩ := hdata x hxU
    have hP0 : P x ≠ 0 := hmon.ne_zero
    have hcball : c ∈ closedBall c ρ := mem_closedBall_self hρpos.le
    have hordc : analyticOrderAt (fun z => Φ (x, z)) c = (P x).rootMultiplicity c := by
      rw [analyticOrderAt_congr (hfu c hcball)]
      exact analyticOrderAt_polynomial_mul hP0 (hu c hcball) (hun c hcball)
    have hsub : (P x).roots.toFinset ⊆ {c} := by
      intro r hr
      rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def] at hr
      have hrb := hroots r hr
      have hzero : Φ (x, r) = 0 := by
        rw [(hfu r (ball_subset_closedBall hrb)).eq_of_nhds, hr, zero_mul]
      by_contra hne
      exact hr₂ne (lt_trans hrb hρ₂) (fun h => hne (Finset.mem_singleton.mpr h)) hzero
    have hsum := sum_rootMultiplicity_roots_toFinset (P x)
    rw [Finset.sum_subset hsub (fun r _ hr => by
      rw [Multiset.mem_toFinset] at hr
      exact rootMultiplicity_eq_zero (fun h => hr ((mem_roots hP0).mpr h))),
      Finset.sum_singleton] at hsum
    rw [← hdeg, ← hsum]
    exact_mod_cast (hord.symm.trans hordc).symm
  refine ⟨ρ, hρpos, hρ₀, ?_⟩
  filter_upwards [hU.mem_nhds hxU] with y hy
  obtain ⟨hmon, hdeg, hroots, u, hu, hun, hfu⟩ := hdata y hy
  have hP0 : P y ≠ 0 := hmon.ne_zero
  have hyan : ∀ z ∈ closedBall c ρ, AnalyticAt ℂ (fun w => Φ (y, w)) z := fun z hz =>
    (hWan _ (hUW ⟨hy, hz⟩)).comp (analyticAt_const.prod analyticAt_id)
  refine ⟨(P y).roots.toFinset, ?_, ?_, hyan, ?_, ?_⟩
  · intro z hz
    rw [(hfu z hz).eq_of_nhds, mul_eq_zero, or_iff_left (hun z hz), Multiset.mem_toFinset,
      mem_roots hP0, IsRoot.def]
  · intro z hz
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def] at hz
    exact hroots z hz
  · intro z hz
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def] at hz
    have hzb := ball_subset_closedBall (hroots z hz)
    rw [analyticOrderAt_congr (hfu z hzb), analyticOrderAt_polynomial_mul hP0 (hu z hzb)
      (hun z hzb)]
    exact ENat.natCast_ne_top _
  · rw [← hde, ← hdeg, ← sum_rootMultiplicity_roots_toFinset (P y)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def] at hz
    have hzb := ball_subset_closedBall (hroots z hz)
    rw [analyticOrderAt_congr (hfu z hzb), analyticOrderAt_polynomial_mul hP0 (hu z hzb)
      (hun z hzb), ENat.toNat_natCast]

/-- Zeros of nearby fibres concentrate at the centre: for every `ρ'`, the
zeros in the disc of radius `ρ` lie in the disc of radius `ρ'` for all
parameters close enough to `x`. -/
theorem exists_local_root_count_shrink {n : ℕ} (Φ : (Fin n → ℂ) × ℂ → ℂ) (x : Fin n → ℂ)
    (c : ℂ) (hΦ : AnalyticAt ℂ Φ (x, c)) (e : ℕ)
    (hord : analyticOrderAt (fun z => Φ (x, z)) c = e) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧ (∀ᶠ y in 𝓝 x, ∃ Z : Finset ℂ,
      (∀ z ∈ closedBall c ρ, Φ (y, z) = 0 ↔ z ∈ Z) ∧ (∀ z ∈ Z, z ∈ ball c ρ) ∧
      (∀ z ∈ closedBall c ρ, AnalyticAt ℂ (fun w => Φ (y, w)) z) ∧
      (∀ z ∈ Z, analyticOrderAt (fun w => Φ (y, w)) z ≠ ⊤) ∧
      ∑ z ∈ Z, (analyticOrderAt (fun w => Φ (y, w)) z).toNat = e) ∧
      ∀ ρ' > 0, ∀ᶠ y in 𝓝 x, ∀ z ∈ closedBall c ρ, Φ (y, z) = 0 → z ∈ ball c ρ' := by
  classical
  obtain ⟨ρ, hρ, hρρ₀, hcount⟩ := exists_local_root_count Φ x c hΦ e hord ρ₀ hρ₀
  refine ⟨ρ, hρ, hρρ₀, hcount, fun ρ' hρ' => ?_⟩
  obtain ⟨ρ₂, hρ₂, hρ₂lt, hcount₂⟩ :=
    exists_local_root_count Φ x c hΦ e hord (min ρ' ρ) (lt_min hρ' hρ)
  filter_upwards [hcount, hcount₂] with y hy hy₂
  obtain ⟨Z, hZ, hZb, hZan, hZfin, hZsum⟩ := hy
  obtain ⟨Z₂, hZ₂, hZ₂b, -, -, hZ₂sum⟩ := hy₂
  intro z hz hzero
  have hρ₂ρ : ρ₂ ≤ ρ := (le_of_lt hρ₂lt).trans (min_le_right _ _)
  have hsub : Z₂ ⊆ Z := by
    intro w hw
    have hwb := hZ₂b w hw
    have hwc : w ∈ closedBall c ρ :=
      ball_subset_closedBall (ball_subset_ball hρ₂ρ hwb)
    exact (hZ w hwc).mp ((hZ₂ w (ball_subset_closedBall hwb)).mpr hw)
  by_contra hzout
  have hzZ : z ∈ Z := (hZ z hz).mp hzero
  have hzZ₂ : z ∉ Z₂ := fun h =>
    hzout (ball_subset_ball ((le_of_lt hρ₂lt).trans (min_le_left _ _)) (hZ₂b z h))
  have hpos : 1 ≤ (analyticOrderAt (fun w => Φ (y, w)) z).toNat := by
    have hne0 : analyticOrderAt (fun w => Φ (y, w)) z ≠ 0 := by
      rw [Ne, (hZan z hz).analyticOrderAt_eq_zero, not_not]
      exact hzero
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hZfin z hzZ)
    rw [← hk] at hne0 ⊢
    rw [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  have hsplit := Finset.sum_sdiff (f := fun w => (analyticOrderAt (fun w' => Φ (y, w')) w).toNat)
    hsub
  have hsingle := Finset.single_le_sum (f := fun w =>
    (analyticOrderAt (fun w' => Φ (y, w')) w).toNat) (fun _ _ => Nat.zero_le _)
    (Finset.mem_sdiff.mpr ⟨hzZ, hzZ₂⟩)
  omega

end OnLeConjecture.Analytic
