/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveFullTwistBranches
public import OnLeConjecture.Analytic.ReducedCurveFullTwistGermBranch
public import OnLeConjecture.Analytic.ReducedCurveBranches

/-!
# The strict-transform sheets of a transverse reduced germ

Let `H` be analytic at `0 ∈ ℂ²` with reduced germ `f`, regular of order `S` in the first
coordinate `ζ` (`f(ζ, 0)` has order `S`) and of multiplicity at least `S` (`f ∈ 𝔪^S`). These are
the corrected hypotheses of record M405: together they say that `f` has multiplicity exactly
`S` and that the projection to the second coordinate `ξ` is transverse, `f_S(1, 0) ≠ 0`.

This module constructs sheet data `D : MultiSheetData S` (Lemma `J14:lem:common`) such that

* the monodromy of the sheets has exactly `irreducibleBranchCount f` cycles;
* for every small source radius `r`, the root strands `θ ↦ D.root 1 r k θ` are zeros of `H` over
  the base circle `ξ = r^q e^{iθ}`;
* the points of the root strands tend to the origin as `r → 0`.

The branches are the irreducible factors of `f`. Each branch is parametrized by an injective
intersection parametrization, normalized so that its second coordinate is `s^{a_j}` with
`a_j = i₀(ξ, f_j)`. The degrees add up to `i₀(ξ, f) = S`. Comparing the exact orders of the
factors with `f ∈ 𝔪^S` shows that every branch is transverse: its first coordinate has order at
least `a_j` (Lemma `J14:lem:slope`). Distinct branches meet only at the origin.
-/

@[expose] public noncomputable section

open Set Filter Metric Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve KnotTheory

/-- A function of order at least `a` at `0` is `s^a` times an analytic function on a disc. -/
theorem exists_pow_mul_of_le_analyticOrderAt {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) {a : ℕ}
    (ha : (a : ℕ∞) ≤ analyticOrderAt h 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (ball 0 ρ) ∧
      ∀ s ∈ ball (0 : ℂ) ρ, h s = s ^ a * v s := by
  rcases eq_or_ne (analyticOrderAt h 0) ⊤ with htop | htop
  · obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (analyticOrderAt_eq_top.mp htop)
    exact ⟨ρ, hρ, fun _ => 0, fun _ _ => analyticAt_const, fun s hs => by
      rw [hball hs, mul_zero]⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    obtain ⟨g, hg, -, hfac⟩ := hh.analyticOrderAt_eq_natCast.mp hn.symm
    obtain ⟨ρ₁, hρ₁, hρ₁g⟩ := hg.exists_ball_analyticOnNhd
    obtain ⟨ρ₂, hρ₂, hρ₂f⟩ := Metric.eventually_nhds_iff.mp hfac
    have han : a ≤ n := by
      have : (a : ℕ∞) ≤ n := hn ▸ ha
      exact_mod_cast this
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun s => s ^ (n - a) * g s, fun s hs =>
      (analyticAt_id.pow _).mul (hρ₁g s (ball_subset_ball (min_le_left _ _) hs)), ?_⟩
    intro s hs
    rw [hρ₂f (ball_subset_ball (min_le_right _ _) hs), sub_zero, smul_eq_mul, ← mul_assoc,
      ← pow_add, Nat.add_sub_cancel' han]

/-- A finite family of positive radii has a common positive lower bound. -/
theorem exists_pos_le_forall {b : ℕ} (ρ : Fin b → ℝ) (hρ : ∀ j, 0 < ρ j) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ j, ρ₀ ≤ ρ j := by
  classical
  refine ⟨(insert 1 (Finset.univ.image ρ)).min' (Finset.insert_nonempty _ _), ?_, fun j => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hρ j
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ j)))

/-! ### Reindexing sheet data -/

namespace MultiSheetData

variable {n m : ℕ}

/-- Sheet data relabelled along an equivalence of label sets. -/
def reindex (D : MultiSheetData n) (e : Fin n ≃ Fin m) : MultiSheetData m where
  q := D.q
  U k := D.U (e.symm k)
  R := D.R
  τ := e.symm.trans (D.τ.trans e)
  q_pos := D.q_pos
  R_pos := D.R_pos
  analytic k := D.analytic _
  distinct k l hkl := D.distinct _ _ fun h => hkl (e.symm.injective h)
  monodromy k t ht := by
    change D.U (e.symm k) _ = D.U (e.symm (e (D.τ (e.symm k)))) t
    rw [Equiv.symm_apply_apply, D.monodromy _ t ht]

theorem reindex_root (D : MultiSheetData n) (e : Fin n ≃ Fin m) (c : ℂ) (r : ℝ) (k : Fin m)
    (θ : ℝ) : (D.reindex e).root c r k θ = D.root c r (e.symm k) θ := rfl

theorem reindex_q (D : MultiSheetData n) (e : Fin n ≃ Fin m) : (D.reindex e).q = D.q := rfl

theorem reindex_R (D : MultiSheetData n) (e : Fin n ≃ Fin m) : (D.reindex e).R = D.R := rfl

theorem permCycleCount_reindex (D : MultiSheetData n) (e : Fin n ≃ Fin m) :
    permCycleCount (D.reindex e).τ = permCycleCount D.τ := by
  classical
  unfold permCycleCount
  let φ : Quotient (Equiv.Perm.SameCycle.setoid D.τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (D.reindex e).τ) :=
    Quotient.congr e fun x y => by
      change D.τ.SameCycle x y ↔ Equiv.Perm.SameCycle (e.permCongr D.τ) (e x) (e y)
      have hpow : ∀ k : ℕ, ((e.permCongr D.τ) ^ k) (e x) = e ((D.τ ^ k) x) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply,
            Equiv.permCongr_apply, Equiv.symm_apply_apply]
      constructor
      · intro h
        obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
        exact ⟨k, by rw [zpow_natCast, hpow, hk]⟩
      · intro h
        obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
        exact ⟨k, by rw [zpow_natCast]; exact e.injective (by rw [← hpow, hk])⟩
  exact (Fintype.card_congr φ).symm.trans (by convert rfl)

end MultiSheetData

/-! ### The sheets of a transverse reduced germ -/

/-- The sheet data of a factorization into transverse branches. -/
theorem exists_multiSheetData_of_factorization {b S : ℕ} (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (F : Fin b → Germ 2) (u : Germ 2) (hu : IsUnit u)
    (hfac : ofFunction H hH = u * ∏ i, F i) (hirr : ∀ i, Irreducible (F i))
    (hnass : ∀ i j, i ≠ j → ¬ Associated (F i) (F j))
    (hreg : IsRegularInFirstCoordinateOfOrder (u * ∏ i, F i) S)
    (hmult : u * ∏ i, F i ∈ maximalIdeal 2 ^ S) :
    ∃ D : MultiSheetData S,
      permCycleCount D.τ = b ∧
      (∀ r, 0 < r → r < D.R → ∀ k θ, H ![D.root 1 r k θ, circlePath (r ^ D.q) θ] = 0) ∧
      ∀ N ∈ 𝓝 (0 : Source 2), ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r, 0 < r → r < r₁ → ∀ k θ,
        ![D.root 1 r k θ, circlePath (r ^ D.q) θ] ∈ N := by
  classical
  set f := u * ∏ i, F i with hfdef
  choose W hW hWF using fun i => exists_ofFunction (F i)
  obtain ⟨Uf, hUf, huU⟩ := exists_ofFunction u
  -- Finite intersections with the axis `ξ = 0`.
  have hfinf : HasFiniteIntersection (coordinate (1 : Fin 2)) f :=
    hasFiniteIntersection_secondCoordinate_of_regular f S hreg
  have hfinuP : HasFiniteIntersection (coordinate (1 : Fin 2)) (u * ∏ i, F i) := hfinf
  have hfinu := ((hasFiniteIntersection_mul_right_iff _ _ _).mp hfinuP).1
  have hfinprod := ((hasFiniteIntersection_mul_right_iff _ _ _).mp hfinuP).2
  have hfinF : ∀ i, HasFiniteIntersection (coordinate (1 : Fin 2)) (F i) :=
    (hasFiniteIntersection_prod_iff _ F).mp hfinprod
  -- Power-normalized parametrizations of the branches.
  choose a G R ha hR hai hGan hGinj hG0 hGpow hGW hGord using
    fun i => exists_power_branch_parametrization (F i) (hirr i) (hfinF i)
  -- The degrees add up to `S`.
  have hsumA : ∑ i, a i = S := by
    have h1 := intersectionMultiplicity_secondCoordinate_of_regular f S hreg hfinf
    rw [intersectionMultiplicity_mul_right _ u _ hfinu hfinprod hfinuP,
      intersectionMultiplicity_eq_zero_of_isUnit_right _ u hu hfinu, zero_add,
      intersectionMultiplicity_prod _ F hfinprod hfinF] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => hai i
  -- Exact orders and transversality of every branch.
  choose m hm hmn using fun i => exists_exact_maximalIdeal_order_of_ne_zero (F i) (hirr i).ne_zero
  obtain ⟨-, hprodn⟩ := exact_maximalIdeal_order_prod F m hm hmn
  have hfn : f ∉ maximalIdeal 2 ^ (∑ i, m i + 1) := by
    have hu0 : u ∈ maximalIdeal 2 ^ 0 := by simp
    have hu1 : u ∉ maximalIdeal 2 ^ (0 + 1) := by
      rw [zero_add, pow_one, mem_maximalIdeal_iff]
      exact valueRingHom_ne_zero_of_isUnit hu
    have h := (exact_maximalIdeal_order_mul 0 (∑ i, m i) u (∏ i, F i) hu0 hu1
      (exact_maximalIdeal_order_prod F m hm hmn).1 hprodn).2
    rwa [zero_add] at h
  have hSle : S ≤ ∑ i, m i := by
    by_contra hlt
    exact hfn (Ideal.pow_le_pow_right (by omega) hmult)
  have hma : ∀ i, m i ≤ a i := by
    intro i
    have h := hGord i (m i) (hm i) (hmn i)
    have : ((m i : ℕ) : ℕ∞) ≤ a i := h ▸ min_le_right _ _
    exact_mod_cast this
  have hmeq : ∀ i, m i = a i := by
    have hsum : ∑ i, m i = ∑ i, a i :=
      le_antisymm (Finset.sum_le_sum fun i _ => hma i) (hsumA ▸ hSle)
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hma i)).mp hsum i (Finset.mem_univ i)
  have hord : ∀ i, (a i : ℕ∞) ≤ analyticOrderAt (fun z => G i z 0) 0 := by
    intro i
    have h := hGord i (m i) (hm i) (hmn i)
    rw [hmeq i] at h
    exact min_eq_right_iff.mp h
  have hG0an : ∀ i, AnalyticAt ℂ (fun z => G i z 0) 0 :=
    fun i => analyticAt_pi_iff.mp (hGan i 0 (mem_ball_self (hR i))) 0
  choose ρv hρv v hv hfacv using fun i => exists_pow_mul_of_le_analyticOrderAt (hG0an i) (hord i)
  -- The function-level factorization of `H` and the separation of the branches.
  have hirrW : ∀ i, Irreducible (ofFunction (W i) (hW i)) := fun i => hWF i ▸ hirr i
  have hH1 : ∀ᶠ z in 𝓝 (0 : Source 2), H z = Uf z * ∏ i, W i z := by
    have hQ : AnalyticAt ℂ (fun z => ∏ i, W i z) 0 :=
      Finset.univ.analyticAt_fun_prod fun i _ => hW i
    have hQgerm : ofFunction (fun z => ∏ i, W i z) hQ = ∏ i, ofFunction (W i) (hW i) := by
      apply Subtype.ext
      change (Filter.Germ.coeRingHom (𝓝 (0 : Source 2))) (fun z => ∏ i, W i z) =
        (analyticGermSubring 2).subtype (∏ i, ofFunction (W i) (hW i))
      have hQfun : (fun z => ∏ i, W i z) = ∏ i, W i := by ext z; simp [Finset.prod_apply]
      rw [hQfun, map_prod, map_prod]
      rfl
    have hfactor : ofFunction H hH = ofFunction (fun z => Uf z * ∏ i, W i z) (hUf.mul hQ) := by
      change ofFunction H hH = ofFunction Uf hUf * ofFunction (fun z => ∏ i, W i z) hQ
      rw [hQgerm, ← huU, hfac, hfdef]
      congr 1
      exact Finset.prod_congr rfl fun i _ => hWF i
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hfactor)
  have hH2 : ∀ᶠ z in 𝓝 (0 : Source 2), ∀ i j, i ≠ j → W i z = 0 → W j z = 0 → z = 0 := by
    have hpair (i j : Fin b) : ∀ᶠ z in 𝓝 (0 : Source 2),
        i ≠ j → W i z = 0 → W j z = 0 → z = 0 := by
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · exact (Germ.eventually_common_zero_imp_eq_zero_of_nonassociated (W i) (W j) (hW i) (hW j)
          (hirrW i) (hirrW j) (by rw [← hWF, ← hWF]; exact hnass i j hij)).mono
            fun _ hz _ => hz
    exact Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)
  set N : Set (Source 2) := {z | H z = Uf z * ∏ i, W i z ∧
    ∀ i j, i ≠ j → W i z = 0 → W j z = 0 → z = 0} with hNdef
  have hN : N ∈ 𝓝 (0 : Source 2) := hH1.and hH2
  -- A common radius for all branches.
  have hrad : ∀ i, ∃ r : ℝ, 0 < r ∧ ∀ s ∈ ball (0 : ℂ) r, s ∈ ball (0 : ℂ) (R i) ∧
      s ∈ ball (0 : ℂ) (ρv i) ∧ G i s ∈ N ∧ W i (G i s) = 0 := by
    intro i
    have hcont : ContinuousAt (G i) 0 := (hGan i 0 (mem_ball_self (hR i))).continuousAt
    have hGN : ∀ᶠ s in 𝓝 (0 : ℂ), G i s ∈ N := by
      have := hcont.tendsto
      rw [hG0 i] at this
      exact this hN
    have hb1 : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ ball (0 : ℂ) (R i) := ball_mem_nhds _ (hR i)
    have hb2 : ∀ᶠ s in 𝓝 (0 : ℂ), s ∈ ball (0 : ℂ) (ρv i) := ball_mem_nhds _ (hρv i)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
      ((hb1.and hb2).and (hGN.and (hGW i (W i) (hW i) (hWF i).symm)))
    exact ⟨r, hr, fun s hs => ⟨(hball hs).1.1, (hball hs).1.2, (hball hs).2.1, (hball hs).2.2⟩⟩
  choose rad hrad hradspec using hrad
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_forall rad hrad
  have hinball : ∀ i, ∀ s ∈ ball (0 : ℂ) ρ, s ∈ ball (0 : ℂ) (rad i) :=
    fun i s hs => ball_subset_ball (hρle i) hs
  -- The point of branch `i` with parameter `s`.
  have hpoint : ∀ i, ∀ s ∈ ball (0 : ℂ) ρ, G i s = ![s ^ a i * v i s, s ^ a i] := by
    intro i s hs
    have h := hradspec i s (hinball i s hs)
    funext c
    fin_cases c
    · simp [hfacv i s h.2.1]
    · simp [hGpow i s h.1]
  -- The transverse branch data.
  let B : TransverseBranchData b :=
    { a := a
      v := v
      ρ := ρ
      a_pos := ha
      ρ_pos := hρ
      analytic := fun i s hs => hv i s (hradspec i s (hinball i s hs)).2.1
      separated := by
        intro j j' s s' hs hs' hs0 hpow hfirst
        have heq : G j s = G j' s' := by
          rw [hpoint j s hs, hpoint j' s' hs', hfirst, hpow]
        by_cases hjj : j = j'
        · subst hjj
          exact ⟨rfl, hGinj j (hradspec j s (hinball j s hs)).1
            (hradspec j s' (hinball j s' hs')).1 heq⟩
        · exfalso
          have hzN := (hradspec j s (hinball j s hs)).2.2.1
          have hz0 := hzN.2 j j' hjj (hradspec j s (hinball j s hs)).2.2.2
            (by rw [heq]; exact (hradspec j' s' (hinball j' s' hs')).2.2.2)
          have h1 := congrFun hz0 1
          rw [hpoint j s hs] at h1
          simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] at h1
          exact hs0 (pow_eq_zero_iff (ha j).ne' |>.mp h1) }
  have hdeg : B.degree = S := hsumA
  let e : (Σ j : Fin b, Fin (B.a j)) ≃ Fin S := B.labels.trans (finCongr hdeg)
  let D := B.toMultiSheetData e
  -- The root points are branch points.
  have hrootpoint : ∀ r, 0 < r → r < min ρ 1 → ∀ (k : Fin S) (θ : ℝ),
      ∃ i, ∃ s ∈ ball (0 : ℂ) ρ, ‖s‖ ≤ r ∧
        ![D.root 1 r k θ, circlePath (r ^ D.q) θ] = G i s := by
    intro r hr hrρ k θ
    set p := e.symm k
    set t := planeBranchAngularParameter B.ramification r θ
    set s := TransverseBranchData.unitRoot (B.a p.1) ^ p.2.val *
      t ^ (B.ramification / B.a p.1)
    have ht : t ∈ ball (0 : ℂ) (min ρ 1) := by
      simpa [t, mem_ball, dist_zero_right, planeBranchAngularParameter_norm, abs_of_pos hr]
        using hrρ
    have hs : s ∈ ball (0 : ℂ) ρ := B.sheet_mem_ball (p := p) ht
    have hsr : ‖s‖ ≤ r := by
      have ht1 : ‖t‖ < 1 := lt_of_lt_of_le (mem_ball_zero_iff.mp ht) (min_le_right _ _)
      have htr : ‖t‖ = r := by
        simp [t, planeBranchAngularParameter_norm, abs_of_pos hr]
      simp only [s, norm_mul, norm_pow, TransverseBranchData.norm_unitRoot, one_pow, one_mul]
      calc ‖t‖ ^ (B.ramification / B.a p.1) ≤ ‖t‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) ht1.le (B.quotient_pos p.1)
        _ = r := by rw [pow_one, htr]
    obtain ⟨hrs, hspow⟩ := B.rootSheet_eq e k t
    refine ⟨p.1, s, hs, hsr, ?_⟩
    rw [hpoint p.1 s hs]
    funext c
    fin_cases c
    · change 1 * (B.toMultiSheetData e).rootSheet k t = _
      rw [one_mul, hrs]
      rfl
    · change circlePath (r ^ B.ramification) θ = _
      rw [hspow]
      change circlePath (r ^ B.ramification) θ = t ^ B.ramification
      rw [planeBranchAngularParameter_pow B.ramification_pos, circlePath]
      push_cast
      ring
  refine ⟨D, ?_, ?_, ?_⟩
  · exact B.permCycleCount_monodromy e
  · intro r hr hrR k θ
    obtain ⟨i, s, hs, -, hpt⟩ := hrootpoint r hr hrR k θ
    rw [hpt]
    have h := hradspec i s (hinball i s hs)
    rw [h.2.2.1.1, Finset.prod_eq_zero (Finset.mem_univ i) h.2.2.2, mul_zero]
  · intro N' hN'
    have hrad' : ∀ i, ∃ r : ℝ, 0 < r ∧ ∀ s ∈ ball (0 : ℂ) r, G i s ∈ N' := by
      intro i
      have hcont : ContinuousAt (G i) 0 := (hGan i 0 (mem_ball_self (hR i))).continuousAt
      have hGN : ∀ᶠ s in 𝓝 (0 : ℂ), G i s ∈ N' := by
        have := hcont.tendsto
        rw [hG0 i] at this
        exact this hN'
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hGN
      exact ⟨r, hr, fun s hs => hball hs⟩
    choose rad' hrad' hrad'spec using hrad'
    obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_forall rad' hrad'
    refine ⟨min δ (min ρ 1), lt_min hδ (lt_min hρ one_pos), fun r hr hrr k θ => ?_⟩
    obtain ⟨i, s, hs, hsr, hpt⟩ :=
      hrootpoint r hr (lt_of_lt_of_le hrr (min_le_right _ _)) k θ
    rw [hpt]
    apply hrad'spec i s
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt hsr (lt_of_lt_of_le hrr ((min_le_left _ _).trans (hδle i)))

/-- **Strict-transform sheets of a transverse reduced germ.** Under the corrected hypotheses
(reduced, regular of order `S` in `ζ`, multiplicity at least `S`), there is sheet data on `S`
sheets whose monodromy has `irreducibleBranchCount f` cycles, whose root strands are zeros of
`H` over the base circle `ξ = r^q e^{iθ}`, and whose root points tend to the origin. -/
theorem exists_transverse_multiSheetData (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hsq : Squarefree (ofFunction H hH)) {S : ℕ}
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S)
    (hmult : ofFunction H hH ∈ maximalIdeal 2 ^ S) :
    ∃ D : MultiSheetData S,
      permCycleCount D.τ = irreducibleBranchCount (ofFunction H hH) ∧
      (∀ r, 0 < r → r < D.R → ∀ k θ, H ![D.root 1 r k θ, circlePath (r ^ D.q) θ] = 0) ∧
      ∀ N ∈ 𝓝 (0 : Source 2), ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r, 0 < r → r < r₁ → ∀ k θ,
        ![D.root 1 r k θ, circlePath (r ^ D.q) θ] ∈ N := by
  obtain ⟨F, u, hu, hfac, hirr, hnass⟩ := exists_branch_factorization (ofFunction H hH) hsq
  have hreg' : IsRegularInFirstCoordinateOfOrder (u * ∏ i, F i) S := hfac ▸ hreg
  have hmult' : u * ∏ i, F i ∈ maximalIdeal 2 ^ S := hfac ▸ hmult
  exact exists_multiSheetData_of_factorization H hH F u hu hfac hirr hnass hreg' hmult'

end OnLeConjecture.Analytic
