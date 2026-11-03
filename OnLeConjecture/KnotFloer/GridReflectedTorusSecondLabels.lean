/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondReduction

/-!
# Coefficients of transported permutations

For a configuration `c` in positive cyclic order and a permutation `ρ` of its
labels, the three coefficient functions of the correction at `cfgPerm c ρ` are
sums over labels. Their conditions are decidable statements about `ρ` and the
cyclic distances between configuration points. This file also proves that the
three-cycle and transposition coefficient is invariant under inversion, and that
the terms of an ordered pair and of its image under an involutive target agree.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ)

section Evaluation

variable {k : ℕ} {c : Fin k ↪ Fin (consecutiveTorusGridSize n)}

/-- The four-cycle coefficient of a transported permutation. -/
theorem torusFourCoeff_cfgPerm (ρ : Equiv.Perm (Fin k)) :
    torusFourCoeff n (cfgPerm c ρ) =
      if ρ.support.card = 4 ∧ ∀ i, ρ (ρ i) = i → ρ i = i then
        ∑ i : Fin k, if ρ i ≠ i ∧ (∃ l, cycDist (c i) (c l) = 1 ∧ ρ l ≠ l) then
          tcW4 (n + 1) (cycDist (c i) (c (ρ i))) (cycDist (c i) (c (ρ (ρ i))))
            (cycDist (c i) (c (ρ (ρ (ρ i)))))
        else 0
      else 0 := by
  classical
  unfold torusFourCoeff
  rw [card_support_cfgPerm]
  have hcond : (∀ x, cfgPerm c ρ (cfgPerm c ρ x) = x → cfgPerm c ρ x = x) ↔
      ∀ i, ρ (ρ i) = i → ρ i = i := by
    constructor
    · intro h i hi
      have := h (c i) (by rw [cfgPerm_apply_emb, cfgPerm_apply_emb, hi])
      rw [cfgPerm_apply_emb] at this
      exact c.injective this
    · intro h x hx
      by_cases hr : x ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hr
        rw [cfgPerm_apply_emb, cfgPerm_apply_emb] at hx
        rw [cfgPerm_apply_emb, h i (c.injective hx)]
      · exact cfgPerm_apply_of_notMem c ρ hr
  by_cases hc : ρ.support.card = 4 ∧ ∀ i, ρ (ρ i) = i → ρ i = i
  · rw [if_pos hc, if_pos ⟨hc.1, hcond.mpr hc.2⟩]
    rw [sum_eq_sum_emb c _ (fun x hx => by
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact h1 (cfgPerm_apply_of_notMem c ρ hx))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [cfgPerm_apply_emb, ne_eq, c.injective.eq_iff]
    congr 1
    apply propext
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨x, hx1, hx2⟩
      by_cases hr : x ∈ Set.range c
      · obtain ⟨l, rfl⟩ := hr
        rw [cfgPerm_apply_emb, c.injective.eq_iff] at hx2
        exact ⟨l, hx1, hx2⟩
      · exact (hx2 (cfgPerm_apply_of_notMem c ρ hr)).elim
    · rintro ⟨l, hl1, hl2⟩
      exact ⟨c l, hl1, by rw [cfgPerm_apply_emb, c.injective.eq_iff]; exact hl2⟩
  · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, hcond.mp h.2⟩)]

/-- The three-cycle and transposition coefficient of a transported permutation. -/
theorem torusFiveCoeff_cfgPerm [NeZero k] (hc : CycSorted c) (ρ : Equiv.Perm (Fin k)) :
    torusFiveCoeff n (cfgPerm c ρ) =
      if ρ.support.card = 5 then
        ∑ i : Fin k, ∑ l : Fin k, if FiveCondIdx ρ i l then
          tcF (n + 1) (cycDist (c i) (c l)) (cycDist (c i) (c (ρ i)))
              (cycDist (c i) (c (ρ l))) +
            tcF (n + 1) (cycDist (c i) (c l)) (cycDist (c i) (c (ρ i)))
              (cycDist (c i) (c (ρ (ρ l))))
        else 0
      else 0 := by
  classical
  unfold torusFiveCoeff
  rw [card_support_cfgPerm]
  split_ifs with h5
  · rw [sum_eq_sum_emb c _ (fun x hx => by
      apply Finset.sum_eq_zero
      intro a _
      rw [if_neg]
      intro h
      exact h.2.1 (cfgPerm_apply_of_notMem c ρ hx))]
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_eq_sum_emb c _ (fun x hx => by
      rw [if_neg]
      intro h
      exact apply_ne_of_fiveCond h (cfgPerm_apply_of_notMem c ρ hx))]
    apply Finset.sum_congr rfl
    intro l _
    rw [if_congr (fiveCond_emb_iff hc ρ i l) rfl rfl]
    simp only [cfgPerm_apply_emb]
  · rfl

end Evaluation

/-! ### Inversion -/

theorem fiveCond_inv_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (u a : Fin m) :
    FiveCond σ⁻¹ u a ↔ FiveCond σ u a := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hu : σ (σ u) = u := by
      have := congrArg (fun x => σ (σ x)) h1
      simpa using this.symm
    have hu' : σ⁻¹ u = σ u := by
      rw [Equiv.Perm.inv_eq_iff_eq, hu]
    have ha : σ (σ (σ a)) = a := by
      have := congrArg (fun x => σ (σ (σ x))) h6
      simpa using this.symm
    have ha1 : σ⁻¹ a = σ (σ a) := by rw [Equiv.Perm.inv_eq_iff_eq, ha]
    have ha2 : σ⁻¹ (σ⁻¹ a) = σ a := by
      rw [ha1, Equiv.Perm.inv_eq_iff_eq]
    rw [hu'] at h2 h3 h4 h5
    rw [ha1] at h4
    rw [ha2] at h5
    exact ⟨hu, h2, h3, h5, h4, ha⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hu' : σ⁻¹ u = σ u := by rw [Equiv.Perm.inv_eq_iff_eq, h1]
    have ha1 : σ⁻¹ a = σ (σ a) := by rw [Equiv.Perm.inv_eq_iff_eq, h6]
    have ha2 : σ⁻¹ (σ⁻¹ a) = σ a := by rw [ha1, Equiv.Perm.inv_eq_iff_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hu', Equiv.Perm.inv_eq_iff_eq]
    · rw [hu']; exact h2
    · rw [hu']; exact h3
    · rw [hu', ha1]; exact h5
    · rw [hu', ha2]; exact h4
    · rw [ha2, Equiv.Perm.inv_eq_iff_eq]

/-- The three-cycle and transposition coefficient is invariant under inversion. -/
theorem torusFiveCoeff_inv (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    torusFiveCoeff n σ⁻¹ = torusFiveCoeff n σ := by
  classical
  unfold torusFiveCoeff
  rw [Equiv.Perm.support_inv]
  split_ifs with h5
  · apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro a _
    by_cases hc : FiveCond σ u a
    · rw [if_pos ((fiveCond_inv_iff σ u a).mpr hc), if_pos hc]
      obtain ⟨h1, -, -, -, -, h6⟩ := hc
      have hu' : σ⁻¹ u = σ u := by rw [Equiv.Perm.inv_eq_iff_eq, h1]
      have ha1 : σ⁻¹ a = σ (σ a) := by rw [Equiv.Perm.inv_eq_iff_eq, h6]
      have ha2 : σ⁻¹ (σ⁻¹ a) = σ a := by rw [ha1, Equiv.Perm.inv_eq_iff_eq]
      rw [hu', ha2, ha1, add_comm]
    · rw [if_neg (fun h => hc ((fiveCond_inv_iff σ u a).mp h)), if_neg hc]
  · rfl

/-- For an involutive target, the image of an ordered pair under the target has the
same `O` count, and its source is the inverse. -/
theorem oCount_apply_apply_of_involutive {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hτ : ∀ x, τ (τ x) = x) (a b : Fin (consecutiveTorusGridSize n)) :
    oCount n τ (τ a) (τ b) = oCount n τ a b := by
  rw [oCount, oCount, hτ, hτ, Finset.inter_comm]

theorem mul_swap_apply_apply_of_involutive {τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (hτ : ∀ x, τ (τ x) = x) (a b : Fin (consecutiveTorusGridSize n)) :
    τ * Equiv.swap (τ a) (τ b) = (τ * Equiv.swap a b)⁻¹ := by
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, eq_comm, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.mul_apply]
  have hinj : Function.Injective τ := τ.injective
  by_cases h1 : x = τ a
  · subst h1; simp [hτ]
  by_cases h2 : x = τ b
  · subst h2; simp [hτ]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne
      (fun h => h1 (by rw [← h, hτ])) (fun h => h2 (by rw [← h, hτ])), hτ]


/-! ### Positions and sums over configurations -/

/-- The distance between two configuration points, through the positions of the
points relative to the first one. -/
theorem cycDist_emb_eq {m k : ℕ} [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (i l : Fin k) :
    cycDist (c i) (c l) =
      if i ≤ l then cycDist (c 0) (c l) - cycDist (c 0) (c i)
      else m + cycDist (c 0) (c l) - cycDist (c 0) (c i) := by
  rw [cycDist_rebase (c 0) (c i) (c l)]
  have h := hc.le_iff_le (a := i) (b := l)
  by_cases hil : i ≤ l
  · rw [if_pos (h.mpr hil), if_pos hil]
  · rw [if_neg (fun h' => hil (h.mp h')), if_neg hil]

theorem sum_offDiag_eq_sum_sum {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : Fin k × Fin k → M) :
    ∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag, F q =
      ∑ i : Fin k, ∑ l : Fin k, if i = l then 0 else F (i, l) := by
  classical
  rw [← Finset.sum_product' (f := fun i l => if i = l then 0 else F (i, l)),
    Finset.univ_product_univ]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin k)).offDiag))
    (fun p _ hp => by
      have : p.1 = p.2 := by
        by_contra hne
        exact hp (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩)
      simp [this])]
  apply Finset.sum_congr rfl
  intro q hq
  rw [if_neg (Finset.mem_offDiag.mp hq).2.2]

/-- The transposition coefficient of a transported permutation. -/
theorem torusEdgeCoeff_cfgPerm {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (ρ : Equiv.Perm (Fin k)) :
    torusEdgeCoeff n (cfgPerm c ρ) =
      if ρ.support.card = 2 then
        ∑ i : Fin k, if i < ρ i then tcE (n + 1) (cycDist (c i) (c (ρ i))) else 0
      else 0 := by
  classical
  split_ifs with h2
  · obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.card_support_eq_two.mp h2
    rw [cfgPerm_swap, torusEdgeCoeff_swap n (c.injective.ne hab)]
    rw [Fintype.sum_eq_add a b hab (fun x hx => by
      rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]; simp)]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hsym : tcE (n + 1) (cycDist (c b) (c a)) = tcE (n + 1) (cycDist (c a) (c b)) := by
      have h := cycDist_add_cycDist_of_ne (c.injective.ne hab)
      have hlt := cycDist_lt (c a) (c b)
      unfold consecutiveTorusGridSize at h hlt
      rw [show cycDist (c b) (c a) = 2 * (n + 1) + 1 - cycDist (c a) (c b) by omega,
        tcE_symm (by omega)]
    rcases lt_or_gt_of_ne hab with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, hsym]
  · exact torusEdgeCoeff_eq_zero_of_card n (by rw [card_support_cfgPerm]; exact h2)

/-- For a derangement of the labels, the coefficient formula splits into the pairs of
configuration points and the remaining pairs. -/
theorem coefFormula_cfgPerm_split {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (π : Equiv.Perm (Fin k)) (hπ : ∀ i, π i ≠ i) (j : ℤ) :
    coefFormula n (cfgPerm c π) j =
      (∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag,
        pairTerm n (cfgPerm c π) j (c q.1) (c q.2)) +
      ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag.filter
          (fun p => ¬ (cfgPerm c π p.1 ≠ p.1 ∧ cfgPerm c π p.2 ≠ p.2)),
        pairTerm n (cfgPerm c π) j p.1 p.2 := by
  classical
  rw [coefFormula, ← Finset.sum_filter_add_sum_filter_not _
    (fun p => cfgPerm c π p.1 ≠ p.1 ∧ cfgPerm c π p.2 ≠ p.2)]
  congr 1
  have hmoved : ∀ x, cfgPerm c π x ≠ x ↔ x ∈ Set.range c := by
    intro x
    constructor
    · intro hx
      by_contra hr
      exact hx (cfgPerm_apply_of_notMem c π hr)
    · rintro ⟨i, rfl⟩
      rw [cfgPerm_apply_emb]
      exact fun h => hπ i (c.injective h)
  have hmap : (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag.filter
      (fun p => cfgPerm c π p.1 ≠ p.1 ∧ cfgPerm c π p.2 ≠ p.2) =
      (Finset.univ : Finset (Fin k)).offDiag.map
        ⟨fun q => (c q.1, c q.2), fun q q' h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (c.injective h.1) (c.injective h.2)⟩ := by
    ext ⟨a, b⟩
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hp, h1, h2⟩
      obtain ⟨i, rfl⟩ := (hmoved a).mp h1
      obtain ⟨l, rfl⟩ := (hmoved b).mp h2
      refine ⟨(i, l), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        fun h => (Finset.mem_offDiag.mp hp).2.2 (by
          have h' : i = l := h
          simp [h'])⟩, rfl⟩
    · rintro ⟨⟨i, l⟩, hq, he⟩
      have he1 : c i = a := congrArg Prod.fst he
      have he2 : c l = b := congrArg Prod.snd he
      subst he1 he2
      exact ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        c.injective.ne (Finset.mem_offDiag.mp hq).2.2⟩, (hmoved _).mpr ⟨i, rfl⟩,
        (hmoved _).mpr ⟨l, rfl⟩⟩
  rw [hmap, Finset.sum_map]
  rfl


/-- Every permutation with `k` moved columns is a transported derangement along a
configuration in positive cyclic order. -/
theorem exists_cfgPerm_of_card {m : ℕ} (τ : Equiv.Perm (Fin m)) {k : ℕ} [NeZero k]
    (h : τ.support.card = k) :
    ∃ (c : Fin k ↪ Fin m) (π : Equiv.Perm (Fin k)), CycSorted c ∧ (∀ i, π i ≠ i) ∧
      cfgPerm c π = τ := by
  subst h
  exact ⟨supportCfg τ, supportPattern τ, cycSorted_supportCfg τ, supportPattern_apply_ne τ,
    cfgPerm_supportPattern τ⟩


/-- The position of a configuration point relative to the first point. -/
def cfgPos {m k : ℕ} [NeZero k] (c : Fin k ↪ Fin m) (l : Fin k) : ℕ := cycDist (c 0) (c l)

@[simp] theorem cfgPos_zero {m k : ℕ} [NeZero k] (c : Fin k ↪ Fin m) : cfgPos c 0 = 0 :=
  cycDist_self _

theorem cycDist_emb_eq_cfgPos {m k : ℕ} [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (i l : Fin k) :
    cycDist (c i) (c l) =
      if i ≤ l then cfgPos c l - cfgPos c i else m + cfgPos c l - cfgPos c i :=
  cycDist_emb_eq hc i l

theorem cfgPos_lt {m k : ℕ} [NeZero k] (c : Fin k ↪ Fin m) (l : Fin k) : cfgPos c l < m :=
  cycDist_lt _ _

theorem cfgPos_lt_cfgPos {m k : ℕ} [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    {i l : Fin k} (h : i < l) : cfgPos c i < cfgPos c l :=
  hc h

end OnLeConjecture.KnotFloer.GridFull
