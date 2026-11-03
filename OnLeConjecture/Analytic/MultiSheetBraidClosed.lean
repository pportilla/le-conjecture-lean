/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidConvexIsotopy

/-!
# Closed braids given by labelled strands, and their isotopies

A closed braid on `S` strands over the parameter interval `[u, v]` is given by
`S` functions `K k : ℝ → ℂ`, continuous on `[u, v]`, with pairwise distinct values at
every parameter, together with a permutation `τ` (the monodromy) such that the final
point of strand `k` is the initial point of strand `τ k`. This is a loop in the space
of unordered configurations of `S` distinct points of `ℂ`, together with a labelling
of its points along the parameter interval.

An isotopy through closed braids with monodromy `τ` is a family `H s`, `s ∈ [0, 1]`,
jointly continuous on `[0, 1] × [u, v]`, such that every `H s` is a closed braid with
monodromy `τ`. This is a free homotopy of loops in the unordered configuration space.
The relation is reflexive, symmetric and transitive on closed braids.

The module proves the elementary sources of isotopies used in job J14:
straight-line interpolation of two closed braids whose pairwise differences are never
opposite in a coordinate, monotone reparametrization of the parameter interval,
relabelling, and multiplication by a nonvanishing closed scalar loop.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace OnLeConjecture.Analytic

/-- The labelled strands `K` form a closed braid over `[u, v]` with monodromy `τ`. -/
structure IsClosedStrandBraid {S : ℕ} (K : Fin S → ℝ → ℂ) (u v : ℝ)
    (τ : Equiv.Perm (Fin S)) : Prop where
  lt : u < v
  continuousOn : ∀ k, ContinuousOn (K k) (Icc u v)
  injective : ∀ t ∈ Icc u v, Function.Injective fun k => K k t
  closing : ∀ k, K k v = K (τ k) u

/-- The family `H s` is an isotopy through closed braids over `[u, v]` with
monodromy `τ`, for the deformation parameter `s ∈ [0, 1]`. -/
structure IsClosedStrandBraidIsotopy {S : ℕ} (H : ℝ → Fin S → ℝ → ℂ) (u v : ℝ)
    (τ : Equiv.Perm (Fin S)) : Prop where
  lt : u < v
  continuousOn : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H p.1 k p.2) (Icc 0 1 ×ˢ Icc u v)
  injective : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, Function.Injective fun k => H s k t
  closing : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, H s k v = H s (τ k) u

/-- The closed braids `K₀` and `K₁` over `[u, v]` with monodromy `τ` are isotopic
through closed braids. -/
def ClosedStrandBraidIsotopic {S : ℕ} (K₀ K₁ : Fin S → ℝ → ℂ) (u v : ℝ)
    (τ : Equiv.Perm (Fin S)) : Prop :=
  ∃ H : ℝ → Fin S → ℝ → ℂ, IsClosedStrandBraidIsotopy H u v τ ∧
    (∀ k, ∀ t ∈ Icc u v, H 0 k t = K₀ k t) ∧ (∀ k, ∀ t ∈ Icc u v, H 1 k t = K₁ k t)

namespace IsClosedStrandBraidIsotopy

variable {S : ℕ} {H : ℝ → Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}

/-- Every member of an isotopy through closed braids is a closed braid. -/
theorem slice (h : IsClosedStrandBraidIsotopy H u v τ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsClosedStrandBraid (H s) u v τ where
  lt := h.lt
  continuousOn k := by
    have hm : MapsTo (fun t : ℝ => (s, t)) (Icc u v) (Icc 0 1 ×ˢ Icc u v) :=
      fun t ht => ⟨hs, ht⟩
    exact (h.continuousOn k).comp (Continuous.prodMk_right s).continuousOn hm
  injective t ht := h.injective s hs t ht
  closing k := h.closing s hs k

/-- An isotopy built from jointly continuous strands. -/
theorem of_continuous (huv : u < v) (hc : ∀ k, Continuous fun p : ℝ × ℝ => H p.1 k p.2)
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, Function.Injective fun k => H s k t)
    (hclose : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, H s k v = H s (τ k) u) :
    IsClosedStrandBraidIsotopy H u v τ :=
  ⟨huv, fun k => (hc k).continuousOn, hinj, hclose⟩

end IsClosedStrandBraidIsotopy

namespace IsClosedStrandBraid

variable {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}

/-- Equality on the parameter interval preserves the closed-braid property. -/
theorem congr (h : IsClosedStrandBraid K u v τ) {K' : Fin S → ℝ → ℂ}
    (he : ∀ k, ∀ t ∈ Icc u v, K' k t = K k t) : IsClosedStrandBraid K' u v τ where
  lt := h.lt
  continuousOn k := (h.continuousOn k).congr (fun t ht => he k t ht)
  injective t ht := by
    have hf : (fun k => K' k t) = fun k => K k t := funext fun k => he k t ht
    rw [hf]
    exact h.injective t ht
  closing k := by
    rw [he k v (right_mem_Icc.mpr h.lt.le), he (τ k) u (left_mem_Icc.mpr h.lt.le)]
    exact h.closing k

/-- The monodromy of a closed braid is determined by its strands. -/
theorem monodromy_unique (h : IsClosedStrandBraid K u v τ) {τ' : Equiv.Perm (Fin S)}
    (h' : IsClosedStrandBraid K u v τ') : τ = τ' := by
  ext k
  have hu := left_mem_Icc.mpr h.lt.le
  have he := (h.closing k).symm.trans (h'.closing k)
  exact congrArg Fin.val (h.injective u hu he)

/-- A continuous change of parameter with the right endpoint values preserves
closed braids. -/
theorem comp_time (h : IsClosedStrandBraid K u v τ) {u' v' : ℝ} (huv' : u' < v')
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc u' v')) (hmaps : MapsTo φ (Icc u' v') (Icc u v))
    (hu : φ u' = u) (hv : φ v' = v) :
    IsClosedStrandBraid (fun k t => K k (φ t)) u' v' τ where
  lt := huv'
  continuousOn k := (h.continuousOn k).comp hφ hmaps
  injective t ht := h.injective (φ t) (hmaps ht)
  closing k := by
    simp only [hu, hv]
    exact h.closing k

/-- Relabelling the strands by `π` conjugates the monodromy. -/
theorem relabel (h : IsClosedStrandBraid K u v τ) (π : Equiv.Perm (Fin S)) :
    IsClosedStrandBraid (fun k t => K (π k) t) u v (π⁻¹ * τ * π) where
  lt := h.lt
  continuousOn k := h.continuousOn (π k)
  injective t ht := (h.injective t ht).comp π.injective
  closing k := by
    have hπ : π (π⁻¹ (τ (π k))) = τ (π k) := by simp
    simp only [Equiv.Perm.mul_apply, hπ]
    exact h.closing (π k)

/-- Multiplication by a nonvanishing closed scalar loop preserves closed braids. -/
theorem mul_left (h : IsClosedStrandBraid K u v τ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc u v)) (hg0 : ∀ t ∈ Icc u v, g t ≠ 0) (hgv : g v = g u) :
    IsClosedStrandBraid (fun k t => g t * K k t) u v τ where
  lt := h.lt
  continuousOn k := hg.mul (h.continuousOn k)
  injective t ht k l hkl := h.injective t ht (mul_left_cancel₀ (hg0 t ht) hkl)
  closing k := by
    simp only [hgv]
    rw [h.closing k]

end IsClosedStrandBraid

namespace ClosedStrandBraidIsotopic

variable {S : ℕ} {K₀ K₁ K₂ : Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}

theorem left (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) : IsClosedStrandBraid K₀ u v τ := by
  obtain ⟨H, hH, h0, _⟩ := h
  exact (hH.slice (left_mem_Icc.mpr zero_le_one)).congr fun k t ht => (h0 k t ht).symm

theorem right (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) : IsClosedStrandBraid K₁ u v τ := by
  obtain ⟨H, hH, _, h1⟩ := h
  exact (hH.slice (right_mem_Icc.mpr zero_le_one)).congr fun k t ht => (h1 k t ht).symm

theorem refl (h : IsClosedStrandBraid K₀ u v τ) : ClosedStrandBraidIsotopic K₀ K₀ u v τ := by
  refine ⟨fun _ => K₀, ⟨h.lt, fun k => ?_, fun _ _ t ht => h.injective t ht,
    fun _ _ k => h.closing k⟩, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  exact (h.continuousOn k).comp continuous_snd.continuousOn (fun p hp => hp.2)

theorem symm (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) :
    ClosedStrandBraidIsotopic K₁ K₀ u v τ := by
  obtain ⟨H, hH, h0, h1⟩ := h
  have hm : ∀ s ∈ Icc (0 : ℝ) 1, 1 - s ∈ Icc (0 : ℝ) 1 :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨fun s => H (1 - s), ⟨hH.lt, fun k => ?_, fun s hs => hH.injective _ (hm s hs),
    fun s hs => hH.closing _ (hm s hs)⟩, ?_, ?_⟩
  · have hcont : Continuous fun p : ℝ × ℝ => (1 - p.1, p.2) := by fun_prop
    exact (hH.continuousOn k).comp hcont.continuousOn
      (fun p hp => ⟨hm p.1 hp.1, hp.2⟩)
  · intro k t ht
    simpa only [sub_zero] using h1 k t ht
  · intro k t ht
    simpa only [sub_self] using h0 k t ht

theorem trans (h₁ : ClosedStrandBraidIsotopic K₀ K₁ u v τ)
    (h₂ : ClosedStrandBraidIsotopic K₁ K₂ u v τ) : ClosedStrandBraidIsotopic K₀ K₂ u v τ := by
  classical
  obtain ⟨H₁, hH₁, h₁0, h₁1⟩ := h₁
  obtain ⟨H₂, hH₂, h₂0, h₂1⟩ := h₂
  let H : ℝ → Fin S → ℝ → ℂ := fun s => if s ≤ 1 / 2 then H₁ (2 * s) else H₂ (2 * s - 1)
  have hseam : ∀ k, ∀ t ∈ Icc u v, H₁ 1 k t = H₂ 0 k t :=
    fun k t ht => (h₁1 k t ht).trans (h₂0 k t ht).symm
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ 1 / 2 → 2 * s ∈ Icc (0 : ℝ) 1 :=
    fun s hs hs' => ⟨by linarith [hs.1], by linarith⟩
  have hhigh : ∀ s ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ s → 2 * s - 1 ∈ Icc (0 : ℝ) 1 :=
    fun s hs hs' => ⟨by linarith, by linarith [hs.2]⟩
  -- On the upper half the family agrees with the reparametrized second isotopy.
  have hHhigh : ∀ s ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ s → ∀ k, ∀ t ∈ Icc u v,
      H s k t = H₂ (2 * s - 1) k t := by
    intro s _ hs' k t ht
    by_cases hle : s ≤ 1 / 2
    · have hs2 : s = 1 / 2 := le_antisymm hle hs'
      simp only [H, hs2]
      norm_num
      exact hseam k t ht
    · simp only [H, if_neg hle]
  have hHlow : ∀ s, s ≤ 1 / 2 → ∀ k t, H s k t = H₁ (2 * s) k t := by
    intro s hs k t
    simp only [H, if_pos hs]
  refine ⟨H, ⟨hH₁.lt, fun k => ?_, ?_, ?_⟩, ?_, ?_⟩
  · have hsplit : Icc (0 : ℝ) 1 ×ˢ Icc u v =
        (Icc (0 : ℝ) (1 / 2) ×ˢ Icc u v) ∪ (Icc (1 / 2 : ℝ) 1 ×ˢ Icc u v) := by
      ext p
      simp only [mem_prod, mem_Icc, mem_union]
      constructor
      · rintro ⟨⟨h0, h1⟩, ht⟩
        by_cases hp : p.1 ≤ 1 / 2
        · exact Or.inl ⟨⟨h0, hp⟩, ht⟩
        · exact Or.inr ⟨⟨by linarith, h1⟩, ht⟩
      · rintro (⟨⟨h0, h1⟩, ht⟩ | ⟨⟨h0, h1⟩, ht⟩)
        · exact ⟨⟨h0, by linarith⟩, ht⟩
        · exact ⟨⟨by linarith, h1⟩, ht⟩
    rw [hsplit]
    apply ContinuousOn.union_of_isClosed _ _ (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc)
    · have hc : Continuous fun p : ℝ × ℝ => (2 * p.1, p.2) := by fun_prop
      apply ((hH₁.continuousOn k).comp hc.continuousOn _).congr
      · intro p hp
        exact hHlow p.1 hp.1.2 k p.2
      · intro p hp
        exact ⟨hlow p.1 ⟨hp.1.1, by linarith [hp.1.2]⟩ hp.1.2, hp.2⟩
    · have hc : Continuous fun p : ℝ × ℝ => (2 * p.1 - 1, p.2) := by fun_prop
      apply ((hH₂.continuousOn k).comp hc.continuousOn _).congr
      · intro p hp
        exact hHhigh p.1 ⟨by linarith [hp.1.1], hp.1.2⟩ hp.1.1 k p.2 hp.2
      · intro p hp
        exact ⟨hhigh p.1 ⟨by linarith [hp.1.1], hp.1.2⟩ hp.1.1, hp.2⟩
  · intro s hs t ht
    by_cases hle : s ≤ 1 / 2
    · have he : (fun k => H s k t) = fun k => H₁ (2 * s) k t := funext fun k => hHlow s hle k t
      rw [he]
      exact hH₁.injective _ (hlow s hs hle) t ht
    · have he : (fun k => H s k t) = fun k => H₂ (2 * s - 1) k t :=
        funext fun k => hHhigh s hs (le_of_not_ge hle) k t ht
      rw [he]
      exact hH₂.injective _ (hhigh s hs (le_of_not_ge hle)) t ht
  · intro s hs k
    have hu := left_mem_Icc.mpr hH₁.lt.le
    have hv := right_mem_Icc.mpr hH₁.lt.le
    by_cases hle : s ≤ 1 / 2
    · rw [hHlow s hle, hHlow s hle]
      exact hH₁.closing _ (hlow s hs hle) k
    · have hs' := (le_of_not_ge hle)
      rw [hHhigh s hs hs' k v hv, hHhigh s hs hs' (τ k) u hu]
      exact hH₂.closing _ (hhigh s hs hs') k
  · intro k t ht
    rw [hHlow 0 (by norm_num)]
    simpa only [mul_zero] using h₁0 k t ht
  · intro k t ht
    rw [hHhigh 1 (right_mem_Icc.mpr zero_le_one) (by norm_num) k t ht]
    simpa only [show (2 : ℝ) * 1 - 1 = 1 by norm_num] using h₂1 k t ht

/-- Equality on the parameter interval preserves isotopy. -/
theorem congr (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) {K₀' K₁' : Fin S → ℝ → ℂ}
    (h0 : ∀ k, ∀ t ∈ Icc u v, K₀' k t = K₀ k t) (h1 : ∀ k, ∀ t ∈ Icc u v, K₁' k t = K₁ k t) :
    ClosedStrandBraidIsotopic K₀' K₁' u v τ := by
  obtain ⟨H, hH, hH0, hH1⟩ := h
  exact ⟨H, hH, fun k t ht => (hH0 k t ht).trans (h0 k t ht).symm,
    fun k t ht => (hH1 k t ht).trans (h1 k t ht).symm⟩

/-- Precomposition with a continuous change of parameter with the right endpoint
values carries isotopies to isotopies. -/
theorem comp_time (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) {u' v' : ℝ} (huv' : u' < v')
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc u' v')) (hmaps : MapsTo φ (Icc u' v') (Icc u v))
    (hu : φ u' = u) (hv : φ v' = v) :
    ClosedStrandBraidIsotopic (fun k t => K₀ k (φ t)) (fun k t => K₁ k (φ t)) u' v' τ := by
  obtain ⟨H, hH, hH0, hH1⟩ := h
  refine ⟨fun s k t => H s k (φ t), ⟨huv', fun k => ?_, fun s hs t ht =>
    hH.injective s hs (φ t) (hmaps ht), fun s hs k => ?_⟩, fun k t ht => hH0 k (φ t) (hmaps ht),
    fun k t ht => hH1 k (φ t) (hmaps ht)⟩
  · have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1, φ p.2)) (Icc 0 1 ×ˢ Icc u' v') :=
      continuous_fst.continuousOn.prodMk (hφ.comp continuous_snd.continuousOn
        (fun p hp => hp.2))
    exact (hH.continuousOn k).comp hc (fun p hp => ⟨hp.1, hmaps hp.2⟩)
  · simp only [hu, hv]
    exact hH.closing s hs k

/-- Relabelling both closed braids by `π` preserves isotopy and conjugates the
monodromy. -/
theorem relabel (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) (π : Equiv.Perm (Fin S)) :
    ClosedStrandBraidIsotopic (fun k t => K₀ (π k) t) (fun k t => K₁ (π k) t) u v
      (π⁻¹ * τ * π) := by
  obtain ⟨H, hH, hH0, hH1⟩ := h
  refine ⟨fun s k t => H s (π k) t, ⟨hH.lt, fun k => hH.continuousOn (π k),
    fun s hs t ht => (hH.injective s hs t ht).comp π.injective, fun s hs k => ?_⟩,
    fun k t ht => hH0 (π k) t ht, fun k t ht => hH1 (π k) t ht⟩
  have hπ : π (π⁻¹ (τ (π k))) = τ (π k) := by simp
  simp only [Equiv.Perm.mul_apply, hπ]
  exact hH.closing s hs (π k)

/-- Multiplication by a nonvanishing closed scalar loop carries isotopies to
isotopies. -/
theorem mul_left (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc u v)) (hg0 : ∀ t ∈ Icc u v, g t ≠ 0) (hgv : g v = g u) :
    ClosedStrandBraidIsotopic (fun k t => g t * K₀ k t) (fun k t => g t * K₁ k t) u v τ := by
  obtain ⟨H, hH, hH0, hH1⟩ := h
  refine ⟨fun s k t => g t * H s k t, ⟨hH.lt, fun k => ?_,
    fun s hs t ht k l hkl => hH.injective s hs t ht (mul_left_cancel₀ (hg0 t ht) hkl),
    fun s hs k => ?_⟩, fun k t ht => by simp only [hH0 k t ht],
    fun k t ht => by simp only [hH1 k t ht]⟩
  · exact (hg.comp continuous_snd.continuousOn (fun p hp => hp.2)).mul (hH.continuousOn k)
  · simp only [hgv]
    rw [hH.closing s hs k]

/-- Straight-line interpolation: two closed braids with the same monodromy whose
pairwise differences have, at every parameter, a common coordinate of the same strict
sign are isotopic. -/
theorem of_separation (h₀ : IsClosedStrandBraid K₀ u v τ) (h₁ : IsClosedStrandBraid K₁ u v τ)
    (hsep : ∀ t ∈ Icc u v, ∀ k l, k ≠ l →
      0 < (K₀ k t - K₀ l t).re * (K₁ k t - K₁ l t).re ∨
      0 < (K₀ k t - K₀ l t).im * (K₁ k t - K₁ l t).im) :
    ClosedStrandBraidIsotopic K₀ K₁ u v τ := by
  refine ⟨fun s k t => (1 - s) * K₀ k t + s * K₁ k t, ⟨h₀.lt, fun k => ?_, ?_, ?_⟩,
    fun k t _ => by simp, fun k t _ => by simp⟩
  · have h0 := (h₀.continuousOn k).comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    have h1 := (h₁.continuousOn k).comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    have hs : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := by fun_prop
    exact ((continuousOn_const.sub hs.continuousOn).mul h0).add (hs.continuousOn.mul h1)
  · intro s hs t ht k l hkl
    by_contra hne
    have h := complex_convex_combination_ne_zero_of_coordinate_mul_pos (hsep t ht k l hne) hs
    apply h
    have hkl' : (1 - (s : ℂ)) * K₀ k t + s * K₁ k t = (1 - s) * K₀ l t + s * K₁ l t := hkl
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    linear_combination hkl'
  · intro s _ k
    simp only [h₀.closing k, h₁.closing k]

/-- Two monotone-type reparametrizations of one closed braid with the same endpoint
values are isotopic, through the convex combinations of the two parameter maps. -/
theorem of_reparam {K : Fin S → ℝ → ℂ} {u₀ v₀ : ℝ} (h : IsClosedStrandBraid K u₀ v₀ τ)
    (huv : u < v) {φ ψ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc u v)) (hψ : ContinuousOn ψ (Icc u v))
    (hφm : MapsTo φ (Icc u v) (Icc u₀ v₀)) (hψm : MapsTo ψ (Icc u v) (Icc u₀ v₀))
    (hφu : φ u = u₀) (hφv : φ v = v₀) (hψu : ψ u = u₀) (hψv : ψ v = v₀) :
    ClosedStrandBraidIsotopic (fun k t => K k (φ t)) (fun k t => K k (ψ t)) u v τ := by
  let χ : ℝ × ℝ → ℝ := fun p => (1 - p.1) * φ p.2 + p.1 * ψ p.2
  have hχm : MapsTo χ (Icc 0 1 ×ˢ Icc u v) (Icc u₀ v₀) := by
    intro p hp
    have h1 := hφm hp.2
    have h2 := hψm hp.2
    have hs := hp.1
    constructor
    · nlinarith [h1.1, h2.1, hs.1, hs.2]
    · nlinarith [h1.2, h2.2, hs.1, hs.2]
  have hχc : ContinuousOn χ (Icc 0 1 ×ˢ Icc u v) := by
    have hφ' := hφ.comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    have hψ' := hψ.comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    exact ((continuousOn_const.sub continuous_fst.continuousOn).mul hφ').add
      (continuous_fst.continuousOn.mul hψ')
  refine ⟨fun s k t => K k (χ (s, t)), ⟨huv, fun k => (h.continuousOn k).comp hχc hχm,
    fun s hs t ht => h.injective _ (hχm ⟨hs, ht⟩), fun s _ k => ?_⟩, ?_, ?_⟩
  · simp only [χ, hφu, hφv, hψu, hψv, show ∀ x : ℝ, (1 - s) * x + s * x = x from
      fun x => by ring]
    exact h.closing k
  · intro k t _
    simp only [χ, sub_zero, one_mul, zero_mul, add_zero]
  · intro k t _
    simp only [χ, sub_self, zero_mul, one_mul, zero_add]

/-- A closed braid is isotopic to its product with a nonzero constant. -/
theorem const_mul (h : IsClosedStrandBraid K₀ u v τ) {c : ℂ} (hc : c ≠ 0) :
    ClosedStrandBraidIsotopic K₀ (fun k t => c * K₀ k t) u v τ := by
  let g : ℝ → ℂ := fun s => Complex.exp (s * Complex.log c)
  have hgc : Continuous g := by fun_prop
  refine ⟨fun s k t => g s * K₀ k t, ⟨h.lt, fun k => ?_,
    fun s _ t ht k l hkl => h.injective t ht (mul_left_cancel₀ (Complex.exp_ne_zero _) hkl),
    fun s _ k => by rw [h.closing k]⟩, fun k t _ => ?_, fun k t _ => ?_⟩
  · exact (hgc.comp continuous_fst).continuousOn.mul
      ((h.continuousOn k).comp continuous_snd.continuousOn (fun p hp => hp.2))
  · simp [g]
  · simp [g, Complex.exp_log hc]

end ClosedStrandBraidIsotopic

end OnLeConjecture.Analytic
