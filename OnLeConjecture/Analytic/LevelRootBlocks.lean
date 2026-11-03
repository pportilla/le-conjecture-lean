/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootFactorization
public import OnLeConjecture.Analytic.BraidMonodromyBlocks

/-!
# Strands in vertical strips

In the local factors of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Local factors, without a generic-Morse
projection") the sheets near a critical value are grouped into clusters occupying disjoint
vertical strips of the fibre line. This module computes the path word of such a configuration by
iterating `IsPathWord.twoBlock`.

* `blockOffset size i = size 0 + ⋯ + size (i - 1)`: the first position of the block `i`.
* `blockShift n size word i`: the positive word `word i` on `size i` strands placed on the
  positions `blockOffset size i, …, blockOffset size i + size i - 1` of `n` strands, and
  `blockProduct n m size word`, the product of the first `m` placed block words.
* `IsPathWord.signedBraidConj_blockProduct`: if the strands of a family stay in `m` ordered
  vertical strips, the strip `i` containing `size i` strands, and every path word of the strands
  of the strip `i` is conjugate to `word i`, then every path word of the family is conjugate to
  `blockProduct n m size word`.
* `IsStripDecomposition`, `IsStripDecomposition.signedBraidConj`: the same statement for a
  set-valued family of roots, with strips `Ioo (edge i) (edge (i + 1))` and the conjugacy
  hypothesis stated for all labellings of the roots in each strip (`stripRoots`).
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

/-! ### Positions of blocks -/

/-- The first position `size 0 + ⋯ + size (i - 1)` of the block `i`. -/
def blockOffset (size : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, size j

@[simp] theorem blockOffset_zero (size : ℕ → ℕ) : blockOffset size 0 = 0 := by
  simp [blockOffset]

theorem blockOffset_succ (size : ℕ → ℕ) (i : ℕ) :
    blockOffset size (i + 1) = blockOffset size i + size i :=
  Finset.sum_range_succ _ _

theorem blockOffset_succ' (size : ℕ → ℕ) (i : ℕ) :
    blockOffset size (i + 1) = size 0 + blockOffset (fun j => size (j + 1)) i := by
  unfold blockOffset
  rw [Finset.sum_range_succ', add_comm]

theorem blockOffset_mono (size : ℕ → ℕ) {i i' : ℕ} (h : i ≤ i') :
    blockOffset size i ≤ blockOffset size i' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem blockOffset_add_le (size : ℕ → ℕ) {i m : ℕ} (h : i < m) :
    blockOffset size i + size i ≤ blockOffset size m := by
  rw [← blockOffset_succ]
  exact blockOffset_mono size h

/-- The word of the block `i` placed on its positions. -/
def blockShift (n : ℕ) (size : ℕ → ℕ) (word : ∀ i, PositiveAdjacentWord (size i)) (i : ℕ) :
    PositiveAdjacentWord n :=
  if h : blockOffset size i + size i ≤ n then shiftPositive (blockOffset size i) h (word i)
  else []

/-- The product of the placed words of the first `m` blocks. -/
def blockProduct (n m : ℕ) (size : ℕ → ℕ) (word : ∀ i, PositiveAdjacentWord (size i)) :
    PositiveAdjacentWord n :=
  (List.range m).flatMap (blockShift n size word)

theorem blockShift_eq {n : ℕ} {size : ℕ → ℕ} {word : ∀ i, PositiveAdjacentWord (size i)} {i : ℕ}
    (h : blockOffset size i + size i ≤ n) :
    blockShift n size word i = shiftPositive (blockOffset size i) h (word i) := by
  rw [blockShift, dif_pos h]

theorem toSigned_flatMap {n : ℕ} {α : Type*} (l : List α) (f : α → PositiveAdjacentWord n) :
    PositiveAdjacentWord.toSigned (l.flatMap f) = l.flatMap fun a => (f a).toSigned := by
  simp only [PositiveAdjacentWord.toSigned, List.map_flatMap]

/-- The first block word is the lifted word and the others are the shifted block words. -/
theorem blockProduct_succ (m : ℕ) (size : ℕ → ℕ) (word : ∀ i, PositiveAdjacentWord (size i)) :
    (blockProduct (size 0 + blockOffset (fun j => size (j + 1)) m) (m + 1) size word).toSigned =
      liftSigned (Nat.le_add_right _ _) (word 0).toSigned ++
        shiftSigned (size 0) (blockProduct (blockOffset (fun j => size (j + 1)) m) m
          (fun j => size (j + 1)) (fun j => word (j + 1))).toSigned := by
  set k := blockOffset (fun j => size (j + 1)) m
  rw [blockProduct, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [PositiveAdjacentWord.toSigned, List.map_append]
  congr 1
  · rw [blockShift_eq (by simp)]
    simp only [shiftPositive, liftSigned, List.map_map]
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    apply Fin.ext
    simp
  · rw [blockProduct, List.map_flatMap, shiftSigned, List.map_flatMap, List.map_flatMap]
    refine List.flatMap_congr fun i _ => ?_
    simp only [Nat.succ_eq_add_one]
    by_cases h : blockOffset (fun j => size (j + 1)) i + size (i + 1) ≤ k
    · have h' : blockOffset size (i + 1) + size (i + 1) ≤ size 0 + k := by
        rw [blockOffset_succ']; omega
      rw [blockShift_eq h', blockShift_eq (size := fun j => size (j + 1))
        (word := fun j => word (j + 1)) h]
      simp only [shiftPositive, List.map_map]
      refine List.map_congr_left fun a _ => ?_
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      apply Fin.ext
      simp only
      rw [blockOffset_succ']
      omega
    · have h' : ¬ blockOffset size (i + 1) + size (i + 1) ≤ size 0 + k := by
        rw [blockOffset_succ']; omega
      rw [blockShift, dif_neg h', blockShift, dif_neg h]
      rfl

theorem eq_nil_of_zero (W : SignedAdjacentWord 0) : W = [] := by
  rcases W with _ | ⟨a, W⟩
  · rfl
  · exact a.1.elim0

/-! ### The path word of strands in ordered strips -/

/-- **Strands in ordered vertical strips.** Let the strands of `K` on `[u, v]` stay in `m`
vertical strips `edge i < Re < edge (i + 1)`, the strand `k` in the strip `strip k`, with
`size i` strands in the strip `i`. If every path word of the strands of the strip `i` (in any
enumeration) is conjugate to `word i`, every path word of `K` is conjugate to the product of the
words `word i` placed on consecutive positions. -/
theorem IsPathWord.signedBraidConj_blockProduct : ∀ (m n : ℕ) (size : ℕ → ℕ)
    (word : ∀ i, PositiveAdjacentWord (size i)) (edge : ℕ → ℝ) (K : Fin n → ℝ → ℂ)
    (strip : Fin n → ℕ) {u v : ℝ}, u < v →
    (∀ i < m, edge i < edge (i + 1)) → blockOffset size m = n → (∀ k, strip k < m) →
    (∀ k, ∀ t ∈ Icc u v, (K k t).re ∈ Ioo (edge (strip k)) (edge (strip k + 1))) →
    (∀ i < m, Fintype.card {k // strip k = i} = size i) →
    (∀ k, ContinuousOn (K k) (Icc u v)) → (∀ t ∈ Icc u v, Injective fun k => K k t) →
    (∀ i < m, ∀ ι : Fin (size i) → Fin n, Injective ι → (∀ a, strip (ι a) = i) →
      ∀ W, IsPathWord (fun a => K (ι a)) u v W → SignedBraidConj W (word i).toSigned) →
    ∀ W, IsPathWord K u v W → SignedBraidConj W (blockProduct n m size word).toSigned := by
  intro m
  induction m with
  | zero =>
    intro n size word edge K strip u v _ _ hn _ _ _ _ _ _ W _
    simp only [blockOffset_zero] at hn
    subst hn
    rw [eq_nil_of_zero W, eq_nil_of_zero (blockProduct 0 0 size word).toSigned]
    exact SignedBraidConj.refl _
  | succ m ih =>
    classical
    intro n size word edge K strip u v huv hedge hn hstrip hre hcard hcont hinj hconj W hW
    rw [blockOffset_succ'] at hn
    subst hn
    generalize hk : blockOffset (fun j => size (j + 1)) m = k at *
    -- The strands of the first strip and the others.
    have hc0 : Fintype.card {x // strip x = 0} = (size 0) := hcard 0 (Nat.succ_pos m)
    have hc1 : Fintype.card {x // ¬ strip x = 0} = k := by
      rw [Fintype.card_subtype_compl, hc0, Fintype.card_fin]; omega
    let e₁ : Fin (size 0) ≃ {x // strip x = 0} := (Fintype.equivFinOfCardEq hc0).symm
    let e₂ : Fin k ≃ {x // ¬ strip x = 0} := (Fintype.equivFinOfCardEq hc1).symm
    let σ : Equiv.Perm (Fin ((size 0) + k)) :=
      finSumFinEquiv.symm.trans ((e₁.sumCongr e₂).trans (Equiv.sumCompl fun x => strip x = 0))
    have hσL : ∀ a, σ (Fin.castAdd k a) = (e₁ a).1 := fun a => by simp [σ]
    have hσR : ∀ b, σ (Fin.natAdd (size 0) b) = (e₂ b).1 := fun b => by simp [σ]
    set K' : Fin ((size 0) + k) → ℝ → ℂ := fun p t => K (σ p) t with hK'
    have hW' : IsPathWord K' u v W := (IsPathWord.relabel hinj σ).mpr hW
    have hinj' : ∀ t ∈ Icc u v, Injective fun p => K' p t :=
      fun t ht => (hinj t ht).comp σ.injective
    have hcont' : ∀ p, ContinuousOn (K' p) (Icc u v) := fun p => hcont (σ p)
    -- The two blocks are separated by the line `Re = edge 1`.
    have hsep : ∀ t ∈ Icc u v, IsBlockConfig (size 0) k (edge 1) fun p => K' p t := by
      intro t ht
      refine ⟨fun a => ?_, fun b => ?_⟩
      · have h1 := hre (e₁ a).1 t ht
        rw [(e₁ a).2] at h1
        simpa [hK', hσL] using h1.2
      · have h1 := hre (e₂ b).1 t ht
        have hs := (e₂ b).2
        have hlt := hstrip (e₂ b).1
        have hle : edge 1 ≤ edge (strip (e₂ b).1) :=
          le_of_lt_succ_of_le hedge (by omega) (by omega)
        simp only [hK', hσR]
        linarith [h1.1]
    -- Path words of the two blocks.
    obtain ⟨WL, hWL⟩ := exists_isPathWord (K := fun a => K' (Fin.castAdd k a)) huv
      (fun a => hcont' _) fun t ht => (hinj' t ht).comp (Fin.castAdd_injective (size 0) k)
    obtain ⟨WR, hWR⟩ := exists_isPathWord (K := fun b => K' (Fin.natAdd (size 0) b)) huv
      (fun b => hcont' _) fun t ht => (hinj' t ht).comp (Fin.natAdd_injective k (size 0))
    have htwo := hWL.twoBlock hinj' hsep hWR
    have hWeq := hW'.unique huv htwo
    -- The first block.
    have hL : SignedBraidConj WL (word 0).toSigned := by
      refine hconj 0 (Nat.succ_pos m) (fun a => (e₁ a).1)
        (fun a a' h => e₁.injective (Subtype.ext h)) (fun a => (e₁ a).2) WL ?_
      simpa [hK', hσL] using hWL
    -- The other blocks, by induction.
    have hR : SignedBraidConj WR (blockProduct k m (fun j => size (j + 1))
        (fun j => word (j + 1))).toSigned := by
      have hpos : ∀ b, 1 ≤ strip (e₂ b).1 := fun b => by have := (e₂ b).2; omega
      refine ih k (fun j => size (j + 1)) (fun j => word (j + 1)) (fun i => edge (i + 1))
        (fun b => K (e₂ b).1) (fun b => strip (e₂ b).1 - 1) huv
        (fun i hi => hedge (i + 1) (by omega)) hk
        (fun b => by have := hstrip (e₂ b).1; have := hpos b; omega)
        (fun b t ht => by
          have h1 := hre (e₂ b).1 t ht
          rw [show strip (e₂ b).1 - 1 + 1 = strip (e₂ b).1 by have := hpos b; omega]
          exact h1)
        (fun i hi => ?_) (fun b => hcont _) (fun t ht => (hinj t ht).comp
          fun b b' h => e₂.injective (Subtype.ext h))
        (fun i hi ι hι hιs W' hW'' => ?_) WR (by simpa [hK', hσR] using hWR)
      · rw [← hcard (i + 1) (by omega)]
        refine Fintype.card_congr
          { toFun := fun b => ⟨(e₂ b.1).1, by have := hpos b.1; have := b.2; omega⟩
            invFun := fun x => ⟨e₂.symm ⟨x.1, by have := x.2; omega⟩, by
              simp only [Equiv.apply_symm_apply]; have := x.2; omega⟩
            left_inv := fun b => by simp
            right_inv := fun x => by simp }
      · refine hconj (i + 1) (by omega) (fun a => (e₂ (ι a)).1)
          (fun a a' h => hι (e₂.injective (Subtype.ext h))) (fun a => ?_) W' hW''
        have := hιs a
        have := hpos (ι a)
        omega
    -- Combination.
    obtain ⟨x, hx⟩ := hL.exists_conjugator
    obtain ⟨y, hy⟩ := hR.exists_conjugator
    have h2 := (hx.liftSigned (Nat.le_add_right (size 0) k)).append (hy.shiftSigned (size 0))
    subst hk
    rw [blockProduct_succ]
    exact (hWeq.trans (h2.trans (conj_twoBlock x _ y _))).toConj.trans
      (SignedBraidConj.conjugate_left _ _)

/-! ### Set-valued families in strips -/

/-- The roots of `Z c` in the vertical strip `x₀ < Re < x₁`. -/
def stripRoots (Z : ℂ → Set ℂ) (x₀ x₁ : ℝ) (c : ℂ) : Set ℂ := Z c ∩ {z | z.re ∈ Ioo x₀ x₁}

/-- **A decomposition into vertical strips** of the roots `Z (γ t)`, `t ∈ [u, v]`: every root
lies in one of the `m` strips `edge i < Re < edge (i + 1)`, the strip `i` contains `size i` roots,
and every path word of every labelling of the roots of the strip `i` is conjugate to `word i`. -/
structure IsStripDecomposition (Z : ℂ → Set ℂ) (γ : ℝ → ℂ) (u v : ℝ) (m : ℕ) (edge : ℕ → ℝ)
    (size : ℕ → ℕ) (word : ∀ i, PositiveAdjacentWord (size i)) : Prop where
  edge_lt : ∀ i < m, edge i < edge (i + 1)
  mem : ∀ t ∈ Icc u v, ∀ z ∈ Z (γ t), ∃ i < m, z.re ∈ Ioo (edge i) (edge (i + 1))
  card : ∀ i < m, ∀ t ∈ Icc u v, (stripRoots Z (edge i) (edge (i + 1)) (γ t)).ncard = size i
  conj : ∀ i < m, ∀ K : Fin (size i) → ℝ → ℂ,
    IsRootLabellingOn (stripRoots Z (edge i) (edge (i + 1))) γ (Icc u v) K →
      ∀ W, IsPathWord K u v W → SignedBraidConj W (word i).toSigned

/-- Distinct open strips are disjoint. -/
theorem strip_eq_of_mem {m : ℕ} {edge : ℕ → ℝ} (hedge : ∀ i < m, edge i < edge (i + 1))
    {i i' : ℕ} (hi : i < m) (hi' : i' < m) {x : ℝ} (hx : x ∈ Ioo (edge i) (edge (i + 1)))
    (hx' : x ∈ Ioo (edge i') (edge (i' + 1))) : i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := le_of_lt_succ_of_le hedge (show i + 1 ≤ i' by omega) hi'.le
    linarith [hx.2, hx'.1]
  · have := le_of_lt_succ_of_le hedge (show i' + 1 ≤ i by omega) hi.le
    linarith [hx'.2, hx.1]

/-- A continuous strand whose real part always lies in one of the strips stays in one strip. -/
theorem exists_strip_of_continuousOn {m : ℕ} {edge : ℕ → ℝ}
    (hedge : ∀ i < m, edge i < edge (i + 1)) {f : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v))
    (hmem : ∀ t ∈ Icc u v, ∃ i < m, (f t).re ∈ Ioo (edge i) (edge (i + 1))) :
    ∃ i < m, ∀ t ∈ Icc u v, (f t).re ∈ Ioo (edge i) (edge (i + 1)) := by
  obtain ⟨i, hi, hiu⟩ := hmem u ⟨le_rfl, huv⟩
  refine ⟨i, hi, fun t ht => ?_⟩
  obtain ⟨i', hi', hit⟩ := hmem t ht
  have hcon : (Set.image (fun s => (f s).re) (Icc u v)).OrdConnected :=
    (isPreconnected_Icc.image _ (Complex.continuous_re.comp_continuousOn hf)).ordConnected
  have hu : (f u).re ∈ (fun s => (f s).re) '' Icc u v := ⟨u, ⟨le_rfl, huv⟩, rfl⟩
  have htt : (f t).re ∈ (fun s => (f s).re) '' Icc u v := ⟨t, ht, rfl⟩
  by_contra hne
  have hii : i ≠ i' := fun h => hne (h ▸ hit)
  -- An edge between the two strips is a value of the real part, in no strip.
  rcases lt_or_gt_of_ne hii with h | h
  · have hle := le_of_lt_succ_of_le hedge (show i + 1 ≤ i' by omega) hi'.le
    have hmid : edge (i + 1) ∈ (fun s => (f s).re) '' Icc u v :=
      hcon.out hu htt ⟨hiu.2.le, hle.trans hit.1.le⟩
    obtain ⟨s, hs, hse⟩ := hmid
    obtain ⟨j, hj, hjs⟩ := hmem s hs
    simp only at hse
    rw [hse] at hjs
    rcases hjs with ⟨h1, h2⟩
    rcases lt_or_ge j (i + 1) with hj1 | hj1
    · have := le_of_lt_succ_of_le hedge (show j + 1 ≤ i + 1 by omega) (by omega)
      linarith
    · have := le_of_lt_succ_of_le hedge (show i + 1 ≤ j by omega) hj.le
      linarith
  · have hle := le_of_lt_succ_of_le hedge (show i' + 1 ≤ i by omega) hi.le
    have hmid : edge (i' + 1) ∈ (fun s => (f s).re) '' Icc u v :=
      hcon.out htt hu ⟨hit.2.le, hle.trans hiu.1.le⟩
    obtain ⟨s, hs, hse⟩ := hmid
    obtain ⟨j, hj, hjs⟩ := hmem s hs
    simp only at hse
    rw [hse] at hjs
    rcases hjs with ⟨h1, h2⟩
    rcases lt_or_ge j (i' + 1) with hj1 | hj1
    · have := le_of_lt_succ_of_le hedge (show j + 1 ≤ i' + 1 by omega) (by omega)
      linarith
    · have := le_of_lt_succ_of_le hedge (show i' + 1 ≤ j by omega) hj.le
      linarith

namespace IsStripDecomposition

variable {Z : ℂ → Set ℂ} {γ : ℝ → ℂ} {u v : ℝ} {m : ℕ} {edge : ℕ → ℝ} {size : ℕ → ℕ}
  {word : ∀ i, PositiveAdjacentWord (size i)}

/-- The strips of the strands of a labelling. -/
theorem exists_strip (hD : IsStripDecomposition Z γ u v m edge size word) (huv : u < v)
    {n : ℕ} {K : Fin n → ℝ → ℂ} (hK : IsRootLabellingOn Z γ (Icc u v) K) :
    ∃ strip : Fin n → ℕ, (∀ k, strip k < m) ∧
      (∀ k, ∀ t ∈ Icc u v, (K k t).re ∈ Ioo (edge (strip k)) (edge (strip k + 1))) ∧
      (∀ i < m, ∀ t ∈ Icc u v,
        stripRoots Z (edge i) (edge (i + 1)) (γ t) = (fun k => K k t) '' {k | strip k = i}) ∧
      (∀ i < m, Fintype.card {k // strip k = i} = size i) ∧ blockOffset size m = n := by
  classical
  have hu : u ∈ Icc u v := ⟨le_rfl, huv.le⟩
  -- The strip of each strand.
  have hex : ∀ k, ∃ i < m, ∀ t ∈ Icc u v, (K k t).re ∈ Ioo (edge i) (edge (i + 1)) := fun k =>
    exists_strip_of_continuousOn hD.edge_lt huv.le (hK.continuousOn k) fun t ht =>
      hD.mem t ht _ (hK.mem ht k)
  choose strip hstrip hre using hex
  -- The roots of a strip at time `t` are the strands of that strip.
  have hstripset : ∀ i < m, ∀ t ∈ Icc u v,
      stripRoots Z (edge i) (edge (i + 1)) (γ t) = (fun k => K k t) '' {k | strip k = i} := by
    intro i hi t ht
    ext z
    constructor
    · rintro ⟨hz, hzs⟩
      rw [← hK.range_eq t ht] at hz
      obtain ⟨k, rfl⟩ := hz
      exact ⟨k, strip_eq_of_mem hD.edge_lt (hstrip k) hi (hre k t ht) hzs, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨hK.mem ht k, ?_⟩
      have := hre k t ht
      rw [hk] at this
      exact this
  have hcard : ∀ i < m, Fintype.card {k // strip k = i} = size i := by
    intro i hi
    rw [← hD.card i hi u hu, hstripset i hi u hu,
      Set.ncard_image_of_injective _ (hK.injective u hu), ← _root_.Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
    rfl
  have hn : blockOffset size m = n := by
    have h1 : Finset.card (Finset.univ : Finset (Fin n)) =
        ∑ i ∈ Finset.range m, (Finset.univ.filter fun k => strip k = i).card :=
      Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_range.mpr (hstrip k)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    rw [h1, blockOffset]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hcard i (Finset.mem_range.mp hi), Fintype.card_subtype]
  exact ⟨strip, hstrip, hre, hstripset, hcard, hn⟩

/-- The strips contain all the roots. -/
theorem blockOffset_eq (hD : IsStripDecomposition Z γ u v m edge size word) (huv : u < v)
    {n : ℕ} {K : Fin n → ℝ → ℂ} (hK : IsRootLabellingOn Z γ (Icc u v) K) :
    blockOffset size m = n :=
  (hD.exists_strip huv hK).choose_spec.2.2.2.2

/-- **Path words of roots in strips.** Every path word of every labelling of the roots is
conjugate to the product of the strip words placed on consecutive positions. -/
theorem signedBraidConj (hD : IsStripDecomposition Z γ u v m edge size word) (huv : u < v)
    {n : ℕ} {K : Fin n → ℝ → ℂ} (hK : IsRootLabellingOn Z γ (Icc u v) K) {W : SignedAdjacentWord n}
    (hW : IsPathWord K u v W) : SignedBraidConj W (blockProduct n m size word).toSigned := by
  obtain ⟨strip, hstrip, hre, hstripset, hcard, hn⟩ := hD.exists_strip huv hK
  refine IsPathWord.signedBraidConj_blockProduct m n size word edge K strip huv hD.edge_lt hn
    hstrip hre hcard hK.continuousOn hK.injective (fun i hi ι hι hιs W' hW' => ?_) W hW
  -- The strands of a strip label its roots.
  refine hD.conj i hi (fun a => K (ι a)) ⟨fun a => hK.continuousOn _,
    fun t ht => (hK.injective t ht).comp hι, fun t ht => ?_⟩ W' hW'
  have hsub : range (fun a => K (ι a) t) ⊆ stripRoots Z (edge i) (edge (i + 1)) (γ t) := by
    rintro _ ⟨a, rfl⟩
    rw [hstripset i hi t ht]
    exact ⟨ι a, hιs a, rfl⟩
  refine Set.eq_of_subset_of_ncard_le hsub ?_ ?_
  · rw [hD.card i hi t ht, ← Set.image_univ,
      Set.ncard_image_of_injective (f := fun a => K (ι a) t) _ ((hK.injective t ht).comp hι),
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  · rw [hstripset i hi t ht]
    exact Set.toFinite _

end IsStripDecomposition

/-! ### Reordering placed block words -/

theorem mem_toSigned_shiftPositive {a n p : ℕ} {h : p + a ≤ n} {w : PositiveAdjacentWord a}
    {x : Fin (n - 1) × ℤˣ} (hx : x ∈ (shiftPositive p h w).toSigned) :
    p ≤ x.1.val ∧ x.1.val + 2 ≤ p + a := by
  simp only [PositiveAdjacentWord.toSigned, shiftPositive, List.map_map, List.mem_map,
    Function.comp_apply] at hx
  obtain ⟨y, -, rfl⟩ := hx
  have := y.isLt
  simp only
  omega

/-- The letters of a placed block word lie in its positions. -/
theorem mem_toSigned_blockShift {n : ℕ} {size : ℕ → ℕ} {word : ∀ i, PositiveAdjacentWord (size i)}
    {i : ℕ} {x : Fin (n - 1) × ℤˣ} (hx : x ∈ (blockShift n size word i).toSigned) :
    blockOffset size i ≤ x.1.val ∧ x.1.val + 2 ≤ blockOffset size i + size i := by
  unfold blockShift at hx
  split_ifs at hx with h
  · exact mem_toSigned_shiftPositive hx
  · simp [PositiveAdjacentWord.toSigned] at hx

/-- Placed words of distinct blocks are far apart. -/
theorem blockShift_far {n : ℕ} {size : ℕ → ℕ} {word : ∀ i, PositiveAdjacentWord (size i)}
    {i i' : ℕ} (hii : i ≠ i') {x y : Fin (n - 1) × ℤˣ}
    (hx : x ∈ (blockShift n size word i).toSigned)
    (hy : y ∈ (blockShift n size word i').toSigned) :
    x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val := by
  have h1 := mem_toSigned_blockShift hx
  have h2 := mem_toSigned_blockShift hy
  rcases lt_or_gt_of_ne hii with h | h
  · have := blockOffset_add_le size h
    omega
  · have := blockOffset_add_le size h
    omega

/-- **Reordering pairwise far words.** -/
theorem flatMap_equiv_of_perm {n : ℕ} {α : Type*} {w : α → SignedAdjacentWord n}
    {l₁ l₂ : List α} (hp : l₁.Perm l₂) (hnd : l₁.Nodup)
    (hfar : ∀ a ∈ l₁, ∀ b ∈ l₁, a ≠ b → ∀ x ∈ w a, ∀ y ∈ w b,
      x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val) :
    SignedBraidEquiv (l₁.flatMap w) (l₂.flatMap w) := by
  induction hp with
  | nil => exact SignedBraidEquiv.refl _
  | cons a hp ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (ih (List.nodup_cons.mp hnd).2 fun x hx y hy => hfar x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)).append_left _
  | swap a b l =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons,
      ← List.append_assoc, ← List.append_assoc]
    have hba : b ≠ a := by
      intro h; subst h; exact (List.nodup_cons.mp hnd).1 (List.mem_cons_self ..)
    refine (SignedBraidEquiv.far_comm _ _ fun x hx y hy => ?_).append_right _
    exact hfar b (List.mem_cons_self ..) a (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hba
      x hx y hy
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ hnd hfar).trans (ih₂ (h₁.nodup_iff.mp hnd) fun a ha b hb =>
      hfar a (h₁.mem_iff.mpr ha) b (h₁.mem_iff.mpr hb))

theorem flatMap_filter_of_nil {n : ℕ} {α : Type*} (w : α → SignedAdjacentWord n)
    (P : α → Prop) [DecidablePred P] (hP : ∀ a, ¬ P a → w a = []) :
    ∀ l : List α, (l.filter fun a => P a).flatMap w = l.flatMap w
  | [] => rfl
  | a :: l => by
    by_cases ha : P a
    · rw [List.filter_cons_of_pos (by simpa using ha), List.flatMap_cons, List.flatMap_cons,
        flatMap_filter_of_nil w P hP l]
    · rw [List.filter_cons_of_neg (by simpa using ha), List.flatMap_cons, hP a ha,
        List.nil_append, flatMap_filter_of_nil w P hP l]

/-- **The block product in any order.** The product of the placed block words is equivalent to
the product, in the order of any duplicate-free list `l` of blocks `< m` containing all blocks with
nonempty words, of the placed words of the blocks of `l`. -/
theorem blockProduct_equiv_flatMap {n m : ℕ} {size : ℕ → ℕ}
    {word : ∀ i, PositiveAdjacentWord (size i)} (l : List ℕ) (hnd : l.Nodup)
    (hl : ∀ i ∈ l, i < m) (hall : ∀ i < m, blockShift n size word i ≠ [] → i ∈ l) :
    SignedBraidEquiv (blockProduct n m size word).toSigned
      (l.flatMap fun i => (blockShift n size word i).toSigned) := by
  classical
  set w : ℕ → SignedAdjacentWord n := fun i => (blockShift n size word i).toSigned
  have hP : ∀ i, ¬ (blockShift n size word i ≠ []) → w i = [] := fun i hi => by
    simp only [ne_eq, not_not] at hi
    simp [w, hi, PositiveAdjacentWord.toSigned]
  rw [blockProduct, toSigned_flatMap]
  change SignedBraidEquiv ((List.range m).flatMap w) (l.flatMap w)
  rw [← flatMap_filter_of_nil w _ hP (List.range m), ← flatMap_filter_of_nil w _ hP l]
  have hnd₁ : ((List.range m).filter fun i => blockShift n size word i ≠ []).Nodup :=
    List.nodup_range.filter _
  refine flatMap_equiv_of_perm ?_ hnd₁ fun a _ b _ hab x hx y hy => blockShift_far hab hx hy
  refine (List.perm_ext_iff_of_nodup hnd₁ (hnd.filter _)).mpr fun i => ?_
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hne⟩; exact ⟨hall i hi hne, hne⟩
  · rintro ⟨hi, hne⟩; exact ⟨hl i hi, hne⟩

end OnLeConjecture.Analytic
