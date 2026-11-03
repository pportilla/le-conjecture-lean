/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondRelative
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Point configurations in cyclic order

A configuration is an embedding `c : Fin k ↪ Fin m` whose points occur in
positive cyclic order. A permutation `ρ` of `Fin k` is transported to the
permutation `cfgPerm c ρ` of `Fin m`, which fixes every point outside the
image of `c`. Comparisons of cyclic distances between configuration points,
and membership of configuration points in cyclic intervals between
configuration points, are computed in `Fin k`.

Every permutation of `Fin m` is the transported permutation of a derangement
along its increasingly enumerated support. A rotation of the labels of a
configuration gives another configuration in cyclic order, so a pattern may be
replaced by any of its conjugates by a rotation of `Fin k`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

section Config

variable {m k : ℕ}

/-- The permutation of `Fin m` transported from a permutation of `Fin k` along an
embedding. It fixes every point outside the image. -/
noncomputable def cfgPerm (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin m) :=
  ρ.viaEmbedding c

@[simp] theorem cfgPerm_apply_emb (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) (i : Fin k) :
    cfgPerm c ρ (c i) = c (ρ i) :=
  Equiv.Perm.viaEmbedding_apply ρ c i

theorem cfgPerm_apply_of_notMem (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) {x : Fin m}
    (hx : x ∉ Set.range c) : cfgPerm c ρ x = x :=
  Equiv.Perm.viaEmbedding_apply_of_notMem ρ c x hx

theorem cfgPerm_mul (c : Fin k ↪ Fin m) (ρ σ : Equiv.Perm (Fin k)) :
    cfgPerm c (ρ * σ) = cfgPerm c ρ * cfgPerm c σ :=
  (Equiv.Perm.viaEmbeddingHom c).map_mul ρ σ

@[simp] theorem cfgPerm_one (c : Fin k ↪ Fin m) : cfgPerm c 1 = 1 :=
  (Equiv.Perm.viaEmbeddingHom c).map_one

theorem cfgPerm_inv (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) :
    cfgPerm c ρ⁻¹ = (cfgPerm c ρ)⁻¹ :=
  (Equiv.Perm.viaEmbeddingHom c).map_inv ρ

theorem cfgPerm_injective (c : Fin k ↪ Fin m) : Function.Injective (cfgPerm c) :=
  Equiv.Perm.viaEmbeddingHom_injective c

theorem cfgPerm_swap (c : Fin k ↪ Fin m) (i j : Fin k) :
    cfgPerm c (Equiv.swap i j) = Equiv.swap (c i) (c j) := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range c
  · obtain ⟨l, rfl⟩ := hx
    rw [cfgPerm_apply_emb, Equiv.swap_apply_def, Equiv.swap_apply_def]
    simp only [c.injective.eq_iff]
    split_ifs <;> rfl
  · have hi : x ≠ c i := fun h => hx ⟨i, h.symm⟩
    have hj : x ≠ c j := fun h => hx ⟨j, h.symm⟩
    rw [cfgPerm_apply_of_notMem c _ hx, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem cfgPerm_mul_swap (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) (i j : Fin k) :
    cfgPerm c ρ * Equiv.swap (c i) (c j) = cfgPerm c (ρ * Equiv.swap i j) := by
  rw [cfgPerm_mul, cfgPerm_swap]

theorem support_cfgPerm (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) :
    (cfgPerm c ρ).support = ρ.support.map c := by
  ext x
  rw [Equiv.Perm.mem_support, Finset.mem_map]
  constructor
  · intro hx
    by_cases hr : x ∈ Set.range c
    · obtain ⟨l, rfl⟩ := hr
      refine ⟨l, ?_, rfl⟩
      rw [Equiv.Perm.mem_support]
      intro h
      apply hx
      rw [cfgPerm_apply_emb, h]
    · exact (hx (cfgPerm_apply_of_notMem c ρ hr)).elim
  · rintro ⟨l, hl, rfl⟩
    rw [cfgPerm_apply_emb]
    intro h
    exact (Equiv.Perm.mem_support.mp hl) (c.injective h)

theorem card_support_cfgPerm (c : Fin k ↪ Fin m) (ρ : Equiv.Perm (Fin k)) :
    (cfgPerm c ρ).support.card = ρ.support.card := by
  rw [support_cfgPerm, Finset.card_map]

/-- A sum over `Fin m` of a function vanishing off a configuration is a sum over the
configuration. -/
theorem sum_eq_sum_emb {M : Type*} [AddCommMonoid M] (c : Fin k ↪ Fin m) (f : Fin m → M)
    (hf : ∀ x, x ∉ Set.range c → f x = 0) : ∑ x, f x = ∑ i, f (c i) := by
  classical
  rw [← Finset.sum_map Finset.univ c f]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  apply hf
  rintro ⟨i, rfl⟩
  exact hx (Finset.mem_map_of_mem _ (Finset.mem_univ _))

/-! ### Configurations in positive cyclic order -/

/-- The points of `c` occur in positive cyclic order, starting with `c 0`. -/
def CycSorted [NeZero k] (c : Fin k ↪ Fin m) : Prop :=
  StrictMono fun i : Fin k => cycDist (c 0) (c i)

theorem cycDist_emb_le_iff [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (i l l' : Fin k) :
    cycDist (c i) (c l) ≤ cycDist (c i) (c l') ↔ cycDist i l ≤ cycDist i l' := by
  have e1 : ∀ a b : Fin k, cycDist (c 0) (c a) ≤ cycDist (c 0) (c b) ↔ a.val ≤ b.val :=
    fun a b => hc.le_iff_le.trans Fin.le_def
  have h1 := e1 i l; have h2 := e1 i l'; have h3 := e1 l l'
  have h4 := e1 l i; have h5 := e1 l' i; have h6 := e1 l' l
  have b1 := cycDist_lt (c 0) (c i); have b2 := cycDist_lt (c 0) (c l)
  have b3 := cycDist_lt (c 0) (c l')
  have hi := i.isLt; have hl := l.isLt; have hl' := l'.isLt
  rw [cycDist_rebase (c 0) (c i) (c l), cycDist_rebase (c 0) (c i) (c l')]
  generalize cycDist (c 0) (c i) = Pi at *
  generalize cycDist (c 0) (c l) = Pl at *
  generalize cycDist (c 0) (c l') = Pl' at *
  unfold cycDist
  split_ifs <;> omega

theorem cycDist_emb_lt_iff [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (i l l' : Fin k) :
    cycDist (c i) (c l) < cycDist (c i) (c l') ↔ cycDist i l < cycDist i l' := by
  rw [← not_le, ← not_le, cycDist_emb_le_iff hc]

theorem cycDist_emb_eq_zero_iff (c : Fin k ↪ Fin m) (i l : Fin k) :
    cycDist (c i) (c l) = 0 ↔ cycDist i l = 0 := by
  rw [cycDist_eq_zero_iff, cycDist_eq_zero_iff, c.injective.eq_iff]

theorem mem_cIoo_emb_iff [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c) (i j l : Fin k) :
    c l ∈ Grid.cIoo (c i) (c j) ↔ l ∈ Grid.cIoo i j := by
  rw [mem_cIoo_iff_cycDist, mem_cIoo_iff_cycDist, cycDist_emb_lt_iff hc,
    Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero, Ne, Ne, cycDist_emb_eq_zero_iff]

theorem mem_cIco_emb_iff [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c) (i j l : Fin k) :
    c l ∈ Grid.cIco (c i) (c j) ↔ l ∈ Grid.cIco i j := by
  rw [mem_cIco_iff_cycDist, mem_cIco_iff_cycDist, cycDist_emb_lt_iff hc]

/-- The vanishing of `icoInterCard` depends only on the comparisons of its three
arguments and on the vanishing of the first and third arguments. -/
theorem icoInterCard_eq_zero_congr {B C D B' C' D' : ℕ}
    (h1 : B ≤ C ↔ B' ≤ C') (h2 : C ≤ B ↔ C' ≤ B') (h3 : C ≤ D ↔ C' ≤ D')
    (h4 : D ≤ C ↔ D' ≤ C') (h5 : B ≤ D ↔ B' ≤ D') (h6 : D ≤ B ↔ D' ≤ B')
    (h7 : B = 0 ↔ B' = 0) (h8 : D = 0 ↔ D' = 0) :
    icoInterCard B C D = 0 ↔ icoInterCard B' C' D' = 0 := by
  unfold icoInterCard
  split_ifs <;> omega

/-- Two half-open cyclic intervals between configuration points meet exactly when
the corresponding intervals of labels meet. -/
theorem card_cIco_inter_emb_eq_zero_iff [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (i j i' j' : Fin k) :
    (Grid.cIco (c i) (c j) ∩ Grid.cIco (c i') (c j')).card = 0 ↔
      (Grid.cIco i j ∩ Grid.cIco i' j').card = 0 := by
  rw [card_cIco_inter_cIco, card_cIco_inter_cIco]
  apply icoInterCard_eq_zero_congr <;>
    first
    | exact cycDist_emb_le_iff hc _ _ _
    | exact cycDist_emb_eq_zero_iff c _ _

/-! ### The increasingly enumerated support -/

/-- The support of a permutation, enumerated increasingly. -/
noncomputable def supportCfg (σ : Equiv.Perm (Fin m)) : Fin σ.support.card ↪ Fin m :=
  (σ.support.orderEmbOfFin rfl).toEmbedding

theorem supportCfg_apply (σ : Equiv.Perm (Fin m)) (i : Fin σ.support.card) :
    supportCfg σ i = σ.support.orderEmbOfFin rfl i := rfl

theorem supportCfg_mem (σ : Equiv.Perm (Fin m)) (i : Fin σ.support.card) :
    supportCfg σ i ∈ σ.support :=
  Finset.orderEmbOfFin_mem _ _ _

theorem range_supportCfg (σ : Equiv.Perm (Fin m)) :
    Set.range (supportCfg σ) = σ.support :=
  Finset.range_orderEmbOfFin σ.support rfl

theorem mem_range_supportCfg_iff (σ : Equiv.Perm (Fin m)) (x : Fin m) :
    x ∈ Set.range (supportCfg σ) ↔ σ x ≠ x := by
  rw [range_supportCfg, Finset.mem_coe, Equiv.Perm.mem_support]

theorem cycSorted_supportCfg (σ : Equiv.Perm (Fin m)) [NeZero σ.support.card] :
    CycSorted (supportCfg σ) := by
  intro i j hij
  have hmono := (σ.support.orderEmbOfFin rfl).strictMono
  have h0 : supportCfg σ 0 ≤ supportCfg σ i :=
    (σ.support.orderEmbOfFin rfl).monotone (Fin.zero_le i)
  have h0' : supportCfg σ 0 ≤ supportCfg σ j :=
    (σ.support.orderEmbOfFin rfl).monotone (Fin.zero_le j)
  have hlt : supportCfg σ i < supportCfg σ j := hmono hij
  simp only [cycDist]
  rw [Fin.le_def] at h0 h0'
  rw [Fin.lt_def] at hlt
  rw [if_pos h0, if_pos h0']
  omega

/-- The derangement of the labels induced by a permutation on its enumerated
support. -/
noncomputable def supportPattern (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin σ.support.card) :=
  ((σ.support.orderIsoOfFin rfl).toEquiv.trans
    (σ.subtypePerm fun _ => Equiv.Perm.apply_mem_support)).trans
    (σ.support.orderIsoOfFin rfl).toEquiv.symm

theorem supportCfg_supportPattern (σ : Equiv.Perm (Fin m)) (i : Fin σ.support.card) :
    supportCfg σ (supportPattern σ i) = σ (supportCfg σ i) := by
  rw [supportCfg_apply, supportCfg_apply, ← Finset.coe_orderIsoOfFin_apply,
    ← Finset.coe_orderIsoOfFin_apply]
  simp [supportPattern]

theorem cfgPerm_supportPattern (σ : Equiv.Perm (Fin m)) :
    cfgPerm (supportCfg σ) (supportPattern σ) = σ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range (supportCfg σ)
  · obtain ⟨i, rfl⟩ := hx
    rw [cfgPerm_apply_emb, supportCfg_supportPattern]
  · rw [cfgPerm_apply_of_notMem _ _ hx]
    rw [mem_range_supportCfg_iff, not_not] at hx
    exact hx.symm

theorem supportPattern_apply_ne (σ : Equiv.Perm (Fin m)) (i : Fin σ.support.card) :
    supportPattern σ i ≠ i := by
  intro h
  have := supportCfg_supportPattern σ i
  rw [h] at this
  exact Equiv.Perm.mem_support.mp (supportCfg_mem σ i) this.symm

/-! ### Rotations of a configuration -/

/-- The configuration with labels rotated by `r`. -/
def rotEmb [NeZero k] (c : Fin k ↪ Fin m) (r : Fin k) : Fin k ↪ Fin m :=
  ⟨fun i => c (i + r), fun i j h => by simpa using c.injective h⟩

@[simp] theorem rotEmb_apply [NeZero k] (c : Fin k ↪ Fin m) (r i : Fin k) :
    rotEmb c r i = c (i + r) := rfl

/-- The pattern conjugated by the rotation of labels by `r`. -/
def rotPattern [NeZero k] (r : Fin k) (ρ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) :=
  (Equiv.addRight r).trans (ρ.trans (Equiv.addRight r).symm)

@[simp] theorem rotPattern_apply [NeZero k] (r : Fin k) (ρ : Equiv.Perm (Fin k)) (i : Fin k) :
    rotPattern r ρ i = ρ (i + r) - r := by
  simp [rotPattern, sub_eq_add_neg]

theorem cfgPerm_rotEmb [NeZero k] (c : Fin k ↪ Fin m) (r : Fin k) (ρ : Equiv.Perm (Fin k)) :
    cfgPerm (rotEmb c r) (rotPattern r ρ) = cfgPerm c ρ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range c
  · obtain ⟨l, rfl⟩ := hx
    have hl : c l = rotEmb c r (l - r) := by simp
    rw [hl, cfgPerm_apply_emb, rotPattern_apply, rotEmb_apply, ← hl, cfgPerm_apply_emb]
    simp
  · have hx' : x ∉ Set.range (rotEmb c r) := by
      rintro ⟨i, rfl⟩
      exact hx ⟨i + r, rfl⟩
    rw [cfgPerm_apply_of_notMem _ _ hx, cfgPerm_apply_of_notMem _ _ hx']

theorem cycDist_add_right [NeZero k] (r i : Fin k) : cycDist r (i + r) = i.val := by
  have hr := r.isLt; have hi := i.isLt
  unfold cycDist
  rw [Fin.val_add]
  split_ifs with h
  · rcases Nat.lt_or_ge (i.val + r.val) k with h' | h'
    · rw [Nat.mod_eq_of_lt h']; omega
    · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h ⊢; omega
  · rcases Nat.lt_or_ge (i.val + r.val) k with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h ⊢; omega
    · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]; omega

theorem cycSorted_rotEmb [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c) (r : Fin k) :
    CycSorted (rotEmb c r) := by
  intro i j hij
  simp only [rotEmb_apply, zero_add]
  rw [cycDist_emb_lt_iff hc, cycDist_add_right, cycDist_add_right]
  exact hij

end Config

end OnLeConjecture.KnotFloer.GridFull
