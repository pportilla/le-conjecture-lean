/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyLocalWord
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Braid words of continuous paths of configurations

Let `K : Fin S → ℝ → ℂ` be a family of `S` strands, continuous on `[u, v]`, with pairwise
distinct points at every time of `[u, v]`. This module attaches to `K` a signed braid word up
to `SignedBraidEquiv`, the *path word*, without any genericity or transversality assumption.

For a sequence `X : ℕ → (Fin S → ℂ)` of configurations, `chainWord X N` is the product of the
local words `localWord (X a) (X a) (X (a + 1))`, `a < N`. For a strict partition `t` of
`[u, v]` (`IsStrictPartition`) the configurations `K · (t a)` give the chain word of the
partition. `IsPathWord K u v W` says that `W` is equivalent to the chain words of all
sufficiently fine strict partitions.

* `exists_config_modulus`: a continuous family of configurations on a compact set has a uniform
  separation `m > 0` and a uniform modulus `δ` for closeness `m / 8`.
* `chainWord_compare`: two chains whose configurations are grouped into cells of nearby
  configurations, with common endpoints, have equivalent chain words. Hence the chain words of
  two strict partitions of mesh less than `δ / 2` are equivalent (`chainWord_partition_equiv`).
* `exists_isPathWord`, `IsPathWord.unique`: every continuous family of configurations has a
  path word, unique up to `SignedBraidEquiv`.
* `IsPathWord.append`, `IsPathWord.relabel`, `IsPathWord.comp_affine`, `IsPathWord.const`:
  concatenation, relabelling, affine reparametrization and constant families.
* `IsPathWord.of_configSort_const`, `IsPathWord.of_configSort_swap`: a family whose
  lexicographic order is constant has trivial path word; a family whose order changes once by an
  adjacent exchange has the corresponding single signed letter as path word.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory

variable {S : ℕ}

/-! ### Uniform separation and closeness on compact sets -/

theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ m > 0, ∀ i, m ≤ μ i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min μ
    exact ⟨μ i₀, hμ i₀, hi₀⟩

/-- **Uniform separation and modulus.** A family of configurations, continuous on a compact
set and injective at each point, has a uniform separation `m > 0` and a modulus `δ > 0` for
closeness `m / 8`. -/
theorem exists_config_modulus {X : Type*} [PseudoMetricSpace X] {A : Set X} (hA : IsCompact A)
    {F : X → Fin S → ℂ} (hF : ∀ k, ContinuousOn (fun x => F x k) A)
    (hinj : ∀ x ∈ A, Injective (F x)) :
    ∃ m > 0, ∃ δ > 0, (∀ x ∈ A, ConfigSeparated (F x) m) ∧
      ∀ x ∈ A, ∀ y ∈ A, dist x y < δ → ConfigNear (F x) (F y) (m / 8) := by
  classical
  have hpair : ∀ p : Fin S × Fin S, ∃ μ > 0, p.1 ≠ p.2 → ∀ x ∈ A, μ ≤ ‖F x p.1 - F x p.2‖ := by
    intro p
    rcases A.eq_empty_or_nonempty with hAe | hAn
    · exact ⟨1, one_pos, fun _ x hx => by rw [hAe] at hx; exact hx.elim⟩
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => (h hp).elim⟩
    have hc : ContinuousOn (fun x => ‖F x p.1 - F x p.2‖) A :=
      ((hF p.1).sub (hF p.2)).norm
    obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn hAn hc
    refine ⟨‖F x₀ p.1 - F x₀ p.2‖, ?_, fun _ x hx => hmin hx⟩
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hp (hinj x₀ hx₀ h))
  choose μ hμ hμA using hpair
  obtain ⟨m, hm, hmμ⟩ := exists_pos_le_of_finite μ hμ
  have hsep : ∀ x ∈ A, ConfigSeparated (F x) m := fun x hx k l hkl =>
    (hmμ (k, l)).trans (hμA (k, l) hkl x hx)
  have hFc : ContinuousOn F A := continuousOn_pi.mpr hF
  have hunif := (hA.uniformContinuousOn_of_continuous hFc)
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ, hδF⟩ := hunif (m / 8) (by positivity)
  refine ⟨m, hm, δ, hδ, hsep, fun x hx y hy hxy k => ?_⟩
  have := (dist_le_pi_dist (F x) (F y) k).trans_lt (hδF x hx y hy hxy)
  rwa [dist_eq_norm] at this

/-! ### Chain words -/

/-- The chain word of a sequence of configurations: the product of the local words of the
consecutive pairs `X a, X (a + 1)`, `a < N`, each with center `X a`. -/
def chainWord (X : ℕ → Fin S → ℂ) : ℕ → SignedAdjacentWord S
  | 0 => []
  | a + 1 => chainWord X a ++ localWord (X a) (X a) (X (a + 1))

@[simp] theorem chainWord_zero (X : ℕ → Fin S → ℂ) : chainWord X 0 = [] := rfl

theorem chainWord_succ (X : ℕ → Fin S → ℂ) (a : ℕ) :
    chainWord X (a + 1) = chainWord X a ++ localWord (X a) (X a) (X (a + 1)) := rfl

theorem chainWord_add (X : ℕ → Fin S → ℂ) (a b : ℕ) :
    chainWord X (a + b) = chainWord X a ++ chainWord (fun c => X (a + c)) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, chainWord_succ, ih, chainWord_succ, List.append_assoc]
    rfl

theorem chainWord_congr {X X' : ℕ → Fin S → ℂ} {N : ℕ} (h : ∀ a ≤ N, X a = X' a) :
    chainWord X N = chainWord X' N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [chainWord_succ, chainWord_succ, ih (fun a ha => h a (by omega)), h N (by omega),
      h (N + 1) le_rfl]

/-- Relabelling all the configurations of a chain does not change its chain word. -/
theorem chainWord_relabel {X : ℕ → Fin S → ℂ} {N : ℕ} (hX : ∀ a ≤ N, Injective (X a))
    (τ : Equiv.Perm (Fin S)) : chainWord (fun a => X a ∘ τ) N = chainWord X N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [chainWord_succ, chainWord_succ, ih (fun a ha => hX a (by omega)),
      localWord_relabel (hX N (by omega)) (hX (N + 1) le_rfl)]

/-- A chain of equal configurations has trivial chain word. -/
theorem chainWord_const {X : ℕ → Fin S → ℂ} {N : ℕ} (h : ∀ a ≤ N, X a = X 0) :
    SignedBraidEquiv (chainWord X N) [] := by
  induction N with
  | zero => exact SignedBraidEquiv.refl _
  | succ N ih =>
    rw [chainWord_succ, h N (by omega), h (N + 1) le_rfl]
    simpa using (ih fun a ha => h a (by omega)).append (localWord_self (X 0) (X 0))

/-! ### Cells -/

/-- A cell: a set of configurations, each with separation at least `m`, pairwise within
`m / 8`. -/
def IsConfigCell (C : Set (Fin S → ℂ)) (m : ℝ) : Prop :=
  (∀ x ∈ C, ConfigSeparated x m) ∧ ∀ x ∈ C, ∀ y ∈ C, ConfigNear x y (m / 8)

theorem IsConfigCell.localWord_center {C : Set (Fin S → ℂ)} {m : ℝ} (hm : 0 < m)
    (hC : IsConfigCell C m) {z z' x y : Fin S → ℂ} (hz : z ∈ C) (hz' : z' ∈ C) (hx : x ∈ C)
    (hy : y ∈ C) : SignedBraidEquiv (localWord z x y) (localWord z' x y) :=
  OnLeConjecture.Analytic.localWord_center hm (hC.1 z hz) (hC.1 z' hz') (hC.2 x hx z hz)
    (hC.2 y hy z hz)
    (hC.2 x hx z' hz') (hC.2 y hy z' hz')

/-- The chain word of a chain inside a cell is the local word between its endpoints, with any
center in the cell. -/
theorem IsConfigCell.chainWord {C : Set (Fin S → ℂ)} {m : ℝ} (hm : 0 < m)
    (hC : IsConfigCell C m) {z : Fin S → ℂ} (hz : z ∈ C) {Y : ℕ → Fin S → ℂ} {b : ℕ}
    (hY : ∀ c ≤ b, Y c ∈ C) :
    SignedBraidEquiv (OnLeConjecture.Analytic.chainWord Y b) (localWord z (Y 0) (Y b)) := by
  induction b with
  | zero => exact (localWord_self z (Y 0)).symm
  | succ b ih =>
    rw [chainWord_succ]
    have h1 := ih fun c hc => hY c (by omega)
    have h2 := hC.localWord_center hm (hY b (by omega)) hz (hY b (by omega)) (hY (b + 1) le_rfl)
    exact (h1.append h2).trans (localWord_comp z _ _ _)

/-- **Comparison of chains.** Let the configurations of the chain `X` (of length `N`) and of
the chain `Y` be grouped by an increasing function `g`: for each `a < N`, the configurations
`X a`, `X (a + 1)` and `Y c`, `g a ≤ c ≤ g (a + 1)`, lie in a cell. If the chains have common
endpoints, their chain words are equivalent. -/
theorem chainWord_compare {m : ℝ} (hm : 0 < m) {X Y : ℕ → Fin S → ℂ} {N : ℕ} (g : ℕ → ℕ)
    (hg : ∀ a < N, g a ≤ g (a + 1)) (hg0 : g 0 = 0) (hX0 : X 0 = Y 0) (hXN : X N = Y (g N))
    (C : ℕ → Set (Fin S → ℂ)) (hC : ∀ a < N, IsConfigCell (C a) m)
    (hXC : ∀ a < N, X a ∈ C a ∧ X (a + 1) ∈ C a)
    (hYC : ∀ a < N, ∀ c, g a ≤ c → c ≤ g (a + 1) → Y c ∈ C a) :
    SignedBraidEquiv (chainWord X N) (chainWord Y (g N)) := by
  have key : ∀ a ≤ N, SignedBraidEquiv (chainWord X a ++ localWord (X a) (X a) (Y (g a)))
      (chainWord Y (g a)) := by
    intro a
    induction a with
    | zero =>
      intro _
      rw [hg0, hX0]
      simpa using localWord_self (Y 0) (Y 0)
    | succ a ih =>
      intro ha
      have haN : a < N := by omega
      obtain ⟨hXa, hXa1⟩ := hXC a haN
      have hYa : Y (g a) ∈ C a := hYC a haN _ le_rfl (hg a haN)
      have hYa1 : Y (g (a + 1)) ∈ C a := hYC a haN _ (hg a haN) le_rfl
      have hCa := hC a haN
      -- Left side.
      have l1 := hCa.localWord_center hm hXa1 hXa hXa1 hYa1
      have l2 : SignedBraidEquiv
          (localWord (X a) (X a) (X (a + 1)) ++ localWord (X (a + 1)) (X (a + 1)) (Y (g (a + 1))))
          (localWord (X a) (X a) (Y (g a)) ++ localWord (X a) (Y (g a)) (Y (g (a + 1)))) :=
        (((SignedBraidEquiv.refl _).append l1).trans (localWord_comp _ _ _ _)).trans
          (localWord_comp _ _ _ _).symm
      have l3 : SignedBraidEquiv
          (chainWord X (a + 1) ++ localWord (X (a + 1)) (X (a + 1)) (Y (g (a + 1))))
          (chainWord Y (g a) ++ localWord (X a) (Y (g a)) (Y (g (a + 1)))) := by
        rw [chainWord_succ, List.append_assoc]
        refine ((SignedBraidEquiv.refl _).append l2).trans ?_
        rw [← List.append_assoc]
        exact (ih (by omega)).append (SignedBraidEquiv.refl _)
      -- Right side.
      have hsplit : g (a + 1) = g a + (g (a + 1) - g a) := by have := hg a haN; omega
      have r1 : SignedBraidEquiv (chainWord (fun c => Y (g a + c)) (g (a + 1) - g a))
          (localWord (X a) (Y (g a + 0)) (Y (g a + (g (a + 1) - g a)))) :=
        hCa.chainWord hm hXa fun c hc => hYC a haN _ (by omega) (by omega)
      have r2 : SignedBraidEquiv (chainWord Y (g (a + 1)))
          (chainWord Y (g a) ++ localWord (X a) (Y (g a)) (Y (g (a + 1)))) := by
        conv_lhs => rw [hsplit, chainWord_add]
        rw [← hsplit] at r1
        simpa using (SignedBraidEquiv.refl _).append r1
      exact l3.trans r2.symm
  have h := key N le_rfl
  rw [hXN] at h
  have h2 := (SignedBraidEquiv.refl (chainWord X N)).append (localWord_self (Y (g N)) (Y (g N)))
  simpa using h2.symm.trans h

/-! ### Partitions -/

/-- A strict partition `u = t 0 < t 1 < ⋯ < t N = v` of mesh less than `δ`. -/
structure IsStrictPartition (t : ℕ → ℝ) (N : ℕ) (u v δ : ℝ) : Prop where
  zero : t 0 = u
  last : t N = v
  step : ∀ a < N, t a < t (a + 1)
  gap : ∀ a < N, t (a + 1) - t a < δ

namespace IsStrictPartition

variable {t : ℕ → ℝ} {N : ℕ} {u v δ : ℝ}

theorem le_of_le (P : IsStrictPartition t N u v δ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) :
    t a ≤ t b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (ih (by omega) (by omega)).trans (P.step b (by omega)).le

theorem lt_of_lt (P : IsStrictPartition t N u v δ) {a b : ℕ} (hab : a < b) (hb : b ≤ N) :
    t a < t b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact (ih h (by omega)).trans (P.step b (by omega))
    · subst h; exact P.step a (by omega)

theorem mem_Icc (P : IsStrictPartition t N u v δ) {a : ℕ} (ha : a ≤ N) : t a ∈ Icc u v :=
  ⟨P.zero ▸ P.le_of_le (Nat.zero_le a) ha, P.last ▸ P.le_of_le ha le_rfl⟩

theorem mono (P : IsStrictPartition t N u v δ) {δ' : ℝ} (h : δ ≤ δ') :
    IsStrictPartition t N u v δ' :=
  ⟨P.zero, P.last, P.step, fun a ha => (P.gap a ha).trans_le h⟩

end IsStrictPartition

/-- The uniform partition of `[u, v]` into `N` intervals. -/
def uniformPartition (u v : ℝ) (N : ℕ) (a : ℕ) : ℝ := u + a * ((v - u) / N)

theorem isStrictPartition_uniform {u v δ : ℝ} (huv : u < v) {N : ℕ} (hN : 0 < N)
    (hδ : (v - u) / N < δ) : IsStrictPartition (uniformPartition u v N) N u v δ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep : 0 < (v - u) / N := div_pos (by linarith) hNr
  refine ⟨by simp [uniformPartition], ?_, fun a _ => ?_, fun a _ => ?_⟩
  · simp only [uniformPartition]
    field_simp
    ring
  · simp only [uniformPartition]; push_cast; linarith
  · simp only [uniformPartition]; push_cast; linarith

theorem exists_uniform_fine {u v : ℝ} (huv : u < v) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (v - u) / N < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((v - u) / δ)
  have hN0 : 0 < N := by
    have : 0 < (v - u) / δ := div_pos (by linarith) hδ
    exact_mod_cast this.trans hN
  refine ⟨N, hN0, ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [div_lt_iff₀ hNr]
  rw [div_lt_iff₀ hδ] at hN
  linarith

/-! ### Path moduli and the comparison of partitions -/

/-- A modulus of a strand family on `[u, v]`: separation `m` at all times, and closeness `m / 8`
for times closer than `δ`. -/
structure PathModulus (K : Fin S → ℝ → ℂ) (u v m δ : ℝ) : Prop where
  pos : 0 < m
  delta_pos : 0 < δ
  sep : ∀ t ∈ Icc u v, ConfigSeparated (fun k => K k t) m
  near : ∀ t ∈ Icc u v, ∀ t' ∈ Icc u v, |t - t'| < δ →
    ConfigNear (fun k => K k t) (fun k => K k t') (m / 8)

theorem exists_pathModulus {K : Fin S → ℝ → ℂ} {u v : ℝ}
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) : ∃ m δ, PathModulus K u v m δ := by
  obtain ⟨m, hm, δ, hδ, hsep, hnear⟩ := exists_config_modulus (F := fun t k => K k t)
    isCompact_Icc hcont hinj
  exact ⟨m, δ, hm, hδ, hsep, fun t ht t' ht' h => hnear t ht t' ht' (by
    rwa [Real.dist_eq])⟩

/-- **Comparison of partitions.** For a strand family with modulus `(m, δ)`, the chain words of
two strict partitions of mesh less than `δ / 2` are equivalent. -/
theorem chainWord_partition_equiv {K : Fin S → ℝ → ℂ} {u v m δ : ℝ}
    (hK : PathModulus K u v m δ) {t t' : ℕ → ℝ} {N M : ℕ}
    (P : IsStrictPartition t N u v (δ / 2)) (P' : IsStrictPartition t' M u v (δ / 2)) :
    SignedBraidEquiv (chainWord (fun a k => K k (t a)) N)
      (chainWord (fun c k => K k (t' c)) M) := by
  classical
  have hex : ∀ a, ∃ c, min (t a) v ≤ t' c ∨ M ≤ c := fun a => ⟨M, Or.inr le_rfl⟩
  have hgex : ∀ a, ∃ c, (min (t a) v ≤ t' c ∨ M ≤ c) ∧
      ∀ c' < c, ¬(min (t a) v ≤ t' c' ∨ M ≤ c') :=
    fun a => ⟨Nat.find (hex a), Nat.find_spec (hex a), fun c' hc' => Nat.find_min (hex a) hc'⟩
  choose g hg1 hg2 using hgex
  have hgM : ∀ a, g a ≤ M := by
    intro a
    by_contra h
    push Not at h
    exact hg2 a M h (Or.inr le_rfl)
  have hgspec : ∀ a ≤ N, t a ≤ t' (g a) := by
    intro a ha
    have hs := hg1 a
    have hta : t a ≤ v := (P.mem_Icc ha).2
    rw [min_eq_left hta] at hs
    rcases hs with hs | hs
    · exact hs
    · have : g a = M := le_antisymm (hgM a) hs
      rw [this, P'.last]
      exact hta
  have hgmin : ∀ a ≤ N, ∀ c < g a, t' c < t a := by
    intro a ha c hc
    have hn := hg2 a c hc
    have hta : t a ≤ v := (P.mem_Icc ha).2
    rw [min_eq_left hta] at hn
    push Not at hn
    exact hn.1
  have hgmono : ∀ a < N, g a ≤ g (a + 1) := by
    intro a ha
    by_contra hlt
    push Not at hlt
    have h1 := hgmin a ha.le _ hlt
    have h2 := hgspec (a + 1) ha
    linarith [P.step a ha]
  have hg0 : g 0 = 0 := by
    by_contra h
    apply hg2 0 0 (Nat.pos_of_ne_zero h)
    left
    rw [P.zero, P'.zero]
    exact min_le_left _ _
  have hgN : g N = M := by
    apply le_antisymm (hgM N)
    by_contra hlt
    push Not at hlt
    have h1 := hgspec N le_rfl
    rw [P.last] at h1
    have h2 := P'.lt_of_lt hlt le_rfl
    rw [P'.last] at h2
    linarith
  have hgpos : ∀ a < N, 0 < g (a + 1) := by
    intro a ha
    by_contra h0
    have h0' : g (a + 1) = 0 := by omega
    have h1 := hgspec (a + 1) ha
    rw [h0', P'.zero] at h1
    have h2 := P.lt_of_lt (Nat.succ_pos a) ha
    rw [P.zero] at h2
    linarith
  let C : ℕ → Set (Fin S → ℂ) := fun a =>
    {x | ∃ s ∈ Icc u v, t a ≤ s ∧ s ≤ t (a + 1) + δ / 2 ∧ x = fun k => K k s}
  have hCcell : ∀ a < N, IsConfigCell (C a) m := by
    intro a ha
    have hgap := P.gap a ha
    refine ⟨?_, ?_⟩
    · rintro x ⟨s, hs, -, -, rfl⟩
      exact hK.sep s hs
    · rintro x ⟨s, hs, hs1, hs2, rfl⟩ y ⟨s', hs', hs1', hs2', rfl⟩
      apply hK.near s hs s' hs'
      rw [abs_lt]
      constructor <;> linarith
  refine (chainWord_compare hK.pos g hgmono hg0 ?_ ?_ C hCcell ?_ ?_).trans
    (SignedBraidEquiv.of_eq (by rw [hgN]))
  · simp only [P.zero, P'.zero]
  · simp only [P.last, hgN, P'.last]
  · intro a ha
    refine ⟨⟨t a, P.mem_Icc ha.le, le_rfl, by linarith [P.step a ha, hK.delta_pos], rfl⟩,
      ⟨t (a + 1), P.mem_Icc ha, (P.step a ha).le, by linarith [hK.delta_pos], rfl⟩⟩
  · intro a ha c hc1 hc2
    have hcM : c ≤ M := hc2.trans (hgM _)
    refine ⟨t' c, P'.mem_Icc hcM, ?_, ?_, rfl⟩
    · exact (hgspec a ha.le).trans (P'.le_of_le hc1 hcM)
    · have hpos := hgpos a ha
      have hprev := hgmin (a + 1) ha (g (a + 1) - 1) (by omega)
      have hgapc := P'.gap (g (a + 1) - 1) (by have := hgM (a + 1); omega)
      rw [show g (a + 1) - 1 + 1 = g (a + 1) by omega] at hgapc
      have := P'.le_of_le hc2 (hgM _)
      linarith

/-! ### Path words -/

/-- **The path word.** `W` is a path word of the strand family `K` on `[u, v]` if it is
equivalent to the chain words of all strict partitions of `[u, v]` of sufficiently small
mesh. -/
def IsPathWord (K : Fin S → ℝ → ℂ) (u v : ℝ) (W : SignedAdjacentWord S) : Prop :=
  ∃ δ > 0, ∀ (t : ℕ → ℝ) (N : ℕ), IsStrictPartition t N u v δ →
    SignedBraidEquiv (chainWord (fun a k => K k (t a)) N) W

namespace IsPathWord

variable {K : Fin S → ℝ → ℂ} {u v : ℝ} {W W' : SignedAdjacentWord S}

theorem congr_equiv (h : IsPathWord K u v W) (hW : SignedBraidEquiv W W') :
    IsPathWord K u v W' := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun t N P => (h t N P).trans hW⟩

/-- Path words are unique up to `SignedBraidEquiv`. -/
theorem unique (huv : u < v) (h : IsPathWord K u v W) (h' : IsPathWord K u v W') :
    SignedBraidEquiv W W' := by
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨δ', hδ', h'⟩ := h'
  obtain ⟨N, hN, hfine⟩ := exists_uniform_fine huv (lt_min hδ hδ')
  have P := isStrictPartition_uniform huv hN hfine
  exact (h _ _ (P.mono (min_le_left _ _))).symm.trans (h' _ _ (P.mono (min_le_right _ _)))

/-- A path word depends only on the values of the strands on `[u, v]`. -/
theorem of_eqOn {K' : Fin S → ℝ → ℂ} (h : IsPathWord K u v W)
    (hKK' : ∀ k, ∀ t ∈ Icc u v, K k t = K' k t) : IsPathWord K' u v W := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun t N P => ?_⟩
  rw [← chainWord_congr (X := fun a k => K k (t a)) fun a ha => funext fun k =>
    hKK' k (t a) (P.mem_Icc ha)]
  exact h t N P

end IsPathWord

/-- A path word for a modulus: the chain word of any strict partition of mesh less than
`δ / 2`. -/
theorem PathModulus.isPathWord {K : Fin S → ℝ → ℂ} {u v m δ : ℝ} (hK : PathModulus K u v m δ)
    {t : ℕ → ℝ} {N : ℕ} (P : IsStrictPartition t N u v (δ / 2)) :
    IsPathWord K u v (chainWord (fun a k => K k (t a)) N) :=
  ⟨δ / 2, half_pos hK.delta_pos, fun _ _ P' => chainWord_partition_equiv hK P' P⟩

/-- **Existence of path words.** A strand family, continuous on `[u, v]` with pairwise distinct
points, has a path word. -/
theorem exists_isPathWord {K : Fin S → ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) : ∃ W, IsPathWord K u v W := by
  obtain ⟨m, δ, hK⟩ := exists_pathModulus hcont hinj
  obtain ⟨N, hN, hfine⟩ := exists_uniform_fine huv (half_pos hK.delta_pos)
  exact ⟨_, hK.isPathWord (isStrictPartition_uniform huv hN hfine)⟩

/-! ### Operations on path words -/

theorem IsStrictPartition.concat {t₁ t₂ : ℕ → ℝ} {N₁ N₂ : ℕ} {u v w δ : ℝ}
    (P₁ : IsStrictPartition t₁ N₁ u v δ) (P₂ : IsStrictPartition t₂ N₂ v w δ) :
    IsStrictPartition (fun a => if a ≤ N₁ then t₁ a else t₂ (a - N₁)) (N₁ + N₂) u w δ := by
  refine ⟨by simp [P₁.zero], ?_, fun a ha => ?_, fun a ha => ?_⟩
  · by_cases h : N₂ = 0
    · subst h; simp [P₁.last, ← P₂.zero, P₂.last]
    · rw [if_neg (by omega), show N₁ + N₂ - N₁ = N₂ by omega, P₂.last]
  · by_cases h1 : a + 1 ≤ N₁
    · rw [if_pos h1, if_pos (by omega)]; exact P₁.step a (by omega)
    · by_cases h2 : a = N₁
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega), P₁.last, show a + 1 - a = 1 by omega, ← P₂.zero]
        exact P₂.step 0 (by omega)
      · rw [if_neg (by omega), if_neg (by omega), show a + 1 - N₁ = a - N₁ + 1 by omega]
        exact P₂.step _ (by omega)
  · by_cases h1 : a + 1 ≤ N₁
    · rw [if_pos h1, if_pos (by omega)]; exact P₁.gap a (by omega)
    · by_cases h2 : a = N₁
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega), P₁.last, show a + 1 - a = 1 by omega, ← P₂.zero]
        exact P₂.gap 0 (by omega)
      · rw [if_neg (by omega), if_neg (by omega), show a + 1 - N₁ = a - N₁ + 1 by omega]
        exact P₂.gap _ (by omega)

namespace IsPathWord

variable {K : Fin S → ℝ → ℂ} {u v : ℝ} {W W' : SignedAdjacentWord S}

/-- Relabelling the strands does not change the path word. -/
theorem relabel (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (σ : Equiv.Perm (Fin S)) :
    IsPathWord (fun k t => K (σ k) t) u v W ↔ IsPathWord K u v W := by
  have key : ∀ (t : ℕ → ℝ) (N : ℕ) (δ : ℝ), IsStrictPartition t N u v δ →
      chainWord (fun a k => K (σ k) (t a)) N = chainWord (fun a k => K k (t a)) N :=
    fun t N δ P => chainWord_relabel (X := fun a k => K k (t a))
      (fun a ha => hinj _ (P.mem_Icc ha)) σ
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun t N P => key t N δ P ▸ h t N P⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun t N P => (key t N δ P).symm ▸ h t N P⟩

/-- An increasing affine reparametrization of the time does not change the path word. -/
theorem comp_affine {φ : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hφ : ∀ t, φ t = α * t + β)
    (h : IsPathWord K (φ u) (φ v) W) : IsPathWord (fun k t => K k (φ t)) u v W := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ / α, div_pos hδ hα, fun t N P => ?_⟩
  have P' : IsStrictPartition (fun a => φ (t a)) N (φ u) (φ v) δ := by
    refine ⟨by rw [P.zero], by rw [P.last], fun a ha => ?_, fun a ha => ?_⟩
    · rw [hφ, hφ]
      have := P.step a ha
      nlinarith
    · rw [hφ, hφ]
      have := P.gap a ha
      rw [lt_div_iff₀ hα] at this
      nlinarith
  exact h _ N P'

/-- A family that is constant on `[u, v]` has trivial path word. -/
theorem const (h : ∀ k, ∀ t ∈ Icc u v, K k t = K k u) : IsPathWord K u v [] := by
  refine ⟨1, one_pos, fun t N P => chainWord_const fun a ha => funext fun k => ?_⟩
  rw [h k _ (P.mem_Icc ha), h k _ (P.mem_Icc (Nat.zero_le N))]

/-- **Concatenation.** Path words of consecutive intervals concatenate. -/
theorem append {w : ℝ} {W₁ W₂ : SignedAdjacentWord S} (huv : u < v) (hvw : v < w)
    (hcont : ∀ k, ContinuousOn (K k) (Icc u w))
    (hinj : ∀ t ∈ Icc u w, Injective fun k => K k t)
    (h₁ : IsPathWord K u v W₁) (h₂ : IsPathWord K v w W₂) : IsPathWord K u w (W₁ ++ W₂) := by
  obtain ⟨m, δ, hK⟩ := exists_pathModulus hcont hinj
  obtain ⟨δ₁, hδ₁, h₁⟩ := h₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := h₂
  set ε := min (δ / 2) (min δ₁ δ₂) with hε
  have hεpos : 0 < ε := lt_min (half_pos hK.delta_pos) (lt_min hδ₁ hδ₂)
  obtain ⟨N₁, hN₁, hf₁⟩ := exists_uniform_fine huv hεpos
  obtain ⟨N₂, hN₂, hf₂⟩ := exists_uniform_fine hvw hεpos
  have P₁ := isStrictPartition_uniform huv hN₁ hf₁
  have P₂ := isStrictPartition_uniform hvw hN₂ hf₂
  have P := P₁.concat P₂
  have hW := hK.isPathWord (P.mono (min_le_left _ _))
  refine hW.congr_equiv ?_
  rw [chainWord_add]
  refine SignedBraidEquiv.append ?_ ?_
  · rw [chainWord_congr (X' := fun a k => K k (uniformPartition u v N₁ a))
      fun a ha => by simp only [if_pos ha]]
    exact h₁ _ _ (P₁.mono ((min_le_right _ _).trans (min_le_left _ _)))
  · rw [chainWord_congr (X' := fun c k => K k (uniformPartition v w N₂ c)) fun c hc => by
      by_cases h0 : c = 0
      · subst h0
        simp only [add_zero, le_refl, if_true, P₁.last, P₂.zero]
      · simp only [if_neg (show ¬ N₁ + c ≤ N₁ by omega), show N₁ + c - N₁ = c by omega]]
    exact h₂ _ _ (P₂.mono ((min_le_right _ _).trans (min_le_right _ _)))

end IsPathWord

/-! ### Evaluation of path words -/

theorem chainWord_of_configSort_const {X : ℕ → Fin S → ℂ} {N : ℕ} {π : Equiv.Perm (Fin S)}
    (h : ∀ a ≤ N, configSort (X a) = π) : SignedBraidEquiv (chainWord X N) [] := by
  induction N with
  | zero => exact SignedBraidEquiv.refl _
  | succ N ih =>
    rw [chainWord_succ]
    simpa using (ih fun a ha => h a (by omega)).append
      (localWord_of_configSort_eq (X N) ((h N (by omega)).trans (h (N + 1) le_rfl).symm))

/-- A family whose lexicographic order is constant on `[u, v]` has trivial path word. -/
theorem IsPathWord.of_configSort_const {K : Fin S → ℝ → ℂ} {u v : ℝ} {π : Equiv.Perm (Fin S)}
    (h : ∀ t ∈ Icc u v, configSort (fun k => K k t) = π) : IsPathWord K u v [] :=
  ⟨1, one_pos, fun _ _ P => chainWord_of_configSort_const fun _ ha => h _ (P.mem_Icc ha)⟩

/-- At the time of an exchange of two adjacent strands, their real parts agree. If the order
before the exchange persists up to and including the time `c`, the strand moving to the left
is the higher one. -/
theorem exchange_heights_of_positive {n : ℕ} {K : Fin (n + 1) → ℝ → ℂ} {u v c : ℝ}
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (hc : u ≤ c) (hcv : c < v)
    {π : Equiv.Perm (Fin (n + 1))} {i : Fin n}
    (hbefore : configSort (fun k => K k c) = π)
    (hafter : ∀ t ∈ Icc u v, c < t →
      configSort (fun k => K k t) = π * adjacentSwap (m := n + 1) i) :
    (K (π (adjacentLower (m := n + 1) i)) c).re = (K (π (adjacentUpper (m := n + 1) i)) c).re ∧
      (K (π (adjacentLower (m := n + 1) i)) c).im <
        (K (π (adjacentUpper (m := n + 1) i)) c).im := by
  set lo := π (adjacentLower (m := n + 1) i)
  set up := π (adjacentUpper (m := n + 1) i)
  have hcI : c ∈ Icc u v := ⟨hc, hcv.le⟩
  have hlex : lexKey (K lo c) < lexKey (K up c) := by
    have := (configSort_symm_lt_iff (hinj c hcI) lo up).mp
    rw [hbefore] at this
    apply this
    simp [lo, up, Fin.lt_def]
  have hre1 := re_le_of_lexKey_lt hlex
  have hre2 : (K up c).re ≤ (K lo c).re := by
    by_contra hlt
    simp only [not_le] at hlt
    have hf : ContinuousOn (fun t => (K up t - K lo t).re) (Icc u v) :=
      Complex.continuous_re.comp_continuousOn ((hcont up).sub (hcont lo))
    have hpos : 0 < (K up c - K lo c).re := by simp only [Complex.sub_re]; linarith
    obtain ⟨η, hη, hηf⟩ := Metric.continuousOn_iff.mp hf c hcI _ hpos
    set t := min v (c + η / 2) with ht
    have htI : t ∈ Icc u v := ⟨by
      rw [ht]; exact le_min (hc.trans hcv.le) (by linarith), min_le_left _ _⟩
    have hct : c < t := lt_min hcv (by linarith)
    have hdist : dist t c < η := by
      have h1 : t ≤ c + η / 2 := min_le_right _ _
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    have h1 := hηf t htI hdist
    rw [Real.dist_eq] at h1
    have h2 : 0 < (K up t - K lo t).re := by
      have := abs_lt.mp h1
      linarith [this.1]
    have hlex' : lexKey (K lo t) < lexKey (K up t) := by
      rw [lexKey_lt_iff]
      left
      simp only [Complex.sub_re] at h2
      linarith
    have := (configSort_symm_lt_iff (hinj t htI) lo up).mpr hlex'
    rw [hafter t htI hct] at this
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, adjacentSwap_symm, lo, up,
      Equiv.symm_apply_apply] at this
    rw [Fin.lt_def, adjacentSwap_apply_val, adjacentSwap_apply_val] at this
    simp at this
  have hre : (K lo c).re = (K up c).re := le_antisymm hre1 hre2
  refine ⟨hre, ?_⟩
  rcases (lexKey_lt_iff _ _).mp hlex with h | h
  · exact absurd hre h.ne
  · exact h.2

end OnLeConjecture.Analytic
