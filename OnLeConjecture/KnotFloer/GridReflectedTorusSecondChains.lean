/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondPattern
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondCoeff

/-!
# The explicit second torus correction

The correction `secondTorusCorrection n R` is the Laurent chain
`U⁻¹(H_e + H_△) + U⁻² H_4 + U⁻³ H_32`. Here `H_△ = firstTorusTriangle n R`, and
the other three chains are sums over relative permutations with the following
coefficients, read modulo two.

* `torusEdgeCoeff`: a transposition `(a b)` has the parity of the shorter cyclic
  distance between `a` and `b`.
* `torusFourCoeff`: a four-cycle receives `tcW4` from every adjacent pair
  `(u, u+1)` of columns in its support.
* `torusFiveCoeff`: a product `(u v)(a b c)` of a transposition and a three-cycle,
  in which exactly one vertex `a` of the three-cycle lies on the positive arc
  from `u` to `v`, has coefficient `F(u,a,v,b) + F(u,a,v,c)`.

The coefficients vanish on all other permutations. The second representative is
`secondTorusCycle n R = firstTorusCycle n R + D(secondTorusCorrection n R)`.

This file proves that the correction has Maslov degree one. The supports of the
three coefficient functions consist of states with native Maslov gradings `-1`,
`-3` and `-5`. These gradings are computed by `torusEll_cfgPerm_eq_ellIdx`.
It also records evaluations of the coefficients on transported permutations.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-! ### Conditions on labels -/

/-- The defining condition of the three-cycle and transposition coefficient: `σ`
swaps `u` and `σ u`, and `a` is a vertex of a three-cycle of `σ` lying on the
positive arc from `u` to `σ u`, whose two other vertices lie on the opposite arc. -/
def FiveCond {m : ℕ} (σ : Equiv.Perm (Fin m)) (u a : Fin m) : Prop :=
  σ (σ u) = u ∧ σ u ≠ u ∧ a ∈ Grid.cIoo u (σ u) ∧ σ a ∈ Grid.cIoo (σ u) u ∧
    σ (σ a) ∈ Grid.cIoo (σ u) u ∧ σ (σ (σ a)) = a

noncomputable instance {m : ℕ} (σ : Equiv.Perm (Fin m)) (u a : Fin m) :
    Decidable (FiveCond σ u a) := by
  unfold FiveCond; infer_instance

/-- The label version of `FiveCond`. -/
def FiveCondIdx {k : ℕ} (ρ : Equiv.Perm (Fin k)) (i l : Fin k) : Prop :=
  ρ (ρ i) = i ∧ ρ i ≠ i ∧ IdxIoo i (ρ i) l ∧ IdxIoo (ρ i) i (ρ l) ∧
    IdxIoo (ρ i) i (ρ (ρ l)) ∧ ρ (ρ (ρ l)) = l

instance {k : ℕ} (ρ : Equiv.Perm (Fin k)) (i l : Fin k) : Decidable (FiveCondIdx ρ i l) := by
  unfold FiveCondIdx; infer_instance

theorem fiveCond_emb_iff {m k : ℕ} [NeZero k] {c : Fin k ↪ Fin m} (hc : CycSorted c)
    (ρ : Equiv.Perm (Fin k)) (i l : Fin k) :
    FiveCond (cfgPerm c ρ) (c i) (c l) ↔ FiveCondIdx ρ i l := by
  unfold FiveCond FiveCondIdx
  simp only [cfgPerm_apply_emb, c.injective.eq_iff, ne_eq, mem_cIoo_emb_iff hc, idxIoo_iff]

theorem apply_ne_of_fiveCond {m : ℕ} {σ : Equiv.Perm (Fin m)} {u a : Fin m}
    (h : FiveCond σ u a) : σ a ≠ a := by
  intro ha
  obtain ⟨-, -, h1, h2, -, -⟩ := h
  rw [ha] at h2
  exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap u (σ u)) h1 h2

variable (n : ℕ)

/-! ### The three coefficient functions -/

/-- The coefficient of a relative state in `H_e`. -/
noncomputable def torusEdgeCoeff (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) : ℕ :=
  if σ.support.card = 2 then
    ∑ a, if a.val < (σ a).val then tcE (n + 1) (cycDist a (σ a)) else 0
  else 0

/-- The coefficient of a relative state in `H_4`. -/
noncomputable def torusFourCoeff (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) : ℕ :=
  if σ.support.card = 4 ∧ ∀ x, σ (σ x) = x → σ x = x then
    ∑ u, if σ u ≠ u ∧ (∃ x, cycDist u x = 1 ∧ σ x ≠ x) then
      tcW4 (n + 1) (cycDist u (σ u)) (cycDist u (σ (σ u))) (cycDist u (σ (σ (σ u))))
    else 0
  else 0

/-- The coefficient of a relative state in `H_32`. -/
noncomputable def torusFiveCoeff (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) : ℕ :=
  if σ.support.card = 5 then
    ∑ u, ∑ a, if FiveCond σ u a then
      tcF (n + 1) (cycDist u a) (cycDist u (σ u)) (cycDist u (σ a)) +
        tcF (n + 1) (cycDist u a) (cycDist u (σ u)) (cycDist u (σ (σ a)))
    else 0
  else 0

/-! ### Chains with prescribed coefficients -/

/-- The Laurent chain with coefficient `h σ • U^k` at every relative state
`relState n σ`. -/
noncomputable def relChain (R : Type*) [CommSemiring R] (k : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ) :
    LaurentChain R (consecutiveTorusGridSize n) :=
  Finsupp.equivFunOnFinite.symm fun x =>
    ((h (reflectedTorusRelativeColumns n x) : ℕ) : R) • LaurentPolynomial.T k

theorem relChain_apply (R : Type*) [CommSemiring R] (k : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ)
    (x : GridState (consecutiveTorusGridSize n)) :
    relChain n R k h x =
      ((h (reflectedTorusRelativeColumns n x) : ℕ) : R) • LaurentPolynomial.T k := by
  simp [relChain]

theorem relChain_relState (R : Type*) [CommSemiring R] (k : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ)
    (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    relChain n R k h (relState n σ) = ((h σ : ℕ) : R) • LaurentPolynomial.T k := by
  rw [relChain_apply, relativeColumns_relState]

theorem T_smul_relChain (R : Type*) [CommSemiring R] (j k : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ) :
    (LaurentPolynomial.T j : LaurentPolynomial R) • relChain n R k h = relChain n R (j + k) h := by
  ext x : 1
  rw [Finsupp.smul_apply, relChain_apply, relChain_apply, smul_eq_mul, mul_smul_comm,
    ← LaurentPolynomial.T_add]

/-- A chain with prescribed coefficients is homogeneous when every state in its
support has the required grading. -/
theorem relChain_mem_maslovPiece (R : Type*) [CommSemiring R] (k d : ℤ)
    (h : Equiv.Perm (Fin (consecutiveTorusGridSize n)) → ℕ)
    (hh : ∀ σ, h σ ≠ 0 → (reflectedTorusGrid n).maslovOℤ (relState n σ) - 2 * k = d) :
    relChain n R k h ∈ laurentMaslovPiece (reflectedTorusGrid n) R d := by
  classical
  rw [mem_laurentMaslovPiece]
  intro x j hj
  rw [relChain_apply, LaurentPolynomial.smul_eq_C_mul,
    ← LaurentPolynomial.single_eq_C_mul_T] at hj
  have hjk : j = k := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
  have hne : h (reflectedTorusRelativeColumns n x) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hj
    simp at hj
  subst hjk
  have hx := hh _ hne
  rw [relState_relativeColumns] at hx
  rw [laurentMaslovDegree]
  exact hx

/-! ### Gradings of the states in the three supports -/

theorem relState_swap (a b : Fin (consecutiveTorusGridSize n)) :
    relState n (Equiv.swap a b) = (reflectedTorusAnchor n).swapColumns a b := by
  rw [← relState_one, swapColumns_relState, one_mul]

theorem torusEll_swap {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) :
    torusEll n (Equiv.swap a b) = 1 := by
  rw [torusEll, relState_swap, maslovO_swap_reflectedTorusAnchor n a b hab,
    maslovO_reflectedTorusAnchor]
  norm_num

theorem torusEll_of_torusEdgeCoeff_ne_zero {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : torusEdgeCoeff n σ ≠ 0) : torusEll n σ = 1 := by
  unfold torusEdgeCoeff at h
  split_ifs at h with hc
  · obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.card_support_eq_two.mp hc
    exact torusEll_swap n hab
  · exact (h rfl).elim

set_option maxRecDepth 100000 in
theorem torusEll_of_torusFourCoeff_ne_zero {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : torusFourCoeff n σ ≠ 0) : torusEll n σ = 3 := by
  unfold torusFourCoeff at h
  split_ifs at h with hc
  · obtain ⟨hcard, hcyc⟩ := hc
    have : NeZero σ.support.card := ⟨by omega⟩
    have hρ1 : ∀ i, supportPattern σ i ≠ i := supportPattern_apply_ne σ
    have hρ2 : ∀ i, supportPattern σ (supportPattern σ i) ≠ i := by
      intro i hi
      have h1 := hcyc (supportCfg σ i)
      rw [← supportCfg_supportPattern, ← supportCfg_supportPattern, hi] at h1
      exact hρ1 i ((supportCfg σ).injective (h1 rfl).symm).symm
    have key : ∀ (k : ℕ), k = 4 → ∀ ρ : Equiv.Perm (Fin k), (∀ i, ρ i ≠ i) →
        (∀ i, ρ (ρ i) ≠ i) → ellIdx ρ = 3 := by
      rintro k rfl
      decide
    rw [← cfgPerm_supportPattern σ, torusEll_cfgPerm_eq_ellIdx n (cycSorted_supportCfg σ),
      key _ hcard _ hρ1 hρ2]
    rfl
  · exact (h rfl).elim

set_option maxRecDepth 100000 in
theorem torusEll_of_torusFiveCoeff_ne_zero {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))}
    (h : torusFiveCoeff n σ ≠ 0) : torusEll n σ = 5 := by
  classical
  unfold torusFiveCoeff at h
  split_ifs at h with hcard
  · obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    have hcond : FiveCond σ u a := by
      by_contra hn
      exact ha (if_neg hn)
    have : NeZero σ.support.card := ⟨by omega⟩
    have hu' : u ∈ Set.range (supportCfg σ) := by
      rw [mem_range_supportCfg_iff]; exact hcond.2.1
    have ha' : a ∈ Set.range (supportCfg σ) := by
      rw [mem_range_supportCfg_iff]; exact apply_ne_of_fiveCond hcond
    obtain ⟨i, rfl⟩ := hu'
    obtain ⟨l, rfl⟩ := ha'
    have hc := cycSorted_supportCfg σ
    have hcond' : FiveCond (cfgPerm (supportCfg σ) (supportPattern σ)) (supportCfg σ i)
        (supportCfg σ l) := by
      rw [cfgPerm_supportPattern]; exact hcond
    rw [fiveCond_emb_iff hc] at hcond'
    have hρ1 : ∀ i, supportPattern σ i ≠ i := supportPattern_apply_ne σ
    have key : ∀ (k : ℕ), k = 5 → ∀ ρ : Equiv.Perm (Fin k), (∀ i, ρ i ≠ i) →
        ∀ i l, FiveCondIdx ρ i l → ellIdx ρ = 5 := by
      rintro k rfl
      decide
    rw [← cfgPerm_supportPattern σ, torusEll_cfgPerm_eq_ellIdx n hc,
      key _ hcard _ hρ1 i l hcond']
    rfl
  · exact (h rfl).elim


/-! ### The correction chain -/

/-- The chain `H_e`. -/
noncomputable def secondTorusEdgeChain (R : Type*) [CommSemiring R] :
    LaurentChain R (consecutiveTorusGridSize n) :=
  relChain n R 0 (torusEdgeCoeff n)

/-- The chain `H_4`. -/
noncomputable def secondTorusFourChain (R : Type*) [CommSemiring R] :
    LaurentChain R (consecutiveTorusGridSize n) :=
  relChain n R 0 (torusFourCoeff n)

/-- The chain `H_32`. -/
noncomputable def secondTorusFiveChain (R : Type*) [CommSemiring R] :
    LaurentChain R (consecutiveTorusGridSize n) :=
  relChain n R 0 (torusFiveCoeff n)

/-- The explicit degree-one correction `U⁻¹(H_e + H_△) + U⁻² H_4 + U⁻³ H_32`. -/
noncomputable def secondTorusCorrection (R : Type*) [CommSemiring R] :
    LaurentChain R (consecutiveTorusGridSize n) :=
  (LaurentPolynomial.T (-1) : LaurentPolynomial R) •
      (secondTorusEdgeChain n R + firstTorusTriangle n R) +
    (LaurentPolynomial.T (-2) : LaurentPolynomial R) • secondTorusFourChain n R +
    (LaurentPolynomial.T (-3) : LaurentPolynomial R) • secondTorusFiveChain n R

/-- The second representative `z₂ = z₁ + D w₂`. -/
noncomputable def secondTorusCycle (R : Type*) [CommSemiring R] :
    LaurentChain R (consecutiveTorusGridSize n) :=
  firstTorusCycle n R + laurentDifferential (reflectedTorusGrid n) R (secondTorusCorrection n R)

theorem maslovOℤ_relState (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    (reflectedTorusGrid n).maslovOℤ (relState n σ) = -torusEll n σ := by
  rw [torusEll, neg_neg]

theorem secondTorusEdgeChain_mem_maslovPiece (R : Type*) [CommSemiring R] :
    secondTorusEdgeChain n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R (-1) := by
  apply relChain_mem_maslovPiece
  intro σ hσ
  rw [maslovOℤ_relState, torusEll_of_torusEdgeCoeff_ne_zero n hσ]
  norm_num

theorem secondTorusFourChain_mem_maslovPiece (R : Type*) [CommSemiring R] :
    secondTorusFourChain n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R (-3) := by
  apply relChain_mem_maslovPiece
  intro σ hσ
  rw [maslovOℤ_relState, torusEll_of_torusFourCoeff_ne_zero n hσ]
  norm_num

theorem secondTorusFiveChain_mem_maslovPiece (R : Type*) [CommSemiring R] :
    secondTorusFiveChain n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R (-5) := by
  apply relChain_mem_maslovPiece
  intro σ hσ
  rw [maslovOℤ_relState, torusEll_of_torusFiveCoeff_ne_zero n hσ]
  norm_num

private theorem T_smul_mem_maslovPiece (R : Type*) [CommSemiring R] (j : ℤ) {d : ℤ}
    {c : LaurentChain R (consecutiveTorusGridSize n)}
    (hc : c ∈ laurentMaslovPiece (reflectedTorusGrid n) R d) :
    (LaurentPolynomial.T j : LaurentPolynomial R) • c ∈
      laurentMaslovPiece (reflectedTorusGrid n) R (d - 2 * j) :=
  laurentMonomial_smul_mem_maslovPiece (reflectedTorusGrid n) j (1 : R) hc

/-- The correction has Maslov degree one. -/
theorem secondTorusCorrection_mem_maslovPiece (R : Type*) [CommSemiring R] :
    secondTorusCorrection n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R 1 := by
  have htri : firstTorusTriangle n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R (-1) := by
    simpa only [maslovO_reflectedTorusAnchor, zero_sub] using
      firstTorusTriangle_mem_maslovPiece n R
  have h1 := T_smul_mem_maslovPiece n R (-1)
    (Submodule.add_mem _ (secondTorusEdgeChain_mem_maslovPiece n R) htri)
  have h2 := T_smul_mem_maslovPiece n R (-2) (secondTorusFourChain_mem_maslovPiece n R)
  have h3 := T_smul_mem_maslovPiece n R (-3) (secondTorusFiveChain_mem_maslovPiece n R)
  rw [show (-1 : ℤ) - 2 * -1 = 1 by norm_num] at h1
  rw [show (-3 : ℤ) - 2 * -2 = 1 by norm_num] at h2
  rw [show (-5 : ℤ) - 2 * -3 = 1 by norm_num] at h3
  exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

/-- The second representative has Maslov degree zero. -/
theorem secondTorusCycle_mem_maslovZero (R : Type*) [CommSemiring R] :
    secondTorusCycle n R ∈ laurentMaslovPiece (reflectedTorusGrid n) R 0 := by
  apply Submodule.add_mem _ (firstTorusCycle_mem_maslovZero n R)
  simpa using laurentDifferential_mem_maslovPiece (reflectedTorusGrid n)
    (secondTorusCorrection_mem_maslovPiece n R)

/-- The second representative is a cycle. -/
theorem laurentDifferential_secondTorusCycle (R : Type*) [CommSemiring R] [CharP R 2] :
    laurentDifferential (reflectedTorusGrid n) R (secondTorusCycle n R) = 0 := by
  rw [secondTorusCycle, map_add, laurentDifferential_firstTorusCycle,
    laurentDifferential_sq_eq_zero, add_zero]

end OnLeConjecture.KnotFloer.GridFull
