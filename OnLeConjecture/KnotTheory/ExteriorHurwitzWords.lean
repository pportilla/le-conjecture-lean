/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedWordGrid
public import OnLeConjecture.KnotTheory.ExteriorHurwitz
public import Mathlib.GroupTheory.FreeGroup.Reduce
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# Hurwitz normalization of signed factorizations

The written proof of Statement E (`statement_E_complete_proof.tex`, Section 12) normalizes the
event factorization by Hurwitz moves: afterwards strand `0` lies in the nontrivial cycle of every
factor and the singular factors come first. This file carries out that step on signed words.

* Signed words and the free group: `SignedAdjacentWord.toFree` and `ofFree`, with
  `toFree (u ++ v) = toFree u * toFree v`, `toFree (inv u) = (toFree u)⁻¹`, and
  `signedBraidEquiv_of_toFree_eq`: words with equal free-group images are related by free
  cancellations.
* `freePerm`, the permutation homomorphism of the free group, with
  `freePerm (toFree w) = w.permutation`.
* Cycles: the permutation of `σ_0` and of a lifted positive word with one cycle are cycles.
* `exists_hurwitz_normalized`: given conjugates of labelled cores with transitive permutations
  and cyclic core permutations, there are new conjugators such that the padded factors in the
  standard label order have a product equal in the braid group to the original product, move
  strand `0`, and still act transitively.

The group-theoretic content is `exists_hurwitzEquiv_ordered_commonStrand_invariants` of
`ExteriorHurwitz.lean`, applied in the free group.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open Equiv

variable {m : ℕ}

/-! ### Signed words and the free group -/

/-- A signed letter as a free-group letter. -/
def toBoolLetter (a : Fin (m - 1) × ℤˣ) : Fin (m - 1) × Bool := (a.1, decide (a.2 = 1))

/-- A free-group letter as a signed letter. -/
def ofBoolLetter (b : Fin (m - 1) × Bool) : Fin (m - 1) × ℤˣ := (b.1, if b.2 then 1 else -1)

theorem ofBoolLetter_toBoolLetter (a : Fin (m - 1) × ℤˣ) : ofBoolLetter (toBoolLetter a) = a := by
  rcases a with ⟨i, e⟩
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp [ofBoolLetter, toBoolLetter]

theorem toBoolLetter_ofBoolLetter (b : Fin (m - 1) × Bool) : toBoolLetter (ofBoolLetter b) = b := by
  rcases b with ⟨i, b⟩
  cases b <;> simp [ofBoolLetter, toBoolLetter]

theorem map_ofBoolLetter_map_toBoolLetter (w : SignedAdjacentWord m) :
    (w.map toBoolLetter).map ofBoolLetter = w := by
  simp [List.map_map, Function.comp_def, ofBoolLetter_toBoolLetter]

/-- The free-group element of a signed word. -/
def SignedAdjacentWord.toFree (w : SignedAdjacentWord m) : FreeGroup (Fin (m - 1)) :=
  FreeGroup.mk (w.map toBoolLetter)

/-- A signed word of a free-group element, its reduced word. -/
def ofFree (g : FreeGroup (Fin (m - 1))) : SignedAdjacentWord m :=
  g.toWord.map ofBoolLetter

theorem SignedAdjacentWord.toFree_append (u v : SignedAdjacentWord m) :
    (u ++ v).toFree = u.toFree * v.toFree := by
  simp only [SignedAdjacentWord.toFree, List.map_append, FreeGroup.mul_mk]

theorem SignedAdjacentWord.toFree_inv (w : SignedAdjacentWord m) :
    (SignedAdjacentWord.inv w).toFree = w.toFree⁻¹ := by
  simp only [SignedAdjacentWord.toFree, FreeGroup.inv_mk, FreeGroup.invRev,
    SignedAdjacentWord.inv, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun a _ => ?_
  rcases a with ⟨i, e⟩
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp [toBoolLetter]

theorem toFree_ofFree (g : FreeGroup (Fin (m - 1))) :
    (ofFree g : SignedAdjacentWord m).toFree = g := by
  simp only [SignedAdjacentWord.toFree, ofFree, List.map_map, Function.comp_def,
    toBoolLetter_ofBoolLetter, List.map_id', FreeGroup.mk_toWord]

theorem toFree_conjugateWord (γ η : SignedAdjacentWord m) :
    (conjugateWord γ η).toFree = γ.toFree * η.toFree * γ.toFree⁻¹ := by
  rw [conjugateWord, SignedAdjacentWord.toFree_append, SignedAdjacentWord.toFree_append,
    SignedAdjacentWord.toFree_inv]

theorem toFree_padWord (S : ℕ) : (padWord S).toFree = 1 := by
  rw [padWord, SignedAdjacentWord.toFree_append, SignedAdjacentWord.toFree_inv, mul_inv_cancel]

theorem signedBraidEquiv_of_red {L₁ L₂ : List (Fin (m - 1) × Bool)} (h : FreeGroup.Red L₁ L₂) :
    SignedBraidEquiv (L₁.map ofBoolLetter) (L₂.map ofBoolLetter) := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih =>
    refine Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ?_)
    rcases hstep with @⟨A, B, x, b⟩
    have e : ofBoolLetter (m := m) (x, !b) = (x, -(ofBoolLetter (m := m) (x, b)).2) := by
      cases b <;> simp [ofBoolLetter]
    simp only [List.map_append, List.map_cons]
    rw [e]
    exact SignedBraidStep.cancel _ _ x _

/-- Words with equal free-group images are equal in the braid group. -/
theorem signedBraidEquiv_of_toFree_eq {u v : SignedAdjacentWord m} (h : u.toFree = v.toFree) :
    SignedBraidEquiv u v := by
  obtain ⟨L, hu, hv⟩ := FreeGroup.Red.exact.mp h
  have h1 := signedBraidEquiv_of_red hu
  have h2 := signedBraidEquiv_of_red hv
  rw [map_ofBoolLetter_map_toBoolLetter] at h1 h2
  exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)

/-! ### Permutations -/

/-- The permutation homomorphism of the free group on the adjacent generators. -/
def freePerm (m : ℕ) : FreeGroup (Fin (m - 1)) →* Perm (Fin m) :=
  FreeGroup.lift adjacentSwap

theorem freePerm_toFree (w : SignedAdjacentWord m) : freePerm m w.toFree = w.permutation := by
  induction w with
  | nil => simp [SignedAdjacentWord.toFree, freePerm]
  | cons a w ih =>
    have hsplit : SignedAdjacentWord.toFree (a :: w) =
        FreeGroup.mk [toBoolLetter a] * SignedAdjacentWord.toFree w := by
      rw [SignedAdjacentWord.toFree, SignedAdjacentWord.toFree, FreeGroup.mul_mk]
      rfl
    rw [hsplit, map_mul, ih, SignedAdjacentWord.permutation_cons]
    congr 1
    rcases a with ⟨i, e⟩
    rcases Int.units_eq_one_or e with rfl | rfl
    · change freePerm m (FreeGroup.of i) = adjacentSwap i
      exact FreeGroup.lift_apply_of
    · have : FreeGroup.mk [toBoolLetter (m := m) (i, -1)] = (FreeGroup.of i)⁻¹ := by
        rw [FreeGroup.of, FreeGroup.inv_mk]
        simp [FreeGroup.invRev, toBoolLetter]
      rw [this, map_inv]
      change (FreeGroup.lift adjacentSwap (FreeGroup.of i))⁻¹ = adjacentSwap i
      rw [FreeGroup.lift_apply_of, SignedAdjacentWord.adjacentSwap_inv]

theorem permutation_conjugateWord (γ η : SignedAdjacentWord m) :
    (conjugateWord γ η).permutation = γ.permutation * η.permutation * γ.permutation⁻¹ := by
  rw [conjugateWord, SignedAdjacentWord.permutation_append, SignedAdjacentWord.permutation_append,
    SignedAdjacentWord.permutation_inv]

/-! ### Cycles of the cores -/

theorem isCycle_permutation_firstLetter {S : ℕ} (hS : 2 ≤ S) :
    (NormalizedFactorization.firstLetter S).permutation.IsCycle := by
  rw [NormalizedFactorization.firstLetter, dif_pos hS, SignedAdjacentWord.permutation_cons,
    SignedAdjacentWord.permutation_nil, mul_one]
  unfold adjacentSwap
  exact Equiv.Perm.isCycle_swap (by simp [Fin.ext_iff])

theorem liftPositiveWord_permutation_castLE {a S : ℕ} (h : a ≤ S) (w : PositiveAdjacentWord a)
    (x : Fin a) :
    (liftPositiveWord h w).permutation (Fin.castLE h x) =
      Fin.castLE h (w.toSigned.permutation x) := by
  induction w with
  | nil => simp [liftPositiveWord, PositiveAdjacentWord.toSigned]
  | cons i w ih =>
    simp only [liftPositiveWord, PositiveAdjacentWord.toSigned, List.map_cons,
      SignedAdjacentWord.permutation_cons, Perm.mul_apply] at ih ⊢
    rw [ih]
    apply Fin.ext
    rw [Fin.val_castLE, adjacentSwap_apply_val, adjacentSwap_apply_val]
    simp only [Fin.val_castLE]

theorem liftPositiveWord_permutation_of_le {a S : ℕ} (h : a ≤ S) (w : PositiveAdjacentWord a)
    (y : Fin S) (hy : a ≤ y.val) : (liftPositiveWord h w).permutation y = y := by
  induction w with
  | nil => simp [liftPositiveWord]
  | cons i w ih =>
    simp only [liftPositiveWord, List.map_cons, SignedAdjacentWord.permutation_cons,
      Perm.mul_apply] at ih ⊢
    rw [ih]
    apply Fin.ext
    rw [adjacentSwap_apply_val]
    have := i.isLt
    simp only [Fin.val_castLE]
    split_ifs <;> omega

/-- A positive word on `a ≥ 2` strands with one cycle, placed on the first `a` of `S` strands, has
a cyclic permutation. -/
theorem isCycle_permutation_liftPositiveWord {a S : ℕ} (h : a ≤ S) (ha : 2 ≤ a)
    (w : PositiveAdjacentWord a) (hw : w.toSigned.cycleCount = 1) :
    (liftPositiveWord h w).permutation.IsCycle := by
  classical
  set σ := w.toSigned.permutation with hσ
  have hsub : Subsingleton (Quotient (Perm.SameCycle.setoid σ)) := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    have : SignedAdjacentWord.cycleCount w.toSigned = 1 := hw
    unfold SignedAdjacentWord.cycleCount at this
    rw [← hσ] at this
    convert this.le
  have hall : ∀ x y : Fin a, σ.SameCycle x y := fun x y =>
    Quotient.exact (Subsingleton.elim (Quotient.mk (Perm.SameCycle.setoid σ) x) ⟦y⟧)
  have hne : ∃ x, σ x ≠ x := by
    by_contra hfix
    simp only [not_exists, not_not] at hfix
    have h01 := hall ⟨0, by omega⟩ ⟨1, by omega⟩
    obtain ⟨k, hk⟩ := h01
    have hid : σ = 1 := Equiv.ext fun x => hfix x
    rw [hid, one_zpow, Perm.one_apply] at hk
    exact absurd (congrArg Fin.val hk) (by simp)
  obtain ⟨x, hx⟩ := hne
  have hcomm : ∀ (n : ℕ) (z : Fin a), ((liftPositiveWord h w).permutation ^ n) (Fin.castLE h z) =
      Fin.castLE h ((σ ^ n) z) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro z
      rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply,
        liftPositiveWord_permutation_castLE]
  refine ⟨Fin.castLE h x, ?_, ?_⟩
  · rw [liftPositiveWord_permutation_castLE]
    exact fun e => hx (Fin.castLE_injective h e)
  · intro y hy
    have hya : y.val < a := by
      by_contra hya
      exact hy (liftPositiveWord_permutation_of_le h w y (by omega))
    obtain ⟨n, hn⟩ := (hall x ⟨y.val, hya⟩).exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hcomm, hn]
    rfl

/-! ### Labels -/

/-- The standard label order: the singular factors `0, …, N - 1` first, then the simple ones. -/
def standardLabel (N B : ℕ) (l : Fin (N + B)) : Option (Fin N) :=
  if h : l.val < N then some ⟨l.val, h⟩ else none

theorem count_ofFn {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {n : ℕ} (f : Fin n → α)
    (o : α) :
    (List.ofFn f).count o = (Finset.univ.filter fun l => f l = o).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ]
    by_cases h : f 0 = o <;> simp [h, add_comm]

/-- The number of factors with a given label, plus the number of unlabelled factors. -/
theorem card_filter_none_add {N B : ℕ} (core : Fin (N + B) → Option (Fin N))
    (hcore : ∀ j, ∃! l, core l = some j) :
    (Finset.univ.filter fun l => core l = none).card + N = N + B := by
  classical
  have hsome : ∀ j : Fin N, (Finset.univ.filter fun l => core l = some j).card = 1 := by
    intro j
    obtain ⟨l, hl, hu⟩ := hcore j
    rw [Finset.card_eq_one]
    exact ⟨l, by ext l'; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; exact ⟨fun h => hu l' h, fun h => h ▸ hl⟩⟩
  have hsplit : ∀ l : Fin (N + B), (if core l = none then 1 else 0) +
      ∑ j : Fin N, (if core l = some j then 1 else 0) = 1 := by
    intro l
    rcases hcl : core l with _ | j
    · simp
    · rw [if_neg (by simp)]
      simp
  have htot := Finset.sum_congr rfl fun l (_ : l ∈ (Finset.univ : Finset (Fin (N + B)))) =>
    hsplit l
  rw [Finset.sum_add_distrib, Finset.sum_comm] at htot
  simp only [Finset.sum_boole, Nat.cast_id, hsome, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at htot
  omega

theorem perm_ofFn_standardLabel {N B : ℕ} (core : Fin (N + B) → Option (Fin N))
    (hcore : ∀ j, ∃! l, core l = some j) :
    (List.ofFn core).Perm (List.ofFn (standardLabel N B)) := by
  have hstd : ∀ j, ∃! l, standardLabel N B l = some j := by
    intro j
    refine ⟨Fin.castAdd B j, by simp [standardLabel], fun l hl => ?_⟩
    simp only [standardLabel] at hl
    split_ifs at hl with h
    · simp only [Option.some.injEq, Fin.ext_iff] at hl
      exact Fin.ext (by simp [← hl])
  rw [List.perm_iff_count]
  intro o
  rw [count_ofFn, count_ofFn]
  rcases o with _ | j
  · have h1 := card_filter_none_add core hcore
    have h2 := card_filter_none_add (standardLabel N B) hstd
    omega
  · have hone : ∀ (f : Fin (N + B) → Option (Fin N)), (∀ j, ∃! l, f l = some j) →
        (Finset.univ.filter fun l => f l = some j).card = 1 := by
      intro f hf
      obtain ⟨l, hl, hu⟩ := hf j
      rw [Finset.card_eq_one]
      exact ⟨l, by ext l'; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]; exact ⟨fun h => hu l' h, fun h => h ▸ hl⟩⟩
    rw [hone core hcore, hone _ hstd]

theorem toFree_flatten (L : List (SignedAdjacentWord m)) :
    SignedAdjacentWord.toFree L.flatten = (L.map SignedAdjacentWord.toFree).prod := by
  induction L with
  | nil => simp [SignedAdjacentWord.toFree]; rfl
  | cons w L ih => rw [List.flatten_cons, SignedAdjacentWord.toFree_append, ih]; simp

/-! ### Hurwitz normalization of signed words -/

/-- **Hurwitz normalization.** Conjugates of labelled cores with transitive factor permutations
and cyclic core permutations can be replaced, by new conjugators, with padded conjugates in the
standard label order whose product is equal in the braid group, every one of which moves strand
`0`, and whose permutations are still transitive. -/
theorem exists_hurwitz_normalized {S N B : ℕ} (hS : 2 ≤ S)
    (core : Fin (N + B) → Option (Fin N)) (hcore : ∀ j, ∃! l, core l = some j)
    (η : Option (Fin N) → SignedAdjacentWord S) (hη : ∀ o, (η o).permutation.IsCycle)
    (γ : Fin (N + B) → SignedAdjacentWord S)
    (htrans : ∀ x y : Fin S, ∃ σ ∈ Subgroup.closure
      (Set.range fun l => (conjugateWord (γ l) (η (core l))).permutation), σ x = y) :
    ∃ γ' : Fin (N + B) → SignedAdjacentWord S,
      SignedBraidEquiv (List.ofFn fun l => conjugateWord (γ l) (η (core l))).flatten
        (List.ofFn fun l => conjugateWord (padWord S ++ γ' l) (η (standardLabel N B l))).flatten ∧
      (∀ l, (conjugateWord (padWord S ++ γ' l) (η (standardLabel N B l))).permutation
        ⟨0, by omega⟩ ≠ ⟨0, by omega⟩) ∧
      (∀ x y : Fin S, ∃ σ ∈ Subgroup.closure (Set.range fun l =>
        (conjugateWord (padWord S ++ γ' l) (η (standardLabel N B l))).permutation), σ x = y) := by
  classical
  set φ := freePerm S with hφ
  set o : Fin S := ⟨0, by omega⟩ with ho
  set l₀ : List (Option (Fin N) × FreeGroup (Fin (S - 1))) :=
    List.ofFn fun l => (core l, (conjugateWord (γ l) (η (core l))).toFree) with hl₀
  have hφconj : ∀ l, φ (conjugateWord (γ l) (η (core l))).toFree =
      (conjugateWord (γ l) (η (core l))).permutation := fun l => freePerm_toFree _
  have hset : {σ | ∃ p ∈ l₀, φ p.2 = σ} =
      Set.range fun l => (conjugateWord (γ l) (η (core l))).permutation := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_range, hl₀, List.mem_ofFn]
    constructor
    · rintro ⟨p, ⟨l, rfl⟩, rfl⟩
      exact ⟨l, (hφconj l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨_, ⟨l, rfl⟩, hφconj l⟩
  have hcyc : ∀ p ∈ l₀, (φ p.2).IsCycle := by
    intro p hp
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hp
    simp only
    rw [hφconj, permutation_conjugateWord]
    exact (hη _).conj
  have htrans₀ : ∀ x : Fin S, ∃ g ∈ Subgroup.closure {σ | ∃ p ∈ l₀, φ p.2 = σ}, g o = x := by
    intro x
    rw [hset]
    exact htrans o x
  have hL : (l₀.map Prod.fst).Perm (List.ofFn (standardLabel N B)) := by
    rw [hl₀, List.map_ofFn]
    exact perm_ofFn_standardLabel core hcore
  obtain ⟨l', hH, hlab, hmove, hprod, -⟩ :=
    exists_hurwitzEquiv_ordered_commonStrand_invariants φ o l₀ hcyc htrans₀ hL
  have hlen : l'.length = N + B := by
    have := congrArg List.length hlab
    simpa using this
  -- the entries of the normalized tuple
  let p : Fin (N + B) → Option (Fin N) × FreeGroup (Fin (S - 1)) :=
    fun k => l'[k.val]'(by rw [hlen]; exact k.isLt)
  have hp_mem : ∀ k, p k ∈ l' := fun k => List.getElem_mem _
  have hp_lab : ∀ k, (p k).1 = standardLabel N B k := by
    intro k
    have := congrArg (fun L => L[k.val]?) hlab
    simp only [List.getElem?_map, List.getElem?_ofFn] at this
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact k.isLt)] at this
    simpa [p] using this
  have hconj : ∀ k, ∃ c : FreeGroup (Fin (S - 1)),
      c * (η (standardLabel N B k)).toFree * c⁻¹ = (p k).2 := by
    intro k
    obtain ⟨q, hq, hq1, hqc⟩ := hH.exists_isConj (hp_mem k)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hq
    simp only at hq1 hqc
    rw [toFree_conjugateWord] at hqc
    have h1 : IsConj (η (core l)).toFree ((γ l).toFree * (η (core l)).toFree * (γ l).toFree⁻¹) :=
      isConj_iff.mpr ⟨(γ l).toFree, rfl⟩
    have h2 := h1.trans hqc
    rw [hq1, hp_lab] at h2
    exact isConj_iff.mp h2
  choose c hc using hconj
  refine ⟨fun k => ofFree (c k), ?_, ?_, ?_⟩
  · apply signedBraidEquiv_of_toFree_eq
    rw [toFree_flatten, toFree_flatten, List.map_ofFn, List.map_ofFn]
    have hnew : ∀ k, SignedAdjacentWord.toFree
        (conjugateWord (padWord S ++ ofFree (c k)) (η (standardLabel N B k))) = (p k).2 := by
      intro k
      rw [toFree_conjugateWord, SignedAdjacentWord.toFree_append, toFree_padWord, toFree_ofFree,
        one_mul, hc]
    have hl' : l'.map Prod.snd = List.ofFn fun k => (p k).2 := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp [p]
    have hold := hprod
    rw [hl', hl₀, List.map_ofFn] at hold
    simp only [Function.comp_def, hnew]
    rw [hold]
    rfl
  · intro k
    rw [← freePerm_toFree, toFree_conjugateWord, SignedAdjacentWord.toFree_append, toFree_padWord,
      toFree_ofFree, one_mul, hc]
    exact hmove _ (hp_mem k)
  · intro x y
    have hclosure : Subgroup.closure (Set.range fun k =>
        (conjugateWord (padWord S ++ ofFree (c k)) (η (standardLabel N B k))).permutation) =
        Subgroup.closure {σ | ∃ q ∈ l', φ q.2 = σ} := by
      congr 1
      ext σ
      simp only [Set.mem_range, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨p k, hp_mem k, ?_⟩
        rw [← hc, ← freePerm_toFree, toFree_conjugateWord, SignedAdjacentWord.toFree_append,
          toFree_padWord, toFree_ofFree, one_mul]
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
        refine ⟨⟨i, by rw [← hlen]; exact hi⟩, ?_⟩
        rw [← freePerm_toFree, toFree_conjugateWord, SignedAdjacentWord.toFree_append,
          toFree_padWord, toFree_ofFree, one_mul, hc]
    rw [hclosure, ← hH.closure_eq φ, hset]
    exact htrans x y

end OnLeConjecture.KnotTheory
