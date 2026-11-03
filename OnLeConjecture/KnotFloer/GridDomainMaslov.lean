/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridDomainIndex
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-!
# The index of a domain and the point-count grading

For an auxiliary permutation `O` of marks and a domain `D` from `u` to `v`,
`GridDomain.index4_eq_markMaslov` proves
`D.index4 u v = 4 * (gridMarkMaslov O u - gridMarkMaslov O v) + 8 * ∑ c, D c (O c)`,
that is, `ι(D;u,v) = M_O(u) - M_O(v) + 2 ∑_c D(c, O c)`.

The proof follows the written proof. The formula holds for the width-one rectangle of an
adjacent transposition (`exists_adjacent_formula`), where the change of the point-count grading
is computed by reindexing the four pair counts. It is preserved by concatenation
(`GridDomain.index4_add`), so it holds for one domain between any two states, because adjacent
transpositions generate the symmetric group as a monoid
(`Equiv.Perm.mclosure_swap_castSucc_succ`). Two domains with the same endpoints differ by a
periodic domain `a c + b r`, whose index and `O`-multiplicity are computed by
`GridDomain.index4_periodic`.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped BigOperators

variable {k : ℕ} [NeZero k]

omit [NeZero k] in
/-- An integer-valued filter count on `Fin k × Fin k` as a sum of indicators. -/
theorem card_filter_prod_eq_sum (P : Fin k × Fin k → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℤ) = ∑ z, if P z then (1 : ℤ) else 0 := by
  rw [Finset.card_filter]
  push_cast
  rfl

/-! ### Adjacent transpositions -/

section Adjacent

variable {p q : Fin k}

omit [NeZero k] in
theorem swap_lt_swap_iff_of_adjacent (hpq : (q : ℕ) = p + 1) {a b : Fin k}
    (h1 : (a, b) ≠ (p, q)) (h2 : (a, b) ≠ (q, p)) :
    Equiv.swap p q a < Equiv.swap p q b ↔ a < b := by
  simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff] at h1 h2
  rw [Fin.lt_def, Fin.lt_def, Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

omit [NeZero k] in
theorem swap_le_iff_of_adjacent (hpq : (q : ℕ) = p + 1) {a b : Fin k}
    (h1 : (a, b) ≠ (p, p)) (h2 : (a, b) ≠ (q, p)) :
    Equiv.swap p q a ≤ b ↔ a ≤ b := by
  simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff] at h1 h2
  rw [Fin.le_def, Fin.le_def, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

omit [NeZero k] in
theorem lt_swap_iff_of_adjacent (hpq : (q : ℕ) = p + 1) {a b : Fin k}
    (h1 : (a, b) ≠ (p, q)) (h2 : (a, b) ≠ (p, p)) :
    a < Equiv.swap p q b ↔ a < b := by
  simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff] at h1 h2
  rw [Fin.lt_def, Fin.lt_def, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

omit [NeZero k] in
/-- Change of the count of increasing pairs under an adjacent transposition. -/
theorem sum_lt_sub_sum_lt_swap (x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    (∑ z : Fin k × Fin k, if z.1 < z.2 ∧ x z.1 < x z.2 then (1 : ℤ) else 0) -
      (∑ z : Fin k × Fin k,
        if z.1 < z.2 ∧ (x * Equiv.swap p q) z.1 < (x * Equiv.swap p q) z.2 then (1 : ℤ) else 0) =
      (if x p < x q then 1 else 0) - (if x q < x p then 1 else 0) := by
  have hlt : p < q := by
    rw [Fin.lt_def]
    omega
  have hnlt : ¬ q < p := by
    rw [Fin.lt_def]
    omega
  have hne : (p, q) ≠ (q, p) := by
    simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff]
    omega
  have hre : (∑ z : Fin k × Fin k,
        if z.1 < z.2 ∧ (x * Equiv.swap p q) z.1 < (x * Equiv.swap p q) z.2 then (1 : ℤ) else 0) =
      ∑ z : Fin k × Fin k,
        if Equiv.swap p q z.1 < Equiv.swap p q z.2 ∧ x z.1 < x z.2 then (1 : ℤ) else 0 :=
    Fintype.sum_equiv ((Equiv.swap p q).prodCongr (Equiv.swap p q)) _ _ fun z => by
      simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.swap_apply_self,
        Equiv.Perm.mul_apply]
      congr 1
  rw [hre, ← Finset.sum_sub_distrib, Fintype.sum_eq_add (p, q) (q, p) hne]
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, hlt, hnlt, true_and, false_and,
      ↓reduceIte]
    ring
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only [swap_lt_swap_iff_of_adjacent hpq h1 h2, sub_self]

omit [NeZero k] in
/-- Change of the count of pairs of a point weakly southwest of a mark under an adjacent
transposition. -/
theorem sum_le_sub_sum_le_swap (O x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    (∑ z : Fin k × Fin k, if z.1 ≤ z.2 ∧ x z.1 ≤ O z.2 then (1 : ℤ) else 0) -
      (∑ z : Fin k × Fin k,
        if z.1 ≤ z.2 ∧ (x * Equiv.swap p q) z.1 ≤ O z.2 then (1 : ℤ) else 0) =
      (if x p ≤ O p then 1 else 0) - (if x q ≤ O p then 1 else 0) := by
  have hnle : ¬ q ≤ p := by
    rw [Fin.le_def]
    omega
  have hne : (p, p) ≠ (q, p) := by
    simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff]
    omega
  have hre : (∑ z : Fin k × Fin k,
        if z.1 ≤ z.2 ∧ (x * Equiv.swap p q) z.1 ≤ O z.2 then (1 : ℤ) else 0) =
      ∑ z : Fin k × Fin k, if Equiv.swap p q z.1 ≤ z.2 ∧ x z.1 ≤ O z.2 then (1 : ℤ) else 0 :=
    Fintype.sum_equiv ((Equiv.swap p q).prodCongr (Equiv.refl _)) _ _ fun z => by
      simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.swap_apply_self,
        Equiv.refl_apply, Equiv.Perm.mul_apply]
      congr 1
  rw [hre, ← Finset.sum_sub_distrib, Fintype.sum_eq_add (p, p) (q, p) hne]
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, le_refl, hnle, true_and,
      false_and, ↓reduceIte]
    ring
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only [swap_le_iff_of_adjacent hpq h1 h2, sub_self]

omit [NeZero k] in
/-- Change of the count of pairs of a mark strictly southwest of a point under an adjacent
transposition. -/
theorem sum_lt_right_sub_sum_lt_right_swap (O x : Equiv.Perm (Fin k))
    (hpq : (q : ℕ) = p + 1) :
    (∑ z : Fin k × Fin k, if z.1 < z.2 ∧ O z.1 < x z.2 then (1 : ℤ) else 0) -
      (∑ z : Fin k × Fin k,
        if z.1 < z.2 ∧ O z.1 < (x * Equiv.swap p q) z.2 then (1 : ℤ) else 0) =
      (if O p < x q then 1 else 0) - (if O p < x p then 1 else 0) := by
  have hlt : p < q := by
    rw [Fin.lt_def]
    omega
  have hne : (p, q) ≠ (p, p) := by
    simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff]
    omega
  have hre : (∑ z : Fin k × Fin k,
        if z.1 < z.2 ∧ O z.1 < (x * Equiv.swap p q) z.2 then (1 : ℤ) else 0) =
      ∑ z : Fin k × Fin k, if z.1 < Equiv.swap p q z.2 ∧ O z.1 < x z.2 then (1 : ℤ) else 0 :=
    Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.swap p q)) _ _ fun z => by
      simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.swap_apply_self,
        Equiv.refl_apply, Equiv.Perm.mul_apply]
      congr 1
  rw [hre, ← Finset.sum_sub_distrib, Fintype.sum_eq_add (p, q) (p, p) hne]
  · simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, hlt, lt_self_iff_false, true_and,
      false_and, ↓reduceIte]
    ring
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only [lt_swap_iff_of_adjacent hpq h1 h2, sub_self]

omit [NeZero k] in
/-- Change of the point-count grading under an adjacent transposition. -/
theorem gridMarkMaslov_sub_swap (O x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    gridMarkMaslov O ⟨x⟩ - gridMarkMaslov O ⟨x * Equiv.swap p q⟩ =
      1 - 2 * (if O p ∈ Grid.cIco (x p) (x q) then 1 else 0) := by
  have h1 := sum_lt_sub_sum_lt_swap x hpq
  have h2 := sum_le_sub_sum_le_swap O x hpq
  have h3 := sum_lt_right_sub_sum_lt_right_swap O x hpq
  have hxne : ((x p : Fin k) : ℕ) ≠ x q := fun h => by
    have := x.injective (Fin.ext h)
    rw [this] at hpq
    omega
  have hfin : ((if x p < x q then (1 : ℤ) else 0) - (if x q < x p then 1 else 0)) -
      ((if x p ≤ O p then 1 else 0) - (if x q ≤ O p then 1 else 0)) -
      ((if O p < x q then 1 else 0) - (if O p < x p then 1 else 0)) =
      1 - 2 * (if O p ∈ Grid.cIco (x p) (x q) then 1 else 0) := by
    simp only [Grid.mem_cIco, Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff, ite_prop_iff_or]
    split_ifs <;> omega
  simp only [gridMarkMaslov, card_filter_prod_eq_sum]
  linear_combination h1 - h2 - h3 + hfin

omit [NeZero k] in
theorem mem_cIco_of_adjacent_iff (hpq : (q : ℕ) = p + 1) (c : Fin k) :
    c ∈ Grid.cIco p q ↔ c = p := by
  have := c.isLt
  simp only [Grid.mem_cIco, ne_eq, Fin.ext_iff, ite_prop_iff_or]
  omega

/-- The width-one rectangle from `x` to `x ∘ (p q)` for columns with `q = p + 1`. -/
def adjacentRectangle (x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    GridRectangleBetween (⟨x⟩ : GridState k) ⟨x * Equiv.swap p q⟩ where
  left := p
  right := q
  left_ne_right := fun h => by
    rw [h] at hpq
    omega
  map_left := by simp
  map_right := by simp
  map_of_ne := fun c h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [NeZero k] in
theorem adjacentRectangle_isEmpty (x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    (adjacentRectangle x hpq).IsEmpty := by
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
  intro c hc
  exfalso
  have := c.isLt
  simp only [adjacentRectangle, Grid.mem_cIoo, ne_eq, Fin.ext_iff, ite_prop_iff_or] at hc
  omega

/-- The formula of `GridDomain.index4_eq_markMaslov` for the width-one rectangle of an adjacent
transposition. -/
theorem exists_adjacent_formula (O x : Equiv.Perm (Fin k)) (hpq : (q : ℕ) = p + 1) :
    ∃ D : GridDomain k, D.IsFrom ⟨x⟩ ⟨x * Equiv.swap p q⟩ ∧
      D.index4 ⟨x⟩ ⟨x * Equiv.swap p q⟩ =
        4 * (gridMarkMaslov O ⟨x⟩ - gridMarkMaslov O ⟨x * Equiv.swap p q⟩) +
          8 * ∑ c, D c (O c) := by
  refine ⟨(adjacentRectangle x hpq).domain, (adjacentRectangle x hpq).domain_isFrom, ?_⟩
  rw [(adjacentRectangle x hpq).index4_domain (adjacentRectangle_isEmpty x hpq),
    gridMarkMaslov_sub_swap O x hpq]
  have hsum : ∑ c, (adjacentRectangle x hpq).domain c (O c) =
      if O p ∈ Grid.cIco (x p) (x q) then 1 else 0 := by
    rw [Fintype.sum_eq_single p]
    · rw [GridRectangleBetween.domain_apply]
      simp only [adjacentRectangle, (mem_cIco_of_adjacent_iff hpq p).mpr rfl, true_and]
    · intro c hc
      rw [GridRectangleBetween.domain_apply, if_neg]
      exact fun h => hc ((mem_cIco_of_adjacent_iff hpq c).mp h.1)
  rw [hsum]
  ring

end Adjacent

/-! ### The formula for every domain -/

/-- Some domain between any two states satisfies the formula of
`GridDomain.index4_eq_markMaslov`. -/
theorem exists_isFrom_markMaslov (O : Equiv.Perm (Fin k)) (u v : GridState k) :
    ∃ D : GridDomain k, D.IsFrom u v ∧
      D.index4 u v = 4 * (gridMarkMaslov O u - gridMarkMaslov O v) + 8 * ∑ c, D c (O c) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 :=
    ⟨k - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos k)).symm⟩
  have key : ∀ σ x : Equiv.Perm (Fin (n + 1)), ∃ D : GridDomain (n + 1),
      D.IsFrom ⟨x⟩ ⟨x * σ⟩ ∧
        D.index4 ⟨x⟩ ⟨x * σ⟩ =
          4 * (gridMarkMaslov O ⟨x⟩ - gridMarkMaslov O ⟨x * σ⟩) + 8 * ∑ c, D c (O c) := by
    intro σ
    have hσ : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem σ hs =>
      obtain ⟨i, rfl⟩ := hs
      intro x
      exact exists_adjacent_formula O x (p := i.castSucc) (q := i.succ) (by simp)
    | one =>
      intro x
      refine ⟨0, ?_, ?_⟩
      · rw [mul_one]
        exact GridDomain.isFrom_zero _
      · rw [mul_one]
        simp
    | mul σ τ _ _ hσ hτ =>
      intro x
      obtain ⟨D₁, hD₁, hf₁⟩ := hσ x
      obtain ⟨D₂, hD₂, hf₂⟩ := hτ (x * σ)
      rw [mul_assoc] at hD₂ hf₂
      refine ⟨D₁ + D₂, hD₁.add hD₂, ?_⟩
      rw [GridDomain.index4_add hD₁ hD₂, hf₁, hf₂]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      ring
  obtain ⟨D, hD, hf⟩ := key (u.toPerm⁻¹ * v.toPerm) u.toPerm
  have hv : (⟨u.toPerm * (u.toPerm⁻¹ * v.toPerm)⟩ : GridState (n + 1)) = v := by
    rw [mul_inv_cancel_left]
  rw [hv] at hD hf
  exact ⟨D, hD, hf⟩

namespace GridDomain

variable {D : GridDomain k} {u v : GridState k}

/-- The index of a domain from `u` to `v` in terms of the point-count grading of an auxiliary
permutation `O` of marks: `ι(D;u,v) = M_O(u) - M_O(v) + 2 ∑_c D(c, O c)`. -/
theorem index4_eq_markMaslov (O : Equiv.Perm (Fin k)) (hD : D.IsFrom u v) :
    D.index4 u v = 4 * (gridMarkMaslov O u - gridMarkMaslov O v) + 8 * ∑ c, D c (O c) := by
  obtain ⟨D₀, hD₀, hf₀⟩ := exists_isFrom_markMaslov O u v
  obtain ⟨a, b, hab⟩ := exists_eq_add_of_boundary_eq_zero
    (isFrom_self_iff_boundary_eq_zero.mp (hD.sub hD₀))
  have hDeq : D = D₀ + fun c r => a c + b r := by
    funext c r
    have := hab c r
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    linarith
  rw [hDeq, index4_linear_add, index4_periodic, hf₀]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  have hO : ∑ c, b (O c) = ∑ r, b r := Equiv.sum_comp O b
  rw [hO]
  ring

end GridDomain

end OnLeConjecture.KnotFloer.GridFull
