/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondAlexander
public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstCycle
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.MarkingCount

/-!
# Relative permutations on the reflected torus grid

Every grid state of `reflectedTorusGrid n` is written uniquely as
`relState n σ`, the state whose point in column `c` is the anchor point of
column `σ c`. This file records the following native facts in these
coordinates.

* The cyclic distance `cycDist x y` on `Fin m` and the cardinality of the
  intersection of two half-open cyclic intervals.
* A target expansion of the full Laurent differential of an arbitrary grid:
  the coefficient at a state `y` is a sum over ordered column pairs.
* For the reflected torus grid, the rectangle with sides `(a, b)` ending at
  `relState n τ` has `O` count `oCount n τ a b` and is state-empty exactly
  when `intCount n τ a b = 0`.
* The general grading formula
  `torusEll n τ - torusEll n (τ * swap a b) = 1 + 2 intCount - 2 oCount`,
  where `torusEll n σ` is minus the native `O` Maslov grading.
* Two consequences: the parity of `torusEll` is the sign of the permutation,
  and `torusEll n σ ≥ 1` for every `σ ≠ 1`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

/-! ### Cyclic distance on `Fin m` -/

section CyclicDistance

variable {m : ℕ}

/-- The forward cyclic distance from `x` to `y` in `Fin m`. -/
def cycDist (x y : Fin m) : ℕ :=
  if x.val ≤ y.val then y.val - x.val else m + y.val - x.val

theorem cycDist_lt (x y : Fin m) : cycDist x y < m := by
  have := x.isLt; have := y.isLt
  unfold cycDist; split_ifs <;> omega

@[simp] theorem cycDist_self (x : Fin m) : cycDist x x = 0 := by
  simp [cycDist]

theorem cycDist_eq_zero_iff {x y : Fin m} : cycDist x y = 0 ↔ x = y := by
  have := x.isLt; have := y.isLt
  rw [Fin.ext_iff]
  unfold cycDist; split_ifs <;> omega

theorem cycDist_add_cycDist_of_ne {x y : Fin m} (h : x ≠ y) :
    cycDist x y + cycDist y x = m := by
  have := x.isLt; have := y.isLt
  rw [Ne, Fin.ext_iff] at h
  unfold cycDist; split_ifs <;> omega

/-- Distances from a second base point are distances from the first base point,
reduced modulo `m`. -/
theorem cycDist_rebase (a x z : Fin m) :
    cycDist x z =
      if cycDist a x ≤ cycDist a z then cycDist a z - cycDist a x
      else m + cycDist a z - cycDist a x := by
  have := a.isLt; have := x.isLt; have := z.isLt
  unfold cycDist; split_ifs <;> omega

/-- The distance from a base point determines the point. -/
theorem eq_of_cycDist_eq {a x y : Fin m} (h : cycDist a x = cycDist a y) : x = y := by
  have := a.isLt; have := x.isLt; have := y.isLt
  rw [Fin.ext_iff]
  unfold cycDist at h; split_ifs at h <;> omega

theorem mem_cIoo_iff_cycDist (a b z : Fin m) :
    z ∈ Grid.cIoo a b ↔ 0 < cycDist a z ∧ cycDist a z < cycDist a b := by
  have := a.isLt; have := b.isLt; have := z.isLt
  rw [Grid.mem_cIoo, Ne, Fin.ext_iff]
  unfold cycDist
  split_ifs <;> omega

theorem mem_cIco_iff_cycDist (a b z : Fin m) :
    z ∈ Grid.cIco a b ↔ cycDist a z < cycDist a b := by
  have := a.isLt; have := b.isLt; have := z.isLt
  rw [Grid.mem_cIco, Ne, Fin.ext_iff]
  unfold cycDist
  split_ifs <;> omega

/-- The distance from a base point, as a point of `Fin m`. -/
def cycPos (a z : Fin m) : Fin m := ⟨cycDist a z, cycDist_lt a z⟩

theorem cycPos_injective (a : Fin m) : Function.Injective (cycPos a) := by
  intro x y h
  exact eq_of_cycDist_eq (congrArg Fin.val h)

/-- The cardinality of the intersection of two half-open intervals of positions. -/
def icoInterCard (B C D : ℕ) : ℕ :=
  if C ≤ D then min B D - C else min B D + (B - C)

theorem icoInterCard_of_le {B C D : ℕ} (h : C ≤ D) : icoInterCard B C D = min B D - C := by
  unfold icoInterCard; rw [if_pos h]

theorem icoInterCard_of_lt {B C D : ℕ} (h : D < C) :
    icoInterCard B C D = min B D + (B - C) := by
  unfold icoInterCard; rw [if_neg (by omega)]

/-- The number of points in the intersection of two half-open cyclic intervals,
computed from the distances of the endpoints to the first endpoint. -/
theorem card_cIco_inter_cIco (a b c d : Fin m) :
    (Grid.cIco a b ∩ Grid.cIco c d).card =
      icoInterCard (cycDist a b) (cycDist a c) (cycDist a d) := by
  classical
  set B := cycDist a b with hB
  set C := cycDist a c with hC
  set D := cycDist a d with hD
  have hBm : B < m := cycDist_lt a b
  have hCm : C < m := cycDist_lt a c
  have hDm : D < m := cycDist_lt a d
  -- Transport the intersection to the positions relative to `a`.
  have hmem (z : Fin m) : z ∈ Grid.cIco a b ∩ Grid.cIco c d ↔
      cycDist a z < B ∧ (if C ≤ D then C ≤ cycDist a z ∧ cycDist a z < D
        else C ≤ cycDist a z ∨ cycDist a z < D) := by
    rw [Finset.mem_inter, mem_cIco_iff_cycDist, mem_cIco_iff_cycDist,
      cycDist_rebase a c z, cycDist_rebase a c d]
    have := cycDist_lt a z
    rw [← hC, ← hD]
    split_ifs <;> omega
  have hcard : (Grid.cIco a b ∩ Grid.cIco c d).card =
      ((Finset.range m).filter fun t => t < B ∧ (if C ≤ D then C ≤ t ∧ t < D
        else C ≤ t ∨ t < D)).card := by
    apply Finset.card_bij (fun z _ => cycDist a z)
    · intro z hz
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨cycDist_lt a z, (hmem z).mp hz⟩
    · intro x _ y _ h
      exact eq_of_cycDist_eq h
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_range] at ht
      have hsurj : Function.Surjective (cycPos a) :=
        Finite.injective_iff_surjective.mp (cycPos_injective a)
      obtain ⟨z, hz⟩ := hsurj ⟨t, ht.1⟩
      have hzt : cycDist a z = t := congrArg Fin.val hz
      refine ⟨z, (hmem z).mpr (hzt ▸ ht.2), hzt⟩
  rw [hcard]
  unfold icoInterCard
  by_cases hCD : C ≤ D
  · rw [if_pos hCD]
    have : (Finset.range m).filter (fun t => t < B ∧ (if C ≤ D then C ≤ t ∧ t < D
        else C ≤ t ∨ t < D)) = Finset.Ico C (min B D) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, if_pos hCD]
      omega
    rw [this, Nat.card_Ico]
  · rw [if_neg hCD]
    have : (Finset.range m).filter (fun t => t < B ∧ (if C ≤ D then C ≤ t ∧ t < D
        else C ≤ t ∨ t < D)) = Finset.Ico 0 (min B D) ∪ Finset.Ico C B := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Finset.mem_union,
        if_neg hCD]
      omega
    rw [this, Finset.card_union_of_disjoint, Nat.card_Ico, Nat.card_Ico]
    · omega
    · rw [Finset.disjoint_left]
      intro t h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      omega

end CyclicDistance

/-! ### A target expansion of the full Laurent differential -/

section TargetExpansion

variable {m : ℕ} (G : GridDiagram m)

/-- The state-emptiness test for the rectangle with initial side `a` and terminal
side `b` that leaves the state `x`. -/
def SideRectEmpty (x : GridState m) (a b : Fin m) : Prop :=
  ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b)

noncomputable instance (x : GridState m) (a b : Fin m) : Decidable (SideRectEmpty x a b) := by
  unfold SideRectEmpty; infer_instance

/-- The columns of the `O` markings covered by the rectangle with initial side `a`
and terminal side `b` that leaves the state `x`. -/
noncomputable def sideRectOColumns (x : GridState m) (a b : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun c => c ∈ Grid.cIco a b ∧ G.O c ∈ Grid.cIco (x a) (x b)

theorem isEmpty_iff_sideRectEmpty {x y : GridState m} (r : GridRectangleBetween x y) :
    r.IsEmpty ↔ SideRectEmpty x r.left r.right := by
  rw [isEmpty_iff_forall_notMem_cIoo]
  rfl

theorem OColumns_eq_sideRectOColumns {x y : GridState m} (r : GridRectangleBetween x y) :
    G.OColumns r.toGridRectangle = sideRectOColumns G x r.left r.right := by
  ext c
  simp only [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows, toGridRectangle_left,
    toGridRectangle_right, toGridRectangle_bottom, toGridRectangle_top, bottom_def, top_def,
    sideRectOColumns, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The coefficient of the full Laurent differential at a state `y` is a sum over
the ordered pairs of distinct columns. The pair `(a, b)` contributes the rectangle
with initial side `a` and terminal side `b` from `y.swapColumns a b` to `y`. -/
theorem laurentDifferential_apply_eq_sum_offDiag (R : Type*) [CommSemiring R]
    (c : LaurentChain R m) (y : GridState m) :
    laurentDifferential G R c y =
      ∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
        c (y.swapColumns p.1 p.2) *
          (if SideRectEmpty (y.swapColumns p.1 p.2) p.1 p.2 then
            LaurentPolynomial.T
              ((sideRectOColumns G (y.swapColumns p.1 p.2) p.1 p.2).card : ℤ)
          else 0) := by
  classical
  rw [laurentDifferential_apply_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  refine Eq.trans ?_ (Finset.sum_fiberwise _ (fun p : Fin m × Fin m => y.swapColumns p.1 p.2) _)
  apply Finset.sum_congr rfl
  intro x _
  rw [laurentCoefficient_eq, Finset.mul_sum, emptyRectangles, Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun p hp => ofSwapColumns x y p.1 p.2
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2 (by
        rw [← (Finset.mem_filter.mp hp).2, GridState.swapColumns_swapColumns]))
    (fun r _ => (r.left, r.right)) ?_ ?_ ?_ ?_ ?_
  · intro p hp; exact Finset.mem_univ _
  · intro r _
    rw [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _, r.left_ne_right⟩,
      r.source_eq_swapColumns.symm⟩
  · intro p hp; simp
  · intro r _
    exact GridRectangleBetween.ext (ofSwapColumns_left _ _ _ _ _ _)
      (ofSwapColumns_right _ _ _ _ _ _)
  · intro p hp
    have hx : y.swapColumns p.1 p.2 = x := (Finset.mem_filter.mp hp).2
    have hl := ofSwapColumns_left x y p.1 p.2
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2 (by
        rw [← hx, GridState.swapColumns_swapColumns])
    have hr := ofSwapColumns_right x y p.1 p.2
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2 (by
        rw [← hx, GridState.swapColumns_swapColumns])
    rw [isEmpty_iff_sideRectEmpty, OColumns_eq_sideRectOColumns, hl, hr]
    simp only [hx]
    split_ifs <;> simp

end TargetExpansion

/-! ### Relative permutation states of the reflected torus grid -/

variable (n : ℕ)

/-- The state whose point in column `c` is the anchor point of column `σ c`. -/
def relState (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    GridState (consecutiveTorusGridSize n) :=
  ⟨σ.trans (reflectedTorusAnchor n).toPerm⟩

@[simp] theorem relState_apply (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (c : Fin (consecutiveTorusGridSize n)) :
    relState n σ c = reflectedTorusAnchor n (σ c) := rfl

@[simp] theorem relState_one : relState n 1 = reflectedTorusAnchor n := by
  ext c; rfl

theorem relState_injective : Function.Injective (relState n) := by
  intro σ τ h
  ext c
  have := congrArg (fun x : GridState (consecutiveTorusGridSize n) => x c) h
  simp only [relState_apply] at this
  exact congrArg Fin.val ((reflectedTorusAnchor n).toPerm.injective this)

@[simp] theorem relativeColumns_relState (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    reflectedTorusRelativeColumns n (relState n σ) = σ := by
  change (σ.trans (reflectedTorusAnchor n).toPerm).trans (reflectedTorusAnchor n).toPerm.symm = σ
  rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl]

@[simp] theorem relState_relativeColumns (x : GridState (consecutiveTorusGridSize n)) :
    relState n (reflectedTorusRelativeColumns n x) = x := by
  ext c
  simp only [relState_apply, reflectedTorusAnchor_relativeColumns]

theorem swapColumns_relState (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (a b : Fin (consecutiveTorusGridSize n)) :
    (relState n σ).swapColumns a b = relState n (σ * Equiv.swap a b) := by
  ext c
  simp [GridState.swapColumns_apply]

/-- The number of `O` markings covered by the rectangle with sides `(a, b)` ending
at the state `relState n τ`. -/
noncomputable def oCount (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (a b : Fin (consecutiveTorusGridSize n)) : ℕ :=
  (Grid.cIco a b ∩ Grid.cIco (τ a) (τ b)).card

/-- The number of source points inside the rectangle with sides `(a, b)` ending at
`relState n τ`. -/
noncomputable def intCount (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (a b : Fin (consecutiveTorusGridSize n)) : ℕ :=
  ((Grid.cIoo a b).filter fun c => τ c ∈ Grid.cIoo (τ a) (τ b)).card

theorem sideRectEmpty_relState_iff (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (a b : Fin (consecutiveTorusGridSize n)) :
    SideRectEmpty (relState n (τ * Equiv.swap a b)) a b ↔ intCount n τ a b = 0 := by
  rw [intCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  unfold SideRectEmpty
  apply forall₂_congr
  intro c hc
  have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hc
  have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hc
  simp only [relState_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hca hcb, reflectedTorusAnchor_apply,
    Grid.mem_cIoo_finRotate_rev]

theorem sideRectOColumns_relState (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    (a b : Fin (consecutiveTorusGridSize n)) :
    sideRectOColumns (reflectedTorusGrid n) (relState n (τ * Equiv.swap a b)) a b =
      Grid.cIco a b ∩ Grid.cIco (τ a) (τ b) := by
  ext c
  simp only [sideRectOColumns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    relState_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    reflectedTorusGrid_O_apply, reflectedTorusAnchor_apply, Grid.rev_mem_cIco_finRotate_rev]

/-- The target expansion of the full Laurent differential at a relative state. -/
theorem laurentDifferential_relState (R : Type*) [CommSemiring R]
    (c : LaurentChain R (consecutiveTorusGridSize n))
    (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    laurentDifferential (reflectedTorusGrid n) R c (relState n τ) =
      ∑ p ∈ (Finset.univ : Finset (Fin (consecutiveTorusGridSize n))).offDiag,
        c (relState n (τ * Equiv.swap p.1 p.2)) *
          (if intCount n τ p.1 p.2 = 0 then
            LaurentPolynomial.T (oCount n τ p.1 p.2 : ℤ) else 0) := by
  rw [laurentDifferential_apply_eq_sum_offDiag]
  apply Finset.sum_congr rfl
  intro p _
  rw [swapColumns_relState]
  congr 1
  exact if_congr (sideRectEmpty_relState_iff n τ _ _)
    (by rw [sideRectOColumns_relState]; rfl) rfl

/-! ### The general grading formula -/

/-- Minus the native `O` Maslov grading of a relative state. -/
def torusEll (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) : ℤ :=
  -(reflectedTorusGrid n).maslovOℤ (relState n σ)

@[simp] theorem torusEll_one : torusEll n 1 = 0 := by
  rw [torusEll, relState_one, maslovO_reflectedTorusAnchor, neg_zero]

private theorem card_pointSet_inter_product {m : ℕ} (x : GridState m) (s t : Finset (Fin m)) :
    (x.pointSet ∩ s ×ˢ t).card = (s.filter fun c => x c ∈ t).card := by
  classical
  symm
  apply Finset.card_bij (fun c _ => (c, x c))
  · intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_inter, GridState.mem_pointSet, Finset.mem_product]
    exact ⟨rfl, hc.1, hc.2⟩
  · intro c _ d _ h
    exact congrArg Prod.fst h
  · intro q hq
    rw [Finset.mem_inter, GridState.mem_pointSet, Finset.mem_product] at hq
    refine ⟨q.1, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hq.2.1, hq.1 ▸ hq.2.2⟩
    · exact Prod.ext rfl hq.1

/-- The general grading formula for an arbitrary rectangle ending at `relState n τ`.
Its two counts are the source points inside the rectangle and the covered `O`
markings. -/
theorem torusEll_sub_torusEll_mul_swap (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) :
    torusEll n τ - torusEll n (τ * Equiv.swap a b) =
      1 + 2 * (intCount n τ a b : ℤ) - 2 * (oCount n τ a b : ℤ) := by
  classical
  set x := relState n (τ * Equiv.swap a b) with hx
  set y := relState n τ with hy
  have hyx : y = x.swapColumns a b := by
    rw [hx, swapColumns_relState, mul_assoc, Equiv.swap_mul_self, mul_one]
  let r := ofSwapColumns x y a b hab hyx
  have hl : r.left = a := ofSwapColumns_left _ _ _ _ _ _
  have hr : r.right = b := ofSwapColumns_right _ _ _ _ _ _
  have h := (reflectedTorusGrid n).maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card r
  rw [(reflectedTorusGrid n).maslovO_eq_intCast, (reflectedTorusGrid n).maslovO_eq_intCast,
    r.pointSet_inter_coveredSquares_eq_insert, Finset.card_insert_of_notMem
      (fun h => r.toGridRectangle.notMem_interior_of_fst_eq_left rfl (Finset.mem_inter.mp h).2),
    ← (reflectedTorusGrid n).card_OColumns] at h
  have hint : (x.pointSet ∩ r.toGridRectangle.interior).card = intCount n τ a b := by
    have hI : r.toGridRectangle.interior = Grid.cIoo a b ×ˢ Grid.cIoo (x a) (x b) := by
      rw [GridRectangle.interior, GridRectangle.columnInterior, GridRectangle.rowInterior]
      simp only [toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
        toGridRectangle_top, bottom_def, top_def, hl, hr]
    rw [hI, card_pointSet_inter_product, intCount]
    congr 1
    apply Finset.filter_congr
    intro c hc
    have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hc
    have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hc
    simp only [hx, relState_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hca hcb, reflectedTorusAnchor_apply,
      Grid.mem_cIoo_finRotate_rev]
  have hO : ((reflectedTorusGrid n).OColumns r.toGridRectangle).card = oCount n τ a b := by
    rw [OColumns_eq_sideRectOColumns, hl, hr, hx, sideRectOColumns_relState]
    rfl
  rw [hint, hO] at h
  have hq : (((reflectedTorusGrid n).maslovOℤ x - (reflectedTorusGrid n).maslovOℤ y : ℤ) : ℚ) =
      ((1 + 2 * (intCount n τ a b : ℤ) - 2 * (oCount n τ a b : ℤ) : ℤ) : ℚ) := by
    push_cast at h ⊢
    linarith
  have hz := Int.cast_injective (α := ℚ) hq
  unfold torusEll
  rw [← hx, ← hy]
  linarith


/-- A single column swap changes the parity of `torusEll`. -/
theorem even_torusEll_mul_swap_iff (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    {a b : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b) :
    Even (torusEll n (τ * Equiv.swap a b)) ↔ ¬ Even (torusEll n τ) := by
  have h := torusEll_sub_torusEll_mul_swap n τ hab
  have h' : torusEll n (τ * Equiv.swap a b) =
      torusEll n τ - 1 - 2 * ((intCount n τ a b : ℤ) - (oCount n τ a b : ℤ)) := by linarith
  rw [h', Int.even_sub, Int.even_sub, Int.even_mul]
  simp

/-- The parity of `torusEll` is the sign of the relative permutation. -/
theorem even_torusEll_iff_sign (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) :
    Even (torusEll n σ) ↔ Equiv.Perm.sign σ = 1 := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f x y hxy ih =>
    rw [even_torusEll_mul_swap_iff n f hxy, ih, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    rcases Int.units_eq_one_or (Equiv.Perm.sign f) with h | h <;> simp [h]

/-- Removing a point from its cycle gives a rectangle with no covered `O` marking
in at least one of the two orientations. -/
theorem oCount_eq_zero_or_of_apply_symm
    (σ : Equiv.Perm (Fin (consecutiveTorusGridSize n)))
    {a : Fin (consecutiveTorusGridSize n)} (ha : σ a ≠ a) :
    oCount n σ a (σ.symm a) = 0 ∨ oCount n σ (σ.symm a) a = 0 := by
  set b := σ.symm a with hb
  have hσb : σ b = a := by rw [hb, Equiv.apply_symm_apply]
  have hba : b ≠ a := by
    intro h; apply ha; have := hσb; rw [h] at this; exact this
  rw [oCount, oCount, hσb, card_cIco_inter_cIco, card_cIco_inter_cIco,
    cycDist_rebase a b a, cycDist_rebase a b (σ a)]
  have h1 := cycDist_lt a b
  have h2 := cycDist_lt a (σ a)
  have h3 : 0 < cycDist a b := Nat.pos_of_ne_zero (fun h => hba (cycDist_eq_zero_iff.mp h).symm)
  have h4 : 0 < cycDist a (σ a) :=
    Nat.pos_of_ne_zero (fun h => ha (cycDist_eq_zero_iff.mp h).symm)
  simp only [cycDist_self, icoInterCard]
  split_ifs <;> omega

/-- Every relative state other than the anchor has negative Maslov grading. -/
theorem one_le_torusEll {σ : Equiv.Perm (Fin (consecutiveTorusGridSize n))} (hσ : σ ≠ 1) :
    1 ≤ torusEll n σ := by
  classical
  induction h : σ.support.card using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
    obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
      by_contra hcon
      push Not at hcon
      exact hσ (Equiv.ext hcon)
    set b := σ.symm a with hb
    have hσb : σ b = a := by rw [hb, Equiv.apply_symm_apply]
    have hab : a ≠ b := by
      intro h'; apply ha; have := hσb; rw [← h'] at this; exact this
    set σ' := σ * Equiv.swap a b with hσ'
    have hsub : σ'.support ⊂ σ.support := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨a, Equiv.Perm.mem_support.mpr ha, ?_⟩
        rw [Equiv.Perm.mem_support, not_not, hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          hσb]
      · intro x hx
        rw [Equiv.Perm.mem_support] at hx ⊢
        intro hfix
        apply hx
        have hxa : x ≠ a := by intro h'; rw [h'] at hfix; exact ha hfix
        have hxb : x ≠ b := by intro h'; rw [h', hσb] at hfix; exact hab hfix
        rw [hσ', Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb, hfix]
    have hσ'ge : 0 ≤ torusEll n σ' := by
      by_cases h1 : σ' = 1
      · rw [h1, torusEll_one]
      · have := ih σ'.support.card (h ▸ Finset.card_lt_card hsub) h1 rfl
        omega
    rcases oCount_eq_zero_or_of_apply_symm n σ ha with h0 | h0 <;> rw [← hb] at h0
    · have hf := torusEll_sub_torusEll_mul_swap n σ hab
      rw [h0] at hf
      have : 0 ≤ (intCount n σ a b : ℤ) := Int.natCast_nonneg _
      rw [← hσ'] at hf
      omega
    · have hf := torusEll_sub_torusEll_mul_swap n σ hab.symm
      rw [h0, Equiv.swap_comm, ← hσ'] at hf
      have : 0 ≤ (intCount n σ b a : ℤ) := Int.natCast_nonneg _
      omega

end OnLeConjecture.KnotFloer.GridFull
