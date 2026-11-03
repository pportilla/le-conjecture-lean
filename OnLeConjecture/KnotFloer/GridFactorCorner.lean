/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFactorAuxiliary
public import OnLeConjecture.KnotFloer.GridFactorComparison
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.Southwest

/-!
# The corner inequality for the Alexander grading

Let `G` be a grid diagram of size `n`. Its row `ρ` carries a horizontal arc from the column
`p = O⁻¹ ρ` of its `O`-marking to the column `q = X⁻¹ ρ` of its `X`-marking. The arc wraps around
the torus when `q < p`, and the number of wrapping rows is `wrapNumber G`. The row `ρ` is active at
the cut before column `c` when `c` lies in the cyclic interval `(p, q]`. Its activity indicator

`rowActive G ρ c = [p < c] - [q < c] + [q < p]`

takes the values `0` and `1`, and at every cut exactly `wrapNumber G` rows are active.

The Alexander grading is a sum over columns (`GridDiagram.alexanderTwoℤ_eq_sum_southwestCount`).
The column contribution `C(c, r)` of a point in row `r` equals the number of wrapping rows below
`r` minus the number `F(c, r)` of rows below `r` active at `c` (Lemma 5.4 of the factor lower bound
proof, valid for every grid). Write `x₀ = cornerShift G.O` for the state at the lower right corners
of the `O`-markings, and `Q = auxiliaryGrid G.O`. The auxiliary grid has one active row at each
cut, namely the row `x₀ c`. Comparing column by column gives the **corner inequality**: if
`wrapNumber G ≤ a`, then for every grid state `x`

`2 A_G(x) - 2 A_G(x₀) ≥ a (2 A_Q(x) - 2 A_Q(x₀))`.

Together with `M_O(x₀) = 0` (so that `A_Q(x₀) = 0`), Lemma 1.3 and Lemma 2.3 this yields the
lower bound `ν_G(t) ≥ (t/2) A_G(x₀)` for `0 ≤ t ≤ 2/a`. This is a common generalization of the
pointwise comparisons in Theorems 3.5 and 5.7 of the written proof: the constant of those
comparisons is the Alexander grading of the single state `x₀`.

## Main results

* `GridDiagram.maslovOℤ_cornerShift`: `M_O(x₀) = 0` for every grid.
* `alexanderTwoℤ_auxiliaryGrid`: `2 A_Q(x) = -2 #{c | x₀ c < x c}`.
* `alexanderTwoℤ_corner_inequality`: the corner inequality.
* `alexander_spectralThreshold_corner`: `ν_G(t) ≥ (t/2) A_G(x₀)` for `0 ≤ t ≤ 2/a`.

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ}

/-! ### Southwest counts as sums over rows -/

/-- A southwest count as a sum of indicators over columns. -/
theorem southwestCount_eq_sum (m : GridState n) (c r : Fin n) :
    (m.southwestCount c r : ℤ) = ∑ d : Fin n, if d < c ∧ m d < r then 1 else 0 := by
  rw [GridState.southwestCount_def, Finset.card_filter]
  push_cast
  rfl

/-- A southwest count as a sum of indicators over rows. -/
theorem southwestCount_eq_sum_rows (m : GridState n) (c r : Fin n) :
    (m.southwestCount c r : ℤ) =
      ∑ ρ : Fin n, if ρ < r ∧ m.toPerm.symm ρ < c then 1 else 0 := by
  rw [southwestCount_eq_sum]
  refine Fintype.sum_equiv m.toPerm _ _ fun d => ?_
  rw [Equiv.symm_apply_apply]
  exact if_congr and_comm rfl rfl

/-! ### Wrapping and active rows -/

/-- The row `ρ` wraps when its `X`-marking lies strictly to the left of its `O`-marking. -/
def wrapInd (G : GridDiagram n) (ρ : Fin n) : ℤ :=
  if G.X.toPerm.symm ρ < G.O.toPerm.symm ρ then 1 else 0

/-- The number of rows whose horizontal arc wraps around the torus. -/
def wrapNumber (G : GridDiagram n) : ℕ :=
  (Finset.univ.filter fun ρ : Fin n => G.X.toPerm.symm ρ < G.O.toPerm.symm ρ).card

/-- The activity indicator of the row `ρ` at the cut before column `c`. -/
def rowActive (G : GridDiagram n) (ρ c : Fin n) : ℤ :=
  (if G.O.toPerm.symm ρ < c then 1 else 0) - (if G.X.toPerm.symm ρ < c then 1 else 0) +
    wrapInd G ρ

/-- The number of rows below `r` that are active at the cut before column `c`. -/
def activeBelow (G : GridDiagram n) (c r : Fin n) : ℤ :=
  ∑ ρ : Fin n, if ρ < r then rowActive G ρ c else 0

/-- The number of wrapping rows below `r`. -/
def wrapBelow (G : GridDiagram n) (r : Fin n) : ℤ :=
  ∑ ρ : Fin n, if ρ < r then wrapInd G ρ else 0

theorem rowActive_nonneg (G : GridDiagram n) (ρ c : Fin n) : 0 ≤ rowActive G ρ c := by
  unfold rowActive wrapInd
  have hne : G.X.toPerm.symm ρ ≠ G.O.toPerm.symm ρ := by
    intro h
    apply G.disjoint (G.O.toPerm.symm ρ)
    rw [Equiv.apply_symm_apply, ← h, Equiv.apply_symm_apply]
  have := lt_or_gt_of_ne hne
  split_ifs <;> simp only [Fin.lt_def] at * <;> omega

/-- The number of rows whose marking of a given kind lies strictly left of `c` is `c`. -/
private theorem sum_ite_symm_lt (m : GridState n) (c : Fin n) :
    (∑ ρ : Fin n, if m.toPerm.symm ρ < c then (1 : ℤ) else 0) = c := by
  rw [← Equiv.sum_comp m.toPerm]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun d : Fin n => d < c) = Finset.Iio c := by
    ext d
    simp
  rw [this, Fin.card_Iio]

/-- At every cut exactly `wrapNumber G` rows are active. -/
theorem sum_rowActive (G : GridDiagram n) (c : Fin n) :
    ∑ ρ : Fin n, rowActive G ρ c = wrapNumber G := by
  unfold rowActive
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ite_symm_lt, sum_ite_symm_lt,
    wrapNumber, Finset.card_filter]
  push_cast
  simp only [sub_self, zero_add]
  rfl

theorem activeBelow_nonneg (G : GridDiagram n) (c r : Fin n) : 0 ≤ activeBelow G c r :=
  Finset.sum_nonneg fun ρ _ => by
    split_ifs
    · exact rowActive_nonneg G ρ c
    · exact le_rfl

theorem activeBelow_mono (G : GridDiagram n) (c : Fin n) {r r' : Fin n} (h : r ≤ r') :
    activeBelow G c r ≤ activeBelow G c r' :=
  Finset.sum_le_sum fun ρ _ => by
    by_cases h1 : ρ < r
    · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h)]
    · rw [if_neg h1]
      split_ifs
      · exact rowActive_nonneg G ρ c
      · exact le_rfl

theorem activeBelow_le_wrapNumber (G : GridDiagram n) (c r : Fin n) :
    activeBelow G c r ≤ wrapNumber G := by
  rw [← sum_rowActive G c]
  exact Finset.sum_le_sum fun ρ _ => by
    split_ifs
    · exact le_rfl
    · exact rowActive_nonneg G ρ c

/-- **Lemma 5.4 (column contributions).** The column contribution of the grid point `(c, r)` is
the number of wrapping rows below `r` minus the number of rows below `r` active at `c`. -/
theorem southwestCount_sub_southwestCount (G : GridDiagram n) (c r : Fin n) :
    (G.X.southwestCount c r : ℤ) - G.O.southwestCount c r = wrapBelow G r - activeBelow G c r := by
  rw [southwestCount_eq_sum_rows, southwestCount_eq_sum_rows, wrapBelow, activeBelow,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold rowActive
  by_cases hρ : ρ < r
  · simp only [hρ, true_and, if_true]
    ring
  · simp [hρ]

/-- Differences of doubled Alexander gradings are differences of active counts. -/
theorem alexanderTwoℤ_sub_alexanderTwoℤ (G : GridDiagram n) (x y : GridState n) :
    G.alexanderTwoℤ x - G.alexanderTwoℤ y =
      2 * ∑ c : Fin n, (activeBelow G c (y c) - activeBelow G c (x c)) := by
  rw [GridDiagram.alexanderTwoℤ_eq_sum_southwestCount,
    GridDiagram.alexanderTwoℤ_eq_sum_southwestCount]
  simp only [southwestCount_sub_southwestCount]
  have hx : ∑ c : Fin n, wrapBelow G (x c) = ∑ r : Fin n, wrapBelow G r :=
    Equiv.sum_comp x.toPerm (wrapBelow G)
  have hy : ∑ c : Fin n, wrapBelow G (y c) = ∑ r : Fin n, wrapBelow G r :=
    Equiv.sum_comp y.toPerm (wrapBelow G)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hx, hy]
  ring

/-! ### The auxiliary grid -/

/-- The activity indicator of an auxiliary grid as a function of cyclic positions. -/
private theorem auxiliary_indicator (hn : 2 ≤ n) (p c : Fin n) :
    ((if p < c then (1 : ℤ) else 0) - (if finRotate n p < c then 1 else 0) +
      (if finRotate n p < p then 1 else 0)) = if c = finRotate n p then 1 else 0 := by
  cases n with
  | zero => exact p.elim0
  | succ k =>
    rcases eq_or_ne p (Fin.last k) with rfl | hp
    · rw [finRotate_last]
      have hc := c.isLt
      by_cases hc0 : c = 0
      · subst hc0
        have hk : (0 : Fin (k + 1)) < Fin.last k := by
          rw [Fin.lt_def, Fin.val_last, Fin.val_zero]
          omega
        rw [if_neg (lt_irrefl _), if_neg (not_lt.mpr (Fin.zero_le _)), if_pos hk, if_pos rfl]
        ring
      · have hc0' : 0 < c.val := by
          rcases Nat.eq_zero_or_pos c.val with h | h
          · exact absurd (Fin.ext h) hc0
          · exact h
        simp only [Fin.lt_def, Fin.val_last, Fin.val_zero, hc0, if_false]
        split_ifs <;> omega
    · have hv : (finRotate (k + 1) p).val = p.val + 1 := coe_finRotate_of_ne_last hp
      have hpl : p.val < k := Fin.val_lt_last hp
      simp only [Fin.lt_def, Fin.ext_iff, hv]
      split_ifs <;> omega

/-- In the auxiliary grid exactly the row `cornerShift O c` is active at the cut before `c`. -/
theorem rowActive_auxiliaryGrid (O : GridState n) (hn : 2 ≤ n) (ρ c : Fin n) :
    rowActive (auxiliaryGrid O hn) ρ c = if ρ = cornerShift O c then 1 else 0 := by
  set p := O.toPerm.symm ρ with hp
  have hX : (cornerShift O).toPerm.symm ρ = finRotate n p := by
    rw [Equiv.symm_apply_eq]
    change ρ = cornerShift O (finRotate n p)
    rw [cornerShift_finRotate, hp]
    exact (Equiv.apply_symm_apply _ _).symm
  have hiff : ρ = cornerShift O c ↔ c = finRotate n p := by
    rw [cornerShift_apply, hp]
    constructor
    · intro h
      have h' : O.toPerm.symm ρ = (finRotate n).symm c := by
        rw [h]
        exact O.toPerm.symm_apply_apply _
      rw [h', Equiv.apply_symm_apply]
    · intro h
      rw [h, Equiv.symm_apply_apply]
      exact (Equiv.apply_symm_apply _ _).symm
  unfold rowActive wrapInd
  change ((if O.toPerm.symm ρ < c then (1 : ℤ) else 0) -
      (if (cornerShift O).toPerm.symm ρ < c then 1 else 0) +
        (if (cornerShift O).toPerm.symm ρ < O.toPerm.symm ρ then 1 else 0)) = _
  rw [hX, ← hp, auxiliary_indicator hn p c]
  by_cases h : ρ = cornerShift O c
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem activeBelow_auxiliaryGrid (O : GridState n) (hn : 2 ≤ n) (c r : Fin n) :
    activeBelow (auxiliaryGrid O hn) c r = if cornerShift O c < r then 1 else 0 := by
  unfold activeBelow
  simp only [rowActive_auxiliaryGrid]
  rw [Finset.sum_eq_single (cornerShift O c)]
  · simp
  · intro ρ _ hρ
    simp [hρ]
  · simp

/-- The auxiliary Alexander grading relative to the corner state counts the columns where the
state lies above the corner state. -/
theorem alexanderTwoℤ_auxiliaryGrid_sub (O : GridState n) (hn : 2 ≤ n) (x : GridState n) :
    (auxiliaryGrid O hn).alexanderTwoℤ x - (auxiliaryGrid O hn).alexanderTwoℤ (cornerShift O) =
      -2 * ∑ c : Fin n, if cornerShift O c < x c then 1 else 0 := by
  rw [alexanderTwoℤ_sub_alexanderTwoℤ]
  simp only [activeBelow_auxiliaryGrid, lt_irrefl, if_false, zero_sub]
  rw [Finset.sum_neg_distrib]
  ring

/-! ### The Maslov grading of the corner state -/

/-- A Maslov grading relative to the `O`-marking state, as southwest counts. -/
private theorem maslovOℤ_sub_maslovOℤ_O (G : GridDiagram n) (x : GridState n) :
    G.maslovOℤ x - G.maslovOℤ G.O =
      ∑ c : Fin n, (x.southwestCount c (x c) : ℤ) -
        2 * ∑ c : Fin n, (G.O.southwestCount c (x c) : ℤ) +
          ∑ c : Fin n, (G.O.southwestCount c (G.O c) : ℤ) := by
  simp only [GridDiagram.maslovOℤ_def, GridDiagram.OSet_def,
    GridState.I_self_pointSet_eq_sum_southwestCount,
    GridState.JNumCenter_pointSet_eq_sum_southwestCount, Nat.cast_sum]
  have hx : ∑ c : Fin n, ((x c : ℕ) : ℤ) = ∑ c : Fin n, ((c : ℕ) : ℤ) :=
    Equiv.sum_comp x.toPerm (fun r : Fin n => ((r : ℕ) : ℤ))
  have hO : ∑ c : Fin n, ((G.O c : ℕ) : ℤ) = ∑ c : Fin n, ((c : ℕ) : ℤ) :=
    Equiv.sum_comp G.O.toPerm (fun r : Fin n => ((r : ℕ) : ℤ))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hx, hO]
  ring

/-- The southwest count at a point of a state, read one column further right. -/
private theorem southwestCount_succ_self (O : GridState (k + 1)) (j : Fin k) :
    O.southwestCount j.succ (O j.castSucc) = O.southwestCount j.castSucc (O j.castSucc) := by
  rw [GridState.southwestCount_def, GridState.southwestCount_def]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hne : d ≠ j.castSucc := fun he => (lt_irrefl _) (he ▸ h2)
    rw [Fin.lt_def, Fin.val_succ] at h1
    rw [Fin.lt_def, Fin.val_castSucc]
    have : d.val ≠ j.val := fun h => hne (Fin.ext (by rw [Fin.val_castSucc]; exact h))
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [Fin.lt_def, Fin.val_castSucc] at h1
    rw [Fin.lt_def, Fin.val_succ]
    omega

/-- **The corner state has Maslov grading zero.** For every grid diagram, the state at the lower
right corners of the `O`-markings has `M_O = 0`. -/
theorem maslovOℤ_cornerShift (G : GridDiagram n) (hn : 1 ≤ n) :
    G.maslovOℤ (cornerShift G.O) = 0 := by
  have h := maslovOℤ_sub_maslovOℤ_O G (cornerShift G.O)
  rw [GridDiagram.maslovOℤ_O] at h
  cases n with
  | zero => omega
  | succ k =>
  set O := G.O with hOdef
  have hx0 : ∀ j : Fin k, cornerShift O j.succ = O j.castSucc := by
    intro j
    rw [cornerShift_apply]
    congr 1
    rw [Equiv.symm_apply_eq]
    ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j), Fin.val_castSucc, Fin.val_succ]
  have hx00 : cornerShift O 0 = O (Fin.last k) := by
    rw [cornerShift_apply]
    congr 1
  set S : Fin k → ℤ := fun j => (O.southwestCount j.castSucc (O j.castSucc) : ℤ) with hS
  -- the O-counts at the corner state
  have hA : ∑ c : Fin (k + 1), (O.southwestCount c (cornerShift O c) : ℤ) = ∑ j, S j := by
    rw [Fin.sum_univ_succ]
    have h0 : O.southwestCount 0 (cornerShift O 0) = 0 := by
      rw [GridState.southwestCount_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun d _ hd => Fin.not_lt_zero d hd.1
    rw [h0]
    simp only [Nat.cast_zero, zero_add, hx0, southwestCount_succ_self, hS]
  -- the self-counts of the corner state
  have hB : ∑ c : Fin (k + 1), ((cornerShift O).southwestCount c (cornerShift O c) : ℤ) =
      ∑ j : Fin k, ((if O (Fin.last k) < O j.castSucc then 1 else 0) + S j) := by
    rw [Fin.sum_univ_succ]
    have h0 : (cornerShift O).southwestCount 0 (cornerShift O 0) = 0 := by
      rw [GridState.southwestCount_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun d _ hd => Fin.not_lt_zero d hd.1
    rw [h0, Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [southwestCount_eq_sum, Fin.sum_univ_succ, hx0, hx00, hS]
    simp only
    rw [southwestCount_eq_sum, Fin.sum_univ_castSucc]
    have hlast : ¬ (Fin.last k < j.castSucc) := not_lt.mpr (Fin.le_last _)
    simp only [hlast, false_and, if_false, add_zero, Fin.succ_pos, true_and, hx0,
      Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff]
  -- the self-counts of the O-markings
  have hC : ∑ c : Fin (k + 1), (O.southwestCount c (O c) : ℤ) =
      ∑ j, S j + (O.southwestCount (Fin.last k) (O (Fin.last k)) : ℤ) := by
    rw [Fin.sum_univ_castSucc]
  have hD : (O.southwestCount (Fin.last k) (O (Fin.last k)) : ℤ) =
      ∑ j : Fin k, if O j.castSucc < O (Fin.last k) then 1 else 0 := by
    rw [southwestCount_eq_sum, Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_lt_last, true_and, lt_irrefl, false_and, if_false, add_zero]
  have hE : ∑ j : Fin k, ((if O (Fin.last k) < O j.castSucc then (1 : ℤ) else 0) +
      (if O j.castSucc < O (Fin.last k) then 1 else 0)) = k := by
    have hne : ∀ j : Fin k, O j.castSucc ≠ O (Fin.last k) := fun j he =>
      Fin.castSucc_ne_last j (O.toPerm.injective he)
    have : ∀ j : Fin k, ((if O (Fin.last k) < O j.castSucc then (1 : ℤ) else 0) +
        (if O j.castSucc < O (Fin.last k) then 1 else 0)) = 1 := by
      intro j
      rcases lt_or_gt_of_ne (hne j) with h1 | h1
      · rw [if_neg (not_lt.mpr h1.le), if_pos h1]
        ring
      · rw [if_pos h1, if_neg (not_lt.mpr h1.le)]
        ring
    simp [this]
  rw [hA, hB, hC, hD] at h
  rw [Finset.sum_add_distrib] at h
  have hE' := hE
  rw [Finset.sum_add_distrib] at hE'
  push_cast at h hE' ⊢
  linarith

/-- The auxiliary grid has Alexander grading zero at the corner state. -/
theorem alexanderTwoℤ_auxiliaryGrid_cornerShift (O : GridState n) (hn : 2 ≤ n) :
    (auxiliaryGrid O hn).alexanderTwoℤ (cornerShift O) = 0 := by
  rw [GridDiagram.alexanderTwoℤ_def]
  have h1 : (auxiliaryGrid O hn).maslovOℤ (cornerShift O) = 0 :=
    maslovOℤ_cornerShift (auxiliaryGrid O hn) (by omega)
  have h2 : (auxiliaryGrid O hn).maslovXℤ (cornerShift O) = 1 - (n : ℤ) :=
    GridDiagram.maslovXℤ_X (auxiliaryGrid O hn)
  rw [h1, h2]
  ring

/-- **Lemma 2.6.** The doubled Alexander grading of an auxiliary grid is minus twice the number of
columns where the state lies above the corner state. -/
theorem alexanderTwoℤ_auxiliaryGrid (O : GridState n) (hn : 2 ≤ n) (x : GridState n) :
    (auxiliaryGrid O hn).alexanderTwoℤ x =
      -2 * ∑ c : Fin n, if cornerShift O c < x c then 1 else 0 := by
  have h := alexanderTwoℤ_auxiliaryGrid_sub O hn x
  rw [alexanderTwoℤ_auxiliaryGrid_cornerShift] at h
  linarith

/-! ### The corner inequality -/

/-- **The corner inequality.** If at most `a` rows of `G` wrap, then for every state `x`,
`2 A_G(x) ≥ 2 A_G(x₀) + a · 2 A_Q(x)`, where `x₀ = cornerShift G.O` and `Q = auxiliaryGrid G.O`. -/
theorem alexanderTwoℤ_corner_inequality (G : GridDiagram n) (hn : 2 ≤ n) (a : ℕ)
    (ha : wrapNumber G ≤ a) (x : GridState n) :
    G.alexanderTwoℤ (cornerShift G.O) + (a : ℤ) * (auxiliaryGrid G.O hn).alexanderTwoℤ x ≤
      G.alexanderTwoℤ x := by
  have hG := alexanderTwoℤ_sub_alexanderTwoℤ G x (cornerShift G.O)
  rw [alexanderTwoℤ_auxiliaryGrid]
  have hcol : ∀ c : Fin n,
      -(a : ℤ) * (if cornerShift G.O c < x c then 1 else 0) ≤
        activeBelow G c (cornerShift G.O c) - activeBelow G c (x c) := by
    intro c
    by_cases hc : cornerShift G.O c < x c
    · rw [if_pos hc]
      have h1 := activeBelow_nonneg G c (cornerShift G.O c)
      have h2 := activeBelow_le_wrapNumber G c (x c)
      have h3 : (wrapNumber G : ℤ) ≤ a := by exact_mod_cast ha
      linarith
    · rw [if_neg hc]
      have h1 := activeBelow_mono G c (not_lt.mp hc)
      linarith
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hcol c
  rw [← Finset.mul_sum] at hsum
  linarith

/-- **The corner lower bound.** If at most `a` rows of `G` wrap, with `a ≥ 1`, then for
`0 ≤ t ≤ 2/a` the canonical class of `G` has weighted spectral threshold at least `t/2` times the
Alexander grading of the corner state `cornerShift G.O`. -/
theorem alexander_spectralThreshold_corner (G : GridDiagram n) (hn : 2 ≤ n) (a : ℕ)
    (ha1 : 1 ≤ a) (ha : wrapNumber G ≤ a) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 / (a : ℝ)) :
    ((t / 2 * (G.alexander (cornerShift G.O) : ℝ) : ℝ) : EReal) ≤
      ((laurentMaslovBifiltration G (ZMod 2)).weighted t).spectralThreshold 0
        (gridCanonicalClass G hn) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hat : (a : ℝ) * t ≤ 2 := by
    rw [le_div_iff₀ ha0] at ht
    linarith
  have ht2 : t ≤ 2 := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    nlinarith
  have hA : ∀ x : GridState n, (G.alexander (cornerShift G.O) : ℝ) +
      (a : ℝ) * ((auxiliaryGrid G.O hn).alexander x : ℝ) ≤ (G.alexander x : ℝ) := by
    intro x
    have h := alexanderTwoℤ_corner_inequality G hn a ha x
    have e1 := G.two_mul_alexander_eq_intCast x
    have e2 := G.two_mul_alexander_eq_intCast (cornerShift G.O)
    have e3 := (auxiliaryGrid G.O hn).two_mul_alexander_eq_intCast x
    have e3' : (a : ℚ) * (2 * (auxiliaryGrid G.O hn).alexander x) =
        (a : ℚ) * ((auxiliaryGrid G.O hn).alexanderTwoℤ x : ℚ) := by rw [e3]
    have h' : ((G.alexanderTwoℤ (cornerShift G.O) : ℚ) +
        (a : ℚ) * ((auxiliaryGrid G.O hn).alexanderTwoℤ x : ℚ)) ≤ (G.alexanderTwoℤ x : ℚ) := by
      exact_mod_cast h
    have hq : (G.alexander (cornerShift G.O) : ℚ) +
        (a : ℚ) * (auxiliaryGrid G.O hn).alexander x ≤ G.alexander x := by
      linarith
    exact_mod_cast hq
  have hcmp := spectralThreshold_add_le_of_alexander_le G (auxiliaryGrid G.O hn) hn rfl
    (a : ℝ) (G.alexander (cornerShift G.O) : ℝ) t ht0 ht2 hA
  rw [auxiliaryGrid_spectralThreshold G.O hn ((a : ℝ) * t) (by positivity) hat, add_zero] at hcmp
  convert hcmp using 2
  ring

end OnLeConjecture.KnotFloer.GridFull
