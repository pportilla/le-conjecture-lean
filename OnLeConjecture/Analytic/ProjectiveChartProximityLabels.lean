/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-!
# Exceptional-divisor labels in rooted projective charts

The new exceptional divisor at a nonroot vertex has the label of its
immediate predecessor. The other coordinate axis, when present, retains
an older exceptional label. The latter label is recursively determined
by the projective chart: the complementary point exchanges the axes,
the finite zero point retains the old axis, and another finite point
misses it.

These rules construct proximity parents, their generation inequalities,
and nestedness. No multiplicities, proximity inequalities, or branch-count
identities are assumed or concluded.
-/

public section

namespace OnLeConjecture.Analytic

structure RootedProjectiveChartData (α : Type*) where
  root : α
  predecessor : α → α
  predecessor_root : predecessor root = root
  generation : α → ℕ
  generation_decreases : ∀ q, q ≠ root → generation (predecessor q) < generation q
  chartPoint : α → Option ℂ

namespace RootedProjectiveChartData

variable {α : Type*}

/-- The older exceptional divisor on the first coordinate axis. -/
@[expose] noncomputable def xAncestor (D : RootedProjectiveChartData α) (q : α) :
    Option α := by
  classical
  exact if hq : q = D.root then none else
    match D.chartPoint q with
    | none => if D.predecessor q = D.root then none else some (D.predecessor (D.predecessor q))
    | some ζ => if ζ = 0 then D.xAncestor (D.predecessor q) else none
termination_by D.generation q
decreasing_by exact D.generation_decreases q hq

@[simp] theorem xAncestor_root (D : RootedProjectiveChartData α) :
    D.xAncestor D.root = none := by
  rw [xAncestor]
  simp

theorem xAncestor_complementary [DecidableEq α] (D : RootedProjectiveChartData α) (q : α)
    (hq : q ≠ D.root) (hchart : D.chartPoint q = none) :
    D.xAncestor q = if D.predecessor q = D.root then none
      else some (D.predecessor (D.predecessor q)) := by
  classical
  rw [xAncestor, dif_neg hq, hchart]
  split_ifs <;> rfl

theorem xAncestor_zero (D : RootedProjectiveChartData α) (q : α)
    (hq : q ≠ D.root) (hchart : D.chartPoint q = some 0) :
    D.xAncestor q = D.xAncestor (D.predecessor q) := by
  rw [xAncestor, dif_neg hq, hchart]
  simp

theorem xAncestor_nonzero (D : RootedProjectiveChartData α) (q : α)
    (hq : q ≠ D.root) (ζ : ℂ) (hζ : ζ ≠ 0) (hchart : D.chartPoint q = some ζ) :
    D.xAncestor q = none := by
  rw [xAncestor, dif_neg hq, hchart]
  simp only [if_neg hζ]

/-- An older axis label at a child is one of the two exceptional labels
already present at its predecessor. -/
theorem xAncestor_predecessor_cases (D : RootedProjectiveChartData α)
    {q r : α} (h : D.xAncestor q = some r) :
    q ≠ D.root ∧ D.predecessor q ≠ D.root ∧
      (r = D.predecessor (D.predecessor q) ∨
        D.xAncestor (D.predecessor q) = some r) := by
  classical
  have hq : q ≠ D.root := by
    intro hq
    simp only [hq, xAncestor_root] at h
    cases h
  refine ⟨hq, ?_⟩
  cases hc : D.chartPoint q with
  | none =>
      rw [D.xAncestor_complementary q hq hc] at h
      by_cases hp : D.predecessor q = D.root
      · rw [if_pos hp] at h
        cases h
      · rw [if_neg hp] at h
        exact ⟨hp, Or.inl (Option.some.inj h).symm⟩
  | some ζ =>
      by_cases hζ : ζ = 0
      · subst ζ
        rw [D.xAncestor_zero q hq hc] at h
        have hp : D.predecessor q ≠ D.root := by
          intro hp
          simp only [hp, xAncestor_root] at h
          cases h
        exact ⟨hp, Or.inr h⟩
      · rw [D.xAncestor_nonzero q hq ζ hζ hc] at h
        cases h

theorem xAncestor_generation_lt_predecessor (D : RootedProjectiveChartData α)
    {q r : α} (h : D.xAncestor q = some r) :
    D.generation r < D.generation (D.predecessor q) := by
  induction q using (measure D.generation).wf.induction generalizing r with
  | h q ih =>
      obtain ⟨hq, hp, hcases⟩ := D.xAncestor_predecessor_cases h
      rcases hcases with hr | hr
      · rw [hr]
        exact D.generation_decreases _ hp
      · exact (ih (D.predecessor q) (D.generation_decreases q hq) hr).trans
          (D.generation_decreases _ hp)

theorem xAncestor_ne_predecessor (D : RootedProjectiveChartData α)
    {q r : α} (h : D.xAncestor q = some r) : r ≠ D.predecessor q := by
  intro heq
  have hlt := D.xAncestor_generation_lt_predecessor h
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

/-- The two coordinate-axis labels: the newest exceptional label and,
when present, the older label on the other coordinate axis. -/
@[expose] noncomputable def parents (D : RootedProjectiveChartData α) (q : α) : Finset α := by
  classical
  exact if q = D.root then ∅ else
    match D.xAncestor q with
    | none => {D.predecessor q}
    | some r => {D.predecessor q, r}

@[simp] theorem parents_root (D : RootedProjectiveChartData α) : D.parents D.root = ∅ := by
  simp [parents]

theorem mem_parents_iff (D : RootedProjectiveChartData α) (q p : α) :
    p ∈ D.parents q ↔ q ≠ D.root ∧
      (p = D.predecessor q ∨ D.xAncestor q = some p) := by
  classical
  by_cases hq : q = D.root
  · simp [hq]
  · cases hxa : D.xAncestor q with
    | none => simp [parents, hq, hxa]
    | some r => simp [parents, hq, hxa, eq_comm]

theorem predecessor_mem (D : RootedProjectiveChartData α) (q : α) (hq : q ≠ D.root) :
    D.predecessor q ∈ D.parents q :=
  (D.mem_parents_iff _ _).mpr ⟨hq, Or.inl rfl⟩

theorem xAncestor_eq_none_of_predecessor_eq_root (D : RootedProjectiveChartData α)
    (q : α) (hp : D.predecessor q = D.root) : D.xAncestor q = none := by
  classical
  by_cases hq : q = D.root
  · simpa only [hq] using D.xAncestor_root
  · cases hc : D.chartPoint q with
    | none => simpa [hp] using D.xAncestor_complementary q hq hc
    | some ζ =>
        by_cases hζ : ζ = 0
        · subst ζ
          rw [D.xAncestor_zero q hq hc, hp, D.xAncestor_root]
        · exact D.xAncestor_nonzero q hq ζ hζ hc

theorem parents_of_predecessor_eq_root (D : RootedProjectiveChartData α)
    (q : α) (hq : q ≠ D.root) (hp : D.predecessor q = D.root) :
    D.parents q = {D.root} := by
  classical
  simp only [parents, if_neg hq, D.xAncestor_eq_none_of_predecessor_eq_root q hp, hp]

theorem xAncestor_mem_predecessor_parents (D : RootedProjectiveChartData α)
    {q r : α} (h : D.xAncestor q = some r) : r ∈ D.parents (D.predecessor q) := by
  obtain ⟨_hq, hp, hcases⟩ := D.xAncestor_predecessor_cases h
  exact (D.mem_parents_iff _ _).mpr ⟨hp, hcases⟩

theorem nonroot_parent_card (D : RootedProjectiveChartData α) (q : α)
    (hq : q ≠ D.root) : (D.parents q).card = 1 ∨ (D.parents q).card = 2 := by
  classical
  cases hxa : D.xAncestor q with
  | none => simp [parents, hq, hxa]
  | some r =>
      have hr := D.xAncestor_ne_predecessor hxa
      simp [parents, hq, hxa, hr.symm]

theorem generation_lt_of_mem_parents (D : RootedProjectiveChartData α)
    {q p : α} (h : p ∈ D.parents q) : D.generation p < D.generation q := by
  obtain ⟨hq, hcases⟩ := (D.mem_parents_iff _ _).mp h
  rcases hcases with rfl | hxa
  · exact D.generation_decreases q hq
  · exact (D.xAncestor_generation_lt_predecessor hxa).trans (D.generation_decreases q hq)

/-- If two exceptional components meet at a vertex, the older label is
also a proximity parent of the newest label. -/
theorem nested_parents (D : RootedProjectiveChartData α) (q : α)
    (hcard : (D.parents q).card = 2) :
    ∃ p r, p ∈ D.parents q ∧ r ∈ D.parents q ∧ r ∈ D.parents p := by
  classical
  have hq : q ≠ D.root := by
    intro hq
    simp only [hq, parents_root, Finset.card_empty] at hcard
    omega
  cases hxa : D.xAncestor q with
  | none =>
      simp only [parents, if_neg hq, hxa, Finset.card_singleton] at hcard
      omega
  | some r =>
      exact ⟨D.predecessor q, r, D.predecessor_mem q hq,
        (D.mem_parents_iff _ _).mpr ⟨hq, Or.inr hxa⟩,
        D.xAncestor_mem_predecessor_parents hxa⟩

end RootedProjectiveChartData

end OnLeConjecture.Analytic
