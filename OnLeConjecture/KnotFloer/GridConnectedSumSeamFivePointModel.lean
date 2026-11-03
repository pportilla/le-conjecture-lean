/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# A computable model of the five-point seam grid

For `n = m = 2` the seam grid has size five. A state is modelled by its
column-to-row function `Fin 5 → Fin 5`. The model records the cyclic
open-interval test, the emptiness test for a rectangle with ordered column
sides, the column exchange, the pair sector, the first two southwest
columns, the selected partner, and the entry, internal, and exit tests.
Every test is decidable by kernel evaluation.

The lists `seamFiveE0`, `seamFiveE1`, `seamFiveE2`, `seamFiveE3` are the
reachability sets `E_0`, ..., `E_3` of Lemma `J05:lem:seam-size-five-truncation`,
written as row lists in column order. The certificates below prove that
every model entry source lies in `E_0`, that every model internal step
maps `E_j` into `E_{j+1}` for `j ≤ 2`, and that no member of `E_3` has an
exit or an internal step. The transfer to native seam objects is in
`GridConnectedSumSeamFivePoint`.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull

/-- Membership of `c` in the clockwise open cyclic interval from `a` to `b`,
written with the inequalities of `TauCeti.Grid.mem_cIoo`. -/
def seamFiveIoo (a b c : Fin 5) : Prop :=
  a ≠ b ∧ (a.val < b.val → a.val < c.val ∧ c.val < b.val) ∧
    (¬ a.val < b.val → a.val < c.val ∨ c.val < b.val)

instance (a b c : Fin 5) : Decidable (seamFiveIoo a b c) :=
  inferInstanceAs (Decidable (a ≠ b ∧ (a.val < b.val → a.val < c.val ∧ c.val < b.val) ∧
    (¬ a.val < b.val → a.val < c.val ∨ c.val < b.val)))

/-- The rectangle with ordered column sides `a`, `b` and row sides `f a`, `f b`
has no point of `f` in its interior. -/
def seamFiveEmpty (f : Fin 5 → Fin 5) (a b : Fin 5) : Prop :=
  ∀ c : Fin 5, seamFiveIoo a b c → ¬ seamFiveIoo (f a) (f b) (f c)

instance (f : Fin 5 → Fin 5) (a b : Fin 5) : Decidable (seamFiveEmpty f a b) :=
  inferInstanceAs (Decidable (∀ c : Fin 5, seamFiveIoo a b c → ¬ seamFiveIoo (f a) (f b) (f c)))

/-- Exchange the rows of `f` in the columns `a` and `b`. -/
def seamFiveSwap (f : Fin 5 → Fin 5) (a b : Fin 5) : Fin 5 → Fin 5 :=
  fun c => if c = a then f b else if c = b then f a else f c

/-- Exchanging the same two columns twice restores the function. -/
theorem seamFiveSwap_swap (f : Fin 5 → Fin 5) (a b : Fin 5) :
    seamFiveSwap (seamFiveSwap f a b) a b = f := by
  funext c
  by_cases hca : c = a
  · subst hca
    by_cases hba : b = c
    · subst hba
      simp [seamFiveSwap]
    · simp [seamFiveSwap, hba]
  · by_cases hcb : c = b
    · subst hcb
      simp [seamFiveSwap, hca]
    · simp [seamFiveSwap, hca, hcb]

/-- The first two columns have rows at most two. -/
def seamFiveSector (f : Fin 5 → Fin 5) : Prop :=
  (f 0).val ≤ 2 ∧ (f 1).val ≤ 2

instance (f : Fin 5 → Fin 5) : Decidable (seamFiveSector f) :=
  inferInstanceAs (Decidable ((f 0).val ≤ 2 ∧ (f 1).val ≤ 2))

/-- The first column `c ≥ 2` with row at most two, if there are two such columns. -/
def seamFiveFirst (f : Fin 5 → Fin 5) : Fin 5 :=
  if (f 2).val ≤ 2 then 2 else if (f 3).val ≤ 2 then 3 else 4

/-- The second column `c ≥ 2` with row at most two, if there are two such columns. -/
def seamFiveSecond (f : Fin 5 → Fin 5) : Fin 5 :=
  if (f 2).val ≤ 2 then (if (f 3).val ≤ 2 then 3 else 4) else 4

/-- Exchange the rows in the first two southwest columns. -/
def seamFivePartner (f : Fin 5 → Fin 5) : Fin 5 → Fin 5 :=
  seamFiveSwap f (seamFiveFirst f) (seamFiveSecond f)

/-- A complementary state whose first two southwest rows increase. -/
def seamFiveSource (f : Fin 5 → Fin 5) : Prop :=
  ¬ seamFiveSector f ∧ (f (seamFiveFirst f)).val < (f (seamFiveSecond f)).val

instance (f : Fin 5 → Fin 5) : Decidable (seamFiveSource f) :=
  inferInstanceAs (Decidable (¬ seamFiveSector f ∧
    (f (seamFiveFirst f)).val < (f (seamFiveSecond f)).val))

/-- The source reached by the rectangle with sides `a`, `b` followed by the partner exchange. -/
def seamFiveNext (f : Fin 5 → Fin 5) (a b : Fin 5) : Fin 5 → Fin 5 :=
  seamFivePartner (seamFiveSwap f a b)

/-- The row list of `f` in column order. -/
def seamFiveCode (f : Fin 5 → Fin 5) : List (Fin 5) :=
  [f 0, f 1, f 2, f 3, f 4]

/-- The function whose row list is `l`. -/
def seamFiveOfCode (l : List (Fin 5)) : Fin 5 → Fin 5 :=
  fun i => l.getD i.val 0

theorem seamFiveOfCode_code (f : Fin 5 → Fin 5) : seamFiveOfCode (seamFiveCode f) = f := by
  funext i
  fin_cases i <;> rfl

/-- An internal transition with ordered column sides `a`, `b`. -/
def seamFiveStepAt (f : Fin 5 → Fin 5) (a b : Fin 5) : Prop :=
  a ≠ b ∧ seamFiveEmpty f a b ∧ ¬ seamFiveSector (seamFiveSwap f a b) ∧
    seamFiveSource (seamFiveNext f a b) ∧ seamFiveCode (seamFiveNext f a b) ≠ seamFiveCode f

instance (f : Fin 5 → Fin 5) (a b : Fin 5) : Decidable (seamFiveStepAt f a b) :=
  inferInstanceAs (Decidable (a ≠ b ∧ seamFiveEmpty f a b ∧
    ¬ seamFiveSector (seamFiveSwap f a b) ∧ seamFiveSource (seamFiveNext f a b) ∧
      seamFiveCode (seamFiveNext f a b) ≠ seamFiveCode f))

/-- Some empty rectangle runs from a pair-sector state to the partner of `f`. -/
def seamFiveHasEntry (f : Fin 5 → Fin 5) : Prop :=
  ∃ a b : Fin 5, a ≠ b ∧ seamFiveSector (seamFiveSwap (seamFivePartner f) a b) ∧
    seamFiveEmpty (seamFiveSwap (seamFivePartner f) a b) a b

instance (f : Fin 5 → Fin 5) : Decidable (seamFiveHasEntry f) :=
  inferInstanceAs (Decidable (∃ a b : Fin 5, a ≠ b ∧
    seamFiveSector (seamFiveSwap (seamFivePartner f) a b) ∧
      seamFiveEmpty (seamFiveSwap (seamFivePartner f) a b) a b))

/-- Some empty rectangle runs from `f` to a pair-sector state. -/
def seamFiveHasExit (f : Fin 5 → Fin 5) : Prop :=
  ∃ a b : Fin 5, a ≠ b ∧ seamFiveEmpty f a b ∧ seamFiveSector (seamFiveSwap f a b)

instance (f : Fin 5 → Fin 5) : Decidable (seamFiveHasExit f) :=
  inferInstanceAs (Decidable (∃ a b : Fin 5, a ≠ b ∧ seamFiveEmpty f a b ∧
    seamFiveSector (seamFiveSwap f a b)))

/-- The 34 sources with an entry, the set `E_0`. -/
def seamFiveE0 : List (List (Fin 5)) :=
  [[0, 3, 1, 2, 4], [0, 3, 1, 4, 2], [0, 3, 4, 1, 2], [0, 4, 1, 2, 3], [0, 4, 1, 3, 2],
    [1, 3, 0, 2, 4], [1, 3, 0, 4, 2], [1, 3, 4, 0, 2], [1, 4, 0, 2, 3], [1, 4, 0, 3, 2],
    [1, 4, 3, 0, 2], [2, 3, 0, 1, 4], [2, 3, 0, 4, 1], [2, 3, 4, 0, 1], [2, 4, 0, 1, 3],
    [2, 4, 0, 3, 1], [2, 4, 3, 0, 1], [3, 0, 1, 2, 4], [3, 0, 1, 4, 2], [3, 0, 4, 1, 2],
    [3, 1, 0, 2, 4], [3, 1, 0, 4, 2], [3, 1, 4, 0, 2], [3, 2, 0, 4, 1], [3, 2, 4, 0, 1],
    [4, 0, 1, 2, 3], [4, 0, 1, 3, 2], [4, 0, 3, 1, 2], [4, 1, 0, 2, 3], [4, 1, 0, 3, 2],
    [4, 1, 3, 0, 2], [4, 2, 0, 1, 3], [4, 2, 0, 3, 1], [4, 2, 3, 0, 1]]

/-- The sources reached by one internal transition from `E_0`. -/
def seamFiveE1 : List (List (Fin 5)) :=
  [[1, 3, 4, 0, 2], [1, 4, 0, 2, 3], [2, 3, 0, 4, 1], [2, 3, 4, 0, 1], [2, 4, 0, 3, 1],
    [3, 0, 1, 4, 2], [3, 1, 4, 0, 2], [3, 4, 0, 1, 2], [3, 4, 0, 2, 1], [4, 0, 1, 2, 3],
    [4, 0, 1, 3, 2], [4, 1, 0, 2, 3], [4, 3, 0, 1, 2], [4, 3, 0, 2, 1]]

/-- The sources reached by two internal transitions from `E_0`. -/
def seamFiveE2 : List (List (Fin 5)) :=
  [[0, 3, 4, 1, 2], [3, 0, 4, 1, 2], [3, 4, 0, 1, 2], [4, 0, 3, 1, 2]]

/-- The sources reached by three internal transitions from `E_0`. -/
def seamFiveE3 : List (List (Fin 5)) :=
  [[2, 3, 4, 0, 1], [4, 0, 1, 2, 3]]

/-- Every permutation that is a source with an entry lies in `E_0`. -/
theorem seamFive_entry_mem_E0 :
    ∀ a₀ a₁ : Fin 5, a₀ ≠ a₁ → ∀ a₂ : Fin 5, a₀ ≠ a₂ → a₁ ≠ a₂ →
      ∀ a₃ : Fin 5, a₀ ≠ a₃ → a₁ ≠ a₃ → a₂ ≠ a₃ →
        ∀ a₄ : Fin 5, a₀ ≠ a₄ → a₁ ≠ a₄ → a₂ ≠ a₄ → a₃ ≠ a₄ →
          seamFiveSource (seamFiveOfCode [a₀, a₁, a₂, a₃, a₄]) →
            seamFiveHasEntry (seamFiveOfCode [a₀, a₁, a₂, a₃, a₄]) →
              [a₀, a₁, a₂, a₃, a₄] ∈ seamFiveE0 := by
  decide +kernel

/-- Every internal transition from `E_0` reaches `E_1`. This is table (J05.F5.2). -/
theorem seamFive_step_E0 : ∀ l ∈ seamFiveE0, ∀ a b : Fin 5,
    seamFiveStepAt (seamFiveOfCode l) a b →
      seamFiveCode (seamFiveNext (seamFiveOfCode l) a b) ∈ seamFiveE1 := by
  decide +kernel

/-- Every internal transition from `E_1` reaches `E_2`. -/
theorem seamFive_step_E1 : ∀ l ∈ seamFiveE1, ∀ a b : Fin 5,
    seamFiveStepAt (seamFiveOfCode l) a b →
      seamFiveCode (seamFiveNext (seamFiveOfCode l) a b) ∈ seamFiveE2 := by
  decide +kernel

/-- Every internal transition from `E_2` reaches `E_3`. -/
theorem seamFive_step_E2 : ∀ l ∈ seamFiveE2, ∀ a b : Fin 5,
    seamFiveStepAt (seamFiveOfCode l) a b →
      seamFiveCode (seamFiveNext (seamFiveOfCode l) a b) ∈ seamFiveE3 := by
  decide +kernel

/-- No member of `E_3` has an exit or an internal transition. -/
theorem seamFive_E3_terminal : ∀ l ∈ seamFiveE3,
    ¬ seamFiveHasExit (seamFiveOfCode l) ∧
      ∀ a b : Fin 5, ¬ seamFiveStepAt (seamFiveOfCode l) a b := by
  decide +kernel

/-- Transport `seamFive_step_E0` to an arbitrary function with code in `E_0`. -/
theorem seamFive_next_mem_E1 {f : Fin 5 → Fin 5} (hf : seamFiveCode f ∈ seamFiveE0)
    {a b : Fin 5} (h : seamFiveStepAt f a b) : seamFiveCode (seamFiveNext f a b) ∈ seamFiveE1 := by
  have hs := seamFive_step_E0 _ hf a b
  rw [seamFiveOfCode_code] at hs
  exact hs h

/-- Transport `seamFive_step_E1` to an arbitrary function with code in `E_1`. -/
theorem seamFive_next_mem_E2 {f : Fin 5 → Fin 5} (hf : seamFiveCode f ∈ seamFiveE1)
    {a b : Fin 5} (h : seamFiveStepAt f a b) : seamFiveCode (seamFiveNext f a b) ∈ seamFiveE2 := by
  have hs := seamFive_step_E1 _ hf a b
  rw [seamFiveOfCode_code] at hs
  exact hs h

/-- Transport `seamFive_step_E2` to an arbitrary function with code in `E_2`. -/
theorem seamFive_next_mem_E3 {f : Fin 5 → Fin 5} (hf : seamFiveCode f ∈ seamFiveE2)
    {a b : Fin 5} (h : seamFiveStepAt f a b) : seamFiveCode (seamFiveNext f a b) ∈ seamFiveE3 := by
  have hs := seamFive_step_E2 _ hf a b
  rw [seamFiveOfCode_code] at hs
  exact hs h

/-- A function with code in `E_3` has no exit. -/
theorem seamFive_not_hasExit_of_mem_E3 {f : Fin 5 → Fin 5} (hf : seamFiveCode f ∈ seamFiveE3) :
    ¬ seamFiveHasExit f := by
  have hs := (seamFive_E3_terminal _ hf).1
  rwa [seamFiveOfCode_code] at hs

/-- A function with code in `E_3` has no internal transition. -/
theorem seamFive_not_stepAt_of_mem_E3 {f : Fin 5 → Fin 5} (hf : seamFiveCode f ∈ seamFiveE3)
    (a b : Fin 5) : ¬ seamFiveStepAt f a b := by
  have hs := (seamFive_E3_terminal _ hf).2 a b
  rwa [seamFiveOfCode_code] at hs

end OnLeConjecture.KnotFloer.GridFull
