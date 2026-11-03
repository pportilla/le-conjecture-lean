/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFiniteTensorComparison
public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstClass

/-!
# Numerical comparison from the explicit reflected torus class

The first of the two source representatives is constructed in
`GridReflectedTorusFirstClass`. Only the second representative remains an
input here. The target is the native finite tensor complex. The map, its
filtration bound, its action on the selected classes, the factor lower
bounds, and the genus identity remain inputs. This result makes no geometric
identification of either grid complex.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Staircase

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {sizes : ι → ℕ}

/-- The first source representative is discharged by its explicit rectangle calculation. -/
theorem estimates_of_reflected_torus_and_finite_tensor_map
    (n M m : ℕ) (hn : 2 ≤ n) (hm : 0 < m)
    (G : ∀ j, GridDiagram (sizes j))
    (φ : laurentMaslovComplex (reflectedTorusGrid n) K ⟶
      laurentFiniteMaslovComplex (K := K) G)
    (gCob : ℝ)
    (hφ : (laurentMaslovBifiltration (reflectedTorusGrid n) K).Shifts
      (laurentFiniteMaslovBifiltration G) φ 0 gCob)
    (hcycle₂ : ((laurentMaslovBifiltration (reflectedTorusGrid n) K).weighted
      (2 / (m : ℝ))).RepresentedBelow 0 (reflectedTorusAnchorClass n K)
        (consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩))
    (c : ∀ j, (laurentMaslovComplex (G j) K).cycles 0)
    (g : ι → ℝ)
    (hthreshold : ∀ j, ((g j * (2 / (m : ℝ)) / 2 : ℝ) : EReal) ≤
      ((laurentMaslovBifiltration (G j) K).weighted (2 / (m : ℝ))).spectralThreshold 0
        ((laurentMaslovComplex (G j) K).homologyπ 0 (c j)))
    (hclass : homologyMap φ 0 (reflectedTorusAnchorClass n K) = laurentFiniteNativeClass G c)
    (hgenus : (n : ℝ) * ((n : ℝ) + 1) / 2 - (∑ j, g j) + gCob =
      ((n : ℝ) + 1) - (M : ℝ)) :
    M ≤ m ∧ n + 1 + M ≤ 3 * m := by
  exact estimates_of_two_cycles_and_finite_tensor_map G φ gCob hφ
    (reflectedTorusAnchorClass n K) n M m hn hm
    (reflectedTorusAnchorClass_representedBelow_first_vertex n K (by omega) _)
    hcycle₂ (fun j => (laurentMaslovComplex (G j) K).homologyπ 0 (c j))
    c (fun _ => rfl) g hthreshold hclass hgenus

end OnLeConjecture.KnotFloer.GridFull
