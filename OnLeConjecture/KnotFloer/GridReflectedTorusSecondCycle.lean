/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondAssembly
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondReduction
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondDouble
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondTriangle
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondFive
public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondSix

/-!
# The strict-range second torus representative

This file collects the statements about the second representative
`secondTorusCycle n (ZMod 2) = firstTorusCycle n (ZMod 2) + D(secondTorusCorrection n (ZMod 2))`.

Proved without further hypotheses:

* `secondTorusCorrection_mem_maslovPiece`: the correction has Maslov degree one.
* `secondTorusNativeCycle_homology`: the representative is a degree-zero cycle whose
  homology class is exactly `reflectedTorusAnchorClass n (ZMod 2)`.

The support bound `SecondTorusSupportBound n` is reduced by
`secondTorusSupportBound_of_obligations` to four obligations indexed by the number
of moved columns of the target. These are the coefficient identities of the written
proof for three-cycle targets (exponent `-1`), targets with two transpositions,
five-cycle targets (exponents `-2` and `-3`), and targets moving six columns
(exponent `-3`). All four are proved: `triangleObligation` (for `1 ≤ n`),
`doubleObligation`, `pentagonObligation` and `hexagonObligation`.

The statements with the suffix `_of_remaining` take the obligations for three, five
and six columns as hypotheses. The final statements below discharge them:

* `secondTorusSupportBound_holds`: the support bound for `1 ≤ n`;
* `secondTorusCycle_mem_second_vertex`: the parameter-free strengthening;
* `reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt`: the strict-range
  acceptance statement;
* `secondTorusCycle_displacement`: the integer displacement inequality of M903.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable (n : ℕ)

/-- The support bound, from the three remaining obligations. -/
theorem secondTorusSupportBound_of_remaining (h3 : TriangleObligation n)
    (h5 : PentagonObligation n) (h6 : HexagonObligation n) : SecondTorusSupportBound n :=
  secondTorusSupportBound_of_obligations n h3 (doubleObligation n) h5 h6

/-- The parameter-free strengthening at the second staircase vertex, conditional on
the three remaining coefficient obligations. -/
theorem secondTorusCycle_mem_second_vertex_of_remaining (h3 : TriangleObligation n)
    (h5 : PentagonObligation n) (h6 : HexagonObligation n) :
    secondTorusCycle n (ZMod 2) ∈ laurentBifiltrationLevel (reflectedTorusGrid n) (ZMod 2) 3
      (((n : ℝ) - 2) * ((n : ℝ) - 1) / 2) :=
  secondTorusCycle_mem_second_staircase_vertex (secondTorusSupportBound_of_remaining n h3 h5 h6)

/-- The strict-range acceptance statement, conditional on the three remaining
coefficient obligations. -/
theorem reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt_of_remaining
    (m : ℕ) (hn : 2 ≤ n) (_hm : 0 < m) (_hS : 2 * m < n + 1) (h3 : TriangleObligation n)
    (h5 : PentagonObligation n) (h6 : HexagonObligation n) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) (ZMod 2)).weighted
      (2 / (m : ℝ))).RepresentedBelow 0 (reflectedTorusAnchorClass n (ZMod 2))
      (Staircase.consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩) :=
  reflectedTorusAnchorClass_representedBelow_second_vertex
    (secondTorusSupportBound_of_remaining n h3 h5 h6) hn _

/-- The integer displacement inequality of M903, conditional on the three remaining
coefficient obligations. -/
theorem secondTorusCycle_displacement_of_remaining (h3 : TriangleObligation n)
    (h5 : PentagonObligation n) (h6 : HexagonObligation n) (m : ℕ)
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ ((secondTorusCycle n (ZMod 2)) x).coeff.support) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1) - (m : ℤ) * (3 + k)) ≤
      ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val) :=
  secondTorusCycle_displacement_bound (secondTorusSupportBound_of_remaining n h3 h5 h6) m hk

/-! ### The unconditional statements -/

/-- The support bound for the second representative. -/
theorem secondTorusSupportBound_holds (hn : 1 ≤ n) : SecondTorusSupportBound n :=
  secondTorusSupportBound_of_remaining n (triangleObligation n hn) (pentagonObligation n)
    (hexagonObligation n)

/-- The parameter-free strengthening: the second representative lies in the native
bifiltration level of the second staircase vertex. -/
theorem secondTorusCycle_mem_second_vertex (hn : 1 ≤ n) :
    secondTorusCycle n (ZMod 2) ∈ laurentBifiltrationLevel (reflectedTorusGrid n) (ZMod 2) 3
      (((n : ℝ) - 2) * ((n : ℝ) - 1) / 2) :=
  secondTorusCycle_mem_second_vertex_of_remaining n (triangleObligation n hn)
    (pentagonObligation n) (hexagonObligation n)

/-- The integer displacement inequality of M903 for every monomial of the second
representative. -/
theorem secondTorusCycle_displacement (hn : 1 ≤ n) (m : ℕ)
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ ((secondTorusCycle n (ZMod 2)) x).coeff.support) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1) - (m : ℤ) * (3 + k)) ≤
      ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val) :=
  secondTorusCycle_displacement_of_remaining n (triangleObligation n hn) (pentagonObligation n)
    (hexagonObligation n) m hk

end OnLeConjecture.KnotFloer.GridFull

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The strict-range acceptance statement of J21: the corner class is represented at
the second vertex of the weighted staircase. -/
theorem reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt
    (n m : ℕ) (hn : 2 ≤ n) (hm : 0 < m) (hS : 2 * m < n + 1) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) (ZMod 2)).weighted
      (2 / (m : ℝ))).RepresentedBelow 0 (reflectedTorusAnchorClass n (ZMod 2))
      (Staircase.consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩) :=
  reflectedTorusAnchorClass_representedBelow_second_vertex_of_lt_of_remaining n m hn hm hS
    (triangleObligation n (by omega)) (pentagonObligation n) (hexagonObligation n)

end OnLeConjecture.KnotFloer.GridFull
