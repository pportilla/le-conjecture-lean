/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondFormula
public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstClass
public import OnLeConjecture.KnotFloer.ConsecutiveStaircase

/-!
# From the support bound to the second-vertex statements

`SecondTorusSupportBound n` is the statement that every target with a nonzero
coefficient formula has Laurent exponent `-2` or `-3` and scaled Alexander drop
at least `2(n+1)`. Its proof is the support calculation of the second
representative. This file derives from it, for every `n`,

* the native bifiltration bound at the second staircase vertex
  `(3, (n-2)(n-1)/2)`,
* the identification of the homology class with `reflectedTorusAnchorClass`,
* the weighted representation at the second vertex for every parameter `t`, and
* the integer displacement inequality of M903.

The homology class does not depend on the support bound.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable (n : ℕ)

/-- The scaled Alexander drop of a relative state, as a sum of displacement weights. -/
def torusWeightSum (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) : ℤ :=
  ∑ c : Fin (consecutiveTorusGridSize n),
    reflectedTorusDisplacementWeight n (reflectedTorusCyclicDisplacement n c.val (τ c).val)

/-- The support bound for the second representative: a target with a nonzero
coefficient formula has exponent `-2` or `-3` and scaled Alexander drop at least
`2(n+1)` times the grid size. -/
def SecondTorusSupportBound : Prop :=
  ∀ (τ : Equiv.Perm (Fin (consecutiveTorusGridSize n))) (j : ℤ), torusEll n τ = -2 * j →
    (if τ = 1 ∧ j = 0 then (1 : ZMod 2) else 0) + ((coefFormula n τ j : ℕ) : ZMod 2) ≠ 0 →
      (j = -2 ∨ j = -3) ∧
        (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤ torusWeightSum n τ

variable {n}

/-- Every monomial of the second representative satisfies the support bound. -/
theorem secondTorusCycle_support_bound (hB : SecondTorusSupportBound n)
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ ((secondTorusCycle n (ZMod 2)) x).coeff.support) :
    (k = -2 ∨ k = -3) ∧
      (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤
        ∑ c : Fin (consecutiveTorusGridSize n),
          reflectedTorusDisplacementWeight n
            (reflectedTorusCyclicDisplacement n c.val
              (reflectedTorusRelativeColumns n x c).val) := by
  set τ := reflectedTorusRelativeColumns n x with hτ
  have hx : x = relState n τ := (relState_relativeColumns n x).symm
  rw [hx] at hk
  have hne := Finsupp.mem_support_iff.mp hk
  have hell := torusEll_eq_of_secondTorusCycle_coeff_ne_zero n hne
  rw [secondTorusCycle_coeff n hell] at hne
  exact hB τ k hell hne

/-- The parameter-free strengthening: the second representative lies in the native
bifiltration level of the second staircase vertex. -/
theorem secondTorusCycle_mem_second_staircase_vertex (hB : SecondTorusSupportBound n) :
    secondTorusCycle n (ZMod 2) ∈ laurentBifiltrationLevel (reflectedTorusGrid n) (ZMod 2) 3
      (((n : ℝ) - 2) * ((n : ℝ) - 1) / 2) := by
  intro x k hk
  obtain ⟨hk23, hW⟩ := secondTorusCycle_support_bound hB hk
  have hA := alexander_reflectedTorus_le_of_displacement_weight n x (2 * ((n : ℤ) + 1)) hW
  have hAR : ((reflectedTorusGrid n).alexander x : ℝ) ≤
      (n : ℝ) * ((n : ℝ) + 1) / 2 - 2 * ((n : ℝ) + 1) := by
    have := (Rat.cast_le (K := ℝ)).mpr hA
    push_cast at this
    linarith
  rcases hk23 with rfl | rfl <;> constructor <;> push_cast <;> nlinarith

/-- The second representative as a native cycle in degree zero. -/
noncomputable def secondTorusNativeCycle :
    (laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)).cycles 0 :=
  nativeCornerCycleOfChain n (ZMod 2) (secondTorusCycle n (ZMod 2))
    (secondTorusCycle_mem_maslovZero n (ZMod 2)) (laurentDifferential_secondTorusCycle n (ZMod 2))

theorem secondTorusNativeCycle_apply :
    (laurentMaslovChainEquiv (reflectedTorusGrid n) (ZMod 2) 0
      ((laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)).iCycles 0
        (secondTorusNativeCycle (n := n))) : LaurentChain (ZMod 2) _) =
      secondTorusCycle n (ZMod 2) :=
  nativeCornerCycleOfChain_apply n (ZMod 2) _ _ _

/-- The second representative represents exactly the corner class. -/
theorem secondTorusNativeCycle_homology :
    (laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)).homologyπ 0
      (secondTorusNativeCycle (n := n)) = reflectedTorusAnchorClass n (ZMod 2) := by
  let C := laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)
  let w : C.X 1 := (laurentMaslovChainEquiv (reflectedTorusGrid n) (ZMod 2) 1).symm
    ⟨secondTorusCorrection n (ZMod 2), secondTorusCorrection_mem_maslovPiece n (ZMod 2)⟩
  have hc : secondTorusNativeCycle (n := n) =
      firstTorusNativeCycle n (ZMod 2) + C.toCycles 1 0 w := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    apply (laurentMaslovChainEquiv (reflectedTorusGrid n) (ZMod 2) 0).injective
    apply Subtype.ext
    rw [map_add, map_add, Submodule.coe_add, secondTorusNativeCycle_apply,
      firstTorusNativeCycle_apply]
    have hi := congrArg (fun f : C.X 1 ⟶ C.X 0 => f w) (C.toCycles_i 1 0)
    simp only [ModuleCat.comp_apply] at hi
    have hdd := laurentMaslovChainEquiv_d (reflectedTorusGrid n) (ZMod 2) 0
    rw [show (0 : ℤ) + 1 = 1 by decide] at hdd
    rw [hi, hdd]
    simp only [w, LinearEquiv.apply_symm_apply]
    rfl
  rw [hc, map_add, firstTorusNativeCycle_homology]
  have hh := congrArg (fun f : C.X 1 ⟶ C.homology 0 => f w)
    (C.toCycles_comp_homologyπ 1 0)
  simp only [ModuleCat.comp_apply] at hh
  change C.homologyπ 0 (C.toCycles 1 0 w) = 0 at hh
  rw [hh, add_zero]

/-- The corner class is represented at the second staircase vertex for every
weighted parameter. -/
theorem reflectedTorusAnchorClass_representedBelow_second_vertex
    (hB : SecondTorusSupportBound n) (hn : 2 ≤ n) (t : ℝ) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) (ZMod 2)).weighted t).RepresentedBelow 0
      (reflectedTorusAnchorClass n (ZMod 2))
      (Staircase.consecutiveWeight n t ⟨2, by omega⟩) := by
  refine ⟨secondTorusNativeCycle, Submodule.subset_span ?_, secondTorusNativeCycle_homology⟩
  refine ⟨3, ((n : ℝ) - 2) * ((n : ℝ) - 1) / 2, ?_, ?_⟩
  · change (laurentMaslovChainEquiv (reflectedTorusGrid n) (ZMod 2) 0
      ((laurentMaslovComplex (reflectedTorusGrid n) (ZMod 2)).iCycles 0
        secondTorusNativeCycle) : LaurentChain (ZMod 2) (consecutiveTorusGridSize n)) ∈
        laurentBifiltrationLevel (reflectedTorusGrid n) (ZMod 2) 3
          (((n : ℝ) - 2) * ((n : ℝ) - 1) / 2)
    rw [secondTorusNativeCycle_apply]
    exact secondTorusCycle_mem_second_staircase_vertex hB
  · simp only [Staircase.consecutiveWeight, Staircase.consecutiveFirst,
      Staircase.consecutiveSecond]
    norm_num
    ring_nf
    exact le_rfl

/-- The integer displacement inequality of M903 for every monomial of the second
representative. -/
theorem secondTorusCycle_displacement_bound (hB : SecondTorusSupportBound n) (m : ℕ)
    {x : GridState (consecutiveTorusGridSize n)} {k : ℤ}
    (hk : k ∈ ((secondTorusCycle n (ZMod 2)) x).coeff.support) :
    (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1) - (m : ℤ) * (3 + k)) ≤
      ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val) := by
  obtain ⟨hk23, hW⟩ := secondTorusCycle_support_bound hB hk
  have hN : (0 : ℤ) ≤ consecutiveTorusGridSize n := Int.natCast_nonneg _
  have hm : (0 : ℤ) ≤ m := Int.natCast_nonneg _
  rcases hk23 with rfl | rfl <;> nlinarith

end OnLeConjecture.KnotFloer.GridFull
