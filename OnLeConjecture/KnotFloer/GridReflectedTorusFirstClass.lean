/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusFirstBound
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.KnotFloer.ConsecutiveStaircase

/-!
# The first torus representative in native homology

The computed rectangle cycle represents the corner class in degree-zero homology
of the full Laurent grid complex. Its two coordinate bounds give the first
staircase vertex bound for every weighted filtration. Nonvanishing of this class
and identification with a normalized knot class are separate obligations.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable (n : ℕ) (R : Type*) [CommRing R] [CharP R 2]

/-- Vanishing of the rectangle differential implies vanishing of the native differential. -/
theorem nativeCornerChain_d_zero
    (x : LaurentChain R (consecutiveTorusGridSize n))
    (hm : x ∈ laurentMaslovPiece (reflectedTorusGrid n) R 0)
    (hd : laurentDifferential (reflectedTorusGrid n) R x = 0) :
    (laurentMaslovComplex (reflectedTorusGrid n) R).d 0 (-1)
      ((laurentMaslovChainEquiv (reflectedTorusGrid n) R 0).symm ⟨x, hm⟩) = 0 := by
  apply (laurentMaslovChainEquiv (reflectedTorusGrid n) R (-1)).injective
  apply Subtype.ext
  simp only [map_zero, ZeroMemClass.coe_zero]
  have hdd := laurentMaslovChainEquiv_d (reflectedTorusGrid n) R (-1)
  rw [show (-1 : ℤ) + 1 = 0 by decide] at hdd
  rw [hdd]
  simpa only [LinearEquiv.apply_symm_apply] using hd

/-- A homogeneous rectangle cycle as a native degree-zero cycle. -/
noncomputable def nativeCornerCycleOfChain
    (x : LaurentChain R (consecutiveTorusGridSize n))
    (hm : x ∈ laurentMaslovPiece (reflectedTorusGrid n) R 0)
    (hd : laurentDifferential (reflectedTorusGrid n) R x = 0) :
    (laurentMaslovComplex (reflectedTorusGrid n) R).cycles 0 :=
  (laurentMaslovComplex (reflectedTorusGrid n) R).cyclesMk
    ((laurentMaslovChainEquiv (reflectedTorusGrid n) R 0).symm ⟨x, hm⟩)
    (-1) (by simp) (nativeCornerChain_d_zero n R x hm hd)

theorem nativeCornerCycleOfChain_apply
    (x : LaurentChain R (consecutiveTorusGridSize n))
    (hm : x ∈ laurentMaslovPiece (reflectedTorusGrid n) R 0)
    (hd : laurentDifferential (reflectedTorusGrid n) R x = 0) :
    (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0
      ((laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0
        (nativeCornerCycleOfChain n R x hm hd)) : LaurentChain R _) = x := by
  have hi := (laurentMaslovComplex (reflectedTorusGrid n) R).i_cyclesMk
    ((laurentMaslovChainEquiv (reflectedTorusGrid n) R 0).symm ⟨x, hm⟩)
    (-1) (by simp) (nativeCornerChain_d_zero n R x hm hd)
  change (laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0
    (nativeCornerCycleOfChain n R x hm hd) = _ at hi
  rw [hi, LinearEquiv.apply_symm_apply]

/-- The corner cycle as an element of the native cycle module. -/
noncomputable def reflectedTorusAnchorCycle :
    (laurentMaslovComplex (reflectedTorusGrid n) R).cycles 0 :=
  nativeCornerCycleOfChain n R (Finsupp.single (reflectedTorusAnchor n) 1)
    (reflectedTorusAnchor_mem_maslovPiece n R) (laurentDifferential_reflectedTorusAnchor n R)

/-- The explicitly specified corner homology class. This definition makes no nonvanishing claim. -/
noncomputable def reflectedTorusAnchorClass :
    (laurentMaslovComplex (reflectedTorusGrid n) R).homology 0 :=
  (laurentMaslovComplex (reflectedTorusGrid n) R).homologyπ 0 (reflectedTorusAnchorCycle n R)

/-- The computed first representative as a native cycle. -/
noncomputable def firstTorusNativeCycle :
    (laurentMaslovComplex (reflectedTorusGrid n) R).cycles 0 :=
  nativeCornerCycleOfChain n R (firstTorusCycle n R)
    (firstTorusCycle_mem_maslovZero n R) (laurentDifferential_firstTorusCycle n R)

theorem firstTorusNativeCycle_apply :
    (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0
      ((laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0
        (firstTorusNativeCycle n R)) : LaurentChain R _) = firstTorusCycle n R :=
  nativeCornerCycleOfChain_apply n R _ _ _

omit [CharP R 2] in
/-- The Laurent multiple of the triangle is an explicit degree-one boundary witness. -/
theorem firstTorusBoundary_mem_maslovOne :
    (LaurentPolynomial.T (-1) : LaurentPolynomial R) • firstTorusTriangle n R ∈
      laurentMaslovPiece (reflectedTorusGrid n) R 1 := by
  have h := laurentMonomial_smul_mem_maslovPiece (reflectedTorusGrid n) (-1) (1 : R)
    (firstTorusTriangle_mem_maslovPiece n R)
  change (LaurentPolynomial.T (-1) : LaurentPolynomial R) • _ ∈ _ at h
  simpa only [maslovO_reflectedTorusAnchor, Int.reduceSub, Int.reduceMul,
    Int.reduceNeg] using h

/-- The two displayed cycles have exactly the same native homology class. -/
theorem firstTorusNativeCycle_homology :
    (laurentMaslovComplex (reflectedTorusGrid n) R).homologyπ 0
      (firstTorusNativeCycle n R) = reflectedTorusAnchorClass n R := by
  let C := laurentMaslovComplex (reflectedTorusGrid n) R
  let w : C.X 1 := (laurentMaslovChainEquiv (reflectedTorusGrid n) R 1).symm
    ⟨(LaurentPolynomial.T (-1) : LaurentPolynomial R) • firstTorusTriangle n R,
      firstTorusBoundary_mem_maslovOne n R⟩
  have hc : firstTorusNativeCycle n R =
      reflectedTorusAnchorCycle n R + C.toCycles 1 0 w := by
    apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
    apply (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0).injective
    apply Subtype.ext
    rw [map_add, map_add, Submodule.coe_add, firstTorusNativeCycle_apply]
    rw [show (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0
        (C.iCycles 0 (reflectedTorusAnchorCycle n R)) : LaurentChain R _) =
        Finsupp.single (reflectedTorusAnchor n) 1 from
      nativeCornerCycleOfChain_apply n R _ _ _]
    have hi := congrArg (fun f : C.X 1 ⟶ C.X 0 => f w) (C.toCycles_i 1 0)
    simp only [ModuleCat.comp_apply] at hi
    have hdd := laurentMaslovChainEquiv_d (reflectedTorusGrid n) R 0
    rw [show (0 : ℤ) + 1 = 1 by decide] at hdd
    rw [hi, hdd]
    simp only [w, LinearEquiv.apply_symm_apply, map_smul]
    rfl
  rw [hc, map_add]
  have hh := congrArg (fun f : C.X 1 ⟶ C.homology 0 => f w)
    (C.toCycles_comp_homologyπ 1 0)
  simp only [ModuleCat.comp_apply] at hh
  change C.homologyπ 0 (C.toCycles 1 0 w) = 0 at hh
  rw [hh, add_zero]
  rfl

/-- The corner homology class has a representative at the first consecutive staircase vertex. -/
theorem reflectedTorusAnchorClass_representedBelow_first_vertex (hn : 0 < n) (t : ℝ) :
    ((laurentMaslovBifiltration (reflectedTorusGrid n) R).weighted t).RepresentedBelow 0
      (reflectedTorusAnchorClass n R)
      (Staircase.consecutiveWeight n t ⟨1, by omega⟩) := by
  refine ⟨firstTorusNativeCycle n R, Submodule.subset_span ?_,
    firstTorusNativeCycle_homology n R⟩
  refine ⟨1, (n : ℝ) * ((n : ℝ) - 1) / 2, ?_, ?_⟩
  · change (laurentMaslovChainEquiv (reflectedTorusGrid n) R 0
      ((laurentMaslovComplex (reflectedTorusGrid n) R).iCycles 0
        (firstTorusNativeCycle n R)) : LaurentChain R (consecutiveTorusGridSize n)) ∈
        laurentBifiltrationLevel (reflectedTorusGrid n) R 1
          ((n : ℝ) * ((n : ℝ) - 1) / 2)
    rw [firstTorusNativeCycle_apply]
    exact firstTorusCycle_mem_first_staircase_vertex n R hn
  · simp only [Staircase.consecutiveWeight, Staircase.consecutiveFirst,
      Staircase.consecutiveSecond, Nat.cast_one]
    ring_nf
    exact le_rfl

end OnLeConjecture.KnotFloer.GridFull
