/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationPartialFiltration
public import OnLeConjecture.KnotFloer.GridLaurentMapBounds

/-!
# Degrees and filtration shifts of the stabilization comparison components

The off-center comparison has degree zero and preserves both coordinates. Center
insertion lowers Maslov and Alexander gradings by one, and its projection reverses those shifts.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The first component of the stabilization projection. -/
noncomputable def localStabilizationFirstProjection :
    LaurentChain R (n + 1) →ₗ[LaurentPolynomial R] LaurentChain R n :=
  localComparisonOffCenterToCenter G s R ∘ₗ laurentOffCenterProjection G s R

/-- The uncorrected first component of the stabilization inclusion. -/
noncomputable def localStabilizationFirstInclusion :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R (n + 1) :=
  laurentOffCenterInclusion G s R ∘ₗ localComparisonBackward G s R

/-- The first projection has degree zero and preserves both coordinates. -/
theorem localStabilizationFirstProjection_coefficient_bounds (x : GridState (n + 1))
    (y : GridState n) {k : ℤ}
    (hk : k ∈ (localStabilizationFirstProjection G s R (single x 1) y).coeff.support) :
    G.maslovOℤ y - 2 * k =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x ∧
    -(k : ℚ) ≤ 0 ∧ G.alexander y - k ≤
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x := by
  classical
  change k ∈ (localComparisonOffCenterToCenter G s R
    (laurentOffCenterProjection G s R (single x 1)) y).coeff.support at hk
  by_cases hx : x s.succ = (G.X s).succ
  · obtain ⟨z, rfl⟩ := GridState.exists_insertPoint_eq hx
    rw [← laurentStabilizationCenterInclusion_single G s R z,
      laurentOffCenterProjection_centerInclusion, map_zero, Finsupp.zero_apply] at hk
    simp at hk
  · have hp : laurentOffCenterProjection G s R (single x 1) = single ⟨x, hx⟩ 1 := by
      rw [← laurentOffCenterInclusion_single G s R ⟨x, hx⟩ 1]
      exact laurentOffCenterProjection_inclusion G s R _
    rw [hp] at hk
    exact localComparisonOffCenterToCenter_coefficient_bounds G s R ⟨x, hx⟩ y hk

/-- The first inclusion has degree zero and preserves both coordinates. -/
theorem localStabilizationFirstInclusion_coefficient_bounds (x : GridState n)
    (y : GridState (n + 1)) {k : ℤ}
    (hk : k ∈ (localStabilizationFirstInclusion G s R (single x 1) y).coeff.support) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * k = G.maslovOℤ x ∧
    -(k : ℚ) ≤ 0 ∧
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y - k ≤ G.alexander x := by
  classical
  change k ∈ (laurentOffCenterInclusion G s R
    (localComparisonBackward G s R (single x 1)) y).coeff.support at hk
  by_cases hy : y s.succ = (G.X s).succ
  · obtain ⟨z, rfl⟩ := GridState.exists_insertPoint_eq hy
    have hz := congrArg (fun c => c z)
      (laurentStabilizationCenterProjection_offCenterInclusion G s R
        (localComparisonBackward G s R (single x 1)))
    rw [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply] at hz
    rw [hz] at hk
    simp at hk
  · have he : laurentOffCenterInclusion G s R (localComparisonBackward G s R (single x 1)) y =
        localComparisonBackward G s R (single x 1) ⟨y, hy⟩ :=
      Finsupp.mapDomain_apply Subtype.val_injective _ ⟨y, hy⟩
    rw [he] at hk
    exact localComparisonBackward_coefficient_bounds G s R x ⟨y, hy⟩ hk

omit [CharP R 2] in
/-- Center insertion has degree minus one and lowers Alexander grading by one. -/
theorem laurentStabilizationCenterInclusion_coefficient_bounds (x : GridState n)
    (y : GridState (n + 1)) {k : ℤ}
    (hk : k ∈ (laurentStabilizationCenterInclusion G s R (single x 1) y).coeff.support) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * k = G.maslovOℤ x - 1 ∧
    -(k : ℚ) ≤ 0 ∧
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y - k ≤ G.alexander x - 1 := by
  classical
  rw [laurentStabilizationCenterInclusion_single] at hk
  by_cases hy : y = x.insertPoint s.succ (G.X s).succ
  · subst y
    rw [Finsupp.single_eq_same] at hk
    change k ∈ (Finsupp.single 0 (1 : R)).support at hk
    have hk0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    subst k
    simp only [mul_zero, sub_zero, Int.cast_zero, neg_zero, le_refl, true_and,
      G.maslovOℤ_stabilizeX_insertPoint, G.alexander_stabilizeX_insertPoint]
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

omit [CharP R 2] in
/-- Center projection reverses the insertion grading shifts. -/
theorem laurentStabilizationCenterProjection_coefficient_bounds (x : GridState (n + 1))
    (y : GridState n) {k : ℤ}
    (hk : k ∈ (laurentStabilizationCenterProjection G s R (single x 1) y).coeff.support) :
    G.maslovOℤ y - 2 * k =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x + 1 ∧
    -(k : ℚ) ≤ 0 ∧ G.alexander y - k ≤
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x + 1 := by
  classical
  rw [laurentStabilizationCenterProjection_apply] at hk
  by_cases hx : x = y.insertPoint s.succ (G.X s).succ
  · subst x
    rw [Finsupp.single_eq_same] at hk
    change k ∈ (Finsupp.single 0 (1 : R)).support at hk
    have hk0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    subst k
    simp only [mul_zero, sub_zero, Int.cast_zero, neg_zero, le_refl, true_and,
      G.maslovOℤ_stabilizeX_insertPoint, G.alexander_stabilizeX_insertPoint,
      sub_add_cancel]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hx)] at hk
    simp at hk

/-- The first comparison projection is homogeneous of degree zero. -/
theorem localStabilizationFirstProjection_mem_maslovPiece {m : ℤ} {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    localStabilizationFirstProjection G s R c ∈ laurentMaslovPiece G R m := by
  simpa only [add_zero] using laurentMap_mem_maslovPiece
    (G.stabilizeX s.castSucc (G.X s).castSucc s) G (localStabilizationFirstProjection G s R) 0
    (fun x y k hk => by simpa only [add_zero] using
      (localStabilizationFirstProjection_coefficient_bounds G s R x y hk).1) hc

/-- The first comparison inclusion is homogeneous of degree zero. -/
theorem localStabilizationFirstInclusion_mem_maslovPiece {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) :
    localStabilizationFirstInclusion G s R c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m := by
  simpa only [add_zero] using laurentMap_mem_maslovPiece G
    (G.stabilizeX s.castSucc (G.X s).castSucc s) (localStabilizationFirstInclusion G s R) 0
    (fun x y k hk => by simpa only [add_zero] using
      (localStabilizationFirstInclusion_coefficient_bounds G s R x y hk).1) hc

/-- The first comparison projection preserves both real filtration levels. -/
theorem localStabilizationFirstProjection_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    localStabilizationFirstProjection G s R c ∈ laurentBifiltrationLevel G R u v := by
  simpa only [Rat.cast_zero, add_zero] using laurentMap_mem_bifiltrationLevel
    (G.stabilizeX s.castSucc (G.X s).castSucc s) G (localStabilizationFirstProjection G s R) 0
    (fun x y k hk => by simpa only [add_zero] using
      (localStabilizationFirstProjection_coefficient_bounds G s R x y hk).2) hc

/-- The first comparison inclusion preserves both real filtration levels. -/
theorem localStabilizationFirstInclusion_mem_bifiltrationLevel {u v : ℝ} {c : LaurentChain R n}
    (hc : c ∈ laurentBifiltrationLevel G R u v) :
    localStabilizationFirstInclusion G s R c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
  simpa only [Rat.cast_zero, add_zero] using laurentMap_mem_bifiltrationLevel G
    (G.stabilizeX s.castSucc (G.X s).castSucc s) (localStabilizationFirstInclusion G s R) 0
    (fun x y k hk => by simpa only [add_zero] using
      (localStabilizationFirstInclusion_coefficient_bounds G s R x y hk).2) hc

omit [CharP R 2] in
/-- Center inclusion shifts the homogeneous degree by minus one. -/
theorem laurentStabilizationCenterInclusion_mem_maslovPiece {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) :
    laurentStabilizationCenterInclusion G s R c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m - 1) := by
  simpa only [sub_eq_add_neg] using laurentMap_mem_maslovPiece G
    (G.stabilizeX s.castSucc (G.X s).castSucc s) (laurentStabilizationCenterInclusion G s R) (-1)
    (fun x y k hk => by simpa only [sub_eq_add_neg] using
      (laurentStabilizationCenterInclusion_coefficient_bounds G s R x y hk).1) hc

omit [CharP R 2] in
/-- Center projection shifts the homogeneous degree by one. -/
theorem laurentStabilizationCenterProjection_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    laurentStabilizationCenterProjection G s R c ∈ laurentMaslovPiece G R (m + 1) :=
  laurentMap_mem_maslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) G
    (laurentStabilizationCenterProjection G s R) 1
    (fun x y _k hk => (laurentStabilizationCenterProjection_coefficient_bounds G s R x y hk).1) hc

omit [CharP R 2] in
/-- Center inclusion lowers the Alexander filtration bound by one. -/
theorem laurentStabilizationCenterInclusion_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R n} (hc : c ∈ laurentBifiltrationLevel G R u v) :
    laurentStabilizationCenterInclusion G s R c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u (v - 1) := by
  simpa only [Rat.cast_neg, Rat.cast_one, sub_eq_add_neg] using laurentMap_mem_bifiltrationLevel G
    (G.stabilizeX s.castSucc (G.X s).castSucc s) (laurentStabilizationCenterInclusion G s R) (-1)
    (fun x y k hk => by simpa only [sub_eq_add_neg] using
      (laurentStabilizationCenterInclusion_coefficient_bounds G s R x y hk).2) hc

omit [CharP R 2] in
/-- Center projection raises the Alexander filtration bound by one. -/
theorem laurentStabilizationCenterProjection_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    laurentStabilizationCenterProjection G s R c ∈ laurentBifiltrationLevel G R u (v + 1) := by
  simpa only [Rat.cast_one] using laurentMap_mem_bifiltrationLevel
    (G.stabilizeX s.castSucc (G.X s).castSucc s) G (laurentStabilizationCenterProjection G s R) 1
    (fun x y k hk => (laurentStabilizationCenterProjection_coefficient_bounds G s R x y hk).2) hc

end OnLeConjecture.KnotFloer.GridFull
