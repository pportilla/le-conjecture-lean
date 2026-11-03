/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationPartialContraction

/-!
# Filtration of the partially blocked stabilization homotopy

The constructed homotopy has Maslov degree one and preserves both Laurent coordinates.
These properties justify the remaining X-crossing perturbation on the actual stabilized module.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- Every nonzero coefficient of the stabilization homotopy has the stated degree and bounds. -/
theorem localStabilizationRetraction_homotopy_coefficient_bounds (x y : GridState (n + 1))
    {k : ℤ}
    (hk : k ∈ ((localStabilizationRetraction G s R).homotopy (single x 1) y).coeff.support) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * k =
      (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x + 1 ∧
    -(k : ℚ) ≤ 0 ∧
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y - k ≤
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x := by
  classical
  rw [localStabilizationRetraction_homotopy, Finsupp.neg_apply,
    AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] at hk
  by_cases hx : x s.succ = (G.X s).succ
  · obtain ⟨z, rfl⟩ := GridState.exists_insertPoint_eq hx
    rw [← laurentStabilizationCenterInclusion_single G s R z,
      laurentOffCenterProjection_centerInclusion, map_zero, map_zero, Finsupp.zero_apply] at hk
    simp at hk
  · have hp : laurentOffCenterProjection G s R (single x 1) = single ⟨x, hx⟩ 1 := by
      rw [← laurentOffCenterInclusion_single G s R ⟨x, hx⟩ 1]
      exact laurentOffCenterProjection_inclusion G s R _
    rw [hp] at hk
    by_cases hy : y s.succ = (G.X s).succ
    · obtain ⟨z, rfl⟩ := GridState.exists_insertPoint_eq hy
      have hz := congrArg (fun c => c z)
        (laurentStabilizationCenterProjection_offCenterInclusion G s R
          (localComparisonOffCenterInverseHomotopy G s R (single ⟨x, hx⟩ 1)))
      rw [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply] at hz
      rw [hz] at hk
      simp at hk
    · have he : laurentOffCenterInclusion G s R
          (localComparisonOffCenterInverseHomotopy G s R (single ⟨x, hx⟩ 1)) y =
        localComparisonOffCenterInverseHomotopy G s R (single ⟨x, hx⟩ 1) ⟨y, hy⟩ :=
        Finsupp.mapDomain_apply Subtype.val_injective _ ⟨y, hy⟩
      rw [he] at hk
      exact localComparisonOffCenterInverseHomotopy_coefficient_bounds G s R ⟨x, hx⟩ ⟨y, hy⟩ hk

omit [CharP R 2] in
/-- Laurent matrix multiplication adds an input exponent to a matrix-entry exponent. -/
theorem exists_support_laurentEnd {ι : Type*} [Finite ι]
    (f : Module.End (LaurentPolynomial R) (ι →₀ LaurentPolynomial R))
    (c : ι →₀ LaurentPolynomial R) {y : ι} {k : ℤ}
    (hk : k ∈ (f c y).coeff.support) :
    ∃ x : ι, ∃ j ∈ (c x).coeff.support, ∃ d ∈ (f (single x 1) y).coeff.support, k = j + d := by
  classical
  let := Fintype.ofFinite ι
  rw [finiteEnd_apply_apply, AddMonoidAlgebra.coeff_sum] at hk
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hk)
  obtain ⟨j, hj, d, hd, hsum⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hx)
  exact ⟨x, j, hj, d, hd, hsum.symm⟩

/-- The constructed homotopy raises Maslov degree by one. -/
theorem localStabilizationRetraction_homotopy_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    (localStabilizationRetraction G s R).homotopy c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m + 1) := by
  intro y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentEnd R _ c hk
  have hm := (localStabilizationRetraction_homotopy_coefficient_bounds G s R x y hd).1
  have hx := hc x j hj
  change (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x - 2 * j = m at hx
  change (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y - 2 * (j + d) = m + 1
  omega

/-- The constructed homotopy preserves both Laurent filtration coordinates. -/
theorem localStabilizationRetraction_homotopy_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    (localStabilizationRetraction G s R).homotopy c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
  intro y k hk
  obtain ⟨x, j, hj, d, hd, rfl⟩ := exists_support_laurentEnd R _ c hk
  obtain ⟨_, hfirst, hsecond⟩ :=
    localStabilizationRetraction_homotopy_coefficient_bounds G s R x y hd
  have hfirst' : -(d : ℝ) ≤ 0 := by exact_mod_cast hfirst
  have hsecond' : ((G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y : ℝ) - d ≤
      (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander x := by exact_mod_cast hsecond
  obtain ⟨hx, hy⟩ := hc x j hj
  push_cast
  constructor <;> linarith

/-- The crossing correction composed with the constructed homotopy is locally nilpotent. -/
theorem stabilizationXCrossing_homotopy_locallyNilpotent (c : LaurentChain R (n + 1)) :
    ∃ k : ℕ, ((laurentXCrossingDifferential
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ} *
        (localStabilizationRetraction G s R).homotopy) ^ k) c = 0 := by
  apply exists_pow_apply_eq_zero_of_laurent_lowering
    (G.stabilizeX s.castSucc (G.X s).castSucc s) R
  · intro m z hz
    simpa only [Module.End.mul_apply, add_sub_cancel_right] using
      laurentXCrossingDifferential_mem_maslovPiece
        (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
        (localStabilizationRetraction_homotopy_mem_maslovPiece G s R hz)
  · intro u v z hz
    exact laurentXCrossingDifferential_mem_bifiltrationLevel
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
      (localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R hz)

/-- The concrete remaining-X perturbation admits the homological perturbation inverse. -/
theorem isUnit_one_add_stabilizationXCrossing_homotopy :
    IsUnit (1 + laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} * (localStabilizationRetraction G s R).homotopy) :=
  isUnit_one_add_laurentXCrossing_comp_homotopy
    (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
    (localStabilizationRetraction G s R).homotopy
    (fun _ _ hc => localStabilizationRetraction_homotopy_mem_maslovPiece G s R hc)
    (fun _ _ _ hc => localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R hc)

end OnLeConjecture.KnotFloer.GridFull
