/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationTransferredHomotopy
public import OnLeConjecture.KnotFloer.GridStabilizationPartialFilteredComparison

/-!
# Filtered comparison with the transferred stabilization differential

The full comparison maps preserve the specified shifted Maslov pieces and both filtration
coordinates. The explicit transferred differential lowers degree by one and is filtered.
Its identification with a standard grid stabilization factor remains a separate assertion.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The finite crossing series lowers Maslov degree by one. -/
theorem stabilizationXSeries_mem_maslovPiece {m : ℤ} {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    stabilizationXSeries G s R c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m - 1) := by
  rw [stabilizationXSeries, LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply]
  apply MatchingContraction.ringInverse_one_add_mem _
    (stabilizationXCrossing_homotopy_locallyNilpotent G s R)
    (laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m - 1)).toAddSubgroup
  · intro z hz
    change laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} ((localStabilizationRetraction G s R).homotopy z) ∈
        laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m - 1)
    simpa only [add_sub_cancel_right] using laurentXCrossingDifferential_mem_maslovPiece
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
      (localStabilizationRetraction_homotopy_mem_maslovPiece G s R hz)
  · exact laurentXCrossingDifferential_mem_maslovPiece
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ} hc

/-- The finite crossing series lowers the Alexander filtration bound by one. -/
theorem stabilizationXSeries_mem_bifiltrationLevel {u v : ℝ} {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    stabilizationXSeries G s R c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u (v - 1) := by
  rw [stabilizationXSeries, LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply]
  apply MatchingContraction.ringInverse_one_add_mem _
    (stabilizationXCrossing_homotopy_locallyNilpotent G s R)
    (laurentBifiltrationLevel
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R u (v - 1)).toAddSubgroup
  · intro z hz y k hk
    obtain ⟨hfirst, hsecond⟩ := (laurentXCrossingDifferential_mem_bifiltrationLevel
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
      (localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R hz)) y k hk
    exact ⟨hfirst, by linarith⟩
  · exact laurentXCrossingDifferential_mem_bifiltrationLevel
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ} hc

/-- The finite crossing series also preserves every unshifted filtration level. -/
theorem stabilizationXSeries_mem_bifiltrationLevel_self {u v : ℝ} {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    stabilizationXSeries G s R c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v :=
  laurentBifiltrationLevel_mono (G.stabilizeX s.castSucc (G.X s).castSucc s) R le_rfl
    (by linarith : v - 1 ≤ v) (stabilizationXSeries_mem_bifiltrationLevel G s R hc)

/-- The full inclusion preserves the shifted Maslov grading. -/
theorem fullStabilizationTransferredRetraction_incl_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R n × LaurentChain R n} (hc : c ∈ stabilizationTargetMaslovPiece G R m) :
    (fullStabilizationTransferredRetraction G s R).incl c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m := by
  rw [fullStabilizationTransferredRetraction_incl, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  have hi := localStabilizationRetraction_incl_mem_maslovPiece G s R hc
  apply Submodule.sub_mem _ hi
  simpa only [sub_add_cancel] using localStabilizationRetraction_homotopy_mem_maslovPiece G s R
    (stabilizationXSeries_mem_maslovPiece G s R hi)

/-- The full projection preserves the shifted Maslov grading. -/
theorem fullStabilizationTransferredRetraction_proj_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    (fullStabilizationTransferredRetraction G s R).proj c ∈
      stabilizationTargetMaslovPiece G R m := by
  rw [fullStabilizationTransferredRetraction_proj, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  apply Submodule.sub_mem _ (localStabilizationRetraction_proj_mem_maslovPiece G s R hc)
  apply localStabilizationRetraction_proj_mem_maslovPiece
  simpa only [add_sub_cancel_right] using stabilizationXSeries_mem_maslovPiece G s R
    (localStabilizationRetraction_homotopy_mem_maslovPiece G s R hc)

/-- The full inclusion preserves both shifted filtration bounds. -/
theorem fullStabilizationTransferredRetraction_incl_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R n × LaurentChain R n}
    (hc : c ∈ stabilizationTargetBifiltrationLevel G R u v) :
    (fullStabilizationTransferredRetraction G s R).incl c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
  rw [fullStabilizationTransferredRetraction_incl, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  have hi := localStabilizationRetraction_incl_mem_bifiltrationLevel G s R hc
  exact Submodule.sub_mem _ hi (localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R
    (stabilizationXSeries_mem_bifiltrationLevel_self G s R hi))

/-- The full projection preserves both shifted filtration bounds. -/
theorem fullStabilizationTransferredRetraction_proj_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    (fullStabilizationTransferredRetraction G s R).proj c ∈
      stabilizationTargetBifiltrationLevel G R u v := by
  rw [fullStabilizationTransferredRetraction_proj, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  apply Submodule.sub_mem _ (localStabilizationRetraction_proj_mem_bifiltrationLevel G s R hc)
  exact localStabilizationRetraction_proj_mem_bifiltrationLevel G s R
    (stabilizationXSeries_mem_bifiltrationLevel_self G s R
      (localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R hc))

/-- The transferred differential is homogeneous of degree minus one. -/
theorem stabilizationTransferredDifferential_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R n × LaurentChain R n} (hc : c ∈ stabilizationTargetMaslovPiece G R m) :
    stabilizationTransferredDifferential G s R c ∈
      stabilizationTargetMaslovPiece G R (m - 1) := by
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    ((fullStabilizationTransferredRetraction G s R).incl c)
  rw [LinearSpecialContraction.proj_incl_apply] at h
  rw [← h]
  exact fullStabilizationTransferredRetraction_proj_mem_maslovPiece G s R
    (laurentDifferential_mem_maslovPiece _
      (fullStabilizationTransferredRetraction_incl_mem_maslovPiece G s R hc))

/-- The transferred differential preserves the shifted bifiltration. -/
theorem stabilizationTransferredDifferential_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R n × LaurentChain R n}
    (hc : c ∈ stabilizationTargetBifiltrationLevel G R u v) :
    stabilizationTransferredDifferential G s R c ∈
      stabilizationTargetBifiltrationLevel G R u v := by
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    ((fullStabilizationTransferredRetraction G s R).incl c)
  rw [LinearSpecialContraction.proj_incl_apply] at h
  rw [← h]
  exact fullStabilizationTransferredRetraction_proj_mem_bifiltrationLevel G s R
    (laurentDifferential_mem_bifiltrationLevel _ R _ _ _
      (fullStabilizationTransferredRetraction_incl_mem_bifiltrationLevel G s R hc))

end OnLeConjecture.KnotFloer.GridFull
