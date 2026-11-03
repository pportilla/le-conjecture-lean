/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingOrder

/-!
# The finite transition operator for full matching paths

The internal matrix reads the full differential from each noncritical source to the
matched target of another source. Its diagonal is one. Removing that diagonal gives
a strictly decreasing operator. Local nilpotence proves that the full internal
matching matrix is invertible.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- The target state matched to a noncritical source. -/
def stabilizationMatchingTargetState (x : StabilizationMatchingNode G s) : GridState (n + 1) :=
  x.val.swapRows (G.X s).castSucc (G.X s).succ

/-- Distinct noncritical sources have distinct matching targets. -/
theorem stabilizationMatchingTargetState_injective :
    Function.Injective (stabilizationMatchingTargetState G s) := by
  intro x y h
  apply Subtype.ext
  have hh := congrArg (fun z : GridState (n + 1) =>
    z.swapRows (G.X s).castSucc (G.X s).succ) h
  simpa only [stabilizationMatchingTargetState, GridState.swapRows_swapRows] using hh

variable (R : Type*) [CommRing R]

/-- Include the noncritical source basis in the full state module. -/
noncomputable def stabilizationMatchingSourceInclusion :
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R (n + 1) :=
  Finsupp.lmapDomain (LaurentPolynomial R) (LaurentPolynomial R) Subtype.val

/-- Read the coefficients at the noncritical matching targets. -/
noncomputable def stabilizationMatchingTargetProjection :
    LaurentChain R (n + 1) →ₗ[LaurentPolynomial R]
      (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  Finsupp.lcomapDomain (stabilizationMatchingTargetState G s)
    (stabilizationMatchingTargetState_injective G s)

@[simp]
theorem stabilizationMatchingSourceInclusion_single (x : StabilizationMatchingNode G s)
    (a : LaurentPolynomial R) :
    stabilizationMatchingSourceInclusion G s R (single x a) = single x.val a :=
  Finsupp.mapDomain_single

@[simp]
theorem stabilizationMatchingTargetProjection_apply (c : LaurentChain R (n + 1))
    (x : StabilizationMatchingNode G s) :
    stabilizationMatchingTargetProjection G s R c x = c (stabilizationMatchingTargetState G s x) :=
  rfl

/-- The off-diagonal internal transition matrix of the actual full differential. -/
noncomputable def stabilizationMatchingTransition : Module.End (LaurentPolynomial R)
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) :=
  stabilizationMatchingTargetProjection G s R ∘ₗ
    laurentDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s) R ∘ₗ
      stabilizationMatchingSourceInclusion G s R - LinearMap.id

open Classical in
/-- Its entries are exactly the nonmatching full Laurent rectangle coefficients. -/
theorem stabilizationMatchingTransition_single_apply (x z : StabilizationMatchingNode G s) :
    stabilizationMatchingTransition G s R (single x 1) z = if x = z then 0 else
      laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R x.val
        (stabilizationMatchingTargetState G s z) := by
  classical
  rw [stabilizationMatchingTransition, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, stabilizationMatchingSourceInclusion_single, Finsupp.sub_apply,
    stabilizationMatchingTargetProjection_apply, laurentDifferential_single,
    laurentOnGenerator_apply, LinearMap.id_apply, Finsupp.single_apply]
  by_cases h : x = z
  · subst z
    rw [if_pos rfl, if_pos rfl,
      show laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R x.val
        (stabilizationMatchingTargetState G s x) = 1 from
          laurentCoefficient_stabilizationMatching_source G s R x.val x.property.1 x.property.2,
      sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- Every nonzero internal transition strictly lowers the concrete matching-node weight. -/
theorem stabilizationMatchingTransition_support_lt (x z : StabilizationMatchingNode G s)
    (hz : z ∈ (stabilizationMatchingTransition G s R (single x 1)).support) :
    stabilizationMatchingNodeWeight G s z < stabilizationMatchingNodeWeight G s x := by
  classical
  rw [Finsupp.mem_support_iff, stabilizationMatchingTransition_single_apply] at hz
  split_ifs at hz with h
  · exact False.elim (hz rfl)
  · exact stabilizationMatchingNodeWeight_lt_of_coefficient_ne_zero G s R x z h hz

/-- The internal matching transition has only finitely many nonzero iterates on every chain. -/
theorem stabilizationMatchingTransition_locallyNilpotent
    (c : StabilizationMatchingNode G s →₀ LaurentPolynomial R) :
    ∃ k : ℕ, (stabilizationMatchingTransition G s R ^ k) c = 0 := by
  exact Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _
    (stabilizationMatchingNodeWeight G s) (stabilizationMatchingNodeWeight_wellFounded G s)
    (fun x z hz => stabilizationMatchingTransition_support_lt G s R x z hz) c

/-- The full internal matching matrix is invertible. -/
theorem isUnit_one_add_stabilizationMatchingTransition :
    IsUnit (1 + stabilizationMatchingTransition G s R) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    (stabilizationMatchingTransition_locallyNilpotent G s R)

end OnLeConjecture.KnotFloer.GridFull
