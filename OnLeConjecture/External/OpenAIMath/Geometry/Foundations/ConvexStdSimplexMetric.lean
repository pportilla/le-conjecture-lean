module

/- Vendored from openai/math, commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
   Original path: lean/OAI/Geometry/Foundations/ConvexStdSimplexMetric.lean. Retrieved 2026-10-29.
   Apache 2.0 license retained in OnLeConjecture/External/OpenAIMath/LICENSE.
   Modified for module visibility, import paths, and Lean/mathlib compatibility.
   See rational-homology-provenance.json. -/

/-
Derived from Formal Conjectures:
  HodgeConjecture/Mathlib/Geometry/Convex/StdSimplexMetric.lean
The upstream Formal Conjectures repository is licensed under Apache 2.0.
This file has been modified.
-/

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.Real.Lemmas

set_option linter.style.longLine false

@[expose] public section

/-! # Convex Std Simplex Metric -/

namespace OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

noncomputable section

/-! The finite real standard simplex carries the metric on its barycentric weights. -/

/-- The sup metric on barycentric coordinates, preserving the standard simplex topology. -/
instance metricSpace (ι : Type*) [Fintype ι] : MetricSpace (stdSimplex ℝ ι) :=
  inferInstance

/-- Barycentric coordinates of a real simplex point. -/
scoped instance coeFn (ι : Type*) [Fintype ι] : CoeFun (stdSimplex ℝ ι) (fun _ => ι → ℝ) :=
  ⟨fun x => ⇑x⟩

/-- Construct a finite simplex from nonnegative coordinates summing to one. -/
def ofCoordinates {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) : stdSimplex ℝ ι :=
  ⟨x, hn, ht⟩

@[simp]
theorem ofCoordinates_weights {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hn : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) (i : ι) :
    ofCoordinates x hn ht i = x i := rfl

/-- Coordinates of a finite simplex after identifying vertices. -/
theorem weights_map_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (w : stdSimplex ℝ X) (y : Y) :
    stdSimplex.map f w y = ∑ x with f x = y, w x := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]

/-- Finite barycentric coordinate vectors form a convex set. -/
theorem convex_range_weights (ι : Type*) [Fintype ι] :
    Convex ℝ (Set.range (fun x : stdSimplex ℝ ι => (⇑x : ι → ℝ))) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d hc hd hcd
  refine ⟨ofCoordinates (c • (⇑u : ι → ℝ) + d • (⇑v : ι → ℝ)) ?_ ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg hc (stdSimplex.zero_le u i))
      (mul_nonneg hd (stdSimplex.zero_le v i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one, hcd]
  · rfl

/-- A nonempty finite standard simplex is contractible through its coordinates. -/
instance contractibleSpace (ι : Type*) [Fintype ι] [Nonempty ι] :
    ContractibleSpace (stdSimplex ℝ ι) := by
  classical
  let a : stdSimplex ℝ ι := stdSimplex.vertex (Classical.choice ‹Nonempty ι›)
  exact (convex_stdSimplex ℝ ι).contractibleSpace ⟨a, a.2⟩

/-- The finite-coordinate linear map agrees with mapping barycentric weights. -/
theorem map_coordinates {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : stdSimplex ℝ X) :
    (⇑(stdSimplex.map f w) : Y → ℝ) = FunOnFinite.linearMap ℝ ℝ f (⇑w : X → ℝ) :=
  rfl

/-- Distance is the sup distance between the barycentric coordinate vectors. -/
theorem dist_eq_weights {ι : Type*} [Fintype ι] (x y : stdSimplex ℝ ι) :
    dist x y = dist (⇑x : ι → ℝ) (⇑y : ι → ℝ) := rfl

/-- Recover a simplex from a vector known to be its barycentric coordinates. -/
def ofMemRange {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : stdSimplex ℝ ι => (⇑y : ι → ℝ))) :
    stdSimplex ℝ ι := Classical.choose hx

@[simp]
theorem ofMemRange_weights {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : x ∈ Set.range (fun y : stdSimplex ℝ ι => (⇑y : ι → ℝ))) :
    (⇑(ofMemRange x hx) : ι → ℝ) = x := Classical.choose_spec hx

/-- Finite real simplices inherit local path connectedness from their coordinate range. -/
instance locallyPathConnectedSpace (ι : Type*) [Fintype ι] :
    LocallyPathConnectedSpace (stdSimplex ℝ ι) :=
  (convex_stdSimplex ℝ ι).locallyPathConnectedSpace

/-- Barycentric coordinates realize the chosen metric isometrically. -/
theorem isometry_weights (ι : Type*) [Fintype ι] :
    Isometry (fun x : stdSimplex ℝ ι => (⇑x : ι → ℝ)) :=
  Isometry.of_dist_eq fun x y => (dist_eq_weights x y).symm

end

end OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
