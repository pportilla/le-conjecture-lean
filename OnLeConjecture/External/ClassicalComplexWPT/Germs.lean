module

/- Vendored from BochaoKong/classical-complex-wpt, commit b4a7273fe5c9752753c52e10494097569089642d.
   Original path: ClassicalComplexWPT/Germs.lean. Retrieved 2026-10-29.
   Apache 2.0 license retained in this directory.
   Module visibility and import paths adapted to this project.
   Proof compatibility edits are recorded in OnLeConjecture/External/LocalComplexGeometry/patches/ruckert-compatibility.patch. -/

public import OnLeConjecture.External.ClassicalComplexWPT.Basic
public import Mathlib.Order.Filter.Germ.Basic

@[expose] public section


open Filter
open scoped Topology

/-!
# Elementary facts about analytic function germs

The public theorem represents germs by functions modulo `=ᶠ[𝓝 x]`.  These
lemmas record the corresponding ring-theoretic unit fact without introducing a
separate sheaf or stalk API into the public statement.
-/

namespace ClassicalComplexWPT

/-- A representative which is eventually nonzero defines a unit in the function-germ ring. -/
theorem germ_isUnit_of_eventually_ne {X : Type*} {l : Filter X} {g : X → ℂ}
    (hg : ∀ᶠ x in l, g x ≠ 0) : IsUnit (g : Filter.Germ l ℂ) := by
  refine ⟨⟨(g : Filter.Germ l ℂ), (g⁻¹ : Filter.Germ l ℂ), ?_, ?_⟩, rfl⟩
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact mul_inv_cancel₀ hx
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact inv_mul_cancel₀ hx

/-- A nonvanishing analytic germ is a ring-theoretic unit. -/
theorem analytic_germ_isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {x : E} (hg : AnalyticAt ℂ g x) (hg0 : g x ≠ 0) :
    IsUnit (g : Filter.Germ (𝓝 x) ℂ) := by
  apply germ_isUnit_of_eventually_ne
  exact hg.continuousAt.eventually_ne hg0

end ClassicalComplexWPT
