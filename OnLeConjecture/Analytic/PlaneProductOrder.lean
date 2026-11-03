/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveBlowupSquareFactor

/-!
# Exact order of products of analytic plane equations

The nonzero initial form of a factor permits cancellation of its order.
Consequently exact maximal-ideal orders add under finite products.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.Analytic.Germ

/-- A finite product has the sum of the exact orders of its factors. -/
theorem exact_maximalIdeal_order_finset_prod {ι : Type*}
    (s : Finset ι) (F : ι → Germ 2) (m : ι → ℕ)
    (hF : ∀ i ∈ s, F i ∈ maximalIdeal 2 ^ m i)
    (hFn : ∀ i ∈ s, F i ∉ maximalIdeal 2 ^ (m i + 1)) :
    (∏ i ∈ s, F i) ∈ maximalIdeal 2 ^ (∑ i ∈ s, m i) ∧
      (∏ i ∈ s, F i) ∉ maximalIdeal 2 ^ ((∑ i ∈ s, m i) + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mem_maximalIdeal_iff]
  | @insert i s hi ih =>
      have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
        (fun j hj => hFn j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using
        exact_maximalIdeal_order_mul (m i) (∑ j ∈ s, m j) (F i) (∏ j ∈ s, F j)
          (hF i (Finset.mem_insert_self _ _)) (hFn i (Finset.mem_insert_self _ _)) hs.1 hs.2

end OnLeConjecture.Analytic.Germ
