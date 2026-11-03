/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.NonsquareGenericMember
public import OnLeConjecture.DTwo.ProximityNumericalAssembly

/-!
# Quadratic jets and genus identities for general members

The coefficient of a scalar quadratic jet is an actual linear form in the
target coefficients. The genus identity in multiplicity two is derived
from the full point-basis sum identity.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ Numerical

theorem scalarJetCoefficient_ne_zero {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∃ i, a i ≠ 0) : scalarJetCoefficient a ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := ha
  intro hz
  have h := congrArg (fun L : (ι → ℂ) →ₗ[ℂ] ℂ => L (Pi.single i 1)) hz
  exact hi (by simpa [scalarJetCoefficient, Pi.single_apply] using h)

theorem quadratic_genus_identity_of_point_basis_sums
    {N : ℕ} (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2) (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (mu : ℕ)
    (hgenus : c.squareMultiplicity + 1 = mu + c.totalMultiplicity + c.branchCount) :
    2 * c.multiplicityCount 2 + 1 = mu + c.branchCount := by
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : Fin N) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hsquares := c.squareMultiplicity_eq_four_mul_count_two_add_count_one hpositive hbounded
  omega

end OnLeConjecture.DTwo
