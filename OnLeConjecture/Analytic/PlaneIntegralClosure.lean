/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneIntegralClosureReduction
public import OnLeConjecture.Analytic.PlaneWeierstrassPrimes

/-!
# Integral closure of the plane analytic germ ring

Every nonzero prime ideal is transported by a linear coordinate change to a
prime ideal containing a distinguished Weierstrass polynomial. Factorization
over the one variable germ ring supplies a prime polynomial factor in that
ideal. Analytic Weierstrass division shows that its evaluation is a prime
plane analytic germ. Kaplansky's criterion therefore makes the plane analytic
germ ring a unique factorization domain, hence an integrally closed domain.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The plane analytic germ ring is integrally closed. -/
noncomputable instance instIsIntegrallyClosedTwo :
    IsIntegrallyClosed (Germ 2) :=
  Germ.isIntegrallyClosed_two_of_distinguishedWeierstrass_primes (by
    intro d P hPMonic hPDegree hPCoeff I hIPrime _hIBot hPI
    exact Germ.exists_prime_mem_of_distinguishedWeierstrass_mem_prime
      d P hPMonic hPDegree hPCoeff I hIPrime hPI)

end Germ

end OnLeConjecture.Analytic
