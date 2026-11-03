import OnLeConjecture.Analytic.LeConjectureNative
import Lean.Util.CollectAxioms

#check @OnLeConjecture.Analytic.LeConjecture
#print OnLeConjecture.Analytic.LeConjecture
#check @OnLeConjecture.Analytic.leConjecture_native
#print axioms OnLeConjecture.Analytic.leConjecture_native

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``OnLeConjecture.Analytic.leConjecture_native] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} in {name}"
