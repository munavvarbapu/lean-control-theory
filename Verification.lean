import ControlTheory

/-!
Inspect the actual dependencies of the main theorem constants. These
commands do not replace compilation; they make the trust boundary visible.
-/

#print axioms ControlTheory.reachable_minimal
#print axioms ControlTheory.reachable_closedLoop
#print axioms ControlTheory.reachable_transport
#print axioms ControlTheory.controllable_iff_dual_observable
#print axioms ControlTheory.reachable_eq_finiteReachable
#print axioms ControlTheory.range_kalmanMap
#print axioms ControlTheory.controllable_iff_surjective_kalmanMap
#print axioms ControlTheory.observable_iff_eigenvector_test
#print axioms ControlTheory.controllable_iff_hautus
#print axioms ControlTheory.Examples.doubleIntegrator_controllable
#print axioms ControlTheory.Examples.twoStepControl_reaches
#print axioms ControlTheory.Examples.hiddenMode_not_controllable
#print axioms ControlTheory.Examples.energy_decay
#print axioms ControlTheory.Examples.state_square_decay
