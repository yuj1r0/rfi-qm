module
public import FoliationQM.SpinHOneUniversal
public import FoliationQM.PuncturedPlaneSpinSign

/-!
# An order-two class in all-cover cohomology of the punctured plane

For the global Spin-frame component of v13 `prop:takabayasi`, the sign on
one edge of the three half-plane charts represents an explicit nonidentity
global class. Its order follows from the exponent of the physical signs.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.PuncturedPlaneGlobalSign
open SpinAllCoverHOne PuncturedPlaneSignCover

/-- Image of the explicit three-chart cocycle in the all-cover degree-one group. -/
def sign (n : WithTop ℕ∞) : GlobalH1 model Plane n :=
  ofCover domains covers (SpinSignHOne.classOf (PuncturedPlaneSpinSign.cocycle n))

/-- The negative edge cannot be removed by choosing a finer presentation. -/
theorem sign_ne_one (n : WithTop ℕ∞) : sign n ≠ 1 := by
  intro h
  apply PuncturedPlaneSpinSign.class_ne_one n
  apply ofCover_injective domains covers
  exact h.trans (map_one _).symm

/-- The explicit global punctured-plane sign class has order exactly two. -/
theorem sign_orderOf (n : WithTop ℕ∞) : orderOf (sign n) = 2 := by
  apply orderOf_eq_prime
  · simpa [pow_two] using SpinHOneUniversal.global_square (sign n)
  · exact sign_ne_one n

end FoliationQM.PuncturedPlaneGlobalSign
