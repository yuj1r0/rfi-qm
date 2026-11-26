module
public import FoliationQM.SpinHOnePullback
public import FoliationQM.SpinHOneRestriction
public import FoliationQM.ModTwoPullbackRefinement

/-!
# Degree-one pullback and open-cover refinement

For the smooth Spin classification supporting v13 `prop:takabayasi`,
pullback of a smooth sign cocycle commutes with restriction to a cover
refinement. The same statement holds for chart signs and the explicit
gauge comparing alternative choices of parent charts.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SpinHOnePullbackRefinement
open CliffordSpinCoverRefinement SpinSignCohomology SpinSignOneCocycle SpinSignHOne
open SpinHOneRestriction SpinHOnePullback ModTwoPullbackRefinement

variable {X B ι κ EX EB HX HB : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {n : WithTop ℕ∞} {U : ι → TopologicalSpace.Opens B}
  (f : C(X, B)) (hf : ContMDiff IX IB n f)

/-- Pullback of the parent chart signs agrees with their restriction on the preimage opens. -/
theorem zero_restrict (R : Refinement U κ) (a : ZeroCochain IB U n) :
    zero f hf (restrictZero R a) = restrictZero (refinement f R) (zero f hf a) := rfl

/-- Pullback of the raw pair signs agrees with the signs restricted by the same parents. -/
theorem one_restrict (R : Refinement U κ) (b : OneCochain IB U n) :
    one f hf (SignClassRestriction.restrictOne R b) =
      SignClassRestriction.restrictOne (refinement f R) (one f hf b) := rfl

/-- The two constructions agree on the whole normalized smooth cocycle. -/
theorem cocycle_restrict (R : Refinement U κ) (z : Cocycle IB U n) :
    cocycle f hf (restrictCocycle R z) = restrictCocycle (refinement f R) (cocycle f hf z) := rfl

/-- Pullback preserves the explicit chart gauge for a second choice of containing parents. -/
theorem zero_parentGauge (R : Refinement U κ) (q : κ → ι)
    (hq : ∀ i, (R.domain i : Set B) ⊆ U (q i)) (z : Cocycle IB U n) :
    zero f hf (parentGauge R q hq z) =
      parentGauge (refinement f R) q (fun i _ hx => hq i hx) (cocycle f hf z) := rfl

/-- Restricting a degree-one class before pullback equals restriction on the pulled refinement. -/
theorem hom_restrict (R : Refinement U κ) (c : H1 IB U n) :
    hom f hf R.domain (restrictHom R c) =
      restrictHom (refinement f R) (hom f hf U c) := by
  obtain ⟨z, rfl⟩ := SpinSignHOne.classOf_surjective c
  exact congrArg SpinSignHOne.classOf (cocycle_restrict f hf R z)

/-- The restriction and pullback square commutes as an equality of group homomorphisms. -/
theorem hom_square (R : Refinement U κ) :
    (hom f hf R.domain).comp (restrictHom R) =
      (restrictHom (refinement f R)).comp (hom f hf U) :=
  MonoidHom.ext (hom_restrict f hf R)

end FoliationQM.SpinHOnePullbackRefinement
