module
public import FoliationQM.SmoothPrincipalPullback
public import FoliationQM.PullbackSpinCriterion

/-!
# Smooth Spin criteria for the constructed fiber-product charts

For the frame component of v13 `prop:takabayasi`, the differentiability
of the base map and of the original Lorentz principal charts supplies
the smooth geometric target in the Spin existence criterion. The
physical lift map lands in the fiber product with its product-model charts.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.ConstructedPullbackSpinCriterion
open GeometricPrincipalPullback CliffordSpinLorentzSmooth LorentzMatrixGroup

variable {X B T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] {proj : T → B}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞}

/-- Physical smooth lifts into the actual fiber product with the constructed charts. -/
abbrev Lift (IX : ModelWithCorners ℝ EX HX) (n : WithTop ℕ∞) (f : C(X, B))
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  GeometricSpinObstruction.SmoothLift IX (IX.prod lorentzModel) (atlas f A) n

/-- The quotient by physical Spin isomorphisms for these same target charts. -/
abbrev Classes (IX : ModelWithCorners ℝ EX HX) (n : WithTop ℕ∞) (f : C(X, B))
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι) :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  SmoothSpinRelativeClass.PhysicalClass IX (IX.prod lorentzModel) (atlas f A) n

variable [IsManifold IX n X] [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace X]
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (S : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)
  (h : PresentedLorentzBundle.HasPresentation proj A.right)

include S hf in
/-- Vanishing of the original class after pullback characterizes existence on the constructed smooth target. -/
theorem nonempty_iff : Nonempty (Lift IX n f A) ↔
    ModTwoGlobalPullback.pull f (PresentedLorentzBundle.obstruction h) = 0 :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  PullbackSpinCriterion.nonempty_iff f h (SmoothPrincipalPullback.smoothAtlas f hf S) rfl

/-- Vanishing after pullback supplies the new base's degree-one torsor of physical lift classes. -/
@[instance_reducible] def torsor_of_zero
    (hz : ModTwoGlobalPullback.pull f (PresentedLorentzBundle.obstruction h) = 0) :
    Torsor (SpinAllCoverHOne.GlobalH1 IX X n) (Classes IX n f A) :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  PullbackSpinCriterion.torsor_of_zero f h (SmoothPrincipalPullback.smoothAtlas f hf S) rfl hz

include S hf in
/-- Exactly one physical class exists when the pulled obstruction is zero and global degree one is trivial. -/
theorem unique_iff : (∃! _p : Classes IX n f A, True) ↔
    ModTwoGlobalPullback.pull f (PresentedLorentzBundle.obstruction h) = 0 ∧
      Subsingleton (SpinAllCoverHOne.GlobalH1 IX X n) :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  PullbackSpinCriterion.unique_iff f h (SmoothPrincipalPullback.smoothAtlas f hf S) rfl

end FoliationQM.ConstructedPullbackSpinCriterion
