module
public import FoliationQM.GeometricSpinPullback

/-!
# The two physical Spin sheets after base change

For the frame component of v13 `prop:takabayasi`, each fiber over a
pulled Lorentz frame is identified with the fiber over its original
frame. The identification keeps the physical Spin point and reconstructs
its new base coordinate. It accounts for both sheets even before imposing
smoothness on the base map.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackFibers
open GeometricPrincipalPullback CliffordSpinMap LorentzMatrixGroup CliffordSpinLorentzSmooth

section Fibers
variable {X B Q T ι κ : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace Q] [TopologicalSpace T] {p : T → B} {q : Q → B}
  {C : GeometricPrincipalAtlas.Data (G := Spin) q κ}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  (f : C(X, B)) (F : GeometricSpinLift.Map C A) (z : Total f p)

/-- The pulled fiber is equivalent to the original physical fiber at the original Lorentz frame. -/
def fiberEquiv : {s : Total f q // GeometricSpinPullback.map f F s = z} ≃
    {s : Q // F s = toOriginal f p z} where
  toFun s := ⟨s.val.val.2, congrArg (toOriginal f p) s.property⟩
  invFun s := ⟨⟨(z.val.1, s.val), z.property.trans ((congrArg p s.property).symm.trans (F.proj s.val))⟩,
    Subtype.ext (Prod.ext rfl s.property)⟩
  left_inv s := Subtype.ext (Subtype.ext (Prod.ext (congrArg (projection f p) s.property).symm rfl))
  right_inv _ := rfl

/-- The sheet correspondence reads the actual original Spin point. -/
theorem fiberEquiv_val (s : {s : Total f q // GeometricSpinPullback.map f F s = z}) :
    (fiberEquiv f F z s).val = s.val.val.2 := rfl

/-- Every pulled Lorentz frame has exactly two preimages under the pulled physical map. -/
theorem fiber_card : Nat.card {s : Total f q // GeometricSpinPullback.map f F s = z} = 2 :=
  (Nat.card_congr (fiberEquiv f F z)).trans (F.fiber_card _)
end Fibers

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] {p : T → B}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} [IsManifold IX n X] {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  (f : C(X, B)) (hf : ContMDiff IX IB n f) (M : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)
  (S : GeometricSpinObstruction.SmoothLift IB K A n)

/-- The pulled smooth physical lift is a covering, a local diffeomorphism, and has these two sheets at every frame. -/
theorem two_sheeted :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    let V := GeometricSpinPullback.lift f hf M S
    IsCoveringMap V.map ∧ IsLocalDiffeomorph (IX.prod spinModel) (IX.prod lorentzModel) n V.map ∧
      ∀ z, Nat.card {s : V.Carrier // V.map s = z} = 2 :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  GeometricSpinObstruction.smoothLift_two_sheeted (SmoothPrincipalPullback.smoothAtlas f hf M)
    (GeometricSpinPullback.lift f hf M S)

end FoliationQM.SpinPullbackFibers
