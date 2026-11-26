module
public import FoliationQM.ConstructedPullbackSpinCriterion
public import FoliationQM.SmoothPullbackMapOver

/-!
# Pullback of an actual geometric Spin lift

For the frame-bundle interpretation of v13 `prop:takabayasi`, a geometric
Spin map pulls back by sending its original Spin frame to its Lorentz frame
and keeping the new base point. For a smooth base map, the original Spin
and Lorentz principal charts supply the two smooth structures on these
fiber products and give a smooth physical lift of the same order.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.GeometricSpinPullback
open GeometricPrincipalPullback CliffordSpinMap CliffordSpinLorentz CliffordSpinLorentzSmooth
open LorentzMatrixGroup GeometricSpinObstruction

section Map
variable {X B Q T κ ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  [TopologicalSpace Q] [TopologicalSpace T] {q : Q → B} {p : T → B}
  {C : GeometricPrincipalAtlas.Data (G := Spin) q κ}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  (f : C(X, B)) (F : GeometricSpinLift.Map C A)

/-- Pull the continuous physical map back between the two actual principal fiber products. -/
def map : GeometricSpinLift.Map (atlas f C) (atlas f A) where
  toFun := SmoothPullbackMapOver.map f F F.proj
  continuous_toFun := ((continuous_projection f).prodMk
    (F.continuous_toFun.comp (continuous_toOriginal f))).subtype_mk _
  proj := SmoothPullbackMapOver.projection_map f F F.proj
  equivariant := SmoothPullbackMapOver.map_right f F F.proj C.right A.right C.proj_right
    A.proj_right lorentzHom F.equivariant

/-- The physical map has the same new base point and the image of its original Spin frame. -/
theorem map_val (z : Total f q) : (map f F z).val = (z.val.1, F z.val.2) := rfl

/-- Projecting the pulled map to the original frame gives the supplied physical map. -/
theorem original_map (z : Total f q) :
    toOriginal f p (map f F z) = F (toOriginal f q z) := rfl

/-- Right translating a pulled Spin frame maps to translation by its genuine Lorentz image. -/
theorem map_equivariant (z : Total f q) (s : Spin) :
    map f F ((atlas f C).right z s) = (atlas f A).right (map f F z) (lorentzHom s) :=
  (map f F).equivariant z s

end Map

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T] {proj : T → B}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB}
  {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} [IsManifold IX n X]
  (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n) (S : SmoothLift IB K A n)

/-- A specified smooth Spin lift gives a smooth lift on the actual Lorentz fiber product. -/
def lift : ConstructedPullbackSpinCriterion.Lift IX n f A := by
  let := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  let SM := SmoothPrincipalPullback.smoothAtlas f hf S.smoothAtlas
  let FM := SmoothPrincipalPullback.smoothAtlas f hf LM
  exact
    { Carrier := Total f S.proj
      Index := S.Index
      manifold := SmoothPrincipalPullback.isManifold_total f hf S.smoothAtlas
      proj := projection f S.proj
      atlas := atlas f S.atlas
      smoothAtlas := SM
      map := map f S.map
      smooth_map := SmoothPullbackMapOver.contMDiff_map f hf S.smoothAtlas LM SM FM
        S.map S.map.proj S.smooth_map }

/-- The source is exactly the fiber product of the original Spin projection and the base map. -/
theorem lift_carrier :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).Carrier = Total f S.proj := rfl

/-- The pulled source retains the original Spin chart indices. -/
theorem lift_index :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).Index = S.Index := rfl

/-- The source charts are the product charts built on the actual pulled Spin trivializations. -/
theorem lift_charted :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).charted =
      SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas := rfl

/-- The pulled Spin atlas consists of actual pullbacks of the original principal charts. -/
theorem lift_atlas :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).atlas = atlas f S.atlas := rfl

/-- The projection of a pulled Spin frame is its new base point. -/
theorem lift_proj (z : Total f S.proj) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).proj z = z.val.1 := rfl

/-- Translation in the pulled Spin source acts on its original Spin frame. -/
theorem lift_right (z : Total f S.proj) (s : Spin) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    ((lift f hf LM S).atlas.right z s).val = (z.val.1, S.atlas.right z.val.2 s) := rfl

/-- The physical map of the smooth lift is the pullback of the original equivariant map. -/
theorem lift_map :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    (lift f hf LM S).map = map f S.map := rfl

/-- The smooth physical map keeps the new base point and sends the original Spin frame to its image. -/
theorem lift_map_val (z : Total f S.proj) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    ((lift f hf LM S).map z).val = (z.val.1, S.map z.val.2) := rfl

end FoliationQM.GeometricSpinPullback
