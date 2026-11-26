module
public import FoliationQM.MetricLorentzTetradCover
public import FoliationQM.GeometricFrameSpinLift

/-!
# Geometric Spin structures for the metric-derived Lorentz frame cover

Source scope: the geometric tetrad and Spin-structure components of v13
`prop:takabayasi`. The geometric inputs are the actual smooth bilinear metric,
pointwise Lorentz-signature witnesses, and independent orientation/future
continuity in the original vector bundle. The smooth oriented future tetrad
cover is constructed from these inputs; it is not a premise of this module.

A compatible genuine Clifford Spin cocycle gives a physical smooth two-sheeted
map into the literal original geometric frame total space. Its vector formula
uses the actual normalized metric-derived tetrad sections. Existence of an
adapted geometric Spin structure is equivalent to a genuine cocycle lift on
this exact derived cover, or to the explicit smooth central-sign correction
for normalized pair lifts. The constructed-pair version retains simple and
local path connectivity on every nonempty actual pair overlap. No correction
solvability, arbitrary Spin-structure existence, global frame, or
refinement-independent obstruction classification is concluded.
-/

@[expose] public section
noncomputable section
open Bundle Set
open scoped Manifold Topology Matrix.Norms.Operator
namespace FoliationQM.MetricGeometricSpinStructure
open MetricLorentzTetradCover GeometricLorentzFrameBundle SmoothLorentzFrameBundle
open CliffordSpinPrincipalBundle CliffordSpinLorentzSmooth CliffordSpinMap

variable {E H B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I] [IsManifold I n B]
  (D : SmoothLorentzMetricGeometry.Data (F := F) I V n)
  {S : CliffordSpinPolarCocycle.Data I B B n}
  (C : Compatible S (principalData (tetradData D)))

/-- The actual physical Spin map into the original geometric metric-frame total space, using the independently derived smooth tetrad cover. -/
def geometricMap : GeometricSpinLift.Map
    (PrincipalCocycleBundle.geometricData (spinData S)) (principalAtlas (tetradData D)) :=
  GeometricFrameSpinLift.geometricMap (tetradData D) C

/-- Each projected original vector-bundle point is literally the physical Lorentz-matrix combination of the computed metric-normalized sections on its true derived chart domain. -/
theorem geometricMap_vectorPoint (i : B) (p : SpinTotal S)
    (hp : p.proj ∈ (tetradData D).domain i) (a : Fin 4) :
    (⟨(geometricMap D C p).proj, (geometricMap D C p).snd.basis a⟩ : TotalSpace F V) =
      ⟨p.proj, ∑ b : Fin 4,
        SpinLorentzAction.lorentzMatrix
          (toMatrix (((PrincipalCocycleBundle.core (spinData S)).localTriv i p).2)).val b a •
            tetrad D i b p.proj⟩ :=
  GeometricFrameSpinLift.geometricMap_vectorPoint (tetradData D) C i p hp a

/-- A compatible actual Spin cocycle gives a genuine smooth two-sheeted covering of the original metric-oriented-future frame bundle; the smooth tetrad cover is a derived conclusion. -/
theorem geometricMap_smooth_two_sheeted :
    IsCoveringMap (geometricMap D C) ∧
      IsLocalDiffeomorph (I.prod spinModel) (I.prod lorentzModel) n (geometricMap D C) ∧
      ∀ p : Total (tetradData D), Nat.card {q : SpinTotal S // geometricMap D C q = p} = 2 :=
  GeometricFrameSpinLift.geometricMap_smooth_two_sheeted (tetradData D) C

/-- The independent metric geometry has an actual geometric Spin structure adapted to its derived cover exactly when the actual derived Lorentz transitions have a same-cover genuine Clifford Spin cocycle lift. -/
theorem nonempty_lift_iff :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas (tetradData D)) n) ↔
      CliffordSpinCocycleCorrection.HasSpinCocycleLift
        (SmoothLorentzTetrad.lorentzData (tetradData D)) :=
  GeometricFrameSpinLift.nonempty_lift_iff (tetradData D)

/-- For any supplied normalized pair lifts of the metric-derived transitions, existence of an actual adapted geometric Spin structure is exactly solvability of their smooth central-sign defect correction. -/
theorem nonempty_lift_iff_correction
    (P : CliffordSpinTransitionLifts.PairLifts (SmoothLorentzTetrad.lorentzData (tetradData D))) :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas (tetradData D)) n) ↔
      ∃ b : CliffordSpinCocycleCorrection.Correction (SmoothLorentzTetrad.lorentzData (tetradData D)),
        CliffordSpinCocycleCorrection.RemovesDefect P b :=
  GeometricFrameSpinLift.nonempty_lift_iff_correction (tetradData D) P

/-- When every nonempty actual derived pair overlap is simply connected and locally path connected, the constructed pair lifts give the exact sign-correction criterion without a supplied smooth tetrad or pair-lift premise. -/
theorem nonempty_lift_iff_constructed_correction
    (hsc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData (tetradData D)) i j) → SimplyConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData (tetradData D)) i j))
    (hlpc : ∀ i j, Nonempty ↥(CliffordSpinPairLiftConstruction.pairOverlap
      (SmoothLorentzTetrad.lorentzData (tetradData D)) i j) → LocallyPathConnectedSpace
        ↥(CliffordSpinPairLiftConstruction.pairOverlap (SmoothLorentzTetrad.lorentzData (tetradData D)) i j)) :
    Nonempty (GeometricSpinStructure.Lift I (principalAtlas (tetradData D)) n) ↔
      ∃ b : CliffordSpinCocycleCorrection.Correction (SmoothLorentzTetrad.lorentzData (tetradData D)),
        CliffordSpinCocycleCorrection.RemovesDefect
          (CliffordSpinPairLiftConstruction.pairLifts
            (SmoothLorentzTetrad.lorentzData (tetradData D)) hsc hlpc) b :=
  GeometricFrameSpinLift.nonempty_lift_iff_constructed_correction (tetradData D) hsc hlpc

end FoliationQM.MetricGeometricSpinStructure
