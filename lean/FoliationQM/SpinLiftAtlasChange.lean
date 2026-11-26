module
public import FoliationQM.SmoothSpinRelativeClass

/-!
# Transport of physical Spin lifts across target atlases

For the geometric frame part of v13 `prop:takabayasi`, a smooth Spin
lift has its own source charts and a smooth equivariant map to the actual
target. Replacing the target atlas for the same projection and action
keeps these data and induces an equivalence on physical isomorphism classes.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinLiftAtlasChange
open LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass

variable {E H ET HT B T ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace T] [ChartedSpace HT T]
  {I : ModelWithCorners ℝ E H} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞} {proj : T → B}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {C : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj κ}

/-- Change only the target atlas through which the equivariance equation is expressed. -/
def rechart (hr : A.right = C.right) (S : SmoothLift I K A n) : SmoothLift I K C n where
  Carrier := S.Carrier
  Index := S.Index
  proj := S.proj
  atlas := S.atlas
  smoothAtlas := S.smoothAtlas
  map := { toFun := S.map, continuous_toFun := S.map.continuous_toFun,
           proj := S.map.proj, equivariant := fun q s => (S.map.equivariant q s).trans (by rw [hr]) }
  smooth_map := S.smooth_map

/-- The smooth equivariant map into the original total space is retained pointwise. -/
theorem rechart_apply (hr : A.right = C.right) (S : SmoothLift I K A n) (q : S.Carrier) :
    (rechart hr S).map q = S.map q := rfl

/-- Reversing the change recovers the starting smooth Spin lift. -/
theorem rechart_reverse (hr : A.right = C.right) (S : SmoothLift I K A n) :
    rechart hr.symm (rechart hr S) = S := rfl

/-- Actual smooth lifts of the two target atlases are equivalent. -/
def liftEquiv (hr : A.right = C.right) : SmoothLift I K A n ≃ SmoothLift I K C n where
  toFun := rechart hr
  invFun := rechart hr.symm
  left_inv := rechart_reverse hr
  right_inv := rechart_reverse hr.symm

/-- A physical isomorphism of smooth lifts uses precisely the same source
diffeomorphism, equivariance and equality over the target after the atlas change. -/
theorem iso_iff (hr : A.right = C.right) (S U : SmoothLift I K A n) :
    Nonempty (SmoothBetween (rechart hr S) (rechart hr U)) ↔ Nonempty (SmoothBetween S U) := Iff.rfl

/-- Changing the target atlas descends to actual physical isomorphism classes. -/
def classMap (hr : A.right = C.right) : PhysicalClass I K A n → PhysicalClass I K C n :=
  Quotient.map (rechart hr) (fun _ _ h => h)

/-- On every represented lift the induced map returns the class of its actual atlas change. -/
theorem classMap_apply (hr : A.right = C.right) (S : SmoothLift I K A n) :
    classMap hr (physicalClass S) = physicalClass (rechart hr S) := rfl

/-- Physical isomorphism classes are equivalent across the two target atlases. -/
def classEquiv (hr : A.right = C.right) : PhysicalClass I K A n ≃ PhysicalClass I K C n where
  toFun := classMap hr
  invFun := classMap hr.symm
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv x := Quotient.inductionOn x (fun _ => rfl)

end FoliationQM.SpinLiftAtlasChange
