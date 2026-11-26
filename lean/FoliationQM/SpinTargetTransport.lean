module
public import FoliationQM.SmoothSpinRelativeClass

/-!
# Physical Spin classes under an isomorphism of Lorentz targets

For the geometric frame component of v13 `prop:takabayasi`, a smooth
equivariant diffeomorphism over the base identifies two actual Lorentz
targets. Composing the physical map with that diffeomorphism transports
a specified lift. Its inverse identifies the physical isomorphism classes
in the opposite direction.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinTargetTransport
open LorentzMatrixGroup GeometricSpinObstruction SmoothSpinRelativeClass

variable {B T U ι κ EX ET EU HX HT HU : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [NormedAddCommGroup EU] [NormedSpace ℝ EU] [TopologicalSpace HU]
  [TopologicalSpace B] [ChartedSpace HX B] [TopologicalSpace T] [ChartedSpace HT T]
  [TopologicalSpace U] [ChartedSpace HU U] {p : T → B} {q : U → B}
  {I : ModelWithCorners ℝ EX HX} {K : ModelWithCorners ℝ ET HT} {J : ModelWithCorners ℝ EU HU}
  {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}
  {D : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ} {n : WithTop ℕ∞}

/-- A diffeomorphism of the actual Lorentz total spaces over the base preserving the geometric right action. -/
structure Iso (K : ModelWithCorners ℝ ET HT) (J : ModelWithCorners ℝ EU HU)
    (A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι)
    (D : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ) (n : WithTop ℕ∞) where
  diffeo : Diffeomorph K J T U n
  over : ∀ t, q (diffeo t) = p t
  equivariant : ∀ t a, diffeo (A.right t a) = D.right (diffeo t) a

namespace Iso
variable (e : Iso K J A D n)

/-- Invert the target diffeomorphism and its base and action laws. -/
def symm : Iso J K D A n where
  diffeo := e.diffeo.symm
  over u := (e.over (e.diffeo.symm u)).symm.trans (congrArg q (e.diffeo.apply_symm_apply u))
  equivariant u a := by
    apply e.diffeo.injective
    change e.diffeo (e.diffeo.symm (D.right u a)) = e.diffeo (A.right (e.diffeo.symm u) a)
    rw [e.equivariant, e.diffeo.apply_symm_apply, e.diffeo.apply_symm_apply]

/-- Transport a supplied physical lift by composing its actual Spin-to-Lorentz map. -/
def change (S : SmoothLift I K A n) : SmoothLift I J D n where
  Carrier := S.Carrier
  Index := S.Index
  proj := S.proj
  atlas := S.atlas
  smoothAtlas := S.smoothAtlas
  map := { toFun := fun t => e.diffeo (S.map t)
           continuous_toFun := e.diffeo.contMDiff_toFun.continuous.comp S.map.continuous_toFun
           proj := fun t => (e.over _).trans (S.map.proj t)
           equivariant := fun t a => (congrArg e.diffeo (S.map.equivariant t a)).trans (e.equivariant _ _) }
  smooth_map := e.diffeo.contMDiff_toFun.comp S.smooth_map

/-- The transported physical map at a source point is composition with the target diffeomorphism. -/
theorem change_apply (S : SmoothLift I K A n) (s : S.Carrier) :
    (e.change S).map s = e.diffeo (S.map s) := rfl

/-- Physical isomorphisms are preserved and reflected by the change of target. -/
theorem iso_iff (S V : SmoothLift I K A n) :
    Nonempty (SmoothBetween (e.change S) (e.change V)) ↔ Nonempty (SmoothBetween S V) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨⟨d.diffeo, d.equivariant, fun t => e.diffeo.injective (d.over t)⟩⟩
  · rintro ⟨d⟩
    exact ⟨⟨d.diffeo, d.equivariant, fun t => congrArg e.diffeo (d.over t)⟩⟩

/-- Going to the new target and back yields a physical isomorphism with the original lift. -/
def roundTrip (S : SmoothLift I K A n) : SmoothBetween (e.symm.change (e.change S)) S where
  diffeo := Diffeomorph.refl _ _ _
  equivariant _ _ := rfl
  over s := (e.diffeo.symm_apply_apply (S.map s)).symm

/-- The induced equivalence of actual physical Spin isomorphism classes on the two targets. -/
def classEquiv : PhysicalClass I K A n ≃ PhysicalClass I J D n where
  toFun := Quotient.map e.change (fun S V => (e.iso_iff S V).mpr)
  invFun := Quotient.map e.symm.change (fun S V => (e.symm.iso_iff S V).mpr)
  left_inv c := Quotient.inductionOn c (fun S => Quotient.sound ⟨e.roundTrip S⟩)
  right_inv c := Quotient.inductionOn c (fun S => Quotient.sound ⟨e.symm.roundTrip S⟩)

/-- On a represented physical class the equivalence uses the explicitly transported lift. -/
theorem classEquiv_apply (S : SmoothLift I K A n) :
    e.classEquiv (physicalClass S) = physicalClass (e.change S) := rfl

end Iso
end FoliationQM.SpinTargetTransport
