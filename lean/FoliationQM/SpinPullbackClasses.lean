module
public import FoliationQM.GeometricSpinPullback

/-!
# Pullback of physical Spin isomorphisms and their classes

For the frame component of v13 `prop:takabayasi`, a physical Spin isomorphism
over a Lorentz bundle induces a diffeomorphism of the actual pullback Spin
spaces. It preserves the new Spin action and commutes with the two maps to
the pulled Lorentz space, so pulling back a lift acts on physical classes.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackClasses
open GeometricPrincipalPullback CliffordSpinLorentzSmooth LorentzMatrixGroup
open GeometricSpinObstruction SmoothSpinRelativeClass

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {S U V : SmoothLift IB K A n}

/-- Commutation over the physical target forces the diffeomorphism to preserve base points. -/
theorem base_eq (e : SmoothBetween S U) (s : S.Carrier) : U.proj (e.diffeo s) = S.proj s := by
  rw [← U.map.proj, e.over, S.map.proj]

/-- The inverse diffeomorphism also preserves base points. -/
theorem symm_base_eq (e : SmoothBetween S U) (t : U.Carrier) : S.proj (e.diffeo.symm t) = U.proj t :=
  (base_eq e (e.diffeo.symm t)).symm.trans (congrArg U.proj (e.diffeo.apply_symm_apply t))

/-- Identity on an actual smooth physical Spin lift. -/
def identityIso (S : SmoothLift IB K A n) : SmoothBetween S S where
  diffeo := Diffeomorph.refl _ _ _
  equivariant _ _ := rfl
  over _ := rfl

/-- Composition of two physical isomorphisms over the same Lorentz space. -/
def composeIso (e : SmoothBetween S U) (d : SmoothBetween U V) : SmoothBetween S V where
  diffeo := e.diffeo.trans d.diffeo
  equivariant s g := (congrArg d.diffeo (e.equivariant s g)).trans (d.equivariant _ _)
  over s := (d.over (e.diffeo s)).trans (e.over s)

variable [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- Both directions of the induced Spin diffeomorphism act on the original-space coordinate. -/
def diffeo (e : SmoothBetween S U) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas
    letI := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f U.atlas
    Diffeomorph (IX.prod spinModel) (IX.prod spinModel) (Total f S.proj) (Total f U.proj) n := by
  let := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f S.atlas
  let := SmoothPullbackChartedSpace.chartedSpace HX CliffordSpinManifold.Model f U.atlas
  let MS := SmoothPrincipalPullback.smoothAtlas f hf S.smoothAtlas
  let MU := SmoothPrincipalPullback.smoothAtlas f hf U.smoothAtlas
  exact
    { toFun := SmoothPullbackMapOver.map f e.diffeo (base_eq e)
      invFun := SmoothPullbackMapOver.map f e.diffeo.symm (symm_base_eq e)
      left_inv := fun z => Subtype.ext (Prod.ext rfl (e.diffeo.symm_apply_apply z.val.2))
      right_inv := fun z => Subtype.ext (Prod.ext rfl (e.diffeo.apply_symm_apply z.val.2))
      contMDiff_toFun := SmoothPullbackMapOver.contMDiff_map f hf S.smoothAtlas U.smoothAtlas MS MU
        e.diffeo (base_eq e) e.diffeo.contMDiff
      contMDiff_invFun := SmoothPullbackMapOver.contMDiff_map f hf U.smoothAtlas S.smoothAtlas MU MS
        e.diffeo.symm (symm_base_eq e) e.diffeo.symm.contMDiff }

/-- The pulled diffeomorphism preserves the Spin action and commutes with the actual pulled Lorentz maps. -/
def iso (e : SmoothBetween S U) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    SmoothBetween (GeometricSpinPullback.lift f hf LM S) (GeometricSpinPullback.lift f hf LM U) := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  exact
    { diffeo := diffeo f hf e
      equivariant := fun z g => Subtype.ext (Prod.ext rfl (e.equivariant z.val.2 g))
      over := fun z => Subtype.ext (Prod.ext rfl (e.over z.val.2)) }

/-- The induced isomorphism retains the new base point and acts by the original diffeomorphism. -/
theorem iso_apply (e : SmoothBetween S U) (z : Total f S.proj) :
    ((iso f hf LM e).diffeo z).val = (z.val.1, e.diffeo z.val.2) := rfl

/-- The inverse of the pulled physical isomorphism uses the original inverse on the fiber. -/
theorem iso_symm_apply (e : SmoothBetween S U) (z : Total f U.proj) :
    ((iso f hf LM e).diffeo.symm z).val = (z.val.1, e.diffeo.symm z.val.2) := rfl

/-- Pullback carries an identity physical isomorphism to the identity at every point. -/
theorem iso_identity_apply (S : SmoothLift IB K A n) (z : Total f S.proj) :
    (iso f hf LM (identityIso S)).diffeo z = z := rfl

/-- The pulled composite agrees with composing the two pulled physical isomorphisms. -/
theorem iso_compose_apply (e : SmoothBetween S U) (d : SmoothBetween U V) (z : Total f S.proj) :
    (iso f hf LM (composeIso e d)).diffeo z = (iso f hf LM d).diffeo ((iso f hf LM e).diffeo z) := rfl

/-- Pullback of actual lifts descends to their physical isomorphism classes. -/
def classMap : PhysicalClass IB K A n → ConstructedPullbackSpinCriterion.Classes IX n f A :=
  letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
  Quotient.map (GeometricSpinPullback.lift f hf LM) (fun _ _ h => h.map (iso f hf LM))

/-- On a represented class the quotient map computes the class of the pulled physical lift. -/
theorem classMap_apply (S : SmoothLift IB K A n) :
    letI := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f A
    classMap f hf LM (physicalClass S) = physicalClass (GeometricSpinPullback.lift f hf LM S) := rfl

end FoliationQM.SpinPullbackClasses
