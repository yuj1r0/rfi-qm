module
public import FoliationQM.SpinTargetTransport
public import FoliationQM.SmoothPullbackComparisons
public import FoliationQM.SmoothPullbackMapOver

/-!
# Lorentz target comparisons for pullback of physical Spin lifts

For the geometric frame bundle in v13 `prop:takabayasi`, the identity
and composition diffeomorphisms of fiber products preserve both the base
and the Lorentz action. A given isomorphism of original Lorentz targets
also pulls back, acting on its original frame coordinate in each direction.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackTargetComparisons
open GeometricPrincipalPullback SpinTargetTransport LorentzMatrixGroup CliffordSpinLorentzSmooth
open SmoothPullbackChartedSpace

variable {EB ET HB HT B T ι : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace T] [ChartedSpace HT T]
  {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT} {n : WithTop ℕ∞}
  {p : T → B} {A : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) p ι}

section Identity
variable [IsManifold IB n B] (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- Over the identity on the base, the pulled Lorentz target is isomorphic to the original target. -/
def identityIso :
    letI := chartedSpace HB LorentzManifold.Model (.id B) A
    Iso (IB.prod lorentzModel) K (atlas (.id B) A) A n := by
  let := chartedSpace HB LorentzManifold.Model (.id B) A
  exact
    { diffeo := SmoothPullbackComparisons.identity LM
      over := GeometricPullbackComparisons.identityEquiv_proj p
      equivariant := SmoothPullbackComparisons.identity_right LM }

/-- The identity comparison sends a frame in the pulled target to its original frame. -/
theorem identityIso_apply (z : Total (.id B) p) :
    letI := chartedSpace HB LorentzManifold.Model (.id B) A
    (identityIso LM).diffeo z = z.val.2 := rfl

/-- The inverse identity comparison reinstates the base point of the given Lorentz frame. -/
theorem identityIso_symm_apply (t : T) :
    letI := chartedSpace HB LorentzManifold.Model (.id B) A
    ((identityIso LM).diffeo.symm t).val = (p t, t) := rfl

end Identity

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [TopologicalSpace X] [ChartedSpace HX X] {IX : ModelWithCorners ℝ EX HX} [IsManifold IX n X]

section Composition
variable {EY HY Y : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [TopologicalSpace Y] [ChartedSpace HY Y] {IY : ModelWithCorners ℝ EY HY} [IsManifold IY n Y]
  (f : C(X, B)) (g : C(Y, X)) (hf : ContMDiff IX IB n f) (hg : ContMDiff IY IX n g)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)

/-- Flatten the Lorentz target of a successive pullback to that of the composite base map. -/
def composeIso :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    Iso (IY.prod lorentzModel) (IY.prod lorentzModel) (atlas g (atlas f A)) (atlas (f.comp g) A) n := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HY LorentzManifold.Model g (atlas f A)
  let := chartedSpace HY LorentzManifold.Model (f.comp g) A
  exact
    { diffeo := SmoothPullbackComparisons.compose f g hf hg LM
      over := fun _ => rfl
      equivariant := SmoothPullbackComparisons.compose_right f g hf hg LM }

/-- Flattening retains the new base point and the original Lorentz frame. -/
theorem composeIso_apply (z : Total g (projection f p)) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    ((composeIso f g hf hg LM).diffeo z).val = (z.val.1, z.val.2.val.2) := rfl

/-- Unflattening recovers the intermediate base point as the image under the inner base map. -/
theorem composeIso_symm_apply (z : Total (f.comp g) p) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HY LorentzManifold.Model g (atlas f A)
    letI := chartedSpace HY LorentzManifold.Model (f.comp g) A
    ((composeIso f g hf hg LM).diffeo.symm z).val = (z.val.1, ⟨(g z.val.1, z.val.2), z.property⟩) := rfl

end Composition

variable {EU HU U κ : Type*} [NormedAddCommGroup EU] [NormedSpace ℝ EU] [TopologicalSpace HU]
  [TopologicalSpace U] [ChartedSpace HU U] {K' : ModelWithCorners ℝ EU HU}
  {q : U → B} {D : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) q κ}
  (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K A n)
  (NM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K' D n) (e : Iso K K' A D n)

/-- Pull an isomorphism of Lorentz targets back along the given smooth base map. -/
def pullIso :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HX LorentzManifold.Model f D
    Iso (IX.prod lorentzModel) (IX.prod lorentzModel) (atlas f A) (atlas f D) n := by
  let := chartedSpace HX LorentzManifold.Model f A
  let := chartedSpace HX LorentzManifold.Model f D
  let MA := SmoothPrincipalPullback.smoothAtlas f hf LM
  let MD := SmoothPrincipalPullback.smoothAtlas f hf NM
  exact
    { diffeo :=
        { toFun := SmoothPullbackMapOver.map f e.diffeo e.over
          invFun := SmoothPullbackMapOver.map f e.diffeo.symm e.symm.over
          left_inv := fun z => Subtype.ext (Prod.ext rfl (e.diffeo.symm_apply_apply z.val.2))
          right_inv := fun z => Subtype.ext (Prod.ext rfl (e.diffeo.apply_symm_apply z.val.2))
          contMDiff_toFun := SmoothPullbackMapOver.contMDiff_map f hf LM NM MA MD
            e.diffeo e.over e.diffeo.contMDiff
          contMDiff_invFun := SmoothPullbackMapOver.contMDiff_map f hf NM LM MD MA
            e.diffeo.symm e.symm.over e.diffeo.symm.contMDiff }
      over := fun _ => rfl
      equivariant := fun z a => Subtype.ext (Prod.ext rfl (e.equivariant z.val.2 a)) }

/-- The induced target isomorphism keeps the new base point and applies the given isomorphism. -/
theorem pullIso_apply (z : Total f p) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HX LorentzManifold.Model f D
    ((pullIso f hf LM NM e).diffeo z).val = (z.val.1, e.diffeo z.val.2) := rfl

/-- Its inverse keeps the new base point and applies the inverse original isomorphism. -/
theorem pullIso_symm_apply (z : Total f q) :
    letI := chartedSpace HX LorentzManifold.Model f A
    letI := chartedSpace HX LorentzManifold.Model f D
    ((pullIso f hf LM NM e).diffeo.symm z).val = (z.val.1, e.diffeo.symm z.val.2) := rfl

end FoliationQM.SpinPullbackTargetComparisons
