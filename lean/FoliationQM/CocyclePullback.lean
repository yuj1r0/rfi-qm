module
public import FoliationQM.CocycleGaugeTransform

/-!
# Actual pullback of supplied smooth transition cocycles

Source: base-change infrastructure for the supplied-cocycle interpretation
of v13 `prop:takabayasi`. A genuine bundled smooth map pulls the original
open cover back to its actual preimage open sets. Transitions are composed
with that map, and their overlap regularity and cocycle identities follow
from the original data. The selected covering index is exactly the original
index evaluated at the image point.

Each actual preimage chart has a genuine bundled smooth map to its original
open chart domain. Identity and successive pullbacks agree as full cocycle
data and as actual local base maps. Local frame changes pull back by the
same composition, commute with transformed transitions, and retain their
inverse and ordered-composition laws. No invertibility or surjectivity of
the supplied base map is required, and no bundle isomorphism over an
arbitrary base change is asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocyclePullback
open PolarTransitionCocycle CocycleGaugeTransform SourcePolarDatum

variable {E H E' H' B B' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B] [ChartedSpace H B]
  [TopologicalSpace B'] [ChartedSpace H' B'] {ι : Type*} {n : WithTop ℕ∞}
  (D : Data I B ι n) (f : C^n⟮J, B'; I, B⟯)

/-- A genuine smooth base map constructs a cocycle on the actual preimage open cover, with transitions composed with that map. -/
def pullback : Data J B' ι n where
  domain i := ⟨f ⁻¹' (D.domain i : Set B), (D.domain i).isOpen.preimage f.contMDiff.continuous⟩
  covers x := D.covers (f x)
  transition i j x := D.transition i j (f x)
  smooth_transition i j := (D.smooth_transition i j).comp f.contMDiff.contMDiffOn
    (fun _ hx => hx)
  identity i x hx := D.identity i (f x) hx
  comp i j k x hi hj hk := D.comp i j k (f x) hi hj hk

/-- Every pulled-back chart domain is exactly the actual preimage of the original open domain. -/
theorem pullback_domain (i : ι) :
    ((pullback D f).domain i : Set B') = f ⁻¹' (D.domain i : Set B) := rfl

/-- Every actual pulled-back transition is the original determinant-one matrix transition evaluated at the image base point. -/
theorem pullback_transition (i j : ι) (x : B') :
    (pullback D f).transition i j x = D.transition i j (f x) := rfl

/-- The selected index of the pullback is exactly the original selected index at the actual image point. -/
theorem indexAt_pullback (x : B') :
    indexAt (pullback D f) x = indexAt D (f x) := rfl

/-- The actual pulled-back polar coordinate change is the original coordinate change at the image point. -/
theorem polarChange_pullback (i j : ι) (x : B') (p : DensityFrameManifold.Product) :
    polarChange (pullback D f) i j x p = polarChange D i j (f x) p := rfl

/-- The actual pulled-back represented-spinor coordinate change is the original change at the image point. -/
theorem spinorChange_pullback (i j : ι) (x : B') (q : PolarSignQuotient.RegularSpinor) :
    spinorChange (pullback D f) i j x q = spinorChange D i j (f x) q := rfl

/-- The smooth base map restricts to a genuine bundled smooth map from each actual preimage open chart to its original open chart. -/
def localBaseMap (i : ι) : C^n⟮J, (pullback D f).domain i; I, D.domain i⟯ :=
  ⟨fun x => ⟨f x.val, x.property⟩, by
    intro x
    have hh := (f.contMDiff.comp (contMDiff_subtype_val
      (I := J) (U := (pullback D f).domain i))) x
    have hi : ContMDiffWithinAt J I n
        (Subtype.val ∘ (fun x : (pullback D f).domain i =>
          (⟨f x.val, x.property⟩ : D.domain i))) univ x ↔
        ContMDiffWithinAt J I n
          (fun x : (pullback D f).domain i => (⟨f x.val, x.property⟩ : D.domain i)) univ x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact hi.mp hh⟩

/-- The local base map is the literal restriction of the supplied smooth map, with membership in the actual original domain. -/
theorem localBaseMap_apply (i : ι) (x : (pullback D f).domain i) :
    localBaseMap D f i x = ⟨f x.val, x.property⟩ := rfl

/-- The ambient value of the local base map is exactly the supplied smooth map applied to the original local point. -/
theorem localBaseMap_val (i : ι) (x : (pullback D f).domain i) :
    (localBaseMap D f i x).val = f x.val := rfl

/-- Local matrix frame changes pull back by actual composition, requiring smoothness only on the corresponding preimage chart domains. -/
def pullbackFrameChange (h : FrameChange D) : FrameChange (pullback D f) where
  value i x := h.value i (f x)
  smooth_value i := (h.smooth_value i).comp f.contMDiff.contMDiffOn (fun _ hx => hx)

/-- The actual pulled-back local frame matrix is the original frame-change matrix evaluated at the image point. -/
theorem pullbackFrameChange_value (h : FrameChange D) (i : ι) (x : B') :
    (pullbackFrameChange D f h).value i x = h.value i (f x) := rfl

/-- Pulling back a frame-transformed cocycle gives exactly the transformed pulled-back cocycle, preserving the actual matrix multiplication order. -/
theorem pullback_transformed (h : FrameChange D) :
    pullback (transformed D h) f =
      transformed (pullback D f) (pullbackFrameChange D f h) := rfl

/-- Pullback along the genuine identity smooth map leaves the full supplied cocycle data unchanged. -/
theorem pullback_identity : pullback D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) = D := rfl

/-- The local base map for identity pullback is the actual identity on the original open chart. -/
theorem localBaseMap_identity (i : ι) (x : D.domain i) :
    localBaseMap D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) i x = x := rfl

/-- Identity pullback preserves each actual local frame change as full frame-change data. -/
theorem pullbackFrameChange_identity (h : FrameChange D) :
    pullbackFrameChange D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) h = h := rfl

/-- Pullback commutes exactly with the actual inverse local frame change for the transformed cocycle. -/
theorem pullback_inverseChange (h : FrameChange D) :
    pullbackFrameChange (transformed D h) f (inverseChange D h) =
      inverseChange (pullback D f) (pullbackFrameChange D f h) := rfl

/-- Pullback preserves the actual ordered composition of successive local frame changes. -/
theorem pullback_composeChange (h : FrameChange D) (k : FrameChange (transformed D h)) :
    pullbackFrameChange D f (composeChange D h k) =
      composeChange (pullback D f) (pullbackFrameChange D f h)
        (pullbackFrameChange (transformed D h) f k) := rfl

variable {E'' H'' B''  : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace B''] [ChartedSpace H'' B'']

/-- Successive genuine smooth base changes give exactly the cocycle pulled back along their actual bundled composition. -/
theorem pullback_comp (g : C^n⟮K, B''; J, B'⟯) :
    pullback (pullback D f) g = pullback D (f.comp g) := rfl

/-- The actual local base maps compose exactly as the corresponding bundled smooth base maps do. -/
theorem localBaseMap_comp (g : C^n⟮K, B''; J, B'⟯) (i : ι)
    (x : (pullback (pullback D f) g).domain i) :
    localBaseMap D f i (localBaseMap (pullback D f) g i x) =
      localBaseMap D (f.comp g) i x := rfl

/-- Successive pullbacks of actual local frame changes agree exactly with pullback along the composed smooth base map. -/
theorem pullbackFrameChange_comp (g : C^n⟮K, B''; J, B'⟯) (h : FrameChange D) :
    pullbackFrameChange (pullback D f) g (pullbackFrameChange D f h) =
      pullbackFrameChange D (f.comp g) h := rfl

end FoliationQM.CocyclePullback
