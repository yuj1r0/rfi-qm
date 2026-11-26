module
public import FoliationQM.CocyclePullbackBundles
public import FoliationQM.CocyclePullbackFamilies
public import FoliationQM.CocycleGaugeSections

/-!
# Actual smooth sections under smooth base-map pullback

Source: the supplied-cocycle smooth-section interpretation of v13
`prop:takabayasi`. A genuine smooth base map constructs an actual
preimage-cover cocycle. Independently graph-defined smooth sections pull
back by the compatible local-family correspondence, with their actual
fiber value proved to be the original section evaluated at the base map.

The section graphs have the exact canonical bundle-map formula, and
actual realization, inverse quotient-valued reconstruction and invariant
density commute with pullback. No invertibility of an arbitrary base map
or smooth selection of cover indices is assumed. Both base manifolds have
the stated regularity; this does not identify abstract spacetime Spin data.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold
open Function Set Topology
namespace FoliationQM.CocyclePullbackSections
open DiracMatrices PolarSignQuotient SourcePolarProductQuotient
open PolarTransitionCocycle PolarCocycleBundles PolarCocycleSections
open CocyclePullback

variable {E H B E' H' B' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace B'] [ChartedSpace H' B'] {J : ModelWithCorners ℝ E' H'}
  {ι : Type*} {n : WithTop ℕ∞} (D : Data I B ι n)
  (f : C^n⟮J, B'; I, B⟯) [IsManifold I n B] [IsManifold J n B']

/-- An actual graph-smooth polar section pulls back to a graph-smooth section of the genuine preimage-cover cocycle bundle. -/
def polarSectionPullback (s : PolarSection D) : PolarSection (pullback D f) :=
  (PolarCocycleSections.polarFamilyEquiv (pullback D f)).symm
    (CocyclePullbackFamilies.polarFamilyPullback D f
      (PolarCocycleSections.polarFamilyEquiv D s))

/-- A graph-smooth represented-spinor section pulls back by actual local precomposition and the proved local-family-to-section correspondence. -/
def spinorSectionPullback (s : SpinorSection D) : SpinorSection (pullback D f) :=
  (PolarCocycleSections.spinorFamilyEquiv (pullback D f)).symm
    (CocyclePullbackFamilies.spinorFamilyPullback D f
      (PolarCocycleSections.spinorFamilyEquiv D s))

/-- The actual pulled-back polar section has precisely the original fiber value at the image base point. -/
theorem polarSectionPullback_apply (s : PolarSection D) (x : B') :
    (polarSectionPullback D f s).val x = s.val (f x) := by
  change ((polarCore D).localTriv (indexAt (pullback D f) x)
    (⟨f x, s.val (f x)⟩ : PolarTotal D)).2 = s.val (f x)
  exact (polarCore D).coordChange_self (indexAt D (f x)) (f x)
    (mem_domain_indexAt D (f x)) (s.val (f x))

/-- The actual represented-spinor pullback likewise evaluates to the original section at the actual base-map value. -/
theorem spinorSectionPullback_apply (s : SpinorSection D) (x : B') :
    (spinorSectionPullback D f s).val x = s.val (f x) := by
  change ((spinorCore D).localTriv (indexAt (pullback D f) x)
    (⟨f x, s.val (f x)⟩ : SpinorTotal D)).2 = s.val (f x)
  exact (spinorCore D).coordChange_self (indexAt D (f x)) (f x)
    (mem_domain_indexAt D (f x)) (s.val (f x))

/-- The canonical actual polar bundle pullback map carries the pulled-back section graph to the original graph evaluated at the base map. -/
theorem polarSectionPullback_graph (s : PolarSection D) (x : B') :
    CocyclePullbackBundles.polarMap D f
      (⟨x, (polarSectionPullback D f s).val x⟩ : PolarTotal (pullback D f)) =
      (⟨f x, s.val (f x)⟩ : PolarTotal D) := by
  change (⟨f x, (polarSectionPullback D f s).val x⟩ : PolarTotal D) = _
  rw [polarSectionPullback_apply]

/-- The canonical represented-spinor bundle pullback map has the exact analogous graph law. -/
theorem spinorSectionPullback_graph (s : SpinorSection D) (x : B') :
    CocyclePullbackBundles.spinorMap D f
      (⟨x, (spinorSectionPullback D f s).val x⟩ : SpinorTotal (pullback D f)) =
      (⟨f x, s.val (f x)⟩ : SpinorTotal D) := by
  change (⟨f x, (spinorSectionPullback D f s).val x⟩ : SpinorTotal D) = _
  rw [spinorSectionPullback_apply]

/-- Actual polar section realization commutes with pullback along any supplied smooth base map. -/
theorem realization_commutes (s : PolarSection D) :
    PolarCocycleSections.sectionEquiv (pullback D f) (polarSectionPullback D f s) =
      spinorSectionPullback D f (PolarCocycleSections.sectionEquiv D s) := by
  apply Subtype.ext
  funext x
  simp only [PolarCocycleSections.sectionEquiv_apply,
    polarSectionPullback_apply, spinorSectionPullback_apply]
  rfl

/-- Actual quotient-valued section reconstruction commutes with the same smooth base pullback. -/
theorem reconstruction_commutes (s : SpinorSection D) :
    (PolarCocycleSections.sectionEquiv (pullback D f)).symm (spinorSectionPullback D f s) =
      polarSectionPullback D f ((PolarCocycleSections.sectionEquiv D).symm s) := by
  apply Subtype.ext
  funext x
  simp only [PolarCocycleSections.sectionEquiv_symm_apply,
    polarSectionPullback_apply, spinorSectionPullback_apply]
  rfl

/-- Actual positive section density pulls back by ordinary composition with the supplied base map. -/
theorem polarSectionPullback_density (s : PolarSection D) (x : B') :
    ((polarSectionPullback D f s).val x).1 = (s.val (f x)).1 := by
  rw [polarSectionPullback_apply]

/-- The original bilinear spinor invariant density pulls back by the same actual base-map composition. -/
theorem spinorSectionPullback_density (s : SpinorSection D) (x : B') :
    SpinorRegularity.invariantDensity ((spinorSectionPullback D f s).val x).val =
      SpinorRegularity.invariantDensity (s.val (f x)).val := by
  rw [spinorSectionPullback_apply]

/-- Reading actual local coordinates after polar section pullback gives exactly the separately defined compatible local-family pullback. -/
theorem polarSectionPullback_family (s : PolarSection D) :
    PolarCocycleSections.polarFamilyEquiv (pullback D f) (polarSectionPullback D f s) =
      CocyclePullbackFamilies.polarFamilyPullback D f
        (PolarCocycleSections.polarFamilyEquiv D s) :=
  (PolarCocycleSections.polarFamilyEquiv (pullback D f)).apply_symm_apply _

/-- Actual local coordinates of the pulled-back represented-spinor section equal the independently constructed local-family pullback. -/
theorem spinorSectionPullback_family (s : SpinorSection D) :
    PolarCocycleSections.spinorFamilyEquiv (pullback D f) (spinorSectionPullback D f s) =
      CocyclePullbackFamilies.spinorFamilyPullback D f
        (PolarCocycleSections.spinorFamilyEquiv D s) :=
  (PolarCocycleSections.spinorFamilyEquiv (pullback D f)).apply_symm_apply _

/-- Pullback along the actual identity base map returns the same graph-smooth polar section. -/
theorem polarSectionPullback_id (s : PolarSection D) :
    polarSectionPullback D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) s = s := by
  apply Subtype.ext
  funext x
  exact polarSectionPullback_apply D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) s x

/-- Pullback along the actual identity base map returns the same graph-smooth represented-spinor section. -/
theorem spinorSectionPullback_id (s : SpinorSection D) :
    spinorSectionPullback D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) s = s := by
  apply Subtype.ext
  funext x
  exact spinorSectionPullback_apply D (ContMDiffMap.id : C^n⟮I, B; I, B⟯) s x

/-- Changing the local matrix frames and then pulling back gives precisely the same polar section as pulling back both the frame change and section first. -/
theorem polarSectionPullback_gauge (h : CocycleGaugeTransform.FrameChange D)
    (s : PolarSection D) :
    polarSectionPullback (CocycleGaugeTransform.transformed D h) f
      (CocycleGaugeSections.polarSectionEquiv D h s) =
    CocycleGaugeSections.polarSectionEquiv (pullback D f) (pullbackFrameChange D f h)
      (polarSectionPullback D f s) := by
  apply Subtype.ext
  funext x
  simp only [polarSectionPullback_apply, CocycleGaugeSections.polarSectionEquiv_apply]
  rfl

/-- Actual represented-spinor section gauge change commutes with pulling back the supplied local matrix frames and original section. -/
theorem spinorSectionPullback_gauge (h : CocycleGaugeTransform.FrameChange D)
    (s : SpinorSection D) :
    spinorSectionPullback (CocycleGaugeTransform.transformed D h) f
      (CocycleGaugeSections.spinorSectionEquiv D h s) =
    CocycleGaugeSections.spinorSectionEquiv (pullback D f) (pullbackFrameChange D f h)
      (spinorSectionPullback D f s) := by
  apply Subtype.ext
  funext x
  simp only [spinorSectionPullback_apply, CocycleGaugeSections.spinorSectionEquiv_apply]
  rfl

variable {E'' H'' B'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace B''] [ChartedSpace H'' B''] [IsManifold K n B'']

/-- Successive smooth base pullbacks of an actual polar section agree exactly with pullback by the composed actual base map. -/
theorem polarSectionPullback_comp (g : C^n⟮K, B''; J, B'⟯) (s : PolarSection D) :
    polarSectionPullback (pullback D f) g (polarSectionPullback D f s) =
      polarSectionPullback D (f.comp g) s := by
  apply Subtype.ext
  funext x
  simp only [polarSectionPullback_apply]
  rfl

/-- Successive pullbacks of a graph-smooth represented-spinor section agree exactly with pullback by the composed base map. -/
theorem spinorSectionPullback_comp (g : C^n⟮K, B''; J, B'⟯) (s : SpinorSection D) :
    spinorSectionPullback (pullback D f) g (spinorSectionPullback D f s) =
      spinorSectionPullback D (f.comp g) s := by
  apply Subtype.ext
  funext x
  simp only [spinorSectionPullback_apply]
  rfl

end FoliationQM.CocyclePullbackSections
