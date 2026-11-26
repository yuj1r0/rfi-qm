module
public import FoliationQM.CocycleGaugeBundles
public import FoliationQM.CocyclePullbackBundles

/-!
# Global smooth positive density on the actual cocycle total spaces

Source: the positive scalar density in the supplied-cocycle interpretation
of v13 `prop:takabayasi`. Actual polar and represented-spinor transitions
preserve the density before any smoothness is claimed. Their genuine local
trivializations therefore identify the selected-coordinate functions below
with the ordinary fiber density in every chart. Local bundle smoothness then
proves globally smooth positive density on the existing total spaces.

The represented density is exactly the original real spinor bilinear
invariant. Actual realization, supplied local frame changes, and canonical
smooth base pullback maps preserve these global functions. All constructions
retain the supplied cocycle, actual core topology, and independent total
atlas; no smoothness of the selected index or global frame choice is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator Manifold
open Set Topology
namespace FoliationQM.CocycleBundleDensity
open DiracMatrices PolarAmplitudeTopology PolarTransitionCocycle PolarCocycleBundles
open PolarCocycleManifold SourcePolarProductQuotient CocycleGaugeTransform CocyclePullback

variable {E H B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace B] [ChartedSpace H B] {n : WithTop ℕ∞}
  (D : Data I B ι n)

/-- The actual polar total-space density is its positive density coordinate in the selected fiber. -/
def polarDensity (p : PolarTotal D) : PositiveDensity := p.2.1

/-- The actual represented total-space density is the recovered positive density of its selected regular-spinor fiber. -/
def spinorDensity (q : SpinorTotal D) : PositiveDensity := DensityFrameFields.density q.2

/-- The global polar density has the literal selected-fiber coordinate formula. -/
theorem polarDensity_apply (p : PolarTotal D) : polarDensity D p = p.2.1 := rfl

/-- The represented global density is actual positive-density recovery in the selected fiber. -/
theorem spinorDensity_apply (q : SpinorTotal D) :
    spinorDensity D q = DensityFrameFields.density q.2 := rfl

/-- The real value of represented total-space density is precisely the original bilinear invariant density. -/
theorem spinorDensity_value (q : SpinorTotal D) :
    (spinorDensity D q : ℝ) = SpinorRegularity.invariantDensity q.2.val :=
  DensityFrameFields.density_value_eq_invariantDensity q.2

/-- Actual density preservation by polar transition actions makes every local fiber density agree with the global function. -/
theorem localTriv_polarDensity (i : ι) (p : PolarTotal D) :
    ((polarCore D).localTriv i p).2.1 = polarDensity D p := by
  rw [FiberBundleCore.localTriv_apply]
  exact DensityFrameAction.productAction_density
    (D.transition (indexAt D p.proj) i p.proj) p.2

/-- The actual represented transition preserves recovered positive density in every local trivialization. -/
theorem localTriv_spinorDensity (i : ι) (q : SpinorTotal D) :
    DensityFrameFields.density (((spinorCore D).localTriv i) q).2 =
      spinorDensity D q := by
  rw [FiberBundleCore.localTriv_apply]
  exact RegularSpinorAction.density_act
    (D.transition (indexAt D q.proj) i q.proj) q.2

/-- Actual total-space realization preserves the global positive density exactly. -/
theorem spinorDensity_realization (p : PolarTotal D) :
    spinorDensity D (totalRealization D p) = polarDensity D p := by
  change (productRegularHomeomorph.symm (productRegularHomeomorph p.2)).1 = p.2.1
  rw [productRegularHomeomorph.symm_apply_apply]

/-- Actual inverse total-space realization recovers exactly the represented global density. -/
theorem polarDensity_reconstruction (q : SpinorTotal D) :
    polarDensity D ((totalRealization D).symm q) = spinorDensity D q := rfl

section Smooth
variable [IsManifold I n B]

/-- The actual polar total-space density is globally smooth, proved from its genuine local-trivialization formula. -/
theorem contMDiff_polarDensity :
    ContMDiff (polarModel I) 𝓘(ℝ, ℝ) n (polarDensity D) := by
  intro p
  let i := indexAt D p.proj
  have hp : p ∈ ((polarCore D).localTriv i).source := mem_domain_indexAt D p.proj
  have ht := (contMDiffOn_polar_localTriv D i).contMDiffAt
    (((polarCore D).localTriv i).open_source.mem_nhds hp)
  apply ht.snd.fst.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun q => (localTriv_polarDensity D i q).symm)

/-- The represented total-space density is globally smooth through the independently smooth inverse realization and the proved actual density identity. -/
theorem contMDiff_spinorDensity :
    ContMDiff (spinorModel I) 𝓘(ℝ, ℝ) n (spinorDensity D) := by
  exact (contMDiff_polarDensity D).comp (contMDiff_totalRealization_symm D)

/-- The real positive-density value is globally smooth on the actual polar total space. -/
theorem contMDiff_polarDensity_value :
    ContMDiff (polarModel I) 𝓘(ℝ, ℝ) n (fun p => (polarDensity D p : ℝ)) :=
  (PolarScalarManifolds.contMDiff_density_value n).comp (contMDiff_polarDensity D)

/-- The original real spinor bilinear invariant is globally smooth on the actual represented total space. -/
theorem contMDiff_spinorDensity_value :
    ContMDiff (spinorModel I) 𝓘(ℝ, ℝ) n
      (fun q : SpinorTotal D => SpinorRegularity.invariantDensity q.2.val) := by
  have ht := (PolarScalarManifolds.contMDiff_density_value n).comp (contMDiff_spinorDensity D)
  simpa only [Function.comp_def, spinorDensity_value] using ht
end Smooth

/-- Every supplied local frame change preserves the global actual polar total-space density. -/
theorem polarDensity_gauge (h : FrameChange D) (p : PolarTotal D) :
    polarDensity (transformed D h) (CocycleGaugeBundles.polarMap D h p) =
      polarDensity D p := rfl

/-- Every actual represented local frame change preserves the global positive spinor density. -/
theorem spinorDensity_gauge (h : FrameChange D) (q : SpinorTotal D) :
    spinorDensity (transformed D h) (CocycleGaugeBundles.spinorMap D h q) =
      spinorDensity D q :=
  RegularSpinorAction.density_act (h.value (indexAt D q.proj) q.proj) q.2

/-- The actual inverse polar frame change also preserves global positive density. -/
theorem polarDensity_gauge_inverse (h : FrameChange D) (p : PolarTotal (transformed D h)) :
    polarDensity D (CocycleGaugeBundles.polarInvMap D h p) =
      polarDensity (transformed D h) p := rfl

/-- The actual inverse represented frame change preserves recovered positive density. -/
theorem spinorDensity_gauge_inverse (h : FrameChange D) (q : SpinorTotal (transformed D h)) :
    spinorDensity D (CocycleGaugeBundles.spinorInvMap D h q) =
      spinorDensity (transformed D h) q :=
  RegularSpinorAction.density_act (h.value (indexAt D q.proj) q.proj)⁻¹ q.2

variable {E' H' B' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace B'] [ChartedSpace H' B']
  (f : C^n⟮J, B'; I, B⟯)

/-- The canonical smooth base-pullback map preserves the actual polar total-space density without an invertibility premise. -/
theorem polarDensity_pullback (p : PolarTotal (pullback D f)) :
    polarDensity D (CocyclePullbackBundles.polarMap D f p) =
      polarDensity (pullback D f) p := rfl

/-- The canonical represented-spinor base-pullback map preserves the actual global positive density. -/
theorem spinorDensity_pullback (q : SpinorTotal (pullback D f)) :
    spinorDensity D (CocyclePullbackBundles.spinorMap D f q) =
      spinorDensity (pullback D f) q := rfl

end FoliationQM.CocycleBundleDensity
