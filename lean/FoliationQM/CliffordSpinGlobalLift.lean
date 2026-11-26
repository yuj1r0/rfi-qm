module
public import FoliationQM.CliffordSpinUniversalCover
public import FoliationQM.CliffordSpinLorentzFields

/-!
# Global anchored genuine Spin lifts on simply connected bases

Source scope: the global lifting component of the actual Spin/Lorentz
field correspondence in v13 `prop:takabayasi` and `eq:tetrad_rotor_map`.
A continuous Lorentz field on a simply connected, locally path-connected
base has a unique global individual Clifford Spin lift through every
prescribed compatible anchor. The actual covering-space lifting theorem
constructs this field; no global individual lift is an input.

For every differentiability order, a bundled smooth Lorentz field has
the same genuine global lift, now proved smooth using the established
local-diffeomorphism regularity theorem. Its quotient class agrees
exactly with the earlier globally recovered sign-class field. The
charted base need not have an additional manifold hypothesis.

Simple connectivity and local path connectivity are explicit source
hypotheses. These conclusions do not give a global section of the
Lorentz group, lift arbitrary Lorentz transition cocycles, or assert
existence of geometric spacetime Spin structures or dynamics.
-/

@[expose] public section
noncomputable section
open scoped Topology Manifold
namespace FoliationQM.CliffordSpinGlobalLift
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup

/-- The genuine Clifford Spin model used for individual lifted fields. -/
abbrev spinModel := CliffordSpinLorentzSmooth.spinModel

/-- The independent Lorentz Cayley model used for the given physical fields. -/
abbrev lorentzModel := CliffordSpinLorentzSmooth.lorentzModel

section ContinuousLifts
variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
  [LocallyPathConnectedSpace X]

/-- Every continuous Lorentz field on a simply connected locally path-connected base has exactly one global actual Spin lift through any prescribed compatible value. -/
theorem existsUnique_continuousLift (L : C(X, ProperFutureLorentz))
    (x0 : X) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    ∃! f : C(X, Spin), f x0 = s0 ∧ lorentzHom ∘ f = L :=
  lorentzHom_isCoveringMap.existsUnique_continuousMap_lifts L x0 s0 hs

/-- The genuine global continuous Spin lift specified by its Lorentz field and one compatible anchor. -/
def continuousLift (L : C(X, ProperFutureLorentz))
    (x0 : X) (s0 : Spin) (hs : lorentzHom s0 = L x0) : C(X, Spin) :=
  (existsUnique_continuousLift L x0 s0 hs).choose

/-- The global continuous lift takes exactly its prescribed actual Clifford Spin value at the anchor. -/
theorem continuousLift_at (L : C(X, ProperFutureLorentz))
    (x0 : X) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    continuousLift L x0 s0 hs x0 = s0 :=
  (existsUnique_continuousLift L x0 s0 hs).choose_spec.1.1

/-- The actual physical Lorentz projection of the constructed global continuous lift is the entire given field. -/
theorem projection_continuousLift (L : C(X, ProperFutureLorentz))
    (x0 : X) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    lorentzHom ∘ continuousLift L x0 s0 hs = L :=
  (existsUnique_continuousLift L x0 s0 hs).choose_spec.1.2

/-- Any global continuous actual Spin field with the same physical projection and anchor equals the constructed lift. -/
theorem continuousLift_unique (L : C(X, ProperFutureLorentz))
    (x0 : X) (s0 : Spin) (hs : lorentzHom s0 = L x0)
    (f : C(X, Spin)) (hf0 : f x0 = s0) (hf : lorentzHom ∘ f = L) :
    f = continuousLift L x0 s0 hs :=
  (existsUnique_continuousLift L x0 s0 hs).choose_spec.2 f ⟨hf0, hf⟩

end ContinuousLifts

section SmoothLifts
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
  {n : WithTop ℕ∞}

/-- The constructed continuous global lift of any smooth Lorentz field is genuinely smooth to the same order by the actual covering's local-diffeomorphism regularity. -/
theorem contMDiff_continuousLift (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    ContMDiff I spinModel n (continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs) :=
  CliffordSpinLorentzFields.continuous_lift_contMDiff
    (continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs).continuous L.contMDiff
      (projection_continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs)

/-- The same anchored actual global Spin lift, bundled with its proved smoothness for an arbitrary stated order. -/
def smoothLift (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) : C^n⟮I, M; spinModel, Spin⟯ :=
  ⟨continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs, contMDiff_continuousLift L x0 s0 hs⟩

/-- The smooth lift retains exactly the original anchored continuous lift pointwise, with no second lift choice. -/
theorem smoothLift_apply (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) (x : M) :
    smoothLift L x0 s0 hs x = continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs x := rfl

/-- The bundled global smooth Spin lift returns precisely its prescribed anchor. -/
theorem smoothLift_at (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    smoothLift L x0 s0 hs x0 = s0 := continuousLift_at ⟨L, L.contMDiff.continuous⟩ x0 s0 hs

/-- The actual Lorentz projection of the bundled global smooth Spin lift is exactly the given smooth field. -/
theorem projection_smoothLift (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    lorentzHom ∘ smoothLift L x0 s0 hs = L :=
  projection_continuousLift ⟨L, L.contMDiff.continuous⟩ x0 s0 hs

/-- Every bundled smooth global actual Spin field with the stated physical projection and anchor is the constructed lift. -/
theorem smoothLift_unique (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0)
    (f : C^n⟮I, M; spinModel, Spin⟯) (hf0 : f x0 = s0) (hf : lorentzHom ∘ f = L) :
    f = smoothLift L x0 s0 hs := by
  apply ContMDiffMap.coe_injective
  exact congrArg (fun g : C(M, Spin) => (g : M → Spin))
    (continuousLift_unique ⟨L, L.contMDiff.continuous⟩ x0 s0 hs ⟨f, f.contMDiff.continuous⟩ hf0 hf)

/-- Every smooth Lorentz field on an explicitly simply connected locally path-connected charted base has exactly one bundled global individual Spin lift through a prescribed compatible anchor. -/
theorem existsUnique_smoothLift (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) :
    ∃! f : C^n⟮I, M; spinModel, Spin⟯, f x0 = s0 ∧ lorentzHom ∘ f = L :=
  ⟨smoothLift L x0 s0 hs, ⟨smoothLift_at L x0 s0 hs, projection_smoothLift L x0 s0 hs⟩,
    fun f hf => smoothLift_unique L x0 s0 hs f hf.1 hf.2⟩

/-- The global individual Spin lift represents exactly the earlier globally recovered actual sign-class field at every source point. -/
theorem quotient_smoothLift (L : C^n⟮I, M; lorentzModel, ProperFutureLorentz⟯)
    (x0 : M) (s0 : Spin) (hs : lorentzHom s0 = L x0) (x : M) :
    (QuotientGroup.mk (smoothLift L x0 s0 hs x) : SignQuotient) =
      CliffordSpinLorentzFields.classOf (L x) := by
  calc
    (QuotientGroup.mk (smoothLift L x0 s0 hs x) : SignQuotient) =
        CliffordSpinLorentzFields.classOf (lorentzHom (smoothLift L x0 s0 hs x)) :=
      (CliffordSpinLorentzFields.classOf_image _).symm
    _ = CliffordSpinLorentzFields.classOf (L x) :=
      congrArg CliffordSpinLorentzFields.classOf (congrFun (projection_smoothLift L x0 s0 hs) x)

end SmoothLifts
end FoliationQM.CliffordSpinGlobalLift
