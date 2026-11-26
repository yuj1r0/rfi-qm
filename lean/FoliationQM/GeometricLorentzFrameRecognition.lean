module
public import FoliationQM.GeometricLorentzFrame
public import FoliationQM.LorentzFutureCone

/-!
# Recognition of geometric Lorentz frames from one future vector

Source scope: the geometric tangent-frame bridge underlying v13
`prop:takabayasi`. An existing pointwise geometric Lorentz frame witnesses
Lorentz signature and identifies the specified future cone. It implies
symmetry and nondegeneracy of the original bilinear metric. A second actual
basis with Gram matrix (+---), the specified orientation, and future zeroth
vector is proved to identify the entire future cone. This recognition uses
the intrinsic metric-preserving matrix criterion, without a Spin-image or
smooth-frame hypothesis. No local or global smooth tetrad is constructed here.
-/

@[expose] public section
noncomputable section
open Matrix
namespace FoliationQM.GeometricLorentzFrameRecognition
open GeometricLorentzFrame LorentzMatrixGroup RealLorentzFrame

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {g : LinearMap.BilinForm ℝ V} {orientation : Orientation ℝ V (Fin 4)}
  {future : Set V}

/-- A genuine pointwise Lorentz frame forces symmetry of the original geometric bilinear metric. -/
theorem metric_symm (e : Frame g orientation future) : g.IsSymm := by
  constructor
  intro x y
  have hxy := metric_coordinates e (e.basis.equivFun x) (e.basis.equivFun y)
  have hyx := metric_coordinates e (e.basis.equivFun y) (e.basis.equivFun x)
  simp only [LinearEquiv.symm_apply_apply] at hxy hyx
  rw [hxy, hyx]
  unfold minkowski
  ring

/-- A genuine pointwise Lorentz frame forces both left and right nondegeneracy of the original metric. -/
theorem metric_nondegenerate (e : Frame g orientation future) : g.Nondegenerate := by
  have hr : ∀ x : V, (∀ y : V, g y x = 0) → x = 0 := by
    intro x hx
    apply e.basis.repr.injective
    ext i
    simp [repr_eq_signed_metric e, hx]
  exact ⟨fun x hx => hr x (fun y => (metric_symm e).eq y x |>.trans (hx y)), hr⟩

/-- Membership in the specified future cone is exactly the intrinsic future condition on coordinates in the existing geometric frame. -/
theorem mem_future_iff_coordinates (e : Frame g orientation future) (v : V) :
    v ∈ future ↔ futureCone (e.basis.equivFun v) := by
  simpa only [LinearEquiv.symm_apply_apply] using e.future_iff (e.basis.equivFun v)

/-- Any actual eta-normalized basis has a metric-preserving change matrix into the existing geometric frame. -/
theorem basis_change_metric (e : Frame g orientation future)
    (b : Module.Basis (Fin 4) ℝ V) (hb : g.toMatrix b = eta) :
    (e.basis.toMatrix b).transpose * eta * e.basis.toMatrix b = eta := by
  simpa only [e.metric, hb] using g.toMatrix_mul_basis_toMatrix e.basis b

/-- A future zeroth basis vector gives strictly positive temporal entry in the actual change-of-basis matrix. -/
theorem basis_change_time_pos (e : Frame g orientation future)
    (b : Module.Basis (Fin 4) ℝ V) (hfuture : b 0 ∈ future) :
    0 < e.basis.toMatrix b 0 0 := by
  have h := ((mem_future_iff_coordinates e (b 0)).mp hfuture).1
  simpa only [Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply] using h

/-- Metric normalization and a future zeroth vector imply preservation of the entire model future timelike cone by the actual change matrix. -/
theorem basis_change_preservesFutureCone (e : Frame g orientation future)
    (b : Module.Basis (Fin 4) ℝ V) (hb : g.toMatrix b = eta)
    (hfuture : b 0 ∈ future) : preservesFutureCone (e.basis.toMatrix b) :=
  (LorentzFutureCone.preserves_futureCone_iff_time_pos _ (basis_change_metric e b hb)).mpr
    (basis_change_time_pos e b hfuture)

/-- An eta-normalized basis with a future zeroth vector identifies the entire specified geometric future cone, without assuming this full cone identity. -/
theorem basis_future_iff (e : Frame g orientation future)
    (b : Module.Basis (Fin 4) ℝ V) (hb : g.toMatrix b = eta)
    (hfuture : b 0 ∈ future) (v : Covector) :
    b.equivFun.symm v ∈ future ↔ futureCone v := by
  rw [mem_future_iff_coordinates e]
  have hc : e.basis.toMatrix b *ᵥ v = e.basis.equivFun (b.equivFun.symm v) := by
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
      (b.toMatrix_mulVec_repr e.basis (b.equivFun.symm v))
  rw [← hc]
  exact basis_change_preservesFutureCone e b hb hfuture v

/-- An actual eta-normalized basis with the specified orientation and future zeroth vector is a genuine geometric Lorentz frame; full future-cone compatibility is derived. -/
def ofBasis (e : Frame g orientation future) (b : Module.Basis (Fin 4) ℝ V)
    (hb : g.toMatrix b = eta) (ho : b.orientation = orientation)
    (hfuture : b 0 ∈ future) : Frame g orientation future where
  basis := b
  metric := hb
  oriented := ho
  future_iff := basis_future_iff e b hb hfuture

/-- Frame recognition retains precisely the supplied actual basis vectors. -/
theorem ofBasis_basis (e : Frame g orientation future) (b : Module.Basis (Fin 4) ℝ V)
    (hb : g.toMatrix b = eta) (ho : b.orientation = orientation)
    (hfuture : b 0 ∈ future) : (ofBasis e b hb ho hfuture).basis = b := rfl

end FoliationQM.GeometricLorentzFrameRecognition
