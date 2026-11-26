module
public import FoliationQM.GlobalLorentzGaugeAtlas
public import FoliationQM.GeometricPrincipalSmoothAtlas
public import FoliationQM.CliffordSpinLorentzSmooth
public import FoliationQM.LorentzGroupManifold

/-!
# Smoothness of the whole-base Lorentz gauge charts

For the frame-bundle component of v13 `prop:takabayasi`, both actual charts
on the product Lorentz bundle retain the regularity of the supplied gauge.
The second chart and its inverse use smooth Lorentz multiplication and
inversion at the given order. In particular, the identity self-gauge gives
a smooth atlas at every order on the actual matrix group.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SmoothGlobalLorentzGaugeAtlas
open LorentzMatrixGroup CliffordSpinLorentzSmooth GlobalLorentzGaugeAtlas

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {n : WithTop ℕ∞} (k : C(B, ProperFutureLorentz)) (hk : ContMDiff I lorentzModel n k)

include hk in
/-- The forward chart of a smooth gauge is smooth on the whole product total space. -/
theorem smooth_forward (i : Bool) : ContMDiff (I.prod lorentzModel) (I.prod lorentzModel) n
    ((atlas k).triv i) := by
  cases i
  · rw [show ⇑((atlas k).triv false) = id from funext (triv_false k)]
    exact contMDiff_id
  · rw [show ⇑((atlas k).triv true) = fun p => (p.1, k p.1 * p.2) from funext (triv_true k)]
    exact contMDiff_fst.prodMk ((LorentzGroupManifold.contMDiff_mul n).comp
      ((hk.comp contMDiff_fst).prodMk contMDiff_snd))

include hk in
/-- The inverse of the gauged chart is smooth on the whole product. -/
theorem smooth_inverse (i : Bool) : ContMDiff (I.prod lorentzModel) (I.prod lorentzModel) n
    ((atlas k).triv i).toOpenPartialHomeomorph.symm := by
  cases i
  · rw [show ⇑((atlas k).triv false).toOpenPartialHomeomorph.symm = id from funext (symm_false k)]
    exact contMDiff_id
  · rw [show ⇑((atlas k).triv true).toOpenPartialHomeomorph.symm =
        fun p => (p.1, (k p.1)⁻¹ * p.2) from funext (symm_true k)]
    exact contMDiff_fst.prodMk ((LorentzGroupManifold.contMDiff_mul n).comp
      (((LorentzGroupManifold.contMDiff_inv n).comp (hk.comp contMDiff_fst)).prodMk contMDiff_snd))

include hk in
/-- The two actual principal trivializations determine a smooth atlas at the gauge order. -/
theorem smoothAtlas : GeometricPrincipalSmoothAtlas.Data I lorentzModel (I.prod lorentzModel)
    (atlas k) n where
  smooth_triv i := (smooth_forward k hk i).contMDiffOn
  smooth_symm i := (smooth_inverse k hk i).contMDiffOn

/-- The two charts obtained from the identity self-gauge are smooth at every order. -/
theorem identity_smoothAtlas (n : WithTop ℕ∞) :
    GeometricPrincipalSmoothAtlas.Data lorentzModel lorentzModel (lorentzModel.prod lorentzModel)
      (atlas (ContinuousMap.id ProperFutureLorentz)) n :=
  smoothAtlas _ (contMDiff_id : ContMDiff lorentzModel lorentzModel n id)

end FoliationQM.SmoothGlobalLorentzGaugeAtlas
