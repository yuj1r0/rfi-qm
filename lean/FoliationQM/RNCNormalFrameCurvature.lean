module

public import FoliationQM.RNCRicciHalfDensity
public import FoliationQM.RNCLorentzContraction

/-!
# Curvature consistency between centered Lorentz normal frames

For two normal-coordinate descriptions related near the origin by a linear
Lorentz frame change, the actual determinant weights agree after pullback.
Their Hessians therefore transform the Ricci tensor by congruence. The signed
trace gives the same scalar curvature in both frames.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.RNCNormalFrameCurvature

open LorentzMatrixGroup RNCLorentzContraction RNCVolumeDensity RNCHalfDensityJet
open RNCNormalChart RNCRicciHalfDensity RNCCoordinateCurvature Filter Matrix

/-- A Lorentz congruence leaves the actual determinant half-density factor unchanged. -/
theorem weight_congruence (G M : Mat4) (hM : M.transpose * eta * M = eta) :
    metricWeight (M.transpose * G * M) = metricWeight G := by
  have he : (M.transpose * G * M).det = G.det := by
    calc
      _ = (M.det ^ 2) * G.det := by simp only [Matrix.det_mul, Matrix.det_transpose]; ring
      _ = _ := by rw [det_sq_of_metric M hM, one_mul]
  simp only [metricWeight, volumeFactor, he]

/-- A linear pullback acts on both actual Hessian arguments at the origin. -/
theorem hessian_linear_pullback {f : Covector → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (L : Covector →L[ℝ] Covector) (u v : Covector) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) 0 u v = fderiv ℝ (fderiv ℝ f) 0 (L u) (L v) := by
  have hf' : ContDiffAt ℝ 2 f (L 0) := by simpa only [map_zero] using hf
  have he : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.hasFDerivAt.fderiv
  rw [RNCCriticalComposition.hessian_comp L.contDiff.contDiffAt hf', he]
  simp only [map_zero, fderiv_const_apply, _root_.zero_apply, zero_add]

/-- Ricci applied to arbitrary directions equals minus six times the determinant weight's actual Hessian. -/
theorem ricci_pairing {g : Covector → Mat4} (h : IsNormal g) (hg : ContDiffAt ℝ 2 g 0)
    (u v : Covector) :
    form (ricci g 0) u v = -6 * fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 u v := by
  rw [full_hessian h hg, hessian_apply,
    RNCConnectionCyclic.form_symmetric (ricci_symmetric h hg) v u]
  ring

/-- The Ricci tensor calculated separately from the two metrics transforms by congruence in overlapping normal frames. -/
theorem ricci_transform {g k : Covector → Mat4} (hg : IsNormal g) (hk : IsNormal k)
    (hgs : ContDiffAt ℝ 2 g 0) (hks : ContDiffAt ℝ 2 k 0)
    (M : Mat4) (hM : M.transpose * eta * M = eta)
    (hchange : ∀ᶠ y in 𝓝 0, k y = M.transpose * g (M.mulVec y) * M) :
    ricci k 0 = M.transpose * ricci g 0 * M := by
  let L : Covector →L[ℝ] Covector := M.mulVecLin.toContinuousLinearMap
  have he : (metricWeight ∘ k) =ᶠ[𝓝 0] ((metricWeight ∘ g) ∘ L) := by
    filter_upwards [hchange] with y hy
    change metricWeight (k y) = metricWeight (g (M.mulVec y))
    rw [hy, weight_congruence _ _ hM]
  have hh := (he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  ext i j
  let u : Covector := Pi.single i 1
  let v : Covector := Pi.single j 1
  calc
    _ = form (ricci k 0) u v := (form_basis (ricci k 0) i j).symm
    _ = -6 * fderiv ℝ (fderiv ℝ ((metricWeight ∘ g) ∘ L)) 0 u v := by
      rw [ricci_pairing hk hks, hh]
    _ = -6 * fderiv ℝ (fderiv ℝ (metricWeight ∘ g)) 0 (L u) (L v) := by
      rw [hessian_linear_pullback (weight_contDiff hg hgs)]
    _ = form (ricci g 0) (L u) (L v) := (ricci_pairing hg hgs _ _).symm
    _ = form (M.transpose * ricci g 0 * M) u v := form_pullback _ M u v
    _ = _ := form_basis _ i j

/-- The scalar curvature obtained from the full coordinate connection is independent of the overlapping Lorentz normal frame. -/
theorem scalar_transform {g k : Covector → Mat4} (hg : IsNormal g) (hk : IsNormal k)
    (hgs : ContDiffAt ℝ 2 g 0) (hks : ContDiffAt ℝ 2 k 0)
    (M : Mat4) (hM : M.transpose * eta * M = eta)
    (hchange : ∀ᶠ y in 𝓝 0, k y = M.transpose * g (M.mulVec y) * M) :
    scalar k 0 = scalar g 0 := by
  rw [scalar_center hk, scalar_center hg, ricci_transform hg hk hgs hks M hM hchange]
  exact (contract_diagonal _).symm.trans ((contract_congruence _ M hM).trans (contract_diagonal _))

end FoliationQM.RNCNormalFrameCurvature
