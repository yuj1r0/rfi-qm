module
public import FoliationQM.SpinorMatrixSmooth
public import FoliationQM.ReconstructedFrameGeometry
public import FoliationQM.MatrixDifferential
/-!
# Smoothness of the actual reconstructed real frame

Sources: v13 `prop:takabayasi` and `lem:maurer_cartan`.
The concrete sandwich is polynomial over the reals. Exact sign fibers
make the whole frame independent of the local angle branch. The two
open branches therefore prove smoothness on the entire regular domain.
No global smooth angle or abstract smooth quotient-bundle theorem is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
namespace FoliationQM.SpecialLinearFrameSmooth
open DiracMatrices DiracAdjoint SpinorMatrix SpecialLinearSpin SpecialLinearFrame SpinorMatrixSmooth

/-- Extraction of the four real gamma coefficients is an actual real continuous linear map. -/
def coefficientsCLM : Mat →L[ℝ] Covector :=
  ({ toFun := coefficients
     map_add' := by
       intro X Y
       funext i
       fin_cases i <;> simp [coefficients]
       ring
     map_smul' := by
       intro r X
       funext i
       fin_cases i <;> simp [coefficients] } : Mat →ₗ[ℝ] Covector).toContinuousLinearMap
/-- Each row of the actual sandwich frame is smooth in the full two-by-two matrix input. -/
theorem contDiff_frame_row (n : WithTop ℕ∞) (a : Fin 4) : ContDiff ℝ n (fun A : Mat2 => frame A a) := by
  exact coefficientsCLM.contDiff.comp (((contDiff_spin n).mul (contDiff_const (c := gamma a))).mul
    (MatrixDifferential.diracAdjointCLM.contDiff.comp (contDiff_spin n)))
/-- The whole actual sandwich frame is smooth in its two-by-two input. -/
theorem contDiff_frame (n : WithTop ℕ∞) : ContDiff ℝ n frame := by
  apply contDiff_pi.mpr
  intro a
  exact coefficientsCLM.contDiff.comp (((contDiff_spin n).mul (contDiff_const (c := gamma a))).mul
    (MatrixDifferential.diracAdjointCLM.contDiff.comp (contDiff_spin n)))
open ReconstructedFrameGeometry SpinorRegularity RegularPolarReconstruction
open PrincipalPolarSmooth RotatedPolarChart

/-- The actual rotated-branch frame is smooth throughout its open determinant domain. -/
theorem contDiffAt_rotatedFrame (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ RotatedDomain) : ContDiffAt ℝ n rotatedFrame psi :=
  (contDiff_frame n).contDiffAt.comp psi (contDiffAt_rotatedMatrix n hpsi)

/-- The reconstructed real frame is smooth at every regular spinor, including the principal angle cut. -/
theorem contDiffAt_reconstructedFrame (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : Regular psi) : ContDiffAt ℝ n reconstructedFrame psi := by
  rcases regular_two_chart_cover hpsi with hp | hr
  · exact (contDiff_frame n).contDiffAt.comp psi (contDiffAt_normalizedMatrix n hp)
  · have he : reconstructedFrame =ᶠ[𝓝 psi] rotatedFrame :=
      Filter.Eventually.mono (rotatedDomain_isOpen.mem_nhds hr) (fun q hq => (rotatedFrame_eq hq).symm)
    exact (contDiffAt_rotatedFrame n hr).congr_of_eventuallyEq he

/-- The entire reconstructed real frame is smooth on the strict regular domain. -/
theorem contDiffOn_reconstructedFrame (n : WithTop ℕ∞) :
    ContDiffOn ℝ n reconstructedFrame {psi | Regular psi} :=
  fun _ hpsi => (contDiffAt_reconstructedFrame n hpsi).contDiffWithinAt

/-- Every reconstructed real frame entry is smooth at a regular spinor. -/
theorem contDiffAt_reconstructedFrame_entry (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : Regular psi) (a mu : Fin 4) :
    ContDiffAt ℝ n (fun q => reconstructedFrame q a mu) psi :=
  contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_reconstructedFrame n hpsi) a) mu

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A smooth regular original spinor field has an actual equally smooth reconstructed real frame. -/
theorem contDiffAt_reconstructedFrame_comp (n : WithTop ℕ∞) {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ n psi x) (hreg : Regular (psi x)) :
    ContDiffAt ℝ n (fun y => reconstructedFrame (psi y)) x :=
  (contDiffAt_reconstructedFrame n hreg).comp x hpsi

end FoliationQM.SpecialLinearFrameSmooth
