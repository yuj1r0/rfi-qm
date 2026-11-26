module
public import FoliationQM.ReconstructedFrameGeometry
public import FoliationQM.LocalPolarFields
public import FoliationQM.SpecialLinearRicci
/-!
# The canonical original-spinor frame and its actual connection

Sources: v13 `prop:takabayasi` and `lem:maurer_cartan`.
Exact polar fibers prove that every positive-density determinant-one polar
representative gives the canonical real frame of the original spinor.
Local equality then transfers genuine frame derivatives and the derived
Ricci coefficients. These coefficients do not depend on the local polar
choice. The final theorem constructs the local factors from C1 regularity
of the original field alone. No frame or generator expansion is supplied.
Abstract Spin covering, global smooth quotient bundles and integrated
variational dynamics remain separate from this local concrete result.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
open Filter Topology
namespace FoliationQM.ReconstructedFrameConnection
open DiracMatrices SpinorMatrix SpinorRegularity SpecialLinearSpin
open PolarSpinorBilinears RegularPolarReconstruction ReconstructedFrameGeometry
open SpecialLinearFrameLaws LocalPolarFields SpecialLinearConnection RealLorentzFrame

/-- Every positive-density determinant-one polar representative gives the canonical real frame of its actual spinor. -/
theorem reconstructedFrame_of_polar (rho beta : ℝ) (A : Mat2)
    (hrho : 0 < rho) (hA : A.det = 1) :
    reconstructedFrame (polarSpinor rho beta (spin A)) = SpecialLinearFrame.frame A := by
  let psi := polarSpinor rho beta (spin A)
  have hreg : Regular psi := regular_polar_of_pos rho beta (spin A) hrho
    (spin_dirac_isometry A hA) (spin_gamma5_commute A)
  have hd : invariantDensity psi = rho := invariantDensity_polar rho beta (spin A) hrho.le
    (spin_dirac_isometry A hA) (spin_gamma5_commute A)
  have heq : polarSpinor rho beta (spin A) =
      polarSpinor rho (determinantPhase psi) (spin (normalizedMatrix psi)) := by
    simpa only [hd, reconstructedSpin] using regular_reconstruction hreg
  rcases (PolarAngleFibers.polarSpinor_fixedDensity_phase_fibers rho beta
    (determinantPhase psi) A (normalizedMatrix psi) hrho hA (normalizedMatrix_det hreg)).mp heq with h | h
  · change SpecialLinearFrame.frame (normalizedMatrix psi) = SpecialLinearFrame.frame A
    rw [h.2]
  · change SpecialLinearFrame.frame (normalizedMatrix psi) = SpecialLinearFrame.frame A
    rw [h.2, frame_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
/-- Actual local polar equality identifies the canonical original-spinor frame with the constructed matrix frame on a neighborhood. -/
theorem eventually_frame_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y))) :
    (fun y => reconstructedFrame (psi y)) =ᶠ[𝓝 x] (fun y => SpecialLinearFrame.frame (A y)) := by
  filter_upwards [he] with y hy
  rw [hy.2.2, reconstructedFrame_of_polar _ _ _ hy.1 hy.2.1]
omit [NormedSpace ℝ E] in
/-- The canonical frame of an actual locally reconstructed spinor equals its matrix frame at the point. -/
theorem frame_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y))) :
    reconstructedFrame (psi x) = SpecialLinearFrame.frame (A x) :=
  (eventually_frame_of_local_polar he).eq_of_nhds

/-- Actual local polar equality transfers the whole real frame Frechet derivative by neighborhood equality. -/
theorem fderiv_frame_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E}
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y))) :
    fderiv ℝ (fun y => reconstructedFrame (psi y)) x =
      fderiv ℝ (fun y => SpecialLinearFrame.frame (A y)) x :=
  (eventually_frame_of_local_polar he).fderiv_eq
/-- Every smooth regular original field has locally reconstructing polar factors with exactly its canonical real frame. -/
theorem exists_local_frame_fields (n : WithTop ℕ∞) {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ n psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ n beta x ∧ ContDiffAt ℝ n A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      ((fun y => reconstructedFrame (psi y)) =ᶠ[𝓝 x]
        (fun y => SpecialLinearFrame.frame (A y))) := by
  obtain ⟨beta, A, _hrho, hbeta, hA, _hL, he⟩ := exists_local_polar_fields n hpsi hreg
  exact ⟨beta, A, hbeta, hA, he, eventually_frame_of_local_polar he⟩
/-- The canonical original-spinor frame row has the actual connection transport derivative from any differentiable local polar reconstruction. -/
theorem fderiv_reconstructed_frame_row {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E} (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y))) (v : E) (a : Fin 4) :
    fderiv ℝ (fun y => reconstructedFrame (psi y) a) x v =
      fun mu => ∑ b, bodyOmega A x v b a * sign a * reconstructedFrame (psi x) b mu := by
  have hrow : (fun y => reconstructedFrame (psi y) a) =ᶠ[𝓝 x]
      (fun y => SpecialLinearFrame.frame (A y) a) :=
    (eventually_frame_of_local_polar he).mono (fun _ h => congrFun h a)
  rw [hrow.fderiv_eq, frame_of_local_polar he]
  exact SpecialLinearRicci.fderiv_frame_row hA (he.mono (fun _ h => h.2.1)) v a

/-- The actual derivative of the canonical original-spinor frame recovers the derived body coefficient with both metric signs. -/
theorem ricci_rotation_of_local_polar {psi : E → Spinor} {rho beta : E → ℝ}
    {A : E → Mat2} {x : E} (hA : DifferentiableAt ℝ A x)
    (he : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y))) (v : E) (d e : Fin 4) :
    bodyOmega A x v d e = sign d * sign e *
      (∑ mu, sign mu * reconstructedFrame (psi x) d mu *
        fderiv ℝ (fun y => reconstructedFrame (psi y) e mu) x v) := by
  have hd (mu : Fin 4) : fderiv ℝ (fun y => reconstructedFrame (psi y) e mu) x =
      fderiv ℝ (fun y => SpecialLinearFrame.frame (A y) e mu) x := by
    have heq : (fun y => reconstructedFrame (psi y) e mu) =ᶠ[𝓝 x]
        (fun y => SpecialLinearFrame.frame (A y) e mu) :=
      (eventually_frame_of_local_polar he).mono (fun _ h => congrFun (congrFun h e) mu)
    exact heq.fderiv_eq
  simp_rw [hd]
  rw [frame_of_local_polar he]
  exact SpecialLinearRicci.ricci_rotation hA (he.mono (fun _ h => h.2.1)) v d e

/-- Two differentiable local polar reconstructions of the same original spinor field give identical actual body coefficients. -/
theorem bodyOmega_eq_of_local_polar {psi : E → Spinor}
    {rho beta eta theta : E → ℝ} {A B : E → Mat2} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (heA : ∀ᶠ y in 𝓝 x, 0 < rho y ∧ (A y).det = 1 ∧
      psi y = polarSpinor (rho y) (beta y) (spin (A y)))
    (heB : ∀ᶠ y in 𝓝 x, 0 < eta y ∧ (B y).det = 1 ∧
      psi y = polarSpinor (eta y) (theta y) (spin (B y))) (v : E) :
    bodyOmega A x v = bodyOmega B x v := by
  funext d e
  rw [ricci_rotation_of_local_polar hA heA v d e, ricci_rotation_of_local_polar hB heB v d e]

/-- Every C1 regular original spinor field has constructed local polar factors whose actual coefficients give canonical-frame transport and Ricci contraction. -/
theorem exists_reconstructed_frame_connection {psi : E → Spinor} {x : E}
    (hpsi : ContDiffAt ℝ 1 psi x) (hreg : Regular (psi x)) :
    ∃ (beta : E → ℝ) (A : E → Mat2),
      ContDiffAt ℝ 1 beta x ∧ ContDiffAt ℝ 1 A x ∧
      (∀ᶠ y in 𝓝 x, 0 < invariantDensity (psi y) ∧ (A y).det = 1 ∧
        psi y = polarSpinor (invariantDensity (psi y)) (beta y) (spin (A y))) ∧
      (∀ v a, fderiv ℝ (fun y => reconstructedFrame (psi y) a) x v =
        fun mu => ∑ b, bodyOmega A x v b a * sign a * reconstructedFrame (psi x) b mu) ∧
      (∀ v d e, bodyOmega A x v d e = sign d * sign e *
        (∑ mu, sign mu * reconstructedFrame (psi x) d mu *
          fderiv ℝ (fun y => reconstructedFrame (psi y) e mu) x v)) := by
  obtain ⟨beta, A, _hrho, hbeta, hA, _hL, he⟩ := exists_local_polar_fields 1 hpsi hreg
  exact ⟨beta, A, hbeta, hA, he,
    fderiv_reconstructed_frame_row hA.differentiableAt_one he,
    ricci_rotation_of_local_polar hA.differentiableAt_one he⟩
end FoliationQM.ReconstructedFrameConnection
