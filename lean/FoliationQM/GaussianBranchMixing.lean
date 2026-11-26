module

public import FoliationQM.GaussianKGInitialJet

/-!
# Real-linear combinations of massive Fourier branches

For the two Cauchy data in v13's free-Gaussian clause (line 767), the real
part of one positive-frequency wave supplies the initial position, and the
imaginary part of a second supplies the independently prescribed velocity.
The Klein–Gordon operator has real coefficients and commutes with this
combination of the two actual spacetime fields.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.GaussianBranchMixing
open PolarSecondDifferential GaussianCauchySlice OsmoticSliceFields
open scoped ContDiff

/-- Take the real part of the first branch and subtract z times the imaginary part
of the second. This operation is continuous and real-linear. -/
def combine (z : ℂ) : ℂ × ℂ →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp Complex.reCLM).coprod
    ((-z) • (Complex.ofRealCLM.comp Complex.imCLM))

/-- The pointwise expression for the branch combination in complex coordinates. -/
theorem combine_apply (z u v : ℂ) : combine z (u,v) = (u.re : ℂ) - z*(v.im : ℂ) := by
  simp [combine, ContinuousLinearMap.coprod_apply, sub_eq_add_neg]

/-- The derivative of the mixed field is the same combination of the actual first derivatives. -/
theorem directional_combine (z : ℂ) {P Q : Covector → ℂ} (v x : Covector)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    directionalDerivative (fun t => combine z (P t, Q t)) v x =
      combine z (directionalDerivative P v x, directionalDerivative Q v x) := by
  have hd := (combine z).hasFDerivAt.comp x (hP.hasFDerivAt.prodMk hQ.hasFDerivAt)
  change fderiv ℝ ((combine z) ∘ fun t => (P t, Q t)) x v = _
  rw [hd.fderiv]
  rfl

private theorem second_combine (z : ℂ) {P Q : Covector → ℂ} (v x : Covector)
    (hP : ContDiff ℝ 2 P) (hQ : ContDiff ℝ 2 Q) :
    secondDirectionalDerivative (fun t => combine z (P t, Q t)) v x =
      combine z (secondDirectionalDerivative P v x, secondDirectionalDerivative Q v x) := by
  unfold secondDirectionalDerivative
  rw [show directionalDerivative (fun t => combine z (P t,Q t)) v =
    fun t => combine z (directionalDerivative P v t, directionalDerivative Q v t) from
    funext fun t => directional_combine z v t (hP.differentiable (by norm_num) t)
      (hQ.differentiable (by norm_num) t)]
  exact directional_combine z v x
    (PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hP.contDiffAt v)
    (PolarRegularity.differentiableAt_directionalDerivative_of_contDiffAt_two hQ.contDiffAt v)

/-- With a common real mass coefficient, combining the branches preserves the
free Klein–Gordon equation at every spacetime point. -/
theorem kg_combine (z : ℂ) {P Q : Covector → ℂ} {massSq : ℝ} (x : Covector)
    (hP : ContDiff ℝ 2 P) (hQ : ContDiff ℝ 2 Q)
    (hp : box P Madelung.coordinateVector x + (massSq : ℂ) * P x = 0)
    (hq : box Q Madelung.coordinateVector x + (massSq : ℂ) * Q x = 0) :
    box (fun t => combine z (P t,Q t)) Madelung.coordinateVector x +
      (massSq : ℂ) * combine z (P x,Q x) = 0 := by
  have hb : box (fun t => combine z (P t,Q t)) Madelung.coordinateVector x =
      combine z (box P Madelung.coordinateVector x, box Q Madelung.coordinateVector x) := by
    simp only [box, second_combine z _ x hP hQ, ← map_sub]
    rfl
  have hv : (box P Madelung.coordinateVector x, box Q Madelung.coordinateVector x) +
      massSq • (P x, Q x) = 0 := by
    ext1
    · simpa [Complex.real_smul] using hp
    · simpa [Complex.real_smul] using hq
  have hd := congrArg (combine z) hv
  rw [map_add, map_smul, map_zero, Complex.real_smul] at hd
  rwa [hb]

end FoliationQM.GaussianBranchMixing
