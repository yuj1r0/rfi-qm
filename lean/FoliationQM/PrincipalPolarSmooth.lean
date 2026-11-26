module
public import FoliationQM.RegularPolarReconstruction
public import FoliationQM.SpinorMatrixSmooth
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
/-!
# Smoothness of the actual reconstruction on the principal determinant branch

Source: the local smooth polar reconstruction in v13 `prop:takabayasi` and
`eq:takabayasi_polar`. The branch domain is the preimage of the actual
complex slit plane under the actual spinor-matrix determinant. The existing
principal argument, half-angle amplitude, determinant-normalized matrix
and Dirac representative are the functions whose smoothness is proved.

The complex logarithm supplies real smoothness of its actual imaginary
part, the principal argument, on this branch. Positive invariant density
and nonzero amplitude justify the square root and reciprocal. The results
also compose with actual smooth spinor fields on arbitrary real normed
domains. No globally smooth principal angle or smooth quotient
identification is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator
namespace FoliationQM.PrincipalPolarSmooth
open DiracMatrices SpinorMatrix SpinorRegularity RegularPolarReconstruction SpinorMatrixSmooth

/-- The principal reconstruction branch consists of actual spinors whose determinant lies off the nonpositive real cut. -/
def PrincipalDomain : Set Spinor := {psi | Matrix.det (toMatrix psi) ∈ Complex.slitPlane}

/-- Every spinor on the principal branch is strictly invariant-regular. -/
theorem principalDomain_regular {psi : Spinor} (hpsi : psi ∈ PrincipalDomain) : Regular psi :=
  (det_ne_zero_iff_regular psi).mp (Complex.slitPlane_ne_zero hpsi)

/-- On the principal branch the full determinant phase lies strictly between minus pi and pi. -/
theorem determinantPhase_bounds_strict {psi : Spinor} (hpsi : psi ∈ PrincipalDomain) :
    -Real.pi < determinantPhase psi ∧ determinantPhase psi < Real.pi := by
  have hb := determinantPhase_bounds psi
  refine ⟨hb.1, lt_of_le_of_ne hb.2 ?_⟩
  exact Complex.slitPlane_arg_ne_pi hpsi

/-- The actual principal complex argument is real-smooth to every order at every slit-plane point. -/
theorem contDiffAt_arg (n : WithTop ℕ∞) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ n Complex.arg z := by
  have hl : ContDiffAt ℝ n Complex.log z :=
    (Complex.contDiffAt_log hz : ContDiffAt ℂ n Complex.log z).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    (Complex.imCLM.contDiff.contDiffAt.comp z hl)
/-- The actual determinant slit-plane branch is open in the real spinor space. -/
theorem principalDomain_isOpen : IsOpen PrincipalDomain :=
  Complex.isOpen_slitPlane.preimage (contDiff_spinorDet 0).continuous

/-- The existing principal determinant phase is real-smooth to every order on its actual branch. -/
theorem contDiffAt_determinantPhase (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ PrincipalDomain) : ContDiffAt ℝ n determinantPhase psi := by
  exact (contDiffAt_arg n hpsi).comp psi (contDiff_spinorDet n).contDiffAt

/-- The existing half-angle amplitude is real-smooth on the principal branch, where the actual density is positive. -/
theorem contDiffAt_amplitudePhase (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ PrincipalDomain) : ContDiffAt ℝ n amplitudePhase psi := by
  have hr := principalDomain_regular hpsi
  have hpos : 0 < invariantDensity psi := hr
  have hs := (SpinorMatrixSmooth.contDiffAt_invariantDensity n hr).sqrt hpos.ne'
  have hsC : ContDiffAt ℝ n (fun q : Spinor => (Real.sqrt (invariantDensity q) : ℂ)) psi := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp psi hs
  have hbC : ContDiffAt ℝ n (fun q : Spinor => (determinantPhase q : ℂ)) psi := by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp psi (contDiffAt_determinantPhase n hpsi)
  exact hsC.mul (((contDiffAt_const (c := Complex.I)).mul hbC).div_const 2).cexp

/-- The existing determinant-normalized matrix is real-smooth on the branch where its actual complex amplitude is nonzero. -/
theorem contDiffAt_normalizedMatrix (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ PrincipalDomain) : ContDiffAt ℝ n normalizedMatrix psi := by
  have hi := (contDiffAt_amplitudePhase n hpsi).inv
    (amplitudePhase_ne_zero (principalDomain_regular hpsi))
  exact hi.smul (contDiff_toMatrix n).contDiffAt

/-- The actual constructed four-by-four Dirac representative is real-smooth on the principal determinant branch. -/
theorem contDiffAt_reconstructedSpin (n : WithTop ℕ∞) {psi : Spinor}
    (hpsi : psi ∈ PrincipalDomain) : ContDiffAt ℝ n reconstructedSpin psi := by
  exact (contDiff_spin n).contDiffAt.comp psi (contDiffAt_normalizedMatrix n hpsi)

/-- The existing full principal phase is smooth throughout the open branch domain. -/
theorem contDiffOn_determinantPhase (n : WithTop ℕ∞) :
    ContDiffOn ℝ n determinantPhase PrincipalDomain :=
  fun _ hpsi => (contDiffAt_determinantPhase n hpsi).contDiffWithinAt

/-- The existing half-angle amplitude is smooth throughout the open branch domain. -/
theorem contDiffOn_amplitudePhase (n : WithTop ℕ∞) :
    ContDiffOn ℝ n amplitudePhase PrincipalDomain :=
  fun _ hpsi => (contDiffAt_amplitudePhase n hpsi).contDiffWithinAt

/-- The actual determinant-normalized matrix is smooth throughout the open branch domain. -/
theorem contDiffOn_normalizedMatrix (n : WithTop ℕ∞) :
    ContDiffOn ℝ n normalizedMatrix PrincipalDomain :=
  fun _ hpsi => (contDiffAt_normalizedMatrix n hpsi).contDiffWithinAt

/-- The actual reconstructed Dirac representative is smooth throughout the open branch domain. -/
theorem contDiffOn_reconstructedSpin (n : WithTop ℕ∞) :
    ContDiffOn ℝ n reconstructedSpin PrincipalDomain :=
  fun _ hpsi => (contDiffAt_reconstructedSpin n hpsi).contDiffWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual smooth spinor fields have smooth invariant density at every strictly regular value. -/
theorem contDiffAt_invariantDensity_comp (n : WithTop ℕ∞) {f : E → Spinor} {x : E}
    (hf : ContDiffAt ℝ n f x) (hreg : Regular (f x)) :
    ContDiffAt ℝ n (fun y => invariantDensity (f y)) x :=
  (SpinorMatrixSmooth.contDiffAt_invariantDensity n hreg).comp x hf

/-- Actual smooth spinor fields have a smooth principal determinant phase at every value in the branch domain. -/
theorem contDiffAt_determinantPhase_comp (n : WithTop ℕ∞) {f : E → Spinor} {x : E}
    (hf : ContDiffAt ℝ n f x) (hbranch : f x ∈ PrincipalDomain) :
    ContDiffAt ℝ n (fun y => determinantPhase (f y)) x :=
  (contDiffAt_determinantPhase n hbranch).comp x hf

/-- The actual reconstructed half-angle amplitude of a smooth spinor field is smooth at each branch-domain value. -/
theorem contDiffAt_amplitudePhase_comp (n : WithTop ℕ∞) {f : E → Spinor} {x : E}
    (hf : ContDiffAt ℝ n f x) (hbranch : f x ∈ PrincipalDomain) :
    ContDiffAt ℝ n (fun y => amplitudePhase (f y)) x :=
  (contDiffAt_amplitudePhase n hbranch).comp x hf

/-- The actual determinant-normalized matrix of a smooth spinor field is smooth at each branch-domain value. -/
theorem contDiffAt_normalizedMatrix_comp (n : WithTop ℕ∞) {f : E → Spinor} {x : E}
    (hf : ContDiffAt ℝ n f x) (hbranch : f x ∈ PrincipalDomain) :
    ContDiffAt ℝ n (fun y => normalizedMatrix (f y)) x :=
  (contDiffAt_normalizedMatrix n hbranch).comp x hf

/-- The actual reconstructed Dirac matrix field is smooth at each spinor value in the principal branch. -/
theorem contDiffAt_reconstructedSpin_comp (n : WithTop ℕ∞) {f : E → Spinor} {x : E}
    (hf : ContDiffAt ℝ n f x) (hbranch : f x ∈ PrincipalDomain) :
    ContDiffAt ℝ n (fun y => reconstructedSpin (f y)) x :=
  (contDiffAt_reconstructedSpin n hbranch).comp x hf

end FoliationQM.PrincipalPolarSmooth
