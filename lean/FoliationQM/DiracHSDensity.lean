module
public import FoliationQM.DiracPolarVariationTransport
public import FoliationQM.DiracActionSupport
public import FoliationQM.ReconstructedDiracDensity

/-!
# The Hestenes–Takabayasi density on a regular polar field

For v13 `eq:dirac_polar_lagrangian_main` and `thm:dirac_lift`, evaluate the
canonical frame contraction, the chiral derivative and the mass term using
local representatives of the decoded field. The comparison to the symmetric
Dirac density is a theorem about these expressions. Existence and equality
of local values suffice without a global real angle or global rotor field.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Matrix.Norms.Operator
namespace FoliationQM.DiracHSDensity
open DiracMatrices SpinorMatrix SpinorRegularity PolarSpinorBilinears SpecialLinearSpin
open DiracFieldDensity PolarConnectionContraction RealLorentzFrame SpecialLinearConnection
open ReconstructedFrameGeometry DiracPolarCoordinates DiracPolarVariationTransport

/-- Local factors at one spacetime point, expressed as field germs with the
actual positive invariant density and determinant-one condition on a neighborhood. -/
structure LocalFactors (ψ : Covector → Spinor) (x : Covector) where
  angle : Covector → ℝ
  rotor : Covector → Mat2
  density_smooth : ContDiffAt ℝ 1 (fun y => invariantDensity (ψ y)) x
  angle_smooth : ContDiffAt ℝ 1 angle x
  rotor_smooth : ContDiffAt ℝ 1 rotor x
  realization : ∀ᶠ y in 𝓝 x, 0 < invariantDensity (ψ y) ∧ (rotor y).det = 1 ∧
    ψ y = polarSpinor (invariantDensity (ψ y)) (angle y) (spin (rotor y))

/-- Local representatives exist at every C¹ field point whose spinor is strictly regular. -/
theorem localFactors_nonempty {ψ : Covector → Spinor} {x : Covector}
    (hψ : ContDiffAt ℝ 1 ψ x) (hr : Regular (ψ x)) : Nonempty (LocalFactors ψ x) := by
  obtain ⟨β, A, hρ, hβ, hA, _, he⟩ := LocalPolarFields.exists_local_polar_fields 1 hψ hr
  exact ⟨⟨β, A, hρ, hβ, hA, he⟩⟩

/-- The literal real polar Lagrangian on the four actual flat coordinate directions.
No amplitude derivative occurs in this expression. -/
def localExpression (hbar c m : ℝ) (ψ : Covector → Spinor) (β : Covector → ℝ)
    (A : Covector → Mat2) (x : Covector) : ℝ :=
  invariantDensity (ψ x) *
    (canonicalContraction hbar c (reconstructedFrame (ψ x))
        (fun μ => bodyOmega A x (coordinateDirections μ)) -
      (hbar * c / 2) * (∑ μ, inverseCoefficients (reconstructedFrame (ψ x)) μ 3 *
        fderiv ℝ β x (coordinateDirections μ)) - m * c ^ 2 * Real.cos (β x))

variable (hbar c m : ℝ)

/-- Evaluating any valid local factors gives the symmetric Dirac density of the original field. -/
theorem expression_eq_dens {ψ : Covector → Spinor} {x : Covector} (P : LocalFactors ψ x) :
    localExpression hbar c m ψ P.angle P.rotor x = DiracActionSupport.dens hbar c m ψ x :=
  (ReconstructedDiracDensity.fieldDensityRe_of_local_polar P.density_smooth.differentiableAt_one
    P.angle_smooth.differentiableAt_one P.rotor_smooth.differentiableAt_one P.realization
    coordinateDirections hbar c m).symm

/-- The value is independent of both representatives and extensions of the background away from its germ. -/
theorem expression_eq_of_germ {ψ φ : Covector → Spinor} {x : Covector} (h : ψ =ᶠ[𝓝 x] φ)
    (P : LocalFactors ψ x) (R : LocalFactors φ x) :
    localExpression hbar c m ψ P.angle P.rotor x = localExpression hbar c m φ R.angle R.rotor x :=
  (expression_eq_dens hbar c m P).trans ((DiracActionSupport.dens_eq_of_eventuallyEq hbar c m h).trans
    (expression_eq_dens hbar c m R).symm)

/-- The simultaneous sign and two-pi angle change supplies another valid local representative. -/
def signShift {ψ : Covector → Spinor} {x : Covector} (P : LocalFactors ψ x) : LocalFactors ψ x where
  angle y := P.angle y + 2 * Real.pi
  rotor y := -(P.rotor y)
  density_smooth := P.density_smooth
  angle_smooth := P.angle_smooth.add contDiffAt_const
  rotor_smooth := P.rotor_smooth.neg
  realization := by
    filter_upwards [P.realization] with y hy
    refine ⟨hy.1, ?_, ?_⟩
    · simp [Matrix.det_neg, hy.2.1]
    · rw [show spin (-(P.rotor y)) = -spin (P.rotor y) from SpinorMatrixSmooth.spinCLM.map_neg _,
        polarSpinor_shift_neg]
      exact hy.2.2

/-- The explicit density respects the simultaneous sign-gluing relation on every valid local branch. -/
theorem expression_signShift {ψ : Covector → Spinor} {x : Covector} (P : LocalFactors ψ x) :
    localExpression hbar c m ψ (fun y => P.angle y + 2 * Real.pi) (fun y => -P.rotor y) x =
      localExpression hbar c m ψ P.angle P.rotor x :=
  expression_eq_of_germ hbar c m Filter.EventuallyEq.rfl (signShift P) P

/-- Value on a polar field, computed from local representatives at C¹ points of its
realization. The zero value totalizes the expression outside this calculus domain. -/
def density (q : Covector → Q) (x : Covector) : ℝ := by
  classical
  let ψ := fun y => decode (q y)
  exact if hψ : ContDiffAt ℝ 1 ψ x then
    let P := (localFactors_nonempty hψ (regular_decode (q x))).some
    localExpression hbar c m ψ P.angle P.rotor x
  else 0

/-- Any locally reconstructing angle and rotor give the defined value at a C¹ point. -/
theorem density_eq_expression (q : Covector → Q) {x : Covector}
    (hψ : ContDiffAt ℝ 1 (fun y => decode (q y)) x) (P : LocalFactors (fun y => decode (q y)) x) :
    density hbar c m q x = localExpression hbar c m (fun y => decode (q y)) P.angle P.rotor x := by
  classical
  simp only [density, dite_eq_left hψ]
  exact expression_eq_of_germ hbar c m Filter.EventuallyEq.rfl _ P

/-- At a C¹ point the quotient density computes the stipulated Dirac density of its realization. -/
theorem density_eq_decoded (q : Covector → Q) {x : Covector}
    (hψ : ContDiffAt ℝ 1 (fun y => decode (q y)) x) :
    density hbar c m q x = DiracActionSupport.dens hbar c m (fun y => decode (q y)) x := by
  let P := (localFactors_nonempty hψ (regular_decode (q x))).some
  exact (density_eq_expression hbar c m q hψ P).trans (expression_eq_dens hbar c m P)

/-- A represented field on an open domain has the genuine polar density at each C¹ point,
regardless of its ambient and quotient extensions outside that domain. -/
theorem density_eq_dens {U : Set Covector} {q : Covector → Q} {ψ : Covector → Spinor}
    (hU : IsOpen U) (h : Represents U q ψ) {x : Covector} (hx : x ∈ U) (hψ : ContDiffAt ℝ 1 ψ x) :
    density hbar c m q x = DiracActionSupport.dens hbar c m ψ x := by
  have he : (fun y => decode (q y)) =ᶠ[𝓝 x] ψ :=
    Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => h y hy)
  exact (density_eq_decoded hbar c m q (hψ.congr_of_eventuallyEq he)).trans
    (DiracActionSupport.dens_eq_of_eventuallyEq hbar c m he)

end FoliationQM.DiracHSDensity
