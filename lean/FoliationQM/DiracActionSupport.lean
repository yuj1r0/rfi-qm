module
public import FoliationQM.DiracAffineFieldVariation
public import FoliationQM.DiracJetFirstVariation
public import FoliationQM.OpenCompactIntegralVariation

/-!
# Continuity, support and integrability of Dirac variation densities

For v13 `thm:dirac_lift`, the density is evaluated on the four actual
coordinate derivatives of the field. The first variation and the test
density vanish off the test field's topological support. With compact
support in the domain, their integrability follows from local C¹ regularity
even when the background field has no finite action.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DiracActionSupport
open MeasureTheory Set Filter Function DiracMatrices DiracFieldDensity DiracAffineFieldVariation
open DiracPolarizedDensity DiracJetFirstVariation
open scoped Topology

/-- The real Dirac density on the actual four flat coordinate directions. -/
def dens (hbar c m : ℝ) (ψ : Covector → Spinor) (x : Covector) : ℝ :=
  fieldDensityRe hbar c m ψ x coordinateDirections

/-- The coefficient of the real affine test parameter in that same coordinate density. -/
def first (hbar c m : ℝ) (ψ η : Covector → Spinor) (x : Covector) : ℝ :=
  firstDensity hbar c m ψ η x coordinateDirections

/-- The values and coordinate derivatives of a single spinor field at each point. -/
def fieldJet (ψ : Covector → Spinor) (x : Covector) : Jet :=
  (ψ x, fun μ => fderiv ℝ ψ x (coordinateDirections μ))

/-- A C¹ field and its coordinate derivatives together give a continuous full jet at the point. -/
theorem continuousAt_fieldJet {ψ : Covector → Spinor} {x : Covector} (hψ : ContDiffAt ℝ 1 ψ x) :
    ContinuousAt (fieldJet ψ) x := by
  exact hψ.continuousAt.prodMk (continuousAt_pi.mpr fun μ =>
    (hψ.continuousAt_fderiv one_ne_zero).clm_apply (continuousAt_const (y := coordinateDirections μ)))

variable (hbar c m : ℝ)

/-- The actual coordinate density is continuous at every C¹ point of the field. -/
theorem continuousAt_dens {ψ : Covector → Spinor} {x : Covector} (hψ : ContDiffAt ℝ 1 ψ x) :
    ContinuousAt (dens hbar c m ψ) x :=
  (differentiable_value hbar c m (fieldJet ψ x)).continuousAt.comp (continuousAt_fieldJet hψ)

/-- The mixed first density is the cross term of the quadratic density on full jets. -/
theorem first_eq_cross (ψ η : Covector → Spinor) (x : Covector) :
    first hbar c m ψ η x = value hbar c m (fieldJet ψ x + fieldJet η x) -
      dens hbar c m ψ x - dens hbar c m η x := by
  have h := densityRe_affine hbar c m 1 (ψ x) (fieldJet ψ x).2 (η x) (fieldJet η x).2
  simp only [one_smul, one_mul, one_pow] at h
  change _ = DiracDensity.densityRe hbar c m (ψ x + η x) ((fieldJet ψ x).2 + (fieldJet η x).2) - _ - _
  rw [h]
  change _ = (dens hbar c m ψ x + first hbar c m ψ η x + dens hbar c m η x) -
    dens hbar c m ψ x - dens hbar c m η x
  ring

/-- The actual variation coefficient is continuous at common C¹ points of the two fields. -/
theorem continuousAt_first {ψ η : Covector → Spinor} {x : Covector} (hψ : ContDiffAt ℝ 1 ψ x)
    (hη : ContDiffAt ℝ 1 η x) : ContinuousAt (first hbar c m ψ η) x := by
  simp_rw [show first hbar c m ψ η = fun y => value hbar c m (fieldJet ψ y + fieldJet η y) -
    dens hbar c m ψ y - dens hbar c m η y from funext (first_eq_cross hbar c m ψ η)]
  exact (((differentiable_value hbar c m _).continuousAt.comp
    ((continuousAt_fieldJet hψ).add (continuousAt_fieldJet hη))).sub
    (continuousAt_dens hbar c m hψ)).sub (continuousAt_dens hbar c m hη)

/-- The full coordinate jet depends only on values of the field in a neighborhood. -/
theorem fieldJet_eq_of_eventuallyEq {ψ φ : Covector → Spinor} {x : Covector}
    (h : ψ =ᶠ[𝓝 x] φ) : fieldJet ψ x = fieldJet φ x := by
  unfold fieldJet
  rw [h.eq_of_nhds, h.fderiv_eq]

/-- Fields that agree on a neighborhood have the same actual coordinate density at its point. -/
theorem dens_eq_of_eventuallyEq {ψ φ : Covector → Spinor} {x : Covector}
    (h : ψ =ᶠ[𝓝 x] φ) : dens hbar c m ψ x = dens hbar c m φ x := by
  change DiracDensity.densityRe _ _ _ (ψ x) (fun μ => fderiv ℝ ψ x (coordinateDirections μ)) = _
  rw [h.eq_of_nhds, h.fderiv_eq]
  rfl

/-- Agreement of the background and test germs preserves the mixed coordinate density. -/
theorem first_eq_of_eventuallyEq {ψ φ η ξ : Covector → Spinor} {x : Covector}
    (hψ : ψ =ᶠ[𝓝 x] φ) (hη : η =ᶠ[𝓝 x] ξ) : first hbar c m ψ η x = first hbar c m φ ξ x := by
  rw [first_eq_cross, first_eq_cross, fieldJet_eq_of_eventuallyEq hψ, fieldJet_eq_of_eventuallyEq hη,
    dens_eq_of_eventuallyEq hbar c m hψ, dens_eq_of_eventuallyEq hbar c m hη]

/-- The test density vanishes wherever the test field is locally zero. -/
theorem dens_eq_zero_of_notMem_tsupport (η : Covector → Spinor) {x : Covector} (hx : x ∉ tsupport η) :
    dens hbar c m η x = 0 := by
  rw [dens_eq_of_eventuallyEq hbar c m (notMem_tsupport_iff_eventuallyEq.mp hx)]
  simp [dens, fieldDensityRe, fieldDensity, DiracDensity.density, DiracDensity.directionalPair,
    DiracAdjoint.bilinear]

/-- Off the test support both the test value and test derivative slots vanish,
independently of any background regularity. -/
theorem first_eq_zero_of_notMem_tsupport (ψ η : Covector → Spinor) {x : Covector}
    (hx : x ∉ tsupport η) : first hbar c m ψ η x = 0 := by
  have hz : fieldJet η x = 0 := by
    exact Prod.ext (show η x = 0 from image_eq_zero_of_notMem_tsupport hx)
      (funext fun μ => by simp [fieldJet, fderiv_of_notMem_tsupport ℝ hx])
  rw [first_eq_cross, hz, add_zero, dens_eq_zero_of_notMem_tsupport hbar c m η hx]
  change dens hbar c m ψ x - dens hbar c m ψ x - 0 = 0
  ring

/-- The topological support of the test density lies in the support of the test field. -/
theorem tsupport_dens_subset (η : Covector → Spinor) : tsupport (dens hbar c m η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (dens_eq_zero_of_notMem_tsupport hbar c m η hn)

/-- The topological support of the affine coefficient lies in the test support. -/
theorem tsupport_first_subset (ψ η : Covector → Spinor) :
    tsupport (first hbar c m ψ η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  exact hx (first_eq_zero_of_notMem_tsupport hbar c m ψ η hn)

/-- A continuous function on a domain, zero outside a compact subset of it,
is integrable on the domain for the flat coordinate volume. -/
theorem integrableOn_of_compact_support {U K : Set Covector} {f : Covector → ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hf : ContinuousOn f U) (hs : ∀ x ∉ K, f x = 0) :
    IntegrableOn f U := by
  have hsub : support f ⊆ K := by
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  exact ((integrableOn_iff_integrable_of_support_subset hsub).mp
    ((hf.mono hKU).integrableOn_compact hK)).integrableOn

/-- The first density is integrable when the compact support lies in the local regularity domain. -/
theorem integrableOn_first {U : Set Covector} {ψ η : Covector → Spinor}
    (hψ : ∀ x ∈ U, ContDiffAt ℝ 1 ψ x) (hη : ∀ x ∈ U, ContDiffAt ℝ 1 η x)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (first hbar c m ψ η) U :=
  integrableOn_of_compact_support hc hs
    (fun x hx => (continuousAt_first hbar c m (hψ x hx) (hη x hx)).continuousWithinAt)
    (fun _ hx => first_eq_zero_of_notMem_tsupport hbar c m ψ η hx)

/-- The quadratic test density is integrable under the same test support and regularity hypotheses. -/
theorem integrableOn_testDensity {U : Set Covector} {η : Covector → Spinor}
    (hη : ∀ x ∈ U, ContDiffAt ℝ 1 η x) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    IntegrableOn (dens hbar c m η) U :=
  integrableOn_of_compact_support hc hs
    (fun x hx => (continuousAt_dens hbar c m (hη x hx)).continuousWithinAt)
    (fun _ hx => dens_eq_zero_of_notMem_tsupport hbar c m η hx)

end FoliationQM.DiracActionSupport
