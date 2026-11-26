module
public import FoliationQM.DiracPolarVariationTransport

/-!
# Realization of arbitrary spinor tests by smooth polar families

For v13 `thm:dirac_lift`, an arbitrary compact variation of a represented
spinor field has a quotient variation agreeing through realization near
zero. In particular every smooth compact interior spinor test occurs as
the derivative of a realized quotient family at each point of the domain.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracPolarTestRealization
open DiracMatrices DiracPolarCoordinates DiracRegularVariations DiracPolarVariation
open DiracPolarVariationTransport DiracInteriorVariation

variable {U : Set Covector} {q : Covector → Q} {ψ : Covector → Spinor}
variable (hU : IsOpen U) (h : Represents U q ψ)

/-- Realize an arbitrary compact variation after shortening its parameter neighborhood. -/
def lift (V : Variation U ψ) : PolarVariation U q :=
  toPolar hU h (restrict V hU (fun _ hx => regular_of_represents h hx))

/-- The lift has the original compact carrier and only uses admissible parameters. -/
theorem lift_domains (V : Variation U ψ) :
    (lift hU h V).carrier = V.carrier ∧ (lift hU h V).params ⊆ V.params :=
  ⟨rfl, restrict_params_subset V hU (fun _ hx => regular_of_represents h hx)⟩

/-- Every admissible lifted slice realizes exactly the original field on the domain. -/
theorem lift_represents (V : Variation U ψ) {t : ℝ} (ht : t ∈ (lift hU h V).params) :
    Represents U (slice (lift hU h V) t) (DiracCurveJetCalculus.slice V.family t) :=
  toPolar_represents hU h _ ht

/-- A single parameter neighborhood of zero works at every spatial point at once. -/
theorem lift_germ (V : Variation U ψ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), Represents U (slice (lift hU h V) t) (DiracCurveJetCalculus.slice V.family t) :=
  Filter.mem_of_superset ((lift hU h V).params_open.mem_nhds (lift hU h V).zero_mem)
    (fun _ ht => lift_represents hU h V ht)

include hU h in
/-- Any smooth compact interior spinor test is the parameter derivative of an actual
smooth compact polar family. The same family realizes that test at every point of U. -/
theorem exists_polar_test (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x) (η : Covector → Spinor)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) :
    ∃ P : PolarVariation U q, P.carrier = tsupport η ∧
      ∀ x ∈ U, HasDerivAt (fun t => decode (P.family (t,x))) (η x) 0 := by
  let V := affineVariation η hψ hη hc hs
  refine ⟨lift hU h V, rfl, ?_⟩
  intro x hx
  have hd : HasDerivAt (fun t : ℝ => ψ x + t • η x) (η x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add (ψ x)
  apply hd.congr_of_eventuallyEq
  exact (lift_germ hU h V).mono (fun _ ht => ht x hx)

end FoliationQM.DiracPolarTestRealization
