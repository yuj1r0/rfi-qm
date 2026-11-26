module
public import FoliationQM.DiracCurveJetCalculus
public import FoliationQM.OpenPolarVariations

/-!
# Compact interior variations of a spinor field

For v13 `thm:dirac_lift`, the parameterized field is jointly smooth on
an open interval or parameter neighborhood times the open domain. It agrees
with the background off a common compact interior set. These requirements
imply that its actual parameter velocity is a globally smooth compact test.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff
namespace FoliationQM.DiracInteriorVariation
open DiracMatrices DiracCurveJetCalculus

/-- An admissible parameter family. No smoothness is required away from the spacetime domain. -/
structure Variation (U : Set Covector) (ψ : Covector → Spinor) where
  /-- Actual field depending on the real parameter and the spatial point. -/
  family : ℝ × Covector → Spinor
  /-- Open parameter neighborhood of zero. -/
  params : Set ℝ
  params_open : IsOpen params
  zero_mem : 0 ∈ params
  /-- A common compact interior set containing the change. -/
  carrier : Set Covector
  compact : IsCompact carrier
  interior : carrier ⊆ U
  initial : ∀ x, family (0, x) = ψ x
  smooth : ∀ t ∈ params, ∀ x ∈ U, ContDiffAt ℝ ∞ family (t, x)
  fixed : ∀ t ∈ params, ∀ x ∉ carrier, family (t, x) = ψ x

variable {U : Set Covector} {ψ : Covector → Spinor} (V : Variation U ψ)

/-- The background is the actual slice at parameter zero. -/
theorem slice_zero : slice V.family 0 = ψ := funext V.initial

/-- Off the common compact set the dependence on the parameter is locally constant.
This holds even where the background is not differentiable. -/
theorem velocity_zero {t : ℝ} (ht : t ∈ V.params) {x : Covector} (hx : x ∉ V.carrier) :
    velocity V.family t x = 0 := by
  by_cases hd : DifferentiableAt ℝ V.family (t,x)
  · have he : (fun r : ℝ => slice V.family r x) =ᶠ[𝓝 t] fun _ => ψ x := by
      filter_upwards [V.params_open.mem_nhds ht] with r hr
      exact V.fixed r hr x hx
    exact (hasDerivAt_slice_time hd).unique ((hasDerivAt_const t (ψ x)).congr_of_eventuallyEq he)
  · simp only [velocity, fderiv_zero_of_not_differentiableAt hd, zero_apply]

/-- The support of the actual parameter velocity is contained in the prescribed compact set. -/
theorem velocity_tsupport {t : ℝ} (ht : t ∈ V.params) :
    tsupport (velocity V.family t) ⊆ V.carrier := by
  apply closure_minimal _ V.compact.isClosed
  intro x hx
  by_contra hn
  exact hx (velocity_zero V ht hn)

/-- The velocity is a compactly supported field. -/
theorem velocity_compact {t : ℝ} (ht : t ∈ V.params) : HasCompactSupport (velocity V.family t) :=
  V.compact.of_isClosed_subset (isClosed_tsupport _) (velocity_tsupport V ht)

/-- Smoothness on the domain and compact interior support give global test regularity. -/
theorem velocity_contDiff {t : ℝ} (ht : t ∈ V.params) :
    ContDiff ℝ ∞ (velocity V.family t) :=
  OpenPolarVariations.contDiff_of_tsupport_subset
    (fun x hx => contDiffAt_velocity (V.smooth t ht x hx)) ((velocity_tsupport V ht).trans V.interior)

/-- Every smooth compact interior test yields a jointly smooth admissible affine variation. -/
def affineVariation (η : Covector → Spinor) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U) : Variation U ψ where
  family q := ψ q.2 + q.1 • η q.2
  params := Set.univ
  params_open := isOpen_univ
  zero_mem := Set.mem_univ _
  carrier := tsupport η
  compact := hc
  interior := hs
  initial x := by simp
  smooth t _ x hx := ((hψ x hx).comp (t,x) contDiffAt_snd).add
    (contDiffAt_fst.smul (hη.contDiffAt.comp (t,x) contDiffAt_snd))
  fixed t _ x hx := by simp [image_eq_zero_of_notMem_tsupport hx]

/-- The affine variation realizes exactly the prescribed velocity on the open domain. -/
theorem affine_velocity (η : Covector → Spinor) (hψ : ∀ x ∈ U, ContDiffAt ℝ ∞ ψ x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ U)
    (t : ℝ) {x : Covector} (hx : x ∈ U) :
    velocity (affineVariation η hψ hη hc hs).family t x = η x := by
  let W := affineVariation η hψ hη hc hs
  have H := hasDerivAt_slice_time ((W.smooth t (Set.mem_univ _) x hx).differentiableAt (by simp))
  apply H.unique
  change HasDerivAt (fun r : ℝ => ψ x + r • η x) (η x) t
  simpa using ((hasDerivAt_id t).smul_const (η x)).const_add (ψ x)

end FoliationQM.DiracInteriorVariation
