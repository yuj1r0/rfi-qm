module

public import FoliationQM.LocallyFlatNodalSet
public import FoliationQM.NodalSmoothContinuation

/-!
# The weak Klein–Gordon equation across a locally flat nodal set

Source: v13 `thm:wallstrom` Part(c), "`Pψ = 0` holds distributionally across
all of `𝓜`" and the continuation that follows, component kinds C and D. Let
`N` be closed relative to the open coordinate domain `V` and locally a
codimension-two axis there, and `g` a twice continuously differentiable
Lorentzian metric on a subset `U` of `V`. This module proves, for such a pair:

* a field that is square integrable on `U` with square-integrable coordinate
  derivatives, and twice continuously differentiable with the
  curvature-coupled Klein–Gordon equation on `U` off `N`, satisfies the weak
  equation against every smooth compact test supported in `U`;
* finite positive auxiliary-metric polar energy off `N` on a compact subset of
  `V` gives the square-integrable data, the weak directional-derivative
  identity and, with the equation off `N`, the weak equation;
* a twice continuously differentiable field almost everywhere equal on an open
  subset of `V` to a solution off `N` agrees with it off `N`, solves the
  equation on the whole open subset, and has zero set exactly `N` there when a
  continuous extension of the squared modulus vanishes exactly on `N`.

These are the coordinate theorems for a closed embedded surface with the
ambient coordinate space replaced by an open chart image. The existence of the
continued field is a hypothesis, as before; the chart of a manifold that
produces `(N, V)` is separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.LocallyFlatWeakKG

open Filter MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity
open CurvedPolarAction CurvedKGFirstVariation CurvedKGTestResidual CurvedFluxGreen
open RNCCoordinateConnection AdaptedChartCutoffTests AdaptedChartWeakDerivative CrossTestPairing
open CurvedChartTestPartition CurvedWaveDivergence RealLorentzFrame LocallyFlatNodalSet
open AuxiliaryMetricEnergy CirclePolarEnergy
open scoped ContDiff Topology Manifold Matrix.Norms.Operator

variable (p : MassiveParameters) {g : Covector → Mat4} {φ ψ u : Covector → ℂ}
  {U N V K : Set Covector}

/-- The weak Klein–Gordon equation across a locally flat nodal set:
square-integrable field and coordinate derivatives, with twice continuous
differentiability and the equation only off the set, give an integrable cross
pairing with zero integral for every smooth compact test. -/
theorem weak_equation (h : LocallyFlat N V) (hUV : U ⊆ V)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U))
    (hψoff : ∀ x ∈ U \ N, ContDiffAt ℝ 2 ψ x)
    (hKG : ∀ x ∈ U \ N, kgOperator p g ψ x = 0) :
    Integrable (fun x => volumeFactor (g x) • cross p g φ ψ x) volume ∧
    (∫ x, volumeFactor (g x) • cross p g φ ψ x) = 0 := by
  have hK : IsCompact (tsupport φ) := hc
  obtain ⟨hflux, hmass⟩ := fields_memLp p hK hs hg hd hψ hD
  have hzφ (x : Covector) (hx : x ∉ tsupport φ) : volumeFactor (g x) • cross p g φ ψ x = 0 :=
    cross_eq_zero_of_notMem p g ψ hx
  refine ⟨(integral_cross p hflux hmass hφ hc).1.integrable_of_forall_notMem_eq_zero hzφ, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzφ]
  have hsm (η : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞)) : ContDiff ℝ ∞ η.val :=
    contMDiff_iff_contDiff.mp η.property.1
  let Λ : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞) →+ ℂ := AddMonoidHom.mk'
    (fun η => ∫ x in tsupport φ, volumeFactor (g x) • cross p g η.val ψ x) (by
    intro a b
    have hfun : (fun x => volumeFactor (g x) • cross p g (a + b).val ψ x) = fun x =>
        volumeFactor (g x) • cross p g a.val ψ x + volumeFactor (g x) • cross p g b.val ψ x :=
      funext fun x => cross_add p g ψ ((hsm a).differentiable (by simp) x)
        ((hsm b).differentiable (by simp) x)
    change (∫ x in tsupport φ, volumeFactor (g x) • cross p g (a + b).val ψ x) =
      (∫ x in tsupport φ, volumeFactor (g x) • cross p g a.val ψ x) +
        ∫ x in tsupport φ, volumeFactor (g x) • cross p g b.val ψ x
    rw [hfun, integral_add (integral_cross p hflux hmass (hsm a) a.property.2).1
      (integral_cross p hflux hmass (hsm b) b.property.2).1])
  let Φ : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞) :=
    ⟨φ, contMDiff_iff_contDiff.mpr hφ, hc⟩
  change Λ Φ = 0
  have hint (η : testSpace 𝓘(ℝ, Covector) Covector ℂ (⊤ : ℕ∞))
      (hηK : tsupport η.val ⊆ tsupport φ) :
      Λ η = ∫ y, volumeFactor (g y) • cross p g η.val ψ y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      cross_eq_zero_of_notMem p g ψ fun h => hy (hηK h)
  refine TestLocalVanishing.vanish_of_local Λ Φ fun x hx => ?_
  by_cases hxN : x ∈ N
  · obtain ⟨e, hxe, he, hi, haxis⟩ := h.adapted x ⟨hxN, hUV (hs hx)⟩
    refine ⟨e.source, e.open_source, hxe, fun η hηK hηW => ?_⟩
    rw [hint η hηK, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport η.val)
      fun y hy => cross_eq_zero_of_notMem p g ψ hy]
    exact EmbeddedNodalWeakKG.weak_equation_chart p he hi haxis (hsm η) η.property.2
      (hηK.trans hs) hηW hg hd hψ hD hψoff hKG
  · refine ⟨V \ N, h.isOpen_diff, ⟨hUV (hs hx), hxN⟩, fun η hηK hηW => ?_⟩
    rw [hint η hηK]
    exact (EmbeddedNodalWeakKG.integral_cross_eq_zero_of_off p (hsm η) η.property.2
      (fun y hy => ⟨hs (hηK hy), (hηW hy).2⟩) hg hd hψoff hKG).2

variable {H : Covector → Mat4} {R : Covector → ℝ} {q : Covector → ℂ}
  {dR α : Covector → Covector →L[ℝ] ℝ} {omega : ℝ}

/-- Finite positive auxiliary-metric polar energy off a locally flat nodal set
gives square-integrable field and derivative data on the whole compact set and
the weak directional-derivative identity across the set. -/
theorem polar_weak_extension (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    (hR : ∀ x ∈ K \ N, HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ K \ N,
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ K \ N, ‖q x‖ = 1)
    (he : Integrable (fun x => (R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
      ((volume.restrict (K \ N)).withDensity
        (fun x => ENNReal.ofReal (density (H x))))) :
    MemLp (field R q) 2 (volume.restrict K) ∧
    (∀ v : Covector, MemLp (fun x => fderiv ℝ (field R q) x v) 2 (volume.restrict K)) ∧
    ∀ {φ : Covector → ℂ}, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ K →
      ∀ v : Covector,
      Integrable (fun x => star (fderiv ℝ φ x v) * field R q x) volume ∧
      Integrable (fun x => star (φ x) * fderiv ℝ (field R q) x v) volume ∧
      (∫ x, star (fderiv ℝ φ x v) * field R q x) =
        -(∫ x, star (φ x) * fderiv ℝ (field R q) x v) := by
  have hμ : volume.restrict (K \ N) = volume.restrict K := h.restrict_sdiff hKV
  have hS : MeasurableSet (K \ N) := h.measurableSet_sdiff hK.measurableSet hKV
  obtain ⟨hψ, hD⟩ := WeightedPolarEnergyL2.polar_memLp hK hS sdiff_subset hH hpos hR hq hunit he
  rw [hμ] at hψ
  have hD' (v : Covector) : MemLp (fun x => fderiv ℝ (field R q) x v) 2 (volume.restrict K) :=
    EmbeddedNodalPolarExtension.memLp_fderiv_apply (fun i => hμ ▸ hD i) v
  have hdiff : ∀ x ∈ K \ N, DifferentiableAt ℝ (field R q) x := fun x hx =>
    (hasFDerivAt_field (hR x hx) (hq x hx)).differentiableAt
  exact ⟨hψ, hD', fun hφ hc hs v =>
    h.weak_directional_identity hφ hc hs hKV hψ hdiff v (hD' v)⟩

/-- If the polar field moreover solves the curvature-coupled Klein–Gordon
equation off the nodal set, the weak equation holds across it. -/
theorem polar_weak_equation (h : LocallyFlat N V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hH : ContinuousOn H K) (hpos : ∀ x ∈ K, (H x).PosDef)
    (hR : ∀ x ∈ K \ N, HasFDerivAt R (dR x) x)
    (hq : ∀ x ∈ K \ N,
      HasFDerivAt q ((α x).smulRight (-Complex.I * (omega : ℂ) * q x)) x)
    (hunit : ∀ x ∈ K \ N, ‖q x‖ = 1)
    (he : Integrable (fun x => (R x) ^ 2 +
      realEnergy (H x) (fun i => dR x (axis i)) +
      omega ^ 2 * (R x) ^ 2 * realEnergy (H x) (fun i => α x (axis i)))
      ((volume.restrict (K \ N)).withDensity
        (fun x => ENNReal.ofReal (density (H x)))))
    (hg : ∀ x ∈ K, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ K, (g x).det < 0)
    (hψ2 : ∀ x ∈ K \ N, ContDiffAt ℝ 2 (field R q) x)
    (hKG : ∀ x ∈ K \ N, kgOperator p g (field R q) x = 0)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ K) :
    Integrable (fun x => volumeFactor (g x) • cross p g φ (field R q) x) volume ∧
    (∫ x, volumeFactor (g x) • cross p g φ (field R q) x) = 0 := by
  obtain ⟨hψ, hD, -⟩ := polar_weak_extension h hK hKV hH hpos hR hq hunit he
  exact weak_equation p h hKV hφ hc hs hg hd hψ (fun j => hD (axis j)) hψ2 hKG

/-- Smooth continuation across a locally flat nodal set: a twice continuously
differentiable field almost everywhere equal to a solution off the set agrees
with it off the set, solves the equation on the whole open subset of the
domain, has squared modulus the continuous extension of the density, and
vanishes exactly on the set when that extension does. -/
theorem continuation (h : LocallyFlat N V) (hU : IsOpen U) (hUV : U ⊆ V)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : ∀ x ∈ U \ N, ContDiffAt ℝ 2 ψ x) (hKG : ∀ x ∈ U \ N, kgOperator p g ψ x = 0)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hae : u =ᵐ[volume.restrict U] ψ)
    {ρ : Covector → ℝ} (hρ : ContinuousOn ρ U) (hρψ : ∀ x ∈ U \ N, ρ x = ‖ψ x‖ ^ 2)
    (hzero : ∀ x ∈ U, ρ x = 0 ↔ x ∈ N) :
    EqOn u ψ (U \ N) ∧ (∀ x ∈ U, kgOperator p g u x = 0) ∧
    (∀ x ∈ U, ‖u x‖ ^ 2 = ρ x) ∧ ∀ x ∈ U, u x = 0 ↔ x ∈ N := by
  have hnull := h.volume_inter_eq_zero
  have hsd : U \ N = U \ (N ∩ V) := sdiff_eq hUV
  have hopen : IsOpen (U \ N) := (h.mono hU hUV).isOpen_diff
  have hcu : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcψ : ContinuousOn ψ (U \ N) := fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have heq : EqOn u ψ (U \ N) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sdiff_subset hae)
      hopen (hcu.mono sdiff_subset) hcψ
  have heq' : EqOn u ψ (U \ (N ∩ V)) := hsd ▸ heq
  have hop : ∀ x ∈ U, kgOperator p g u x = 0 :=
    NodalSmoothContinuation.kgOperator_eq_zero p hU hnull hg hd hu fun x hx => by
      have hx' : x ∈ U \ N := hsd ▸ hx
      rw [NodalSmoothContinuation.kgOperator_congr p (heq.eventuallyEq_of_mem (hopen.mem_nhds hx'))]
      exact hKG x hx'
  have hρψ' : ∀ x ∈ U \ (N ∩ V), ρ x = ‖ψ x‖ ^ 2 := fun x hx => hρψ x (hsd ▸ hx)
  have hzero' : ∀ x ∈ U, ρ x = 0 ↔ x ∈ N ∩ V := fun x hx =>
    (hzero x hx).trans ⟨fun hn => ⟨hn, hUV hx⟩, fun hn => hn.1⟩
  refine ⟨heq, hop, NodalSmoothContinuation.norm_sq_eq hU hnull hcu heq' hρ hρψ', fun x hx => ?_⟩
  exact (NodalSmoothContinuation.eq_zero_iff hU hnull hcu heq' hρ hρψ' hzero' x hx).trans
    ⟨fun hn => hn.1, fun hn => ⟨hn, hUV hx⟩⟩

end FoliationQM.LocallyFlatWeakKG
