module

public import FoliationQM.CrossTestPairing
public import FoliationQM.TestLocalVanishing
public import FoliationQM.EmbeddedNodalGlobalWeakDerivative

/-!
# The weak Klein–Gordon equation across a closed embedded nodal surface

Source: v13 `thm:wallstrom` Part(c), "`Pψ = 0` holds distributionally across
all of `𝓜`", with `eq:weak_pde_cutoff_bound`, component kinds C and D. Let `𝒩`
be the closed image of a smooth embedding of a surface in coordinate
four-space and `g` a twice continuously differentiable Lorentzian metric on a
set `U`. A field that is square integrable on `U` with square-integrable
coordinate derivatives, and that is twice continuously differentiable and
solves the curvature-coupled Klein–Gordon equation on `U` off `𝒩`, satisfies
the weak equation against every smooth compact test supported in `U`.

The cutoff error is removed by the proved adapted-chart pairing limits applied
to the metric flux and mass field, and the local equations are summed over a
partition of unity. No chart, nullity, cutoff estimate or partition is a
hypothesis. The statement is in ambient coordinates with coordinate volume;
the displayed localized error inequality, an abstract four-manifold ambient
and the Cauchy continuation are separate.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.EmbeddedNodalWeakKG

open Filter MeasureTheory Set Manifold LorentzMatrixGroup RNCVolumeDensity
open CurvedPolarAction CurvedKGFirstVariation CurvedKGTestResidual CurvedFluxGreen
open RNCCoordinateConnection AdaptedChartCutoffTests AdaptedChartWeakDerivative CrossTestPairing
open CurvedChartTestPartition CurvedWaveDivergence RealLorentzFrame
open scoped ContDiff Topology Manifold Matrix.Norms.Operator

variable (p : MassiveParameters) {g : Covector → Mat4} {φ ψ η : Covector → ℂ}
  {U N : Set Covector}

/-- For a smooth compact test supported where the field is twice continuously
differentiable and solves the Klein–Gordon equation, the weighted cross pairing
is integrable with zero integral. -/
theorem integral_cross_eq_zero_of_off (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ U \ N) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψoff : ∀ x ∈ U \ N, ContDiffAt ℝ 2 ψ x)
    (hKG : ∀ x ∈ U \ N, kgOperator p g ψ x = 0) :
    Integrable (fun x => volumeFactor (g x) • cross p g η ψ x) volume ∧
    (∫ x, volumeFactor (g x) • cross p g η ψ x) = 0 := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by simp)
  have hgV (x) (hx : x ∈ U \ N) := hg x hx.1
  have hdV (x) (hx : x ∈ U \ N) := hd x hx.1
  have hi := integrable_cross p hη1 hc hs hgV hdV hψoff
  have hz (x : Covector) (hx : x ∉ U \ N) : volumeFactor (g x) • cross p g η ψ x = 0 :=
    cross_eq_zero_of_notMem p g ψ fun h => hx (hs h)
  refine ⟨hi.integrable_of_forall_notMem_eq_zero hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    integral_cross_residual p hη1 hc hs hgV hdV hψoff]
  have hr : (∫ x in U \ N, volumeFactor (g x) • (star (η x) * residual p g ψ x)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [(residual_zero_iff p g ψ x).2 (hKG x hx)]
    simp
  rw [hr, neg_zero]

/-- The weak Klein–Gordon equation for tests supported in a smooth chart that
sends the nodal set to the coordinate axis. -/
theorem weak_equation_chart {e : OpenPartialHomeomorph Covector Covector}
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (haxis : ∀ y ∈ e.source, y ∈ N ↔ (e y) 2 = 0 ∧ (e y) 3 = 0)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hse : tsupport φ ⊆ e.source) (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x)
    (hd : ∀ x ∈ U, (g x).det < 0) (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U))
    (hψoff : ∀ x ∈ U \ N, ContDiffAt ℝ 2 ψ x) (hKG : ∀ x ∈ U \ N, kgOperator p g ψ x = 0) :
    (∫ x in tsupport φ, volumeFactor (g x) • cross p g φ ψ x) = 0 := by
  have hK : IsCompact (tsupport φ) := hc
  obtain ⟨hflux, hmass⟩ := fields_memLp p hK hs hg hd hψ hD
  have hlim : Tendsto
      (fun ε : ℝ => ∫ x in tsupport φ, volumeFactor (g x) • cross p g (test e ε φ) ψ x)
      (𝓝[>] 0) (𝓝 (∫ x in tsupport φ, volumeFactor (g x) • cross p g φ ψ x)) := by
    have hk : Tendsto (fun ε : ℝ =>
        (p.hbar ^ 2 : ℝ) • (∑ i, ∫ x in tsupport φ,
          star (fderiv ℝ (test e ε φ) x (axis i)) * flux g ψ x i) -
          ∫ x in tsupport φ, star (test e ε φ x) * massField p g ψ x) (𝓝[>] 0)
        (𝓝 ((p.hbar ^ 2 : ℝ) • (∑ i, ∫ x in tsupport φ,
          star (fderiv ℝ φ x (axis i)) * flux g ψ x i) -
          ∫ x in tsupport φ, star (φ x) * massField p g ψ x)) :=
      ((tendsto_finsetSum _ fun i _ =>
        (test_pairing_limits he hi hφ hc Subset.rfl hse (hflux i) (axis i)).2).const_smul _).sub
        (test_pairing_limits he hi hφ hc Subset.rfl hse hmass 0).1
    rw [(integral_cross p hflux hmass hφ hc).2]
    refine hk.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have Hε := test_data hε.1 hε.2 he hφ hc hse
    exact ((integral_cross p hflux hmass Hε.1 Hε.2.1).2).symm
  have hzero : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ x in tsupport φ, volumeFactor (g x) • cross p g (test e ε φ) ψ x) = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have Hε := test_data hε.1 hε.2 he hφ hc hse
    have hsV : tsupport (test e ε φ) ⊆ U \ N := fun x hx =>
      ⟨hs (Hε.2.2.1 hx), fun hN => Hε.2.2.2 x hx ((haxis x (hse (Hε.2.2.1 hx))).mp hN)⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      cross_eq_zero_of_notMem p g ψ fun h => hx (Hε.2.2.1 h)]
    exact (integral_cross_eq_zero_of_off p Hε.1 Hε.2.1 hsV hg hd hψoff hKG).2
  exact tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hzero

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- The weak Klein–Gordon equation across a closed embedded nodal surface:
square-integrable field and coordinate derivatives, with twice continuous
differentiability and the equation only off the surface, give an integrable
cross pairing with zero integral for every smooth compact test. -/
theorem weak_equation {f : S → Covector}
    (hf : IsSmoothEmbedding 𝓘(ℝ, ℂ) 𝓘(ℝ, Covector) ∞ f) (hN : IsClosed (range f))
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U))
    (hψoff : ∀ x ∈ U \ range f, ContDiffAt ℝ 2 ψ x)
    (hKG : ∀ x ∈ U \ range f, kgOperator p g ψ x = 0) :
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
  by_cases hxN : x ∈ range f
  · obtain ⟨s, rfl⟩ := hxN
    obtain ⟨e, hse, he, haxis⟩ := EmbeddedNodalCoordinates.exists_adapted_chart hf s
    refine ⟨e.source, e.open_source, hse, fun η hηK hηW => ?_⟩
    rw [hint η hηK, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport η.val)
      fun y hy => cross_eq_zero_of_notMem p g ψ hy]
    exact weak_equation_chart p (contMDiffOn_of_mem_maximalAtlas he).contDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas he).contDiffOn haxis (hsm η) η.property.2
      (hηK.trans hs) hηW hg hd hψ hD hψoff hKG
  · refine ⟨(range f)ᶜ, hN.isOpen_compl, hxN, fun η hηK hηW => ?_⟩
    rw [hint η hηK]
    exact (integral_cross_eq_zero_of_off p (hsm η) η.property.2
      (fun y hy => ⟨hs (hηK hy), hηW hy⟩) hg hd hψoff hKG).2

end FoliationQM.EmbeddedNodalWeakKG
