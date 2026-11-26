module

public import FoliationQM.CoordinateCutoffCrossLimit
public import FoliationQM.CurvedKGTestResidual

/-!
# The mass-containing weak equation across the coordinate axis

Source: v13 `eq:weak_pde_cutoff_bound` and the weak-equation passage in
`thm:wallstrom` Part (c), component kinds C and D. The same supplied field
has local coordinate L² data and satisfies the actual curved Klein–Gordon
operator away from the flat coordinate axis. Compact cutoff tests and the
actual cross-integral limit give its ambient weak equation. This does not
construct an extension from polar data or identify a standard local H¹
class, arbitrary nodal geometry, or global smooth Cauchy continuation.
-/

@[expose] public section
noncomputable section

namespace FoliationQM.CoordinateAxisWeakKG

open Filter MeasureTheory Set LorentzMatrixGroup RNCCoordinateConnection
open RNCVolumeDensity CurvedKGFirstVariation CurvedKGTestResidual
open scoped ContDiff Topology Matrix.Norms.Operator

/-- Local L² field and coordinate derivatives, with the actual Klein–Gordon equation and C² regularity only off the axis, give a genuinely integrable ambient cross pairing whose integral vanishes for every smooth compact test. -/
theorem weak_equation (p : MassiveParameters)
    {φ ψ : Covector → ℂ} {g : Covector → Mat4} {U : Set Covector}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U)
    (hg : ∀ x ∈ U, ContDiffAt ℝ 2 g x) (hd : ∀ x ∈ U, (g x).det < 0)
    (hsym : ∀ x ∈ tsupport φ, (g x).IsSymm)
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hD : ∀ j : Fin 4, MemLp (fun x => fderiv ℝ ψ x (axis j)) 2 (volume.restrict U))
    (hψoff : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, ContDiffAt ℝ 2 ψ x)
    (hKG : ∀ x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}, kgOperator p g ψ x = 0) :
    Integrable (fun x => volumeFactor (g x) • cross p g φ ψ x) volume ∧
    (∫ x, volumeFactor (g x) • cross p g φ ψ x) = 0 := by
  have H := CoordinateCutoffCrossLimit.cross_data_and_limit p hφ hc hs hg hd hsym hψ hD
  refine ⟨H.1, ?_⟩
  have hcut : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Integrable (fun x => volumeFactor (g x) • cross p g (CoordinateCutoffTests.test ε φ) ψ x) volume ∧
      (∫ x, volumeFactor (g x) • cross p g (CoordinateCutoffTests.test ε φ) ψ x) = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have ht := CoordinateCutoffTests.test_data hε.1 hε.2 hφ hc hs
    have hη : ContDiff ℝ 1 (CoordinateCutoffTests.test ε φ) := ht.1.of_le (by simp)
    have hgV (x) (hx : x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}) := hg x hx.1
    have hdV (x) (hx : x ∈ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}) := hd x hx.1
    have hi := integrable_cross p hη ht.2.1 ht.2.2.2 hgV hdV hψoff
    have hz (x : Covector) (hx : x ∉ U \ {y : Covector | y 2 = 0 ∧ y 3 = 0}) :
        volumeFactor (g x) • cross p g (CoordinateCutoffTests.test ε φ) ψ x = 0 := by
      have hnot : x ∉ tsupport (CoordinateCutoffTests.test ε φ) := fun h => hx (ht.2.2.2 h)
      have hv := image_eq_zero_of_notMem_tsupport hnot
      have hdη := fderiv_of_notMem_tsupport ℝ hnot
      simp [cross, CurvedFluxGreen.kinetic, hv, hdη]
    refine ⟨hi.integrable_of_forall_notMem_eq_zero hz, ?_⟩
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      integral_cross_residual p hη ht.2.1 ht.2.2.2 hgV hdV hψoff]
    have hr : (∫ x in U \ {y : Covector | y 2 = 0 ∧ y 3 = 0},
        volumeFactor (g x) • (star (CoordinateCutoffTests.test ε φ x) * residual p g ψ x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [(residual_zero_iff p g ψ x).2 (hKG x hx)]
      simp
    rw [hr, neg_zero]
  exact tendsto_nhds_unique_of_eventuallyEq H.2.2 tendsto_const_nhds
    (hcut.mono fun _ h => h.2)

end FoliationQM.CoordinateAxisWeakKG
