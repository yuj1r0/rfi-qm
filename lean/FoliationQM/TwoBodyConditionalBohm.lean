module

public import FoliationQM.TwoBodyBohmFactorization
public import FoliationQM.TwoBodyMadelung

/-!
# The conditional and factorized Bohm potentials on physical time slices

The conditional density is the ratio of the joint density to its actual
first marginal. On positive slices its amplitude times the marginal
amplitude gives the joint amplitude. The spacetime Hamilton–Jacobi equation
therefore contains the conditional cross term from v13.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyConditionalBohm

open MeasureTheory LorentzCoordinates ObserverGaussianFisher TwoBodyCoordinates
open TwoBodyFisherAmplitude TwoBodySchrodingerResidual TwoParticleMarginals
open MarginalDifferentiation TwoBodyBohmFactors

/-- Square root of the first marginal density. -/
def marginalAmplitude (f : Spatial × Spatial → ℝ) (x : Spatial) : ℝ := √(left f x)

/-- Square root of the normalized conditional density. -/
def conditionalAmplitude (f : Spatial × Spatial → ℝ) (z : Spatial × Spatial) : ℝ :=
  √(conditional f z.1 z.2)

/-- The conditional amplitude has unit squared norm on every finite positive fiber. -/
theorem conditional_normalized {f : Spatial × Spatial → ℝ} (H : Regular f) (x : Spatial) :
    (∫ y, conditionalAmplitude f (x,y) ^ 2) = 1 := by
  have hx := left_pos f x (H.left_fiber x) (fun y => H.pos (x,y))
  rw [← integral_conditional f x (H.left_fiber x) hx]
  exact integral_congr_ae (.of_forall fun y => Real.sq_sqrt (div_pos (H.pos (x,y)) hx).le)

/-- The square root of the joint density reconstructs from the two conditional factors. -/
theorem amplitude_reconstruction {f : Spatial × Spatial → ℝ} (H : Regular f) :
    (fun z => √(f z)) = fun z => marginalAmplitude f z.1 * conditionalAmplitude f z := by
  funext z
  rcases z with ⟨x,y⟩
  have hx := left_pos f x (H.left_fiber x) (fun u => H.pos (x,u))
  exact (congrArg Real.sqrt (factorization f x y hx)).trans (Real.sqrt_mul hx.le _)

/-- Positive C² joint and marginal densities give a C² conditional amplitude at the chosen pair. -/
theorem conditional_contDiffAt {f : Spatial × Spatial → ℝ} (H : Regular f) {x y : Spatial}
    (hf : ContDiffAt ℝ 2 f (x,y)) (hm : ContDiffAt ℝ 2 (left f) x) :
    ContDiffAt ℝ 2 (conditionalAmplitude f) (x,y) := by
  have hx := left_pos f x (H.left_fiber x) (fun u => H.pos (x,u))
  have hleft : ContDiffAt ℝ 2 (fun z : Spatial × Spatial => left f z.1) (x,y) :=
    ContDiffAt.comp (g := left f) (f := Prod.fst) (x,y) hm contDiffAt_fst
  have hd : ContDiffAt ℝ 2 (fun z : Spatial × Spatial => f z / left f z.1) (x,y) :=
    hf.div hleft hx.ne'
  exact hd.sqrt (div_pos (H.pos (x,y)) hx).ne'

/-- Freezing physical time gives the spatial Bohm potential from the actual two particle Laplacians. -/
theorem quantum_slice (h m₁ m₂ : ℝ) {R : Point → ℝ} {t : ℝ} {x y : Spatial}
    (hR : ContDiffAt ℝ 2 R ((t,x),y)) :
    quantum h m₁ m₂ R ((t,x),y) = configQ h m₁ m₂ (slice t R) x y := by
  rw [quantum_laplacians]
  have hl : lap (fun u => slice t R (u,y)) x = lap₁ R ((t,x),y) :=
    Finset.sum_congr rfl fun i _ => left_second hR i
  have hr : lap (fun v => slice t R (x,v)) y = lap₂ R ((t,x),y) :=
    Finset.sum_congr rfl fun i _ => right_second hR i
  unfold configQ one
  rw [hl, hr]
  unfold slice
  ring

/-- The conditional amplitudes decompose the physical Bohm potential into the
first marginal, the remote conditional potential, and the displayed cross term. -/
theorem conditional_decomposition (h m₁ m₂ : ℝ) {f : Spatial × Spatial → ℝ} (H : Regular f)
    {x y : Spatial} (hf : ContDiffAt ℝ 2 f (x,y)) (hm : ContDiffAt ℝ 2 (left f) x) :
    configQ h m₁ m₂ (fun z => √(f z)) x y =
      one h m₁ (marginalAmplitude f) x +
      one h m₂ (fun v => conditionalAmplitude f (x,v)) y +
      cross h m₁ (marginalAmplitude f) (conditionalAmplitude f) x y := by
  have hx := left_pos f x (H.left_fiber x) (fun u => H.pos (x,u))
  have hA : ContDiffAt ℝ 2 (marginalAmplitude f) x := hm.sqrt hx.ne'
  have hB := conditional_contDiffAt H hf hm
  have hAn : marginalAmplitude f x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hBn : conditionalAmplitude f (x,y) ≠ 0 := (Real.sqrt_pos.mpr (div_pos (H.pos _) hx)).ne'
  rw [amplitude_reconstruction H]
  exact conditional_product h m₁ m₂ _ _ x y hA (ContDiffAt.comp (g := conditionalAmplitude f)
    (f := fun u => (u,y)) x hB (contDiff_prodMk_left y).contDiffAt) hAn hBn

/-- The Bohm term of the spacetime wave equals the three conditional contributions on its time slice. -/
theorem quantum_conditional (h m₁ m₂ : ℝ) {ρ : Point → ℝ} {t : ℝ} {x y : Spatial}
    (H : Regular (slice t ρ)) (hρ : ContDiffAt ℝ 2 ρ ((t,x),y))
    (hm : ContDiffAt ℝ 2 (left (slice t ρ)) x) :
    quantum h m₁ m₂ (fun z => √(ρ z)) ((t,x),y) =
      one h m₁ (marginalAmplitude (slice t ρ)) x +
      one h m₂ (fun v => conditionalAmplitude (slice t ρ) (x,v)) y +
      cross h m₁ (marginalAmplitude (slice t ρ)) (conditionalAmplitude (slice t ρ)) x y := by
  have hp : 0 < ρ ((t,x),y) := H.pos (x,y)
  have hs : ContDiffAt ℝ 2 (slice t ρ) (x,y) := hρ.comp (x,y)
    (show ContDiffAt ℝ 2 (fun z : Spatial × Spatial => ((t,z.1),z.2)) (x,y) by fun_prop)
  rw [quantum_slice h m₁ m₂ (hρ.sqrt hp.ne')]
  exact conditional_decomposition h m₁ m₂ H hs hm

/-- Zero Fisher excess on the selected time slice splits the actual spacetime
Bohm term into the two one-particle potentials of the physical marginals. -/
theorem quantum_of_excess_zero {h m₁ m₂ t : ℝ} {ρ : Point → ℝ} {x y : Spatial}
    (H : Regular (slice t ρ)) (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hJ : Integrable (TwoParticleFisher.jointDensity h m₁ m₂ (slice t ρ)))
    (hz : TwoParticleFisher.excess h m₁ (slice t ρ) = 0)
    (hρ : ContDiffAt ℝ 2 ρ ((t,x),y)) :
    quantum h m₁ m₂ (fun z => √(ρ z)) ((t,x),y) =
      one h m₁ (fun u => √(left (slice t ρ) u)) x +
      one h m₂ (fun v => √(right (slice t ρ) v)) y := by
  have hp : 0 < ρ ((t,x),y) := H.pos (x,y)
  rw [quantum_slice h m₁ m₂ (hρ.sqrt hp.ne')]
  exact TwoBodyBohmFactorization.configQ_of_excess_zero H hh hm₁ hm₂ hJ hz
    (hρ.comp (x,y) (show ContDiffAt ℝ 2 (fun z : Spatial × Spatial => ((t,z.1),z.2)) (x,y)
      by fun_prop))

end FoliationQM.TwoBodyConditionalBohm
