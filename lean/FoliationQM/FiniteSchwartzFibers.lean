module

public import FoliationQM.SchwartzFiberDerivative
public import FoliationQM.JointL2Curry

/-!
# Finite superpositions of Schwartz fibers

For the scalar current in v13 `eq:marginal_continuity`, a finite sum of
retained amplitudes multiplying remote Schwartz waves gives an actual
differentiable map to the Schwartz space. Its Hilbert derivative has a
scalar representative, and its current includes every pair of remote-wave
overlaps. Square-integrable coefficients give a joint square-integrable wave.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.FiniteSchwartzFibers

open LorentzCoordinates MeasureTheory SchwartzFiberDerivative JointL2Sections HilbertFiberObservables
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The Schwartz wave on each fiber of a finite superposition. -/
def family (a : ι → Spatial → ℂ) (g : ι → Fiber) (x : Spatial) : Fiber :=
  ∑ i, a i x • g i

/-- Scalar wave on the configuration space of the two particles. -/
def wave (a : ι → Spatial → ℂ) (g : ι → Fiber) (z : Spatial × Spatial) : ℂ :=
  ∑ i, a i z.1 * g i z.2

/-- Evaluating the Schwartz fiber gives the chosen joint scalar representative at every point. -/
theorem family_apply (a : ι → Spatial → ℂ) (g : ι → Fiber) (x y : Spatial) :
    family a g x y = wave a g (x,y) := by
  simp [family, wave, sum_apply, smul_apply]

/-- When the retained coefficients are smooth, their joint scalar superposition
is smooth in both spatial variables. -/
theorem contDiff_wave (a : ι → Spatial → ℂ) (g : ι → Fiber) (n : ℕ∞)
    (ha : ∀ i, ContDiff ℝ n (a i)) : ContDiff ℝ n (wave a g) := by
  unfold wave
  apply ContDiff.sum
  intro i _
  exact ((ha i).comp contDiff_fst).mul (((g i).smooth n).comp contDiff_snd)

private def synthesis (g : ι → Fiber) : (ι → ℂ) →L[ℝ] Fiber :=
  (∑ i, (ContinuousLinearMap.proj (R := ℂ) i).smulRight (g i)).restrictScalars ℝ

private theorem synthesis_apply (g : ι → Fiber) (c : ι → ℂ) :
    synthesis g c = ∑ i, c i • g i := by
  simp [synthesis]

/-- Differentiability of each finite coefficient implies genuine Fréchet differentiability
of the retained-position family in the Schwartz topology. -/
theorem differentiableAt_family (a : ι → Spatial → ℂ) (g : ι → Fiber) (x : Spatial)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) : DifferentiableAt ℝ (family a g) x := by
  have hd := hasFDerivAt_pi.mpr (fun i => (ha i).hasFDerivAt)
  have h := hasFDerivAt_image (synthesis g) hd
  unfold family
  simpa only [synthesis_apply] using h.differentiableAt

/-- The directional derivative in the Schwartz topology differentiates each scalar coefficient. -/
theorem fderiv_family (a : ι → Spatial → ℂ) (g : ι → Fiber) (x v : Spatial)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    fderiv ℝ (family a g) x v = ∑ i, fderiv ℝ (a i) x v • g i := by
  have hd := hasFDerivAt_pi.mpr (fun i => (ha i).hasFDerivAt)
  have h := hasFDerivAt_image (synthesis g) hd
  have he := congrArg (fun D : Spatial →L[ℝ] Fiber => D v) h.fderiv
  unfold family
  simpa only [synthesis_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply] using he

/-- The scalar representative of the directional Hilbert derivative is the
sum of differentiated retained coefficients times their original remote waves. -/
theorem derivative_rep (a : ι → Spatial → ℂ) (g : ι → Fiber) (x v : Spatial)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    (fderiv ℝ (hilbertWave (family a g)) x v : Spatial → ℂ) =ᵐ[volume]
      fun y => ∑ i, fderiv ℝ (a i) x v * g i y := by
  rw [fderiv_hilbertWave _ (differentiableAt_family a g x ha), fderiv_family a g x v ha]
  filter_upwards [(∑ i, fderiv ℝ (a i) x v • g i).coeFn_toLp 2 volume] with y hy
  simpa only [sum_apply, smul_apply, smul_eq_mul] using hy

/-- The joint scalar wave is square integrable whenever each retained coefficient is. -/
theorem wave_memLp (a : ι → Spatial → ℂ) (g : ι → Fiber) (ha : ∀ i, MemLp (a i) 2 volume) :
    MemLp (wave a g) 2 volume := by
  change MemLp (fun z : Spatial × Spatial => ∑ i, a i z.1 * g i z.2) 2 (volume.prod volume)
  apply memLp_finsetSum
  intro i _
  have hg := (g i).memLp 2 volume
  apply (memLp_two_iff_integrable_sq_norm ((ha i).aestronglyMeasurable.comp_fst.mul
    hg.aestronglyMeasurable.comp_snd)).mpr
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using (ha i).norm.integrable_sq.mul_prod hg.norm.integrable_sq

/-- Currying the joint L² class recovers the explicitly constructed Hilbert
fiber family at almost every retained position. -/
theorem curry_wave (a : ι → Spatial → ℂ) (g : ι → Fiber) (ha : ∀ i, MemLp (a i) 2 volume) :
    (JointL2Curry.curry ((wave_memLp a g ha).toLp (wave a g)) : Spatial → Remote) =ᵐ[volume]
      hilbertWave (family a g) := by
  filter_upwards [JointL2Curry.curry_toLp (wave_memLp a g ha)] with x hx
  apply Lp.ext
  filter_upwards [hx, (family a g x).coeFn_toLp 2 volume] with y hy hs
  exact hy.trans ((family_apply a g x y).symm.trans hs.symm)

private theorem toLp_sum (c : ι → ℂ) (g : ι → Fiber) :
    (∑ i, c i • g i).toLp 2 volume = ∑ i, c i • (g i).toLp 2 volume := by
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ = _
  simp only [map_sum, map_smul, SchwartzMap.toLpCLM_apply]

/-- The current retains every interference term, including overlaps of distinct
remote waves without an orthogonality hypothesis. -/
theorem current_sum (hbar m : ℝ) (a : ι → Spatial → ℂ) (g : ι → Fiber) (x v : Spatial)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    current hbar m (hilbertWave (family a g)) x v =
      (hbar / m) * (∑ i, ∑ j, star (a i x) * (fderiv ℝ (a j) x v *
        inner ℂ ((g i).toLp 2 volume) ((g j).toLp 2 volume))).im := by
  rw [current, fderiv_hilbertWave _ (differentiableAt_family a g x ha), fderiv_family a g x v ha]
  simp only [hilbertWave, family, toLp_sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_left_comm _ _ _

end FoliationQM.FiniteSchwartzFibers
