module

public import FoliationQM.TwoBodyHamiltonianRealization

/-!
# The canonical two-time decoupled propagator

At target time `t` and initial time `s`, the tensor product of the two
supplied subsystem propagators acts on the full joint L² space. Its
composition and reversal laws follow from those of its factors.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyUnitaryPropagator

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Product JointSubsystemUnitary
open HilbertGeneratorCancellation StrongSchrodingerUniqueness TwoBodyHamiltonianRealization
open JointMarginalHistory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Algebraic evolution laws for a unitary family indexed by target and initial time. -/
structure Laws (U : ℝ → ℝ → E ≃ₗᵢ[ℂ] E) : Prop where
  identity (s : ℝ) : U s s = LinearIsometryEquiv.refl ℂ E
  composition (t s r : ℝ) : (U s r).trans (U t s) = U t r

/-- Reversing the time endpoints gives the inverse unitary. -/
theorem inverse {U : ℝ → ℝ → E ≃ₗᵢ[ℂ] E} (hU : Laws U) (t s : ℝ) :
    (U t s).symm = U s t := by
  ext1 x
  apply (U t s).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  show x = ((U s t).trans (U t s)) x
  rw [hU.composition, hU.identity]
  rfl

variable (U V : ℝ → ℝ → Remote ≃ₗᵢ[ℂ] Remote)

/-- The canonical unitary from time `s` to time `t` for the decoupled joint system. -/
def canonical (t s : ℝ) : Joint ≃ₗᵢ[ℂ] Joint := factor (U t s) (V t s)

private theorem ext_products {A B : Joint ≃ₗᵢ[ℂ] Joint}
    (h : ∀ u v, A (product u v) = B (product u v)) : A = B := by
  have he : A.toContinuousLinearEquiv.toContinuousLinearMap =
      B.toContinuousLinearEquiv.toContinuousLinearMap := JointL2Equivalence.ext_on_products h
  ext1 ψ
  exact DFunLike.congr_fun he ψ

/-- Identity and three-time composition of the joint propagator hold on every joint wave. -/
theorem canonical_laws (hU : Laws U) (hV : Laws V) : Laws (canonical U V) where
  identity s := by
    apply ext_products
    intro u v
    simp only [canonical, factor_product, hU.identity, hV.identity]
    rfl
  composition t s r := by
    apply ext_products
    intro u v
    simp only [LinearIsometryEquiv.trans_apply, canonical, factor_product]
    exact congrArg₂ product (DFunLike.congr_fun (hU.composition t s r) u)
      (DFunLike.congr_fun (hV.composition t s r) v)

/-- Exchanging the two time arguments inverts the joint propagator. -/
theorem canonical_inverse (hU : Laws U) (hV : Laws V) (t s : ℝ) :
    (canonical U V t s).symm = canonical U V s t := inverse (canonical_laws U V hU hV) t s

/-- Strong continuity in both time arguments passes to every joint L² state
by approximation with finite linear combinations of separated waves. -/
theorem strongly_continuous
    (hU : ∀ u, Continuous (fun p : ℝ × ℝ => U p.1 p.2 u))
    (hV : ∀ v, Continuous (fun p : ℝ × ℝ => V p.1 p.2 v)) (ψ : Joint) :
    Continuous (fun p : ℝ × ℝ => canonical U V p.1 p.2 ψ) := by
  let F (p : ℝ × ℝ) := canonical U V p.1 p.2
  have hs {w : Joint} (hw : w ∈ Submodule.span ℂ
      (Set.range fun z : Remote × Remote => product z.1 z.2)) :
      Continuous (fun p => F p w) := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨u,v⟩,rfl⟩ := hw
      simp only [F, canonical, factor_product]
      exact productL.continuous₂.comp ((hU u).prodMk (hV v))
    | zero => simpa only [map_zero] using (continuous_const (y := (0 : Joint)) (X := ℝ × ℝ))
    | add a b _ _ ha hb => simpa only [map_add, Pi.add_def] using ha.add hb
    | smul c a _ ha => simpa only [map_smul, Pi.smul_def] using ha.const_smul c
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp (JointL2Equivalence.dense_products ψ)
    (ε/3) (by positivity)
  have hv := Metric.tendsto_nhds.mp ((hs hw).continuousAt (x := p)) (ε/3) (by positivity)
  filter_upwards [hv] with q hq
  have ht := dist_triangle4 (F q ψ) (F q w) (F p w) (F p ψ)
  rw [(F q).isometry.dist_eq, (F p).isometry.dist_eq, dist_comm w ψ] at ht
  change dist (F q ψ) (F p ψ) < ε
  change dist (F q w) (F p w) < ε / 3 at hq
  linarith

/-- For strong subsystem trajectories, the derivative of the joint evolution
on a separated initial wave is the tensor sum of the two generator actions. -/
theorem strong_product_derivative (h s : ℝ) (A B : ℝ → Remote →ₗ.[ℂ] Remote)
    (u v : Remote) (hu : Strong h A (fun t => U t s u)) (hv : Strong h B (fun t => V t s v))
    (t : ℝ) : HasDerivAt (fun q => canonical U V q s (product u v))
      ((-Complex.I / (h : ℂ)) •
        (product (A t ⟨_, hu.mem t⟩) (V t s v) + product (U t s u) (B t ⟨_, hv.mem t⟩))) t := by
  simp_rw [canonical, factor_product]
  have hd := (productL.bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
    (fun _ => hu.derivative t) (fun _ => hv.derivative t)
  apply hd.congr_deriv
  simp only [generator, smul_add]
  change productL (U t s u) (_ • _) + productL (_ • _) (V t s v) = _
  rw [(productL (U t s u)).map_smul, productL.map_smul, smul_apply]
  exact add_comm _ _

/-- Every supplied two-time joint evolution with the stated differential
generator graph and strong dense-domain evolution equals the canonical family. -/
theorem candidate_eq_canonical {h m₁ m₂ : ℝ} {V₁ V₂ : ℝ → Spatial → ℝ}
    (W : ℝ → ℝ → Joint ≃ₗᵢ[ℂ] Joint) (D : ∀ s, DifferentialEvolution h m₁ m₂ s V₁ V₂
      (fun t => U t s) (fun t => V t s) (fun t => W t s)) :
    W = canonical U V := by
  funext t s
  exact factorization (D s) t

/-- Changing the remote propagator preserves the canonical Born marginal almost
everywhere and preserves the full Born mass of every retained region. -/
theorem marginals (V' : ℝ → ℝ → Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) (t s : ℝ) (A : Set Spatial) :
    born (canonical U V t s ψ) =ᵐ[volume] born (canonical U V' t s ψ) ∧
    regionalBorn (canonical U V t s ψ) A = regionalBorn (canonical U V' t s ψ) A :=
  ⟨(born_factor _ _ _).trans (born_factor _ _ _).symm,
    (regionalBorn_factor _ _ _ A).trans (regionalBorn_factor _ _ _ A).symm⟩

/-- For differentiable Schwartz representatives of the two canonically evolved
states, the physical scalar density and current agree at all positions and times. -/
theorem scalar_histories (V' : ℝ → ℝ → Remote ≃ₗᵢ[ℂ] Remote) (ψ : Joint) (s h m : ℝ)
    (S T : ℝ → Spatial → SchwartzFiberDerivative.Fiber)
    (hs : ∀ t, Differentiable ℝ (S t)) (ht : ∀ t, Differentiable ℝ (T t))
    (hi : ∀ t, MemLp (ScalarMarginalNoSignaling.field (S t)) 2 volume)
    (hj : ∀ t, MemLp (ScalarMarginalNoSignaling.field (T t)) 2 volume)
    (hS : ∀ t, (hi t).toLp _ = canonical U V t s ψ)
    (hT : ∀ t, (hj t).toLp _ = canonical U V' t s ψ) (x v : Spatial) :
    (fun t => (∫ y, ‖S t x y‖^2, (h/m) * ∫ y, (star (S t x y) *
      fderiv ℝ (fun z => S t z y) x v).im)) =
    (fun t => (∫ y, ‖T t x y‖^2, (h/m) * ∫ y, (star (T t x y) *
      fderiv ℝ (fun z => T t z y) x v).im)) := by
  funext t
  obtain ⟨hd, hc⟩ := ScalarMarginalNoSignaling.scalar_integrals (U t s) (V t s) (V' t s) ψ
    (S t) (T t) (hs t) (ht t) (hi t) (hj t) (hS t) (hT t) h m x v
  exact Prod.ext hd hc

end FoliationQM.TwoBodyUnitaryPropagator
