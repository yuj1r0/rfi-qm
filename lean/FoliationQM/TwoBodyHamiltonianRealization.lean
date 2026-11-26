module

public import FoliationQM.TwoBodyDifferentialHamiltonian
public import FoliationQM.ScalarMarginalNoSignaling

/-!
# Differential Hamiltonian realizations and joint Schrödinger evolution

A regular subsystem trajectory represents its generator value by the
literal differential expression on a C² wave. On evolved products of
dense initial tests, a joint realization applies the six-dimensional
expression to the separated representative. The spatial product rule
then gives the tensor-sum action in L². Strong uniqueness on this test
family determines the candidate joint propagator on the full Hilbert space.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.TwoBodyHamiltonianRealization

open MeasureTheory LorentzCoordinates JointL2Sections JointL2Product JointSubsystemUnitary
open HilbertGeneratorCancellation StrongSchrodingerUniqueness JointMarginalHistory
open scoped BigOperators

/-- A scalar C² representative and its differential Hamiltonian represent
a pair of vectors in the graph of a one-particle operator. -/
structure OneGraph (h m : ℝ) (V : Spatial → ℝ) (u au : Remote) (f : Spatial → ℂ) : Prop where
  smooth : ContDiff ℝ 2 f
  state : (u : Spatial → ℂ) =ᵐ[volume] f
  action : (au : Spatial → ℂ) =ᵐ[volume] one h m V f

/-- Square-integrable classical waves and Hamiltonian values have the required
graph representatives under the actual map to L². -/
theorem oneGraph_toLp (h m : ℝ) (V : Spatial → ℝ) {f : Spatial → ℂ}
    (hf : ContDiff ℝ 2 f) (hu : MemLp f 2 volume) (ha : MemLp (one h m V f) 2 volume) :
    OneGraph h m V (hu.toLp f) (ha.toLp _) f := ⟨hf, hu.coeFn_toLp, ha.coeFn_toLp⟩

/-- The sum of the two subsystem actions has the joint differential
Hamiltonian of the separated classical wave as its scalar representative. -/
theorem coe_product_action (h m₁ m₂ : ℝ) {V₁ V₂ : Spatial → ℝ} {u v au bv : Remote}
    {f g : Spatial → ℂ} (hf : OneGraph h m₁ V₁ u au f) (hg : OneGraph h m₂ V₂ v bv g) :
    (product au v + product u bv : Joint) =ᵐ[volume]
      joint h m₁ m₂ V₁ V₂ (fun z => f z.1 * g z.2) := by
  filter_upwards [Lp.coeFn_add (product au v) (product u bv), coe_product au v, coe_product u bv,
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.state,
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.action,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.state,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.action] with z h₀ h₁ h₂ h₃ h₄ h₅ h₆
  change u z.1 = f z.1 at h₃
  change au z.1 = one h m₁ V₁ f z.1 at h₄
  change v z.2 = g z.2 at h₅
  change bv z.2 = one h m₂ V₂ g z.2 at h₆
  rw [h₀, Pi.add_apply, h₁, h₂, h₃, h₄, h₅, h₆, joint_product h m₁ m₂ V₁ V₂ hf.smooth hg.smooth]

/-- The literal joint action is square integrable and its L² class equals
the sum of the two actions whenever the one-body graph representatives exist. -/
theorem toLp_joint_product (h m₁ m₂ : ℝ) {V₁ V₂ : Spatial → ℝ} {u v au bv : Remote}
    {f g : Spatial → ℂ} (hf : OneGraph h m₁ V₁ u au f) (hg : OneGraph h m₂ V₂ v bv g) :
    ∃ hj : MemLp (joint h m₁ m₂ V₁ V₂ (fun z => f z.1*g z.2)) 2 volume,
      hj.toLp _ = product au v + product u bv := by
  have he := coe_product_action h m₁ m₂ hf hg
  have hj := (memLp_congr_ae he).mp (Lp.memLp (product au v + product u bv))
  exact ⟨hj, Lp.ext (hj.coeFn_toLp.trans he.symm)⟩

/-- One explicit choice of dense initial tests is given by the Schwartz waves. -/
theorem dense_schwartz :
    Dense (Set.range (fun f : SchwartzMap Spatial ℂ => f.toLp 2 volume)) :=
  SchwartzMap.denseRange_toLpCLM (F := ℂ) (by norm_num)

/-- On dense subsystem initial tests the supplied propagator solves the
strong equation and admits classical scalar graph representatives at each time. -/
structure Subsystem (h m s : ℝ) (V : ℝ → Spatial → ℝ) (A : ℝ → Remote →ₗ.[ℂ] Remote)
    (U : ℝ → Remote ≃ₗᵢ[ℂ] Remote) (T : Set Remote) : Prop where
  dense : Dense T
  initial : ∀ u ∈ T, U s u = u
  strong : ∀ u ∈ T, Strong h A (fun t => U t u)
  graph (u : Remote) (hu : u ∈ T) (t : ℝ) : ∃ f,
    OneGraph h m (V t) (U t u) (A t ⟨U t u, (strong u hu).mem t⟩) f

/-- Given the two subsystem evolutions alone, their constructed tensor
propagator on separated regular initial tests has the actual time derivative
`−i/ℏ` times the L² class of the literal joint spatial Hamiltonian. -/
theorem differential_product_derivative {h m₁ m₂ s : ℝ} {V₁ V₂ : ℝ → Spatial → ℝ}
    {A B : ℝ → Remote →ₗ.[ℂ] Remote} {U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote}
    {T₁ T₂ : Set Remote} (L : Subsystem h m₁ s V₁ A U T₁) (R : Subsystem h m₂ s V₂ B V T₂)
    (u : Remote) (hu : u ∈ T₁) (v : Remote) (hv : v ∈ T₂) (t : ℝ) :
    ∃ f g : Spatial → ℂ, OneGraph h m₁ (V₁ t) (U t u) (A t ⟨_, (L.strong u hu).mem t⟩) f ∧
      OneGraph h m₂ (V₂ t) (V t v) (B t ⟨_, (R.strong v hv).mem t⟩) g ∧
      ∃ hj : MemLp (joint h m₁ m₂ (V₁ t) (V₂ t) (fun z => f z.1*g z.2)) 2 volume,
        HasDerivAt (fun r => factor (U r) (V r) (product u v))
          ((-Complex.I / (h : ℂ)) • hj.toLp _) t := by
  obtain ⟨f, hf⟩ := L.graph u hu t
  obtain ⟨g, hg⟩ := R.graph v hv t
  obtain ⟨hj, he⟩ := toLp_joint_product h m₁ m₂ hf hg
  refine ⟨f, g, hf, hg, hj, ?_⟩
  simp_rw [factor_product, he]
  have hd := (productL.bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
    (fun _ => (L.strong u hu).derivative t) (fun _ => (R.strong v hv).derivative t)
  apply hd.congr_deriv
  simp only [generator, smul_add]
  change productL (U t u) (_ • _) + productL (_ • _) (V t v) = _
  rw [(productL (U t u)).map_smul, productL.map_smul, smul_apply]
  exact add_comm _ _

/-- The spatial realization and the two supplied subsystem evolutions. The joint
graph is specified by the scalar differential expression on products of
evolved dense tests. Its Hilbert-space tensor-sum identity is a consequence. -/
structure SpatialRealization (h m₁ m₂ s : ℝ) (V₁ V₂ : ℝ → Spatial → ℝ)
    (U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote) where
  A : ℝ → Remote →ₗ.[ℂ] Remote
  B : ℝ → Remote →ₗ.[ℂ] Remote
  H : ℝ → Joint →ₗ.[ℂ] Joint
  leftTests : Set Remote
  rightTests : Set Remote
  left : Subsystem h m₁ s V₁ A U leftTests
  right : Subsystem h m₂ s V₂ B V rightTests
  symmetric : ∀ t, (H t).IsFormalAdjoint (H t)
  product_mem (u : Remote) (hu : u ∈ leftTests) (v : Remote) (hv : v ∈ rightTests) (t : ℝ) :
    product (U t u) (V t v) ∈ (H t).domain
  product_graph (u : Remote) (hu : u ∈ leftTests) (v : Remote) (hv : v ∈ rightTests) (t : ℝ)
    (f g : Spatial → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hf' : (U t u : Spatial → ℂ) =ᵐ[volume] f) (hg' : (V t v : Spatial → ℂ) =ᵐ[volume] g) :
    (H t ⟨product (U t u) (V t v), product_mem u hu v hv t⟩ : Spatial × Spatial → ℂ) =ᵐ[volume]
      joint h m₁ m₂ (V₁ t) (V₂ t) (fun z => f z.1*g z.2)


/-- A candidate joint propagator solves the strong equation on the separated
initial tests and starts there from the identity. -/
structure DifferentialEvolution (h m₁ m₂ s : ℝ) (V₁ V₂ : ℝ → Spatial → ℝ)
    (U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote) (W : ℝ → Joint ≃ₗᵢ[ℂ] Joint)
    extends SpatialRealization h m₁ m₂ s V₁ V₂ U V where
  initial : ∀ u ∈ leftTests, ∀ v ∈ rightTests, W s (product u v) = product u v
  strong : ∀ u ∈ leftTests, ∀ v ∈ rightTests, Strong h H (fun t => W t (product u v))

variable {h m₁ m₂ s : ℝ} {V₁ V₂ : ℝ → Spatial → ℝ} {U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote}
  {W : ℝ → Joint ≃ₗᵢ[ℂ] Joint}

/-- The joint action on each evolved test product equals the subsystem
tensor sum in the actual L² quotient. -/
theorem action_products (D : SpatialRealization h m₁ m₂ s V₁ V₂ U V)
    (u : Remote) (hu : u ∈ D.leftTests) (v : Remote) (hv : v ∈ D.rightTests) (t : ℝ) :
    D.H t ⟨product (U t u) (V t v), D.product_mem u hu v hv t⟩ =
      product (D.A t ⟨U t u, (D.left.strong u hu).mem t⟩) (V t v) +
      product (U t u) (D.B t ⟨V t v, (D.right.strong v hv).mem t⟩) := by
  obtain ⟨f, hf⟩ := D.left.graph u hu t
  obtain ⟨g, hg⟩ := D.right.graph v hv t
  exact Lp.ext ((D.product_graph u hu v hv t f g hf.smooth hg.smooth hf.state hg.state).trans
    (coe_product_action h m₁ m₂ hf hg).symm)

/-- Evolving the two test factors independently gives a strong solution
of the very same joint generator as the supplied joint propagator. -/
theorem product_strong (D : SpatialRealization h m₁ m₂ s V₁ V₂ U V)
    (u : Remote) (hu : u ∈ D.leftTests) (v : Remote) (hv : v ∈ D.rightTests) :
    Strong h D.H (fun t => product (U t u) (V t v)) where
  mem := D.product_mem u hu v hv
  derivative t := by
    have H := (productL.bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
      (fun _ => (D.left.strong u hu).derivative t) (fun _ => (D.right.strong v hv).derivative t)
    apply H.congr_deriv
    simp only [generator, action_products D u hu v hv, smul_add]
    change productL (U t u) (_ • _) + productL (_ • _) (V t v) = _
    rw [(productL (U t u)).map_smul, productL.map_smul, smul_apply]
    exact add_comm _ _

/-- The constructed tensor product of the given subsystem unitaries is a
joint strong evolution on the dense product tests, starting at the given
initial wave. This construction needs no candidate joint propagator. -/
theorem factor_strong (D : SpatialRealization h m₁ m₂ s V₁ V₂ U V)
    (u : Remote) (hu : u ∈ D.leftTests) (v : Remote) (hv : v ∈ D.rightTests) :
    Strong h D.H (fun t => factor (U t) (V t) (product u v)) ∧
      factor (U s) (V s) (product u v) = product u v := by
  simp only [factor_product, D.left.initial u hu, D.right.initial v hv, and_true]
  exact product_strong D u hu v hv

/-- Uniqueness on the evolved dense test products implies factorization
on every joint L² state, including entangled states. -/
theorem factorization (D : DifferentialEvolution h m₁ m₂ s V₁ V₂ U V W) (t : ℝ) :
    W t = factor (U t) (V t) := by
  have he : (W t).toContinuousLinearEquiv.toContinuousLinearMap =
      (factor (U t) (V t)).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply DecoupledPropagator.ext_on_domain_products D.left.dense D.right.dense
    intro u hu v hv
    have H := eq_of_strong D.symmetric (D.strong u hu v hv) (product_strong D.toSpatialRealization u hu v hv)
      (s := s) (by rw [D.initial u hu v hv, D.left.initial u hu, D.right.initial v hv])
    exact (congrFun H t).trans (factor_product (U t) (V t) u v).symm
  ext1 ψ
  exact DFunLike.congr_fun he ψ

/-- The canonical Born marginal agrees almost everywhere with the one
from retained-only evolution; every retained region has the same mass. -/
theorem born_history (D : DifferentialEvolution h m₁ m₂ s V₁ V₂ U V W)
    (ψ : Joint) (t : ℝ) (A : Set Spatial) :
    born (W t ψ) =ᵐ[volume] born (retained (U t) ψ) ∧
      regionalBorn (W t ψ) A = regionalBorn (retained (U t) ψ) A := by
  rw [factorization D t]
  exact ⟨born_factor _ _ _, regionalBorn_factor _ _ _ _⟩

/-- For two choices of the remote potential the scalar Born and current
histories agree at every retained position when both evolved states have
the stated differentiable Schwartz-fiber representatives. -/
theorem scalar_histories {V₃ : ℝ → Spatial → ℝ} {V' : ℝ → Remote ≃ₗᵢ[ℂ] Remote}
    {W' : ℝ → Joint ≃ₗᵢ[ℂ] Joint}
    (D : DifferentialEvolution h m₁ m₂ s V₁ V₂ U V W)
    (D' : DifferentialEvolution h m₁ m₂ s V₁ V₃ U V' W') (ψ : Joint)
    (S T : ℝ → Spatial → SchwartzFiberDerivative.Fiber)
    (hs : ∀ t, Differentiable ℝ (S t)) (ht : ∀ t, Differentiable ℝ (T t))
    (hi : ∀ t, MemLp (ScalarMarginalNoSignaling.field (S t)) 2 volume)
    (hj : ∀ t, MemLp (ScalarMarginalNoSignaling.field (T t)) 2 volume)
    (hS : ∀ t, (hi t).toLp _ = W t ψ) (hT : ∀ t, (hj t).toLp _ = W' t ψ)
    (x v : Spatial) :
    (fun t => (∫ y, ‖S t x y‖^2, (h/m₁) * ∫ y, (star (S t x y) *
      fderiv ℝ (fun z => S t z y) x v).im)) =
    (fun t => (∫ y, ‖T t x y‖^2, (h/m₁) * ∫ y, (star (T t x y) *
      fderiv ℝ (fun z => T t z y) x v).im)) := by
  funext t
  have H := hS t
  have H' := hT t
  rw [factorization D t] at H
  rw [factorization D' t] at H'
  obtain ⟨hd, hc⟩ := ScalarMarginalNoSignaling.scalar_integrals (U t) (V t) (V' t) ψ
    (S t) (T t) (hs t) (ht t) (hi t) (hj t) H H' h m₁ x v
  exact Prod.ext hd hc

end FoliationQM.TwoBodyHamiltonianRealization
