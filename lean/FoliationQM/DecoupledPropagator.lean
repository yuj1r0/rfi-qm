module

public import FoliationQM.JointSubsystemUnitary
public import FoliationQM.StrongSchrodingerUniqueness

/-!
# Factorization of a decoupled strong Schrödinger evolution

For v13 `thm:entanglement_nosignaling`, a tensor-sum Hamiltonian gives the
product of the two subsystem evolutions. On initial domain vectors this follows
from differentiating the actual product wave and uniqueness for the symmetric
joint Hamiltonian. Continuity and density then give operator equality on all
joint states. Each Hamiltonian acts on its own, possibly time-dependent domain.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.DecoupledPropagator

open JointL2Sections JointL2Product JointSubsystemUnitary StrongSchrodingerUniqueness
  HilbertGeneratorCancellation Set

/-- The joint Hamiltonian contains products of the two domains and acts on them
by the sum of the two subsystem actions. -/
structure TensorSum (A B : Remote →ₗ.[ℂ] Remote) (H : Joint →ₗ.[ℂ] Joint) : Prop where
  mem (u : A.domain) (v : B.domain) : product u v ∈ H.domain
  action (u : A.domain) (v : B.domain) :
    H ⟨product u v, mem u v⟩ = product (A u) v + product u (B v)

/-- The Schrödinger velocity on a domain product obeys the bilinear product rule. -/
theorem generator_product (hbar : ℝ) {A B : Remote →ₗ.[ℂ] Remote} {H : Joint →ₗ.[ℂ] Joint}
    (D : TensorSum A B H) (u : A.domain) (v : B.domain) :
    generator hbar H ⟨product u v, D.mem u v⟩ =
      product u (generator hbar B v) + product (generator hbar A u) v := by
  unfold generator
  rw [D.action u v, smul_add]
  change _ = productL (u : Remote) (_ • B v) + productL (_ • A u) (v : Remote)
  rw [(productL (u : Remote)).map_smul, productL.map_smul, smul_apply]
  exact add_comm _ _

/-- Products of strong subsystem solutions are strong solutions of the tensor-sum equation. -/
theorem product_strongOn {hbar : ℝ} {I : Set ℝ} {A B : ℝ → Remote →ₗ.[ℂ] Remote}
    {H : ℝ → Joint →ₗ.[ℂ] Joint} (D : ∀ t ∈ I, TensorSum (A t) (B t) (H t))
    {u v : ℝ → Remote} (hu : StrongOn hbar A u I) (hv : StrongOn hbar B v I) :
    StrongOn hbar H (fun t => product (u t) (v t)) I where
  mem t ht := (D t ht).mem ⟨_, hu.mem t ht⟩ ⟨_, hv.mem t ht⟩
  derivative t ht := by
    rw [generator_product hbar (D t ht) ⟨_, hu.mem t ht⟩ ⟨_, hv.mem t ht⟩]
    exact (productL.bilinearRestrictScalars ℝ).hasDerivWithinAt_of_bilinear
      (hu.derivative t ht) (hv.derivative t ht)

/-- Agreement on products of two dense sets determines a continuous joint operator. -/
theorem ext_on_domain_products {DA DB : Set Remote} (hA : Dense DA) (hB : Dense DB)
    {F G : Joint →L[ℂ] Joint} (h : ∀ u ∈ DA, ∀ v ∈ DB, F (product u v) = G (product u v)) :
    F = G := by
  have he : (fun p : Remote × Remote => F (product p.1 p.2)) =
      fun p => G (product p.1 p.2) :=
    Continuous.ext_on (hA.prod hB) (F.continuous.comp productL.continuous₂)
      (G.continuous.comp productL.continuous₂) (fun p hp => h p.1 hp.1 p.2 hp.2)
  exact JointL2Equivalence.ext_on_products fun u v => congrFun he (u,v)

/-- Domain and evolution hypotheses with initial time `s` and time set `I`.
Strong differentiability is imposed on the evolved vectors with domain initial
data. The joint equation is needed only on their initial products. -/
structure EvolutionOn (hbar s : ℝ) (I : Set ℝ) (A B : ℝ → Remote →ₗ.[ℂ] Remote)
    (H : ℝ → Joint →ₗ.[ℂ] Joint) (U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote)
    (W : ℝ → Joint ≃ₗᵢ[ℂ] Joint) : Prop where
  dense_left : Dense ((A s).domain : Set Remote)
  dense_right : Dense ((B s).domain : Set Remote)
  tensor_sum : ∀ t ∈ I, TensorSum (A t) (B t) (H t)
  symmetric : ∀ t ∈ I, (H t).IsFormalAdjoint (H t)
  left_initial : ∀ u, U s u = u
  right_initial : ∀ v, V s v = v
  joint_initial : ∀ ψ, W s ψ = ψ
  left_strong : ∀ u : (A s).domain, StrongOn hbar A (fun t => U t u) I
  right_strong : ∀ v : (B s).domain, StrongOn hbar B (fun t => V t v) I
  joint_strong : ∀ (u : (A s).domain) (v : (B s).domain),
    StrongOn hbar H (fun t => W t (product u v)) I

variable {hbar s : ℝ} {I : Set ℝ} {A B : ℝ → Remote →ₗ.[ℂ] Remote}
    {H : ℝ → Joint →ₗ.[ℂ] Joint} {U V : ℝ → Remote ≃ₗᵢ[ℂ] Remote}
    {W : ℝ → Joint ≃ₗᵢ[ℂ] Joint}

private theorem factor_of_domain_action (D : EvolutionOn hbar s I A B H U V W) (t : ℝ)
    (he : ∀ (u : (A s).domain) (v : (B s).domain),
      W t (product u v) = product (U t u) (V t v)) : W t = factor (U t) (V t) := by
  have eqOp : (W t).toContinuousLinearEquiv.toContinuousLinearMap =
      (factor (U t) (V t)).toContinuousLinearEquiv.toContinuousLinearMap :=
    ext_on_domain_products D.dense_left D.dense_right (fun u hu v hv =>
      (he ⟨u, hu⟩ ⟨v, hv⟩).trans (factor_product (U t) (V t) u v).symm)
  ext1 ψ
  exact DFunLike.congr_fun eqOp ψ

/-- On a compact time interval, the joint propagator equals the product of the
subsystem propagators at every time, including the endpoints. -/
theorem factorization_Icc {a b : ℝ} (D : EvolutionOn hbar a (Icc a b) A B H U V W) {t : ℝ}
    (ht : t ∈ Icc a b) : W t = factor (U t) (V t) := by
  apply factor_of_domain_action D
  intro u v
  apply eqOn_Icc_of_strong D.symmetric (D.joint_strong u v)
    (product_strongOn D.tensor_sum (D.left_strong u) (D.right_strong v)) _ ht
  simp only [D.joint_initial, D.left_initial, D.right_initial]

private theorem strong_of_univ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {K : ℝ → E →ₗ.[ℂ] E} {u : ℝ → E} (hu : StrongOn hbar K u univ) : Strong hbar K u where
  mem t := hu.mem t (mem_univ t)
  derivative t := hasDerivWithinAt_univ.mp (hu.derivative t (mem_univ t))

/-- With strong evolution on the whole real line, factorization holds at all
times relative to the supplied initial time. -/
theorem factorization (D : EvolutionOn hbar s univ A B H U V W) (t : ℝ) :
    W t = factor (U t) (V t) := by
  apply factor_of_domain_action D
  intro u v
  have he := eq_of_strong (fun q => D.symmetric q (mem_univ q))
    (strong_of_univ (D.joint_strong u v))
    (strong_of_univ (product_strongOn D.tensor_sum (D.left_strong u) (D.right_strong v)))
    (s := s) (by simp only [D.joint_initial, D.left_initial, D.right_initial])
  exact congrFun he t

end FoliationQM.DecoupledPropagator
