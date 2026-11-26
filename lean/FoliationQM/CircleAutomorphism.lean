module

public import FoliationQM.PhaseCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Continuous group automorphisms of the physical phase circle

Source: v13 `lem:uniqueness`, supporting unrestricted Euclidean-completion
rigidity. A continuous circle homomorphism is classified using a genuine
continuous lift through the exponential covering, unique lifting, and real
linearity of continuous additive maps. Injectivity then forces degree one
or minus one. No power formula is assumed for the original map.
-/

@[expose] public section

noncomputable section

namespace FoliationQM.CircleAutomorphism

open Function Topology

/-- A continuous circle homomorphism has an actual continuous additive real
lift along the exponential covering, normalized to zero at the origin. -/
theorem exists_continuous_additive_lift (f : Circle →* Circle) (hf : Continuous f) :
    ∃ g : ℝ →+ ℝ, Continuous g ∧ ∀ t : ℝ, Circle.exp (g t) = f (Circle.exp t) := by
  let : LocallyPathConnectedSpace ℝ :=
    LocallyPathConnectedSpace.of_bases (fun x : ℝ => Metric.nhds_basis_ball)
      (fun x r hr => (convex_ball x r).isPathConnected ⟨x, Metric.mem_ball_self hr⟩)
  let F : C(ℝ, Circle) := ⟨fun t => f (Circle.exp t), hf.comp Circle.exp.continuous⟩
  obtain ⟨g, ⟨hg0, hglift⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0 (by simp [F])
  have he (t : ℝ) : Circle.exp (g t) = f (Circle.exp t) := congrFun hglift t
  have hadd (x y : ℝ) : g (x + y) = g x + g y := by
    have hc : Circle.exp ∘ (fun t => g (t + y)) =
        Circle.exp ∘ (fun t => g t + g y) := by
      funext t
      simp only [Function.comp_apply, Circle.exp_add, he, map_mul]
    have h := Circle.isCoveringMap_exp.eq_of_comp_eq
      (g.continuous.comp (continuous_id.add_const y))
      (g.continuous.add_const (g y)) hc 0 (by simp [hg0])
    exact congrFun h x
  exact ⟨{ toFun := g, map_zero' := hg0, map_add' := hadd }, g.continuous, he⟩

/-- Every continuous group endomorphism of the actual circle is an integer
power map; the exponent is derived from the real covering lift. -/
theorem continuous_hom_eq_zpow (f : Circle →* Circle) (hf : Continuous f) :
    ∃ n : ℤ, ∀ z : Circle, f z = z ^ n := by
  obtain ⟨g, hg, he⟩ := exists_continuous_additive_lift f hf
  have hmul (t : ℝ) : g t = t * g 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul g hg t (1 : ℝ)
  have hp : Circle.exp (g (2 * Real.pi)) = 1 := by
    rw [he, Circle.exp_two_pi, map_one]
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hp
  have hg1 : g 1 = (n : ℝ) := by
    rw [hmul] at hn
    nlinarith [Real.pi_pos]
  refine ⟨n, ?_⟩
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [← he, hmul, hg1, mul_comm, Circle.exp_intCast_mul]

/-- An injective continuous circle homomorphism has only the two possible
angular actions: the original phase or its inverse. No surjectivity premise
or prescribed power representation is needed. -/
theorem continuous_injective_hom_eq_id_or_inv (f : Circle →* Circle)
    (hf : Continuous f) (hinj : Function.Injective f) :
    (∀ z : Circle, f z = z) ∨ (∀ z : Circle, f z = z⁻¹) := by
  obtain ⟨n, hpow⟩ := continuous_hom_eq_zpow f hf
  have hn : n ≠ 0 := by
    intro hn0
    have hconst : f (Circle.exp Real.pi) = f 1 := by
      rw [hpow, hpow, hn0]
      simp
    exact Circle.exp_pi_ne_one (hinj hconst)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hroot : (Circle.exp (2 * Real.pi / (n : ℝ))) ^ n = 1 := by
    rw [← Circle.exp_intCast_mul, mul_div_cancel₀ _ hnR, Circle.exp_two_pi]
  have hroot1 : Circle.exp (2 * Real.pi / (n : ℝ)) = 1 := by
    apply hinj
    rw [hpow, hpow, hroot, one_zpow]
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hroot1
  have hmulR : (n : ℝ) * (m : ℝ) = 1 := by
    have hm' := (div_eq_iff hnR).mp hm
    nlinarith [Real.pi_pos]
  have hnm : n * m = (1 : ℤ) := by exact_mod_cast hmulR
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · left
    intro z
    simpa only [h, zpow_one] using hpow z
  · right
    intro z
    simpa only [h, zpow_neg_one] using hpow z

/-- Every continuous multiplicative equivalence of the physical circle is
identity or inversion, as a consequence of the derived homomorphism classification. -/
theorem continuous_mulEquiv_eq_id_or_inv (e : Circle ≃* Circle) (he : Continuous e) :
    (∀ z : Circle, e z = z) ∨ (∀ z : Circle, e z = z⁻¹) :=
  continuous_injective_hom_eq_id_or_inv e.toMonoidHom he e.injective

/-- On complex coordinates the two possible continuous automorphisms are
identity and ordinary complex conjugation. -/
theorem continuous_injective_hom_coe_eq_id_or_conj (f : Circle →* Circle)
    (hf : Continuous f) (hinj : Function.Injective f) :
    (∀ z : Circle, (f z : ℂ) = z) ∨
      (∀ z : Circle, (f z : ℂ) = star (z : ℂ)) := by
  rcases continuous_injective_hom_eq_id_or_inv f hf hinj with h | h
  · exact Or.inl (fun z => congrArg (fun q : Circle => (q : ℂ)) (h z))
  · right
    intro z
    rw [h z, Circle.coe_inv_eq_conj]
    rfl

end FoliationQM.CircleAutomorphism
