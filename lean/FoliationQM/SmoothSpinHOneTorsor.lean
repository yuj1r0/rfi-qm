module
public import FoliationQM.GlobalSpinRealization

/-!
# The all-cover classification of smooth Spin lifts

For the geometric Spin-frame component of v13 `prop:takabayasi`, choosing
one smooth physical lift identifies the all-cover sign group with all
physical isomorphism classes over the target. The inverse measures
the global transition ratio from the chosen lift. Changing the reference
translates these coordinates by the relative sign of the two references.
-/

@[expose] public section
noncomputable section
namespace FoliationQM.SmoothSpinHOneTorsor
open CliffordSpinLorentzSmooth LorentzMatrixGroup GeometricSpinObstruction
open SpinAllCoverHOne SmoothSpinRelativeClass GlobalSpinDisplacement

universe u
variable {E H EP HP : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {B : Type u} [TopologicalSpace B] [ChartedSpace H B] {I : ModelWithCorners ℝ E H}
  {P ι : Type*} [TopologicalSpace P] [ChartedSpace HP P] {KP : ModelWithCorners ℝ EP HP}
  {proj : P → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  {n : WithTop ℕ∞} (LM : GeometricPrincipalSmoothAtlas.Data I lorentzModel KP L n)
  [IsManifold I n B]

/-- A reference physical class identifies the global sign group with the smooth
Spin lifts up to principal diffeomorphism over the physical Lorentz target. -/
def basedEquiv (p : PhysicalClass I KP L n) : GlobalH1 I B n ≃ PhysicalClass I KP L n :=
  (Equiv.ofBijective (displacement LM p)
    ⟨based_injective LM p, GlobalSpinRealization.surjective LM p⟩).symm

/-- The inverse of the classification measures the relative sign from the reference class. -/
theorem basedEquiv_symm_apply (p q : PhysicalClass I KP L n) :
    (basedEquiv LM p).symm q = displacement LM p q := rfl

/-- Twisting a physical class by a global sign amounts to realizing that sign relative
to the input class. -/
def act (g : GlobalH1 I B n) (p : PhysicalClass I KP L n) : PhysicalClass I KP L n :=
  basedEquiv LM p g

/-- Measuring the displacement of a twist returns the original global sign. -/
theorem displacement_act (g : GlobalH1 I B n) (p : PhysicalClass I KP L n) :
    displacement LM p (act LM g p) = g :=
  (basedEquiv LM p).left_inv g

/-- Twisting the first lift by its displacement from the second realizes the second class. -/
theorem act_displacement (p q : PhysicalClass I KP L n) :
    act LM (displacement LM p q) p = q :=
  (basedEquiv LM p).right_inv q

/-- A given global sign twists one lift class into another exactly when it is their
global transition difference. -/
theorem act_eq_iff (g : GlobalH1 I B n) (p q : PhysicalClass I KP L n) :
    act LM g p = q ↔ displacement LM p q = g := by
  constructor
  · rintro rfl
    exact displacement_act LM g p
  · rintro rfl
    exact act_displacement LM p q

/-- The neutral sign fixes every smooth physical lift class. -/
theorem act_one (p : PhysicalClass I KP L n) : act LM 1 p = p :=
  (act_eq_iff LM 1 p p).mpr ((displacement_one_iff LM p p).mpr rfl)

/-- The unit coordinate classifies the chosen reference itself. -/
theorem basedEquiv_one (p : PhysicalClass I KP L n) : basedEquiv LM p 1 = p :=
  act_one LM p

/-- Successive twists of a physical lift class multiply the global signs. -/
theorem act_mul (g h : GlobalH1 I B n) (p : PhysicalClass I KP L n) :
    act LM (g * h) p = act LM g (act LM h p) := by
  apply (act_eq_iff LM _ _ _).mpr
  rw [← displacement_comp LM p (act LM h p) (act LM g (act LM h p)),
    displacement_act, displacement_act]

/-- Changing the reference physical lift translates all its coordinates by the
displacement between the two references. -/
theorem basedEquiv_change (p q : PhysicalClass I KP L n) (g : GlobalH1 I B n) :
    basedEquiv LM q g = basedEquiv LM p (g * displacement LM p q) := by
  change act LM g q = act LM (g * displacement LM p q) p
  rw [act_mul, act_displacement]

/-- Exactly one global sign carries any given smooth physical lift class to another. -/
theorem existsUnique_act (p q : PhysicalClass I KP L n) :
    ∃! g : GlobalH1 I B n, act LM g p = q := by
  refine ⟨displacement LM p q, act_displacement LM p q, ?_⟩
  intro g hg
  exact ((act_eq_iff LM g p q).mp hg).symm

/-- A global sign stabilizes a smooth physical lift class exactly when it is neutral. -/
theorem act_eq_self_iff (g : GlobalH1 I B n) (p : PhysicalClass I KP L n) :
    act LM g p = p ↔ g = 1 := by
  rw [act_eq_iff, (displacement_one_iff LM p p).mpr rfl, eq_comm]

/-- When a smooth Spin lift exists, all its physical isomorphism classes form a
torsor under the all-cover degree-one group of Clifford signs. -/
@[instance_reducible] def torsor (h : Nonempty (SmoothLift I KP L n)) :
    Torsor (GlobalH1 I B n) (PhysicalClass I KP L n) where
  smul := act LM
  one_smul := act_one LM
  mul_smul := act_mul LM
  sdiv q p := displacement LM p q
  nonempty := h.map physicalClass
  sdiv_smul' q p := act_displacement LM p q
  smul_sdiv' := displacement_act LM

end FoliationQM.SmoothSpinHOneTorsor
