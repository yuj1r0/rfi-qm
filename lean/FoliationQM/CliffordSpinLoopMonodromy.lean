module
public import FoliationQM.LorentzFundamentalGroup

/-!
# Actual Spin endpoints and the Lorentz loop obstruction

Source scope: the two-element fundamental group and Spin covering in
v13 Section 7, supporting `prop:takabayasi` and `eq:tetrad_rotor_map`.
An actual identity-based Lorentz loop is null-homotopic exactly when
its genuine Spin lift through the Clifford unit returns to that unit.
Its other endpoint is precisely the negative Clifford unit, and this
case is the nonzero class in the proved normalized ZMod 2 equivalence.

A genuine continuous Spin path from the unit to the negative unit
projects to an actual non-null Lorentz generator loop. Its homotopy
class is fixed by its endpoint, without prescribing a particular
rotation formula. Traversing any based Lorentz loop twice is
null-homotopic. The actual connected two-sheeted covering also admits
no global continuous section. These are topological statements, not
connection-dependent transport or a spacetime Spin-structure claim.
-/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
open Function
namespace FoliationQM.CliffordSpinLoopMonodromy
open CliffordSpinMap CliffordSpinLorentz CliffordSpinCovering LorentzMatrixGroup
open CliffordSpinPathLifting CliffordSpinSignKernel LorentzFundamentalGroup

/-- The actual fundamental-group class of an identity-based physical Lorentz loop. -/
def loopClass (γ : Path (1 : ProperFutureLorentz) 1) :
    FundamentalGroup ProperFutureLorentz 1 := FundamentalGroup.fromPath (.mk γ)

/-- The actual Clifford Spin lift of an identity-based Lorentz loop through the genuine Clifford unit. -/
def liftLoop (γ : Path (1 : ProperFutureLorentz) 1) : C(I, Spin) :=
  pathLift γ 1 (γ.source.trans (map_one lorentzHom).symm)

/-- Actual path concatenation has the library's reversed fundamental-group multiplication order. -/
theorem loopClass_trans (γ δ : Path (1 : ProperFutureLorentz) 1) :
    loopClass (γ.trans δ) = loopClass δ * loopClass γ := rfl

/-- An actual based Lorentz loop has trivial fundamental-group class exactly when it is homotopic relative to its endpoints to the constant loop. -/
theorem loopClass_eq_one_iff (γ : Path (1 : ProperFutureLorentz) 1) :
    loopClass γ = 1 ↔ γ.Homotopic (Path.refl 1) := by
  constructor
  · intro h
    exact Path.Homotopic.Quotient.eq.mp
      (congrArg (fun c : FundamentalGroup ProperFutureLorentz 1 => c.asHom) h)
  · intro h
    exact congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr h)

/-- The actual Lorentz loop class is trivial exactly when its genuine Clifford Spin lift closes at the Clifford unit. -/
theorem loopClass_eq_one_iff_lift_closes (γ : Path (1 : ProperFutureLorentz) 1) :
    loopClass γ = 1 ↔ liftLoop γ 1 = 1 := by
  rw [← fundamentalGroupEquiv.map_eq_one_iff, fundamentalGroupEquiv_eq_one_iff]
  rfl

/-- An actual identity-based Lorentz loop is null-homotopic precisely when its genuine Spin lift through the unit returns to the unit. -/
theorem loop_nullhomotopic_iff_lift_closes (γ : Path (1 : ProperFutureLorentz) 1) :
    γ.Homotopic (Path.refl 1) ↔ liftLoop γ 1 = 1 :=
  (loopClass_eq_one_iff γ).symm.trans (loopClass_eq_one_iff_lift_closes γ)

/-- The endpoint of the genuine Spin lift of any identity-based physical loop is exactly one of the two actual Clifford signs. -/
theorem liftLoop_one_eq_or_negative (γ : Path (1 : ProperFutureLorentz) 1) :
    liftLoop γ 1 = 1 ∨ liftLoop γ 1 = CliffordSpinEquivalence.negativeOne := by
  apply (lorentzHom_eq_one_iff _).mp
  exact (congrFun (pathLift_projects γ 1
    (γ.source.trans (map_one lorentzHom).symm)) 1).trans γ.target

/-- A based Lorentz loop is non-null-homotopic exactly when its actual Spin lift ends at the genuine negative Clifford unit. -/
theorem loop_not_nullhomotopic_iff_lift_negative (γ : Path (1 : ProperFutureLorentz) 1) :
    ¬ γ.Homotopic (Path.refl 1) ↔ liftLoop γ 1 = CliffordSpinEquivalence.negativeOne := by
  rw [loop_nullhomotopic_iff_lift_closes]
  constructor
  · intro h
    exact (liftLoop_one_eq_or_negative γ).resolve_left h
  · intro h he
    exact CliffordSpinEquivalence.negativeOne_ne_one (h.symm.trans he)

/-- The normalized nonzero ZMod 2 class is exactly the loop whose genuine Spin lift has the actual negative Clifford endpoint. -/
theorem loopClass_eq_generator_iff_lift_negative (γ : Path (1 : ProperFutureLorentz) 1) :
    fundamentalGroupEquiv (loopClass γ) = Multiplicative.ofAdd (1 : ZMod 2) ↔
      liftLoop γ 1 = CliffordSpinEquivalence.negativeOne := by
  rw [← kernelEquivZModTwo_generator, fundamentalGroupEquiv_eq_kernel_iff]
  rfl

/-- An actual continuous path in genuine Spin from its unit to the negative Clifford unit, supplied by the proved path connectivity. -/
def signPath : Path (1 : Spin) CliffordSpinEquivalence.negativeOne :=
  PathConnectedSpace.somePath 1 CliffordSpinEquivalence.negativeOne

/-- The physical projection of the actual unit-to-negative-unit Spin path is an identity-based Lorentz loop. -/
def generatorLoop : Path (1 : ProperFutureLorentz) 1 where
  toFun t := lorentzHom (signPath t)
  continuous_toFun := lorentzHom_isCoveringMap.continuous.comp signPath.continuous
  source' := by rw [signPath.source, map_one]
  target' := by
    rw [signPath.target]
    exact (lorentzHom_eq_one_iff _).mpr (Or.inr rfl)

/-- Lifting the projected actual generator through the Clifford unit returns exactly the original unit-to-negative-unit Spin path. -/
theorem liftLoop_generatorLoop : liftLoop generatorLoop = signPath.toContinuousMap := by
  symm
  apply (eq_pathLift_iff generatorLoop 1 _ signPath.toContinuousMap).mpr
  exact ⟨rfl, signPath.source⟩

/-- The projected actual Spin path represents precisely the nonzero normalized generator of the Lorentz fundamental group. -/
theorem generatorLoop_class :
    fundamentalGroupEquiv (loopClass generatorLoop) = Multiplicative.ofAdd (1 : ZMod 2) := by
  apply (loopClass_eq_generator_iff_lift_negative generatorLoop).mpr
  exact (congrArg (fun f : C(I, Spin) => f 1) liftLoop_generatorLoop).trans signPath.target

/-- The explicitly defined projected Spin path is an actual non-null-homotopic Lorentz loop. -/
theorem generatorLoop_not_nullhomotopic : ¬ generatorLoop.Homotopic (Path.refl 1) := by
  apply (loop_not_nullhomotopic_iff_lift_negative generatorLoop).mpr
  exact (congrArg (fun f : C(I, Spin) => f 1) liftLoop_generatorLoop).trans signPath.target

/-- Traversing any actual identity-based Lorentz loop twice is null-homotopic, by the proved two-element fundamental group and the genuine path composition convention. -/
theorem doubled_loop_nullhomotopic (γ : Path (1 : ProperFutureLorentz) 1) :
    (γ.trans γ).Homotopic (Path.refl 1) := by
  apply (loopClass_eq_one_iff _).mp
  apply fundamentalGroupEquiv.injective
  rw [map_one, loopClass_trans, map_mul]
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd (fundamentalGroupEquiv (loopClass γ)) +
    Multiplicative.toAdd (fundamentalGroupEquiv (loopClass γ)) = (0 : ZMod 2)
  rw [← two_mul]
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- The actual Spin covering has no global continuous individual section over the entire Lorentz group; its connected source and genuine nontrivial sign fiber obstruct such a section. -/
theorem no_continuous_section :
    ¬ ∃ f : C(ProperFutureLorentz, Spin), lorentzHom ∘ f = id := by
  rintro ⟨f, hf⟩
  let s : Spin := f 1
  have hs : lorentzHom s = 1 := congrFun hf 1
  have he : lorentzHom ∘ (f ∘ lorentzHom) = lorentzHom ∘ id := by
    funext a
    exact congrFun hf (lorentzHom a)
  have hanchor : (f ∘ lorentzHom) s = id s := by
    change f (lorentzHom s) = s
    rw [hs]
  have hu := continuous_lift_unique
    (f.continuous.comp lorentzHom_isCoveringMap.continuous) continuous_id he s hanchor
  have h1 : f 1 = (1 : Spin) := by
    simpa only [Function.comp_apply, map_one, id_eq] using congrFun hu (1 : Spin)
  have hnegative : lorentzHom CliffordSpinEquivalence.negativeOne = 1 :=
    (lorentzHom_eq_one_iff _).mpr (Or.inr rfl)
  have hn : f 1 = CliffordSpinEquivalence.negativeOne := by
    simpa only [Function.comp_apply, hnegative, id_eq] using
      congrFun hu CliffordSpinEquivalence.negativeOne
  exact CliffordSpinEquivalence.negativeOne_ne_one (hn.symm.trans h1)

end FoliationQM.CliffordSpinLoopMonodromy
