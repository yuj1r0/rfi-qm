module
public import FoliationQM.SpinPullbackImage

/-!
# Fibers of the pullback on physical Spin classes

For the smooth Spin classification supporting v13 `prop:takabayasi`, a
physical class and its twists by signs in the kernel of the degree-one
pullback have the same image. In a fiber containing a specified class,
the sign relating any two points is their original displacement. This
gives the fiber its action and torsor under that kernel.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackKernelFiber
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass SmoothSpinHOneTorsor
open GlobalSpinDisplacement SpinPullbackClasses SpinHOneGlobalPullback

universe u
variable {X B : Type u} {T ι EX EB ET HX HB HT : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup ET] [NormedSpace ℝ ET] [TopologicalSpace HT]
  [TopologicalSpace X] [ChartedSpace HX X] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace T] [ChartedSpace HT T]
  {IX : ModelWithCorners ℝ EX HX} {IB : ModelWithCorners ℝ EB HB} {K : ModelWithCorners ℝ ET HT}
  {n : WithTop ℕ∞} {proj : T → B} {L : GeometricPrincipalAtlas.Data (G := ProperFutureLorentz) proj ι}
  [IsManifold IX n X] (f : C(X, B)) (hf : ContMDiff IX IB n f)
  (LM : GeometricPrincipalSmoothAtlas.Data IB lorentzModel K L n)

/-- The actual fiber of the physical pullback map over a target isomorphism class. -/
abbrev Fiber (c : ConstructedPullbackSpinCriterion.Classes IX n f L) :=
  {q : PhysicalClass IB K L n // classMap f hf LM q = c}

variable {c : ConstructedPullbackSpinCriterion.Classes IX n f L}

/-- The displacement of two classes in one fiber is an element of the pullback kernel. -/
def kernelSign (p q : Fiber f hf LM c) : (pull f hf).ker :=
  ⟨displacement LM p.val q.val, (SpinPullbackImage.classMap_eq_iff_mem_ker f hf LM p.val q.val).mp
    (p.property.trans q.property.symm)⟩

variable [IsManifold IB n B]

/-- A kernel sign acts within the chosen fiber by twisting its original physical class. -/
def twist (k : (pull f hf).ker) (p : Fiber f hf LM c) : Fiber f hf LM c := by
  let := SmoothPullbackChartedSpace.chartedSpace HX LorentzManifold.Model f L
  refine ⟨act LM k.val p.val, ?_⟩
  have hk : pull f hf k.val = 1 := k.property
  exact (SpinPullbackTorsor.classMap_act f hf LM k.val p.val).trans
    (by rw [hk, act_one, p.property])

/-- A point of a fiber identifies that fiber with the kernel of degree-one pullback. -/
def equivAt (p : Fiber f hf LM c) : (pull f hf).ker ≃ Fiber f hf LM c where
  toFun k := twist f hf LM k p
  invFun q := kernelSign f hf LM p q
  left_inv k := Subtype.ext (displacement_act LM k.val p.val)
  right_inv q := Subtype.ext (act_displacement LM p.val q.val)

/-- The forward coordinate twists the chosen class by the kernel sign. -/
theorem equivAt_apply (p : Fiber f hf LM c) (k : (pull f hf).ker) :
    (equivAt f hf LM p k).val = act LM k.val p.val := rfl

/-- The inverse coordinate is the displacement from the reference class. -/
theorem equivAt_symm_apply (p q : Fiber f hf LM c) :
    ((equivAt f hf LM p).symm q).val = displacement LM p.val q.val := rfl

/-- The neutral kernel sign picks out the reference point. -/
theorem equivAt_one (p : Fiber f hf LM c) : equivAt f hf LM p 1 = p :=
  Subtype.ext (act_one LM p.val)

/-- Changing the reference in a fiber translates the coordinates by their kernel displacement. -/
theorem equivAt_change (p q : Fiber f hf LM c) (k : (pull f hf).ker) :
    equivAt f hf LM q k = equivAt f hf LM p (k * kernelSign f hf LM p q) :=
  Subtype.ext (basedEquiv_change LM p.val q.val k.val)

/-- Over the pulled image of any original physical class, the fiber is equivalent to the kernel. -/
def fiberEquiv (p : PhysicalClass IB K L n) :
    (pull f hf).ker ≃ Fiber f hf LM (classMap f hf LM p) :=
  equivAt f hf LM ⟨p, rfl⟩

/-- In the fiber over the image of a specified class, the forward map is the original twist. -/
theorem fiberEquiv_apply (p : PhysicalClass IB K L n) (k : (pull f hf).ker) :
    (fiberEquiv f hf LM p k).val = act LM k.val p := rfl

/-- Its inverse measures the original displacement between the two physical classes. -/
theorem fiberEquiv_symm_apply (p : PhysicalClass IB K L n) (q : Fiber f hf LM (classMap f hf LM p)) :
    ((fiberEquiv f hf LM p).symm q).val = displacement LM p q.val := rfl

/-- Exactly one kernel sign carries one chosen point of the fiber to another. -/
theorem existsUnique_twist (p q : Fiber f hf LM c) :
    ∃! k : (pull f hf).ker, twist f hf LM k p = q := by
  let e := equivAt f hf LM p
  exact ⟨e.symm q, e.apply_symm_apply q, fun k hk => e.injective (hk.trans (e.apply_symm_apply q).symm)⟩

/-- A represented fiber is a torsor with kernel twists as action and original displacement as division. -/
@[instance_reducible] def fiberTorsor (p : Fiber f hf LM c) : Torsor (pull f hf).ker (Fiber f hf LM c) where
  smul := twist f hf LM
  one_smul q := Subtype.ext (act_one LM q.val)
  mul_smul k l q := Subtype.ext (act_mul LM k.val l.val q.val)
  sdiv q r := kernelSign f hf LM r q
  nonempty := ⟨p⟩
  sdiv_smul' q r := Subtype.ext (act_displacement LM r.val q.val)
  smul_sdiv' k q := Subtype.ext (displacement_act LM k.val q.val)

end FoliationQM.SpinPullbackKernelFiber
