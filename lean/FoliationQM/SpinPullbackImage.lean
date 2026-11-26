module
public import FoliationQM.SpinPullbackTorsor

/-!
# Kernel and image criteria for pullback of physical Spin classes

For the Spin-frame component of v13 `prop:takabayasi`, the kernel of the
map on global signs detects equality after base change. Given an original
physical class as reference, the range of that homomorphism detects which
classes on the new base arise by pullback.
-/

@[expose] public section
noncomputable section
open scoped Manifold
namespace FoliationQM.SpinPullbackImage
open CliffordSpinLorentzSmooth LorentzMatrixGroup SmoothSpinRelativeClass GlobalSpinDisplacement
open SpinAllCoverHOne SmoothSpinHOneTorsor SpinPullbackClasses SpinHOneGlobalPullback
open SmoothPrincipalPullback SmoothPullbackChartedSpace SpinPullbackDisplacement

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

/-- Two original physical classes have the same pullback exactly when their displacement belongs
to the kernel of pullback on global signs. -/
theorem classMap_eq_iff_mem_ker (p q : PhysicalClass IB K L n) :
    classMap f hf LM p = classMap f hf LM q ↔ displacement LM p q ∈ (pull f hf).ker := by
  let := chartedSpace HX LorentzManifold.Model f L
  rw [← displacement_one_iff (smoothAtlas f hf LM), displacement_pullback, MonoidHom.mem_ker]

/-- Injective pullback of global signs gives injective pullback of physical classes. -/
theorem classMap_injective_of_h1_injective (h : Function.Injective (pull f hf)) :
    Function.Injective (classMap f hf LM) := by
  intro p q he
  have hsign := (classMap_eq_iff_mem_ker f hf LM p q).mp he
  exact (displacement_one_iff LM p q).mp (h ((MonoidHom.mem_ker.mp hsign).trans (map_one (pull f hf)).symm))

variable [IsManifold IB n B]

/-- A physical class on the new base descends precisely when its displacement from the pulled
reference belongs to the image of the homomorphism on global signs. -/
theorem mem_range_iff (p : PhysicalClass IB K L n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    q ∈ Set.range (classMap f hf LM) ↔
      displacement (smoothAtlas f hf LM) (classMap f hf LM p) q ∈ (pull f hf).range := by
  let := chartedSpace HX LorentzManifold.Model f L
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨displacement LM p r, (displacement_pullback f hf LM p r).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨act LM g p, (SpinPullbackTorsor.classMap_act f hf LM g p).trans ?_⟩
    exact (act_eq_iff (smoothAtlas f hf LM) _ _ _).mpr hg.symm

/-- The displacement criterion for descent has the same truth value for all original references. -/
theorem range_reference_iff (p r : PhysicalClass IB K L n) (q : ConstructedPullbackSpinCriterion.Classes IX n f L) :
    letI := chartedSpace HX LorentzManifold.Model f L
    displacement (smoothAtlas f hf LM) (classMap f hf LM p) q ∈ (pull f hf).range ↔
      displacement (smoothAtlas f hf LM) (classMap f hf LM r) q ∈ (pull f hf).range :=
  (mem_range_iff f hf LM p q).symm.trans (mem_range_iff f hf LM r q)

/-- In the presence of an original reference class, physical pullback is injective
precisely when pullback on global signs is injective. -/
theorem classMap_injective_iff (p : PhysicalClass IB K L n) :
    Function.Injective (classMap f hf LM) ↔ Function.Injective (pull f hf) := by
  let := chartedSpace HX LorentzManifold.Model f L
  refine ⟨?_, classMap_injective_of_h1_injective f hf LM⟩
  intro h g k hg
  apply (basedEquiv LM p).injective
  apply h
  change classMap f hf LM (act LM g p) = classMap f hf LM (act LM k p)
  rw [SpinPullbackTorsor.classMap_act, SpinPullbackTorsor.classMap_act, hg]

/-- In the presence of an original reference class, every target class descends precisely
when pullback on global signs is surjective. -/
theorem classMap_surjective_iff (p : PhysicalClass IB K L n) :
    Function.Surjective (classMap f hf LM) ↔ Function.Surjective (pull f hf) := by
  let := chartedSpace HX LorentzManifold.Model f L
  constructor
  · intro h g
    let q := act (smoothAtlas f hf LM) g (classMap f hf LM p)
    obtain ⟨k, hk⟩ := (mem_range_iff f hf LM p q).mp (h q)
    exact ⟨k, hk.trans (displacement_act (smoothAtlas f hf LM) g _)⟩
  · intro h q
    exact (mem_range_iff f hf LM p q).mpr (h _)

/-- Given an original reference, physical classes correspond bijectively by pullback
precisely when the global sign homomorphism is bijective. -/
theorem classMap_bijective_iff (p : PhysicalClass IB K L n) :
    Function.Bijective (classMap f hf LM) ↔ Function.Bijective (pull f hf) :=
  and_congr (classMap_injective_iff f hf LM p) (classMap_surjective_iff f hf LM p)

end FoliationQM.SpinPullbackImage
