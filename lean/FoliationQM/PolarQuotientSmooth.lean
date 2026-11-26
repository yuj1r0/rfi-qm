module
public import FoliationQM.PolarDatumSmooth
public import FoliationQM.RegularPolarHomeomorph

/-!
# Independent local smooth lifts for the natural polar quotient

Sources: the local smooth polar representation in v13 `prop:takabayasi`
and `eq:takabayasi_polar`. Local smoothness is defined independently by
an actual datum field whose complex amplitude and complex matrix are
real-smooth to the requested order, and whose natural quotient projection
agrees with the quotient field on a neighborhood. The definition uses
neither smoothness of the realized spinor nor a transported structure.

The genuine realization map and the explicit principal/rotated local
sections prove that this criterion is equivalent to real smoothness of
the actual spinor field. Global and open-domain versions follow, as do
smooth precomposition and reconstruction of sign classes from smooth
regular-spinor fields. At order zero the global criterion agrees with
the existing natural quotient topology. The pointwise criterion implies
continuity at the point; no converse from mere pointwise continuity is
asserted. These are actual coordinate-lift characterizations, not an
abstract quotient-manifold or Spin classification theorem, and they do
not choose one globally smooth datum representative.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Topology
open Filter Topology
namespace FoliationQM.PolarQuotientSmooth
open PolarSignQuotient PolarDatumTopology PolarDatumSmooth RegularPolarHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quotient field is locally smooth at a point when it has an actual polar datum lift with smooth amplitude and matrix coordinates and eventual equality of its quotient class. -/
def LocalSmoothLiftAt (n : WithTop ℕ∞) (f : E → PolarQuotient) (x : E) : Prop :=
  ∃ d : E → Datum, CoordinateContDiffAt n d x ∧
    (fun y => Quotient.mk signSetoid (d y)) =ᶠ[𝓝 x] f

/-- A quotient field is locally smooth everywhere when every point admits a coordinate-smooth local datum lift. -/
def LocallySmooth (n : WithTop ℕ∞) (f : E → PolarQuotient) : Prop :=
  ∀ x, LocalSmoothLiftAt n f x

/-- A quotient field is locally smooth on a set when each of its points has a coordinate-smooth datum lift on an ambient neighborhood. -/
def LocallySmoothOn (n : WithTop ℕ∞) (f : E → PolarQuotient) (s : Set E) : Prop :=
  ∀ x ∈ s, LocalSmoothLiftAt n f x

/-- The independently defined local datum-lift criterion is equivalent to genuine real smoothness of the actual realized spinor field. -/
theorem localSmoothLiftAt_iff {n : WithTop ℕ∞} {f : E → PolarQuotient} {x : E} :
    LocalSmoothLiftAt n f x ↔
      ContDiffAt ℝ n (fun y => (toRegular (f y)).val) x := by
  constructor
  · rintro ⟨d, hd, he⟩
    apply (contDiffAt_realize hd).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact congrArg (fun q => (toRegular q).val) hy.symm
  · intro hf
    obtain ⟨d, hd, he⟩ := exists_coordinateContDiffAt_lift n
      (fun y => toRegular (f y)) hf
    refine ⟨d, hd, Filter.Eventually.of_forall ?_⟩
    intro y
    exact toRegular_bijective.injective (he y)

/-- Eventual equality of quotient fields preserves the independent local smooth-lift criterion. -/
theorem localSmoothLiftAt_congr {n : WithTop ℕ∞} {f g : E → PolarQuotient} {x : E}
    (h : LocalSmoothLiftAt n f x) (he : f =ᶠ[𝓝 x] g) : LocalSmoothLiftAt n g x := by
  obtain ⟨d, hd, hdf⟩ := h
  exact ⟨d, hd, hdf.trans he⟩

/-- An actual coordinate-smooth datum field gives a locally smooth quotient field by the natural projection. -/
theorem localSmoothLiftAt_mk {n : WithTop ℕ∞} {d : E → Datum} {x : E}
    (hd : CoordinateContDiffAt n d x) :
    LocalSmoothLiftAt n (fun y => Quotient.mk signSetoid (d y)) x :=
  ⟨d, hd, Filter.EventuallyEq.rfl⟩

/-- A local coordinate-smooth lift makes the quotient field continuous at the point in its existing natural quotient topology. -/
theorem localSmoothLiftAt_continuousAt {n : WithTop ℕ∞} {f : E → PolarQuotient} {x : E}
    (h : LocalSmoothLiftAt n f x) : ContinuousAt f x := by
  obtain ⟨d, hd, he⟩ := h
  have hdc : ContinuousAt d x := PolarDatumTopology.continuousAt_iff.mpr
    ⟨hd.1.continuousAt, hd.2.continuousAt⟩
  exact (quotient_mk_continuous.continuousAt.comp hdc).congr_of_eventuallyEq he.symm

/-- Lowering the requested differentiability order preserves actual local smooth datum lifts. -/
theorem localSmoothLiftAt_of_le {m n : WithTop ℕ∞} {f : E → PolarQuotient} {x : E}
    (h : LocalSmoothLiftAt n f x) (hmn : m ≤ n) : LocalSmoothLiftAt m f x := by
  obtain ⟨d, hd, he⟩ := h
  exact ⟨d, ⟨hd.1.of_le hmn, hd.2.of_le hmn⟩, he⟩

/-- Smooth precomposition preserves the local datum-lift criterion for quotient fields. -/
theorem localSmoothLiftAt_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {f : E → PolarQuotient} {g : F → E} {x : F}
    (hf : LocalSmoothLiftAt n f (g x)) (hg : ContDiffAt ℝ n g x) :
    LocalSmoothLiftAt n (f ∘ g) x := by
  exact localSmoothLiftAt_iff.mpr ((localSmoothLiftAt_iff.mp hf).comp x hg)

/-- The global local-lift criterion is equivalent to genuine global smoothness of the actual realized spinor field. -/
theorem locallySmooth_iff {n : WithTop ℕ∞} {f : E → PolarQuotient} :
    LocallySmooth n f ↔ ContDiff ℝ n (fun y => (toRegular (f y)).val) := by
  simp only [LocallySmooth, localSmoothLiftAt_iff, contDiff_iff_contDiffAt]

/-- On an open domain, ambient local coordinate-smooth lifts are equivalent to actual smoothness of the realized spinor field throughout that domain. -/
theorem locallySmoothOn_iff {n : WithTop ℕ∞} {f : E → PolarQuotient}
    {s : Set E} (hs : IsOpen s) :
    LocallySmoothOn n f s ↔ ContDiffOn ℝ n (fun y => (toRegular (f y)).val) s := by
  constructor
  · intro h x hx
    exact (localSmoothLiftAt_iff.mp (h x hx)).contDiffWithinAt
  · intro h x hx
    exact localSmoothLiftAt_iff.mpr (h.contDiffAt (hs.mem_nhds hx))

/-- At order zero the global local-lift criterion recovers continuity in the existing natural quotient topology. -/
theorem locallySmooth_zero_iff {f : E → PolarQuotient} :
    LocallySmooth 0 f ↔ Continuous f := by
  constructor
  · intro h
    exact continuous_iff_continuousAt.mpr (fun x => localSmoothLiftAt_continuousAt (h x))
  · intro h
    apply locallySmooth_iff.mpr
    apply contDiff_zero.mpr
    exact continuous_subtype_val.comp (continuous_toRegular.comp h)

/-- The existing quotient inverse of any actual smooth regular-spinor field satisfies the independent local smooth-lift criterion. -/
theorem localSmoothLiftAt_ofRegular {n : WithTop ℕ∞} {f : E → RegularSpinor} {x : E}
    (hf : ContDiffAt ℝ n (fun y => (f y).val) x) :
    LocalSmoothLiftAt n (fun y => ofRegular (f y)) x := by
  apply localSmoothLiftAt_iff.mpr
  simpa only [toRegular_ofRegular] using hf

/-- Globally smooth actual regular-spinor fields give globally locally smooth sign classes through the already constructed quotient inverse. -/
theorem locallySmooth_ofRegular {n : WithTop ℕ∞} {f : E → RegularSpinor}
    (hf : ContDiff ℝ n (fun y => (f y).val)) :
    LocallySmooth n (fun y => ofRegular (f y)) := by
  apply locallySmooth_iff.mpr
  simpa only [toRegular_ofRegular] using hf

end FoliationQM.PolarQuotientSmooth
