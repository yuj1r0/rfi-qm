module
public import FoliationQM.RegularSpinorManifold
public import FoliationQM.PolarManifoldCharts
public import FoliationQM.PolarQuotientSmooth
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# A concrete manifold and diffeomorphism for the natural polar quotient

Sources: the concrete polar quotient component of v13 `prop:takabayasi`
and `eq:takabayasi_polar`. The existing natural sign-quotient topology is
unchanged. Its actual realized-spinor map is an open embedding onto the
strict invariant-regular domain, giving an explicit singleton atlas with
the real spinor model space. The existing regular-spinor realization and
its existing quotient-valued inverse form a genuine bundled diffeomorphism
for these specified atlases, with exactly the earlier homeomorphism as
the underlying topological map.

Compatibility with actual amplitude and matrix coordinates is proved:
for fields from real normed spaces, manifold smoothness is equivalent to
the independently defined local smooth datum-lift criterion from
PolarQuotientSmooth. The global and open-domain formulations retain their
precise domains. Thus this is more than an unchecked assignment of a
transported atlas. It does not identify the concrete determinant-one
model with an abstract Spin group, prove an abstract Spin-to-Lorentz
covering, choose a global individual representative, or derive dynamics.
-/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.Operator Manifold Topology
open Filter Topology Set
namespace FoliationQM.PolarQuotientManifold
open DiracMatrices SpinorRegularity PolarSignQuotient RegularPolarHomeomorph PolarQuotientSmooth

/-- The actual spinor value of a natural polar sign class, using its already proved realization. -/
def value (q : PolarQuotient) : Spinor := (toRegular q).val

/-- The natural polar quotient is nonempty because its existing inverse sends any regular spinor to a sign class. -/
instance instNonemptyPolarQuotient : Nonempty PolarQuotient :=
  ⟨ofRegular (Classical.choice RegularSpinorManifold.instNonemptyRegularSpinor)⟩

/-- The actual realized-spinor value is an open embedding for the independently established natural quotient topology. -/
theorem isOpenEmbedding_value : IsOpenEmbedding value :=
  RegularSpinorManifold.isOpenEmbedding_value.comp regularHomeomorph.isOpenEmbedding

/-- The image of the actual quotient value map is exactly the strict invariant-regular spinor domain. -/
theorem range_value : Set.range value = {psi : Spinor | Regular psi} := by
  ext psi
  constructor
  · rintro ⟨q, rfl⟩
    exact (toRegular q).property
  · intro hpsi
    exact ⟨ofRegular ⟨psi, hpsi⟩, congrArg Subtype.val (toRegular_ofRegular ⟨psi, hpsi⟩)⟩

/-- The natural sign quotient has the singleton atlas supplied by its actual open realized-spinor embedding. -/
instance instChartedSpacePolarQuotient : ChartedSpace Spinor PolarQuotient :=
  isOpenEmbedding_value.singletonChartedSpace

/-- The actual singleton atlas makes the natural quotient a real manifold to every requested differentiability order. -/
instance instIsManifoldPolarQuotient (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ, Spinor) n PolarQuotient :=
  isOpenEmbedding_value.isManifold_singleton

/-- Every preferred quotient chart is exactly the actual realized-spinor map. -/
theorem chartAt_value (q r : PolarQuotient) : chartAt Spinor q r = value r := rfl

/-- The actual quotient chart is defined on every sign class. -/
theorem chartAt_source (q : PolarQuotient) : (chartAt Spinor q).source = Set.univ := rfl

/-- The target of every actual quotient chart is exactly the open strict regular-spinor domain. -/
theorem chartAt_target (q : PolarQuotient) :
    (chartAt Spinor q).target = {psi : Spinor | Regular psi} := by
  change (isOpenEmbedding_value.toOpenPartialHomeomorph value).target = _
  rw [isOpenEmbedding_value.toOpenPartialHomeomorph_target value]
  exact range_value

/-- The actual realized-spinor embedding of the natural quotient is manifold-smooth to every requested order. -/
theorem contMDiff_value (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n value :=
  contMDiff_isOpenEmbedding isOpenEmbedding_value

/-- The existing realization from sign classes to regular spinors is smooth for the explicitly specified natural atlases. -/
theorem contMDiff_toRegular (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n toRegular := by
  exact (contMDiff_value n).of_comp_isOpenEmbedding RegularSpinorManifold.isOpenEmbedding_value

/-- The existing quotient-valued reconstruction of a regular spinor is smooth for the specified atlases. -/
theorem contMDiff_ofRegular (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) n ofRegular := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_value
  simpa only [Function.comp_def, value, toRegular_ofRegular] using
    RegularSpinorManifold.contMDiff_value n

/-- The already constructed polar quotient equivalence is a genuine bundled diffeomorphism for the stated natural quotient and regular-spinor atlases. -/
def regularDiffeomorph (n : WithTop ℕ∞) :
    Diffeomorph 𝓘(ℝ, Spinor) 𝓘(ℝ, Spinor) PolarQuotient RegularSpinor n where
  toEquiv := regularEquiv
  contMDiff_toFun := contMDiff_toRegular n
  contMDiff_invFun := contMDiff_ofRegular n

/-- The bundled diffeomorphism evaluates to the pre-existing actual quotient realization. -/
theorem regularDiffeomorph_apply (n : WithTop ℕ∞) (q : PolarQuotient) :
    regularDiffeomorph n q = toRegular q := rfl

/-- The inverse bundled diffeomorphism evaluates to the pre-existing reconstructed sign class. -/
theorem regularDiffeomorph_symm_apply (n : WithTop ℕ∞) (q : RegularSpinor) :
    (regularDiffeomorph n).symm q = ofRegular q := rfl

/-- The actual diffeomorphism has exactly the earlier natural quotient homeomorphism as its underlying topological map. -/
theorem regularDiffeomorph_toHomeomorph (n : WithTop ℕ∞) :
    (regularDiffeomorph n).toHomeomorph = regularHomeomorph := by
  ext q
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Manifold smoothness of a normed-domain quotient field at a point is exactly the independently defined existence of a smooth local amplitude/matrix lift. -/
theorem contMDiffAt_iff_localSmoothLiftAt {n : WithTop ℕ∞}
    {f : E → PolarQuotient} {x : E} :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f x ↔ LocalSmoothLiftAt n f x := by
  exact (PolarManifoldCharts.contMDiffAt_iff_contDiffAt isOpenEmbedding_value).trans
    localSmoothLiftAt_iff.symm

/-- Global manifold smoothness of a quotient field is exactly the independent local amplitude/matrix lifting criterion at every point. -/
theorem contMDiff_iff_locallySmooth {n : WithTop ℕ∞} {f : E → PolarQuotient} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f ↔ LocallySmooth n f := by
  exact (PolarManifoldCharts.contMDiff_iff_contDiff isOpenEmbedding_value).trans
    locallySmooth_iff.symm

/-- On an open normed domain, manifold smoothness agrees with independent smooth local amplitude/matrix representatives at every point of that domain. -/
theorem contMDiffOn_iff_locallySmoothOn {n : WithTop ℕ∞} {f : E → PolarQuotient}
    {s : Set E} (hs : IsOpen s) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Spinor) n f s ↔ LocallySmoothOn n f s := by
  exact (PolarManifoldCharts.contMDiffOn_iff_contDiffOn isOpenEmbedding_value).trans
    (locallySmoothOn_iff hs).symm

end FoliationQM.PolarQuotientManifold
