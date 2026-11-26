module
public import FoliationQM.DiracPolarCoordinates
public import FoliationQM.DiracRegularVariations
public import FoliationQM.DiracPolarVariation

/-!
# Transport of compact variations through Clifford polar reconstruction

For v13 `prop:takabayasi` and `thm:dirac_lift`, backgrounds agree
through the diffeomorphism on the open domain. Each transported family
takes its prescribed background value elsewhere. Transport preserves
the parameter set and compact carrier and recovers the original family
on every admissible parameter slice.
-/

@[expose] public section
noncomputable section
open scoped Topology ContDiff Manifold
namespace FoliationQM.DiracPolarVariationTransport
open DiracMatrices DiracPolarCoordinates DiracRegularVariations DiracPolarVariation
open SpinorRegularity

/-- The polar and spinor backgrounds correspond at every point of the given domain. -/
def Represents (U : Set Covector) (q : Covector → Q) (ψ : Covector → Spinor) : Prop :=
  ∀ x ∈ U, decode (q x) = ψ x

variable {U : Set Covector} {q : Covector → Q} {ψ : Covector → Spinor}

/-- Realization gives strict regularity on precisely the domain of comparison. -/
theorem regular_of_represents (h : Represents U q ψ) {x : Covector} (hx : x ∈ U) :
    Regular (ψ x) := (h x hx) ▸ regular_decode (q x)

/-- On a regular domain the physical inverse constructs a representing quotient field. -/
theorem encode_represents (hr : ∀ x ∈ U, Regular (ψ x)) :
    Represents U (fun y => encode (ψ y)) ψ := fun x hx => decode_encode (hr x hx)

/-- A representing quotient field is determined by the spinor on the given domain. -/
theorem encode_of_represents (h : Represents U q ψ) {x : Covector} (hx : x ∈ U) :
    encode (ψ x) = q x := by rw [← h x hx, encode_decode]

/-- Realization transports spatial smoothness in either direction on the open domain. -/
theorem smooth_iff (hU : IsOpen U) (h : Represents U q ψ) {n : WithTop ℕ∞} {x : Covector} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ, Covector) model n q x ↔ ContDiffAt ℝ n ψ x := by
  constructor
  · intro hq
    exact (contDiffAt_decode hq).congr_of_eventuallyEq
      (Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => (h y hy).symm))
  · intro hψ
    exact (contMDiffAt_encode hψ (regular_of_represents h hx)).congr_of_eventuallyEq
      (Filter.mem_of_superset (hU.mem_nhds hx) (fun _ hy => (encode_of_represents h hy).symm))

/-- Use the family on the domain and its prescribed background elsewhere. -/
def onDomain {A : Type*} (U : Set Covector) (f : ℝ × Covector → A) (b : Covector → A)
    (z : ℝ × Covector) : A := by
  classical
  exact if z.2 ∈ U then f z else b z.2

/-- On the domain the patched family evaluates to the given field. -/
theorem onDomain_of_mem {A : Type*} {f : ℝ × Covector → A} {b : Covector → A}
    {z : ℝ × Covector} (hz : z.2 ∈ U) : onDomain U f b z = f z := by simp [onDomain, hz]

/-- Outside the domain the patched family evaluates to the background. -/
theorem onDomain_of_notMem {A : Type*} {f : ℝ × Covector → A} {b : Covector → A}
    {z : ℝ × Covector} (hz : z.2 ∉ U) : onDomain U f b z = b z.2 := by simp [onDomain, hz]

/-- Patching on an open spatial domain preserves the joint germ at every interior point. -/
theorem onDomain_germ {A : Type*} {f : ℝ × Covector → A} {b : Covector → A}
    (hU : IsOpen U) {z : ℝ × Covector} (hz : z.2 ∈ U) :
    onDomain U f b =ᶠ[𝓝 z] f :=
  Filter.mem_of_superset ((hU.preimage continuous_snd).mem_nhds hz) (fun _ hy => onDomain_of_mem hy)

/-- Transport a regular spinor variation to a variation in the actual quotient manifold. -/
def toPolar (hU : IsOpen U) (h : Represents U q ψ) (W : RegularVariation U ψ) : PolarVariation U q where
  family := onDomain U (fun z => encode (W.family z)) q
  params := W.params
  params_open := W.params_open
  zero_mem := W.zero_mem
  carrier := W.carrier
  compact := W.compact
  interior := W.interior
  initial x := by
    by_cases hx : x ∈ U
    · rw [onDomain_of_mem hx, W.initial, encode_of_represents h hx]
    · exact onDomain_of_notMem hx
  smooth t ht x hx := (contMDiffAt_encode (W.smooth t ht x hx) (W.regular t ht x hx)).congr_of_eventuallyEq
    (onDomain_germ hU hx)
  fixed t ht x hn := by
    by_cases hx : x ∈ U
    · rw [onDomain_of_mem hx, W.fixed t ht x hn, encode_of_represents h hx]
    · exact onDomain_of_notMem hx

/-- Realize a quotient variation as a compact variation of the original field, regular on U. -/
def toSpinor (hU : IsOpen U) (h : Represents U q ψ) (P : PolarVariation U q) : RegularVariation U ψ where
  family := onDomain U (fun z => decode (P.family z)) ψ
  params := P.params
  params_open := P.params_open
  zero_mem := P.zero_mem
  carrier := P.carrier
  compact := P.compact
  interior := P.interior
  initial x := by
    by_cases hx : x ∈ U
    · rw [onDomain_of_mem hx, P.initial, h x hx]
    · exact onDomain_of_notMem hx
  smooth t ht x hx := (contDiffAt_decode (P.smooth t ht x hx)).congr_of_eventuallyEq (onDomain_germ hU hx)
  fixed t ht x hn := by
    by_cases hx : x ∈ U
    · rw [onDomain_of_mem hx, P.fixed t ht x hn, h x hx]
    · exact onDomain_of_notMem hx
  regular t _ x hx := by rw [onDomain_of_mem hx]; exact regular_decode _

variable (hU : IsOpen U) (h : Represents U q ψ)

/-- Encoding preserves the entire parameter neighborhood and the chosen compact carrier. -/
theorem toPolar_domains (W : RegularVariation U ψ) :
    (toPolar hU h W).params = W.params ∧ (toPolar hU h W).carrier = W.carrier := ⟨rfl, rfl⟩

/-- Decoding preserves the entire parameter neighborhood and the chosen compact carrier. -/
theorem toSpinor_domains (P : PolarVariation U q) :
    (toSpinor hU h P).params = P.params ∧ (toSpinor hU h P).carrier = P.carrier := ⟨rfl, rfl⟩

/-- At an interior point the encoded quotient family uses the genuine inverse coordinates. -/
theorem toPolar_apply (W : RegularVariation U ψ) (t : ℝ) {x : Covector} (hx : x ∈ U) :
    (toPolar hU h W).family (t,x) = encode (W.family (t,x)) :=
  onDomain_of_mem (f := fun z => encode (W.family z)) (b := q) (z := (t,x)) hx

/-- At an interior point the spinor family is the actual realization of the quotient. -/
theorem toSpinor_apply (P : PolarVariation U q) (t : ℝ) {x : Covector} (hx : x ∈ U) :
    (toSpinor hU h P).family (t,x) = decode (P.family (t,x)) :=
  onDomain_of_mem (f := fun z => decode (P.family z)) (b := ψ) (z := (t,x)) hx

/-- A decoded slice and the quotient slice correspond throughout U. -/
theorem toSpinor_represents (P : PolarVariation U q) (t : ℝ) :
    Represents U (slice P t) (DiracCurveJetCalculus.slice (toSpinor hU h P).family t) :=
  fun _ hx => (toSpinor_apply hU h P t hx).symm

/-- An encoded slice realizes the input spinor slice on U for each admissible parameter. -/
theorem toPolar_represents (W : RegularVariation U ψ) {t : ℝ} (ht : t ∈ W.params) :
    Represents U (slice (toPolar hU h W) t) (DiracCurveJetCalculus.slice W.family t) := by
  intro x hx
  exact (congrArg decode (toPolar_apply hU h W t hx)).trans (decode_encode (W.regular t ht x hx))

/-- The quotient-to-spinor-to-quotient round trip restores each admissible slice everywhere. -/
theorem polar_roundtrip (P : PolarVariation U q) {t : ℝ} (ht : t ∈ P.params) :
    slice (toPolar hU h (toSpinor hU h P)) t = slice P t := by
  funext x
  by_cases hx : x ∈ U
  · exact (toPolar_apply hU h (toSpinor hU h P) t hx).trans
      (encode_of_represents (toSpinor_represents hU h P t) hx)
  · have hn : x ∉ P.carrier := fun hc => hx (P.interior hc)
    exact ((toPolar hU h (toSpinor hU h P)).fixed t ht x hn).trans (P.fixed t ht x hn).symm

/-- The spinor-to-quotient-to-spinor round trip restores each admissible slice everywhere. -/
theorem spinor_roundtrip (W : RegularVariation U ψ) {t : ℝ} (ht : t ∈ W.params) :
    DiracCurveJetCalculus.slice (toSpinor hU h (toPolar hU h W)).family t =
      DiracCurveJetCalculus.slice W.family t := by
  funext x
  by_cases hx : x ∈ U
  · exact ((toSpinor_represents hU h (toPolar hU h W) t) x hx).symm.trans
      ((toPolar_represents hU h W ht) x hx)
  · have hn : x ∉ W.carrier := fun hc => hx (W.interior hc)
    exact ((toSpinor hU h (toPolar hU h W)).fixed t ht x hn).trans (W.fixed t ht x hn).symm

end FoliationQM.DiracPolarVariationTransport
