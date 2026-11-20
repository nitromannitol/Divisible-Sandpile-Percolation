import Sandpile.External.Stopping.IndependentBlocks

/-!
# Independent observations of disjoint blocks

Measurable observations of an independent field are independent when each
observation depends only on its own block of coordinates.
-/

open MeasureTheory ProbabilityTheory Set

namespace Sandpile.External.Stopping

/-- A measurable function depending only on a set of coordinates factors
measurably through restriction to that set. -/
theorem exists_measurable_restriction_factor {V α E : Type*} [MeasurableSpace α]
    [Inhabited α] [MeasurableSpace E] (A : Set V) (f : (V → α) → E)
    (hf : Measurable f) (hdep : ∀ x y, (∀ i ∈ A, x i = y i) → f x = f y) :
    ∃ g : (A → α) → E, Measurable g ∧ ∀ x, g (A.domRestrict x) = f x := by
  classical
  let ext : (A → α) → V → α := fun z i => if hi : i ∈ A then z ⟨i, hi⟩ else default
  have hext : Measurable ext := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ A
    · simpa only [ext, dite_eq_left hi] using (measurable_pi_apply (⟨i, hi⟩ : A))
    · simpa only [ext, dite_eq_right hi] using (measurable_const : Measurable (fun _ : A → α => (default : α)))
  refine ⟨f ∘ ext, hf.comp hext, ?_⟩
  intro x
  apply hdep
  intro i hi
  simp only [ext, dite_eq_left hi, Set.domRestrict_apply]

/-- Measurable functions of disjoint coordinate sets of an i.i.d. field are
independent. -/
theorem indepFun_of_depends_on_disjoint_blocks {V α E F : Type*}
    [MeasurableSpace α] [Inhabited α] [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure α) [IsProbabilityMeasure ν] (A B : Set V) (hAB : Disjoint A B)
    (f : (V → α) → E) (g : (V → α) → F) (hf : Measurable f) (hg : Measurable g)
    (hfd : ∀ x y, (∀ i ∈ A, x i = y i) → f x = f y)
    (hgd : ∀ x y, (∀ i ∈ B, x i = y i) → g x = g y) :
    IndepFun f g (Measure.infinitePi fun _ : V => ν) := by
  classical
  obtain ⟨f', hf', hfeq⟩ := exists_measurable_restriction_factor A f hf hfd
  obtain ⟨g', hg', hgeq⟩ := exists_measurable_restriction_factor B g hg hgd
  let C : Bool → Set V := fun b => if b then A else B
  have hC : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [Function.onFun, C, disjoint_comm]
  have h := (iIndepFun_restrict_infinitePi ν C hC).indepFun (i := true) (j := false) (by decide)
  have h' := h.comp hf' hg'
  convert h' using 1 <;> funext x <;> simp [C, hfeq, hgeq]

end Sandpile.External.Stopping
