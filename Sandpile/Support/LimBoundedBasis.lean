import Mathlib

/-!
# An essentially bounded Hilbert basis for `L²`

Shows that a dense submodule of a separable real Hilbert space contains a Hilbert basis, by
applying Gram-Schmidt to a dense sequence and discarding the vectors it sends to zero. The
essentially bounded elements of `L²` form such a dense submodule, since they contain every
simple function, so `L²` has an essentially bounded Hilbert basis indexed by a subset of the
natural numbers, including in finite dimension.
-/

open MeasureTheory ProbabilityTheory Set Filter Submodule InnerProductSpace
open scoped ENNReal NNReal

/-- Gram-Schmidt applied to a sequence valued in a submodule `S` stays in `S`, since each
`gramSchmidtNormed ℝ f n` is a scalar multiple of a vector in the span of finitely many
`f i ∈ S`. -/
theorem Sandpile.Support.gramSchmidtNormed_mem_submodule {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Submodule ℝ E) (f : ℕ → E) (hf : ∀ n, f n ∈ S) (n : ℕ) :
    gramSchmidtNormed ℝ f n ∈ S := by
  unfold gramSchmidtNormed
  apply S.smul_mem
  have hle : Submodule.span ℝ (f '' Set.Iic n) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, _, rfl⟩
    exact hf i
  exact hle (gramSchmidt_mem_span ℝ f (le_refl n))


/-- Deleting the terms of a sequence `f` that equal zero does not change its span, since a
zero term contributes nothing to any span it appears in. -/
theorem Sandpile.Support.span_range_nonzero {E : Type*} [AddCommGroup E] [Module ℝ E] (f : ℕ → E) :
    Submodule.span ℝ (Set.range (fun n : {n : ℕ // f n ≠ 0} => f n)) =
      Submodule.span ℝ (Set.range f) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : f i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩


/-- **A dense submodule of a separable real Hilbert space contains a Hilbert basis.** Applying
Gram-Schmidt to a dense sequence in `S` and discarding the zero vectors produces an orthonormal
family, indexed by a subset `w` of `ℕ`, whose span is dense (hence total, by completeness), and
every basis vector lies in `S`. -/
theorem Sandpile.Support.exists_hilbertBasis_mem_dense_submodule {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] (S : Submodule ℝ E) (hS : Dense (S : Set E)) :
    ∃ (w : Set ℕ) (b : HilbertBasis w ℝ E), ∀ i, b i ∈ S := by
  classical
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq S
  let f : ℕ → E := fun n => v n
  have hf : DenseRange f := hS.denseRange_val.comp hv continuous_subtype_val
  have hspan : Submodule.span ℝ (Set.range (fun n : {n : ℕ // gramSchmidtNormed ℝ f n ≠ 0} =>
      gramSchmidtNormed ℝ f n)) = Submodule.span ℝ (Set.range f) := by
    rw [Sandpile.Support.span_range_nonzero, span_gramSchmidtNormed_range, span_gramSchmidt]
  have htotal : ⊤ ≤ (Submodule.span ℝ (Set.range (fun n : {n : ℕ // gramSchmidtNormed ℝ f n ≠ 0} =>
      gramSchmidtNormed ℝ f n))).topologicalClosure := by
    rw [hspan]
    intro x _
    exact Submodule.closure_subset_topologicalClosure_span (Set.range f) (hf x)
  refine ⟨{n : ℕ | gramSchmidtNormed ℝ f n ≠ 0},
    HilbertBasis.mk (gramSchmidtNormed_orthonormal' f) htotal, ?_⟩
  intro i
  simpa only [HilbertBasis.coe_mk] using
    Sandpile.Support.gramSchmidtNormed_mem_submodule S f (fun n => (v n).property) i.val


/-- The submodule of `Lp ℝ 2 μ` consisting of the classes that are also essentially
bounded, i.e. lie in `MemLp · ∞ μ`. -/
noncomputable def Sandpile.Support.boundedL2Submodule {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f : Lp ℝ 2 μ | MemLp (fun x => f x) ∞ μ}
  zero_mem' := MemLp.ae_eq (Lp.coeFn_zero ℝ 2 μ).symm MemLp.zero
  add_mem' {f g} hf hg := MemLp.ae_eq (Lp.coeFn_add f g).symm (hf.add hg)
  smul_mem' c f hf := MemLp.ae_eq (Lp.coeFn_smul c f).symm (hf.const_smul c)

/-- `boundedL2Submodule μ` is dense in `Lp ℝ 2 μ`, since it contains every simple function and
the simple functions are already dense. -/
theorem Sandpile.Support.dense_boundedL2Submodule {X : Type*} [MeasurableSpace X]
    (μ : Measure X) : Dense (Sandpile.Support.boundedL2Submodule μ : Set (Lp ℝ 2 μ)) := by
  apply (Lp.simpleFunc.dense (E := ℝ) (p := 2) (μ := μ) (by norm_num)).mono
  intro f hf
  let sf : Lp.simpleFunc ℝ 2 μ := ⟨f, hf⟩
  exact MemLp.ae_eq (Lp.simpleFunc.toSimpleFunc_eq_toFun sf)
    ((Lp.simpleFunc.toSimpleFunc sf).memLp_top μ)


/-- **`L² μ` has an essentially bounded Hilbert basis, indexed by a subset of `ℕ`.** Combines
`exists_hilbertBasis_mem_dense_submodule` with the density of `boundedL2Submodule μ` established
in `dense_boundedL2Submodule`. -/
theorem Sandpile.Support.exists_bounded_hilbertBasis {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SecondCountableTopology (Lp ℝ 2 μ)] :
    ∃ (w : Set ℕ) (b : HilbertBasis w ℝ (Lp ℝ 2 μ)),
      ∀ i, MemLp (fun x => b i x) ∞ μ := by
  exact Sandpile.Support.exists_hilbertBasis_mem_dense_submodule
    (Sandpile.Support.boundedL2Submodule μ) (Sandpile.Support.dense_boundedL2Submodule μ)

