import TensorHeatChallenge

/-! Regression for the editorially identified singleton/zero collapse.

The strengthened statement requires arbitrary constant coordinate data at
every nonempty atlas index.  A singleton carrier cannot satisfy that contract
when the matrix fiber is nontrivial. -/

theorem unit_cannot_represent_arbitrary_constants
    {Index X W : Type*} [Nonempty Index] [Nonempty X] [Nontrivial W]
    (value : Unit → Index → X → W) :
    ¬ (∀ c : Index → W, ∃ D, ∀ i x, value D i x = c i) := by
  intro h
  let i : Index := Classical.choice inferInstance
  let x : X := Classical.choice inferInstance
  obtain ⟨c₀, c₁, hne⟩ := exists_pair_ne W
  obtain ⟨D₀, h₀⟩ := h (fun _ => c₀)
  obtain ⟨D₁, h₁⟩ := h (fun _ => c₁)
  have hD : D₀ = D₁ := Subsingleton.elim _ _
  apply hne
  calc
    c₀ = value D₀ i x := (h₀ i x).symm
    _ = value D₁ i x := by rw [hD]
    _ = c₁ := h₁ i x

/-- Instantiate the regression at the matrix fiber used by the selected
statement.  Nontriviality of the finite-dimensional model guarantees at least
one matrix coordinate, so the preceding obstruction is not conditional on an
empty `Fin` index. -/
theorem unit_cannot_represent_selected_matrix_constants
    {E Index : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [Nonempty Index]
    (value : Unit → Index → E →
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ)) :
    ¬ (∀ c : Index →
        (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ),
      ∃ D, ∀ i x, value D i x = c i) := by
  let p : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let c₀ : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ := 0
  let c₁ : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
    fun ij => if ij = (p, p) then 1 else 0
  have hne : c₀ ≠ c₁ := by
    intro h
    have hp := congrFun h (p, p)
    simp [c₀, c₁] at hp
  letI : Nontrivial
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ) :=
    ⟨⟨c₀, c₁, hne⟩⟩
  exact unit_cannot_represent_arbitrary_constants value

#print axioms unit_cannot_represent_arbitrary_constants
#print axioms unit_cannot_represent_selected_matrix_constants
