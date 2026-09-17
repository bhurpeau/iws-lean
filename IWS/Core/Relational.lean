import IWS.Core.State
set_option linter.style.header false

namespace IWS

noncomputable section

def adjacencyMatrix (G : Graph N) : Matrix (Fin N) (Fin N) ℝ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

def adjPlusIdentity (G : Graph N) : Matrix (Fin N) (Fin N) ℝ :=
  adjacencyMatrix G + 1

def rowSums (M : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin N, M i j

def inverseDegMatrix (G : Graph N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => (rowSums (adjPlusIdentity G) i)⁻¹

def normalizedAdjacencyMatrix (G : Graph N) :
    Matrix (Fin N) (Fin N) ℝ :=
  inverseDegMatrix G * adjPlusIdentity G

end

theorem adjPlusIdentity_diagonal_eq_one (G : Graph N) (i : Fin N) :
    adjPlusIdentity G i i = 1 := by
  simp [adjPlusIdentity, adjacencyMatrix, SimpleGraph.irrefl]

theorem rowSums_adjPlusIdentity_pos (G : Graph N) (i : Fin N) :
    0 < rowSums (adjPlusIdentity G) i := by
  unfold rowSums
  have h_le :
    adjPlusIdentity G i i ≤ ∑ j, adjPlusIdentity G i j := by
    apply Finset.single_le_sum
    · intro j hj
      by_cases h : i = j
      · subst j
        simp [adjPlusIdentity, adjacencyMatrix, SimpleGraph.irrefl]
      · by_cases hAdj : G.Adj i j
        · simp [adjPlusIdentity, adjacencyMatrix, h, hAdj]
        · simp [adjPlusIdentity, adjacencyMatrix, h, hAdj]
    · simp
  rw [adjPlusIdentity_diagonal_eq_one G i] at h_le
  linarith

theorem normalizedAdjacencyMatrix_rowStochastic (G : Graph N) :
    normalizedAdjacencyMatrix G ∈ Matrix.rowStochastic ℝ (Fin N) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    simp [normalizedAdjacencyMatrix, inverseDegMatrix]

    have hpos : 0 < rowSums (adjPlusIdentity G) i :=
      rowSums_adjPlusIdentity_pos G i

    have hinv : 0 ≤ (rowSums (adjPlusIdentity G) i)⁻¹ := by
      positivity

    have hentry : 0 ≤ adjPlusIdentity G i j := by
      by_cases h : i = j
      · subst j
        simp [adjPlusIdentity, adjacencyMatrix, SimpleGraph.irrefl]
      · by_cases hAdj : G.Adj i j
        · simp [adjPlusIdentity, adjacencyMatrix, h, hAdj]
         simp [adjPlusIdentity, adjacencyMatrix, h, hAdj]

    exact mul_nonneg hinv hentry
  · intro i
    simp [normalizedAdjacencyMatrix, inverseDegMatrix]
end IWS
