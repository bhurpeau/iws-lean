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

def norm_inf_2 (H : Fin N → InternalVec d) : ℝ := ‖H‖

def blockTanh (y : InternalVec d) : InternalVec d :=
  EuclideanSpace.equiv (Fin d) ℝ |>.symm (fun k => Real.tanh (EuclideanSpace.equiv (Fin d) ℝ y k))

def vecTanh (H : Fin N → InternalVec d) (i : Fin N) : InternalVec d :=
  blockTanh (H i)

def matMul (A : Matrix (Fin N) (Fin N) ℝ) (H : Fin N → InternalVec d) (i : Fin N) : InternalVec d :=
  ∑ j : Fin N, A i j • H j
end


-- Normalized relational matrix
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
        · simp [adjPlusIdentity, adjacencyMatrix, h, hAdj]

    exact mul_nonneg hinv hentry
  · intro i
    simp [normalizedAdjacencyMatrix, inverseDegMatrix]
    rw [← Finset.mul_sum]
    change (rowSums (adjPlusIdentity G) i)⁻¹
    * rowSums (adjPlusIdentity G) i = 1
    have hne : rowSums (adjPlusIdentity G) i ≠ 0 :=
      ne_of_gt (rowSums_adjPlusIdentity_pos G i)
    exact inv_mul_cancel₀ hne

theorem norm_le_of_row_stochastic
    (A : Matrix (Fin N) (Fin N) ℝ)
    (H : Fin N → InternalVec d)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin N)) :
    ‖matMul A H‖ ≤ ‖H‖ := by
  rw [Matrix.mem_rowStochastic_iff_sum] at hA
  rcases hA with ⟨hA_nonneg, hA_sum⟩
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  dsimp [matMul]
  have h1 : ‖∑ j, A i j • H j‖ ≤ ∑ j, ‖A i j • H j‖ := norm_sum_le _ _
  have h2 : (∑ j, ‖A i j • H j‖) = ∑ j, A i j * ‖H j‖ := by
    congr 1 with j
    rw [norm_smul, Real.norm_of_nonneg (hA_nonneg i j)]
  have h3 : (∑ j, A i j * ‖H j‖) ≤ ∑ j, A i j * ‖H‖ := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (norm_le_pi_norm H j) (hA_nonneg i j)
  have h4 : (∑ j, A i j * ‖H‖) = ‖H‖ := by
    rw [← Finset.sum_mul, hA_sum i, one_mul]
  linarith

theorem norm_le_of_normalizedAdjacencyMatrix (G : Graph N) (H : Fin N → InternalVec d) :
    ‖matMul (normalizedAdjacencyMatrix G) H‖ ≤ ‖H‖ := by
  apply norm_le_of_row_stochastic
  exact normalizedAdjacencyMatrix_rowStochastic G

theorem matMul_sub (A : Matrix (Fin N) (Fin N) ℝ) (H K : Fin N → InternalVec d) :
    matMul A H - matMul A K = matMul A (H - K) := by
  funext i
  simp [matMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem normalizedAdjacencyMatrix_lipschitz (G : Graph N) (H K : Fin N → InternalVec d) :
    ‖matMul (normalizedAdjacencyMatrix G) H - matMul (normalizedAdjacencyMatrix G) K‖ ≤ ‖H - K‖ := by
  rw [matMul_sub]
  exact norm_le_of_normalizedAdjacencyMatrix G (H - K)

-- Bounds and regularity of the saturation
theorem Real.abs_tanh_sub_le (a b : ℝ) : |Real.tanh a - Real.tanh b| ≤ |a - b| := by
  have hderiv : ∀ t : ℝ, HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
    intro t
    have hnum : Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq t]
    have hd : HasDerivAt (fun s => Real.sinh s / Real.cosh s)
        ((Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) / Real.cosh t ^ 2) t :=
      (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
    rw [hnum] at hd
    have heq : Real.tanh = fun s => Real.sinh s / Real.cosh s := funext Real.tanh_eq_sinh_div_cosh
    rw [heq]
    exact hd
  have hbound : ∀ t ∈ (Set.univ : Set ℝ), ‖(1 : ℝ) / Real.cosh t ^ 2‖ ≤ 1 := by
    intro t _
    have hcosh1 : (1 : ℝ) ≤ Real.cosh t := by
      nlinarith [Real.cosh_sq t, sq_nonneg (Real.sinh t), Real.cosh_pos t]
    have hcosh2 : (1 : ℝ) ≤ Real.cosh t ^ 2 := by
      nlinarith [hcosh1, Real.cosh_pos t]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith
  have hmvt := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Real.tanh) (f' := fun t => 1 / Real.cosh t ^ 2)
      (fun t _ => (hderiv t).hasDerivWithinAt) hbound (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using hmvt

lemma norm_blockTanh_sub_le (y z : InternalVec d) :
‖blockTanh y - blockTanh z‖ ≤ ‖y - z‖ := by
  have hpt : ∀ k : Fin d, (blockTanh y) k = Real.tanh (y k) := fun _ => rfl
  have hpt' : ∀ k : Fin d, (blockTanh z) k = Real.tanh (z k) := fun _ => rfl
  have hbound : ∀ k : Fin d, ‖(blockTanh y - blockTanh z) k‖ ≤ ‖(y - z) k‖ := by
    intro k
    rw [PiLp.sub_apply, PiLp.sub_apply, hpt k, hpt' k, Real.norm_eq_abs, Real.norm_eq_abs]
    exact Real.abs_tanh_sub_le (y k) (z k)
  have hsum : ∑ k, ‖(blockTanh y - blockTanh z) k‖ ^ 2 ≤ ∑ k, ‖(y - z) k‖ ^ 2 :=
    Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2
  rw [EuclideanSpace.norm_eq (blockTanh y - blockTanh z), EuclideanSpace.norm_eq (y - z)]
  exact Real.sqrt_le_sqrt hsum

theorem norm_tanh_matMul_sub_le (G : Graph N) (H K : Fin N → InternalVec d) :
  ‖vecTanh (matMul (normalizedAdjacencyMatrix G) H) - vecTanh (matMul (normalizedAdjacencyMatrix G) K)‖ ≤ ‖H - K‖ := by
  apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
  intro i
  have h_tanh := norm_blockTanh_sub_le (matMul (normalizedAdjacencyMatrix G) H i) (matMul (normalizedAdjacencyMatrix G) K i)
  have h_matrix : ‖matMul (normalizedAdjacencyMatrix G) H i - matMul (normalizedAdjacencyMatrix G) K i‖ ≤ ‖H - K‖ := by
    have h_sub : matMul (normalizedAdjacencyMatrix G) H i - matMul (normalizedAdjacencyMatrix G) K i =
      (matMul (normalizedAdjacencyMatrix G) H - matMul (normalizedAdjacencyMatrix G) K) i := by rfl
    rw [h_sub]
    have h_max := norm_le_pi_norm (matMul (normalizedAdjacencyMatrix G) H - matMul (normalizedAdjacencyMatrix G) K) i
    have h_lip := normalizedAdjacencyMatrix_lipschitz G H K
    linarith
  dsimp [vecTanh, Pi.sub_apply]
  linarith

end IWS
