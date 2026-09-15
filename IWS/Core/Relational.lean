import IWS.Core.State

namespace IWS

def adjacencyMatrix (G : Graph N) : Matrix (Fin N) (Fin N) ℝ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

def adjPlusIdentity (G : Graph N) : Matrix (Fin N) (Fin N) ℝ :=
  adjacencyMatrix G + 1

def rowSums (M : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin N, M i j

def inverseDegMatrix (G : Graph (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => (rowSums (adjPlusIdentity G) i)⁻¹

def normalizedAdjacencyMatrix (G : Graph (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  inverseDegMatrix G * adjPlusIdentity G

end IWS
