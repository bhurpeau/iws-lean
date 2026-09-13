import IWS.Core.State

namespace IWS

def adjacencyMatrix (G : Graph N) : Matrix (Fin N) (Fin N) ℝ := by
  classical
  exact fun i j => if G.Adj i j then 1 else 0

end IWS
