import Mathlib
set_option linter.style.header false
namespace IWS

variable {N d : ℕ}

abbrev InternalVec (d : ℕ) :=
  EuclideanSpace ℝ (Fin d)

structure ContinuousState (N d : ℕ) where
  H : Fin N → InternalVec d
  V : Fin N → InternalVec d
  tau : Fin N → InternalVec d
  P : Fin N → ℝ

variable (z : ContinuousState N d)
variable (i : Fin N)

def ContinuousState.Admissible (z : ContinuousState N d) : Prop :=
  ∀ i, 0 ≤ z.P i

abbrev Graph (N : ℕ) :=
  SimpleGraph (Fin N)

variable (G : Graph N)

example (G : Graph N) (i : Fin N) :
    ¬ G.Adj i i := by
  exact G.loopless.irrefl i

example (G : Graph N) (i j : Fin N)
    (h : G.Adj i j) :
    G.Adj j i := by
  exact G.symm.symm i j h

end IWS
