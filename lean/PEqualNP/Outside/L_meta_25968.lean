import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25968 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 7, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.not, [12]⟩], 13⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
