import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25966 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [11, 10]⟩,
    ⟨.not, [12]⟩], 13⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
