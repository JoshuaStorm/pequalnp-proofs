import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58324 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274894139 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [3, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [5, 1]⟩, ⟨.not, [1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [10, 8]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [16, 15]⟩, ⟨.or, [17, 6]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
