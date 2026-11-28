import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58311 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274876862 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [12, 6]⟩, ⟨.not, [10]⟩, ⟨.or, [13, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [15, 14]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
