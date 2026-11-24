import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G inst hCycle U hEdge x Y hY R π hBlocks hCover
  have hyAdj (y : Fin n) (hy : y ∈ Y) : G.Adj x y :=
    hEdge _ (hY y hy)
  have blockUnique {B : Finset (Fin n)} (hB : B ∈ π) {a b : Fin n}
      (ha : a ∈ B) (hb : b ∈ B) (hax : G.Adj x a) (hbx : G.Adj x b)
      (hYab : a ∈ Y ∨ b ∈ Y) : a = b := by
    rcases (hBlocks B hB).2 with hSingle | ⟨_, c, hc, hcU⟩
    · exact Finset.card_le_one.mp hSingle.le a ha b hb
    have hcx : c ≠ x := by
      rintro rfl
      rcases hYab with hy | hy
      · exact hcU a ha (hY a hy)
      · exact hcU b hb (hY b hy)
    exact Finset.card_le_one.mp (hCycle c x hcx) a
      (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hc a ha, hax⟩) b
      (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hc b hb, hbx⟩)
  have count (S : Finset (Fin n)) (hSR : S ⊆ R)
      (hSX : ∀ a ∈ S, G.Adj x a)
      (hSY : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ∈ Y ∨ b ∈ Y) :
      S.card ≤ π.card := by
    let chooseBlock (a : Fin n) : Finset (Fin n) :=
      if ha : a ∈ R then (hCover a ha).choose else ∅
    have spec (a : Fin n) (ha : a ∈ S) :
        chooseBlock a ∈ π ∧ a ∈ chooseBlock a := by
      simpa only [chooseBlock, dite_eq_left (hSR ha)] using (hCover a (hSR ha)).choose_spec
    apply Finset.card_le_card_of_injOn chooseBlock
    · intro a ha
      exact (spec a ha).1
    · intro a ha b hb heq
      by_contra hne
      exact hne (blockUnique (spec a ha).1 (spec a ha).2
        (heq.symm ▸ (spec b hb).2) (hSX a ha) (hSX b hb) (hSY a ha b hb hne))
  constructor
  · exact count (R ∩ Y) (fun _ ha => (Finset.mem_inter.mp ha).1)
      (fun a ha => hyAdj a (Finset.mem_inter.mp ha).2)
      (fun a ha _ _ _ => Or.inl (Finset.mem_inter.mp ha).2)
  · intro hAdj hNot
    obtain ⟨r, hr, hrY⟩ : ∃ r : Fin n, r ∈ R ∧ r ∉ Y := by
      by_contra h
      apply hNot
      intro r hr
      by_contra hy
      exact h ⟨r, hr, hy⟩
    have hSub : insert r (R ∩ Y) ⊆ R := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hr
      · exact (Finset.mem_inter.mp ha).1
    have hCount := count (insert r (R ∩ Y)) hSub (fun a ha => hAdj a (hSub ha))
      (by
        intro a ha b hb hne
        rcases Finset.mem_insert.mp ha with rfl | ha
        · rcases Finset.mem_insert.mp hb with rfl | hb
          · exact (hne rfl).elim
          · exact Or.inr (Finset.mem_inter.mp hb).2
        · exact Or.inl (Finset.mem_inter.mp ha).2)
    rwa [Finset.card_insert_of_notMem (fun h => hrY (Finset.mem_inter.mp h).2)] at hCount
