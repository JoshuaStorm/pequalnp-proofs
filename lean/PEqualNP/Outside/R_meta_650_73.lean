import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 15000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_650_73
  (hProjectiveLine : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 19 ∧
    ∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (3, 13), (3, 19), (3, 23), (3, 24), (9, 13), (9, 17), (9, 18), (9, 20)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true))
  (hAffinePlane : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 43 ∧
    ∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ ([(2, 14), (2, 20), (2, 24), (2, 25), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true)) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  classical
  obtain ⟨A, hA, hAsize, hAval⟩ := hProjectiveLine
  obtain ⟨B, hB, hBsize, hBval⟩ := hAffinePlane
  let shift (i : ℕ) : ℕ := if i < 26 then i else i + A.gates.length
  let move (g : Gate) : Gate := ⟨g.op, g.inputs.map shift⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp [step]
      omega
  have runKeeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      apply List.getD_append
      exact hi
  have shifted (gs : List Gate) (w old : List Bool)
      (hlen : w.length = old.length + A.gates.length) (hBase : 26 ≤ old.length)
      (hw : ∀ i, w.getD (shift i) false = old.getD i false) :
      ∀ i, (run (gs.map move) w).getD (shift i) false = (run gs old).getD i false := by
    induction gs generalizing w old with
    | nil => exact hw
    | cons g gs ih =>
      change ∀ i, (run (gs.map move) (step w (move g))).getD (shift i) false =
        (run gs (step old g)).getD i false
      have hgate : (move g).op.eval ((move g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => old.getD i false) := by
        simp only [move, List.map_map]
        congr 1
        exact List.map_congr_left fun i _ => hw i
      apply ih _ _ (by simp [step]; omega) (by simp [step]; omega)
      intro i
      by_cases hi : i < old.length
      · have hi' : shift i < w.length := by
          unfold shift
          split <;> omega
        simp only [step]
        rw [List.getD_append _ _ _ _ hi', List.getD_append _ _ _ _ hi]
        exact hw i
      · have hs : shift i = i + A.gates.length := by
          have hn : ¬ i < 26 := by omega
          simp [shift, hn]
        have hi' : w.length ≤ shift i := by omega
        simp only [step]
        rw [List.getD_append_right _ _ _ _ hi',
          List.getD_append_right _ _ _ _ (by omega), hgate]
        congr 1
        omega
  let pre := A.gates ++ B.gates.map move
  let D : Circuit := ⟨pre ++ [⟨GateOp.or, [A.output, shift B.output]⟩],
    26 + pre.length⟩
  have hAlive : A.output < 26 + A.gates.length := by
    by_contra! h
    have ht := (hAval (fun _ => true)).2
      ⟨0, 13, by decide, rfl, rfl⟩
    change (run A.gates (List.ofFn (fun _ : Fin 26 => true))).getD A.output false = true at ht
    rw [List.getD_eq_default _ _ (by rw [runLength]; simpa using h)] at ht
    contradiction
  have hD : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    change g ∈ (A.gates ++ B.gates.map move) ++
      [⟨GateOp.or, [A.output, shift B.output]⟩] at hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact hA g hg
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        simpa [move] using hB g' hg'
    · obtain rfl := List.mem_singleton.mp hg
      exact ⟨Or.inr rfl, Nat.le_refl 2⟩
  have hLen : D.size ≤ 63 := by
    change D.gates.length ≤ 63
    simp [D, pre]
    change A.gates.length ≤ 19 at hAsize
    change B.gates.length ≤ 43 at hBsize
    omega
  have hEval (x : Fin 26 → Bool) :
      D.eval (List.ofFn x) = (A.eval (List.ofFn x) || B.eval (List.ofFn x)) := by
    let init := List.ofFn x
    let beforeB := run A.gates init
    have hbeforeB : beforeB.length = 26 + A.gates.length := by simp [beforeB, init, runLength]
    have hrelated : ∀ i, beforeB.getD (shift i) false = init.getD i false := by
      intro i
      by_cases hi : i < 26
      · simpa [shift, hi, beforeB] using runKeeps A.gates init i (by simpa [init] using hi)
      · have h0 : init.length ≤ i := by simpa [init] using Nat.le_of_not_lt hi
        have h1 : beforeB.length ≤ shift i := by simp [shift,hi,hbeforeB]; omega
        rw [List.getD_eq_default _ _ h0, List.getD_eq_default _ _ h1]
    have hmem (i : ℕ) : (run pre init).getD i false =
        (run (B.gates.map move) beforeB).getD i false := by
      simp [pre, run, beforeB, List.foldl_append]
    have hleft : (run pre init).getD A.output false = A.eval init := by
      rw [hmem, runKeeps _ _ _ (by rw [hbeforeB]; exact hAlive)]
      rfl
    have hright : (run pre init).getD (shift B.output) false = B.eval init := by
      rw [hmem, shifted B.gates beforeB init (by simp [hbeforeB,init]) (by simp [init]) hrelated]
      rfl
    have hlen : (run pre init).length = 26 + pre.length := by simp [runLength, init]
    change (run (pre ++ [⟨GateOp.or, [A.output, shift B.output]⟩]) init).getD
      (26 + pre.length) false = (A.eval init || B.eval init)
    have stepEval : run (pre ++ [⟨GateOp.or, [A.output, shift B.output]⟩]) init =
        step (run pre init) ⟨GateOp.or, [A.output, shift B.output]⟩ := by
      simp [run, List.foldl_append]
    rw [stepEval, ← hlen]
    have snoc (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    change ((run pre init) ++
      [([ (run pre init).getD A.output false, (run pre init).getD (shift B.output) false ] : List Bool).any id]).getD
      (run pre init).length false = _
    rw [snoc, hleft, hright]
    simp
  refine ⟨D,hD,hLen,?_⟩
  intro x
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  let onLine (p : ℕ × ℕ) : Bool := decide (p.1 ∈ ([0, 1, 3, 9] : List ℕ))
  have ea : edges.filter onLine = [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (3, 13), (3, 19), (3, 23), (3, 24), (9, 13), (9, 17), (9, 18), (9, 20)] := rfl
  have eb : edges.filter (fun e => !(onLine e)) = [(2, 14), (2, 20), (2, 24), (2, 25), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] := rfl
  have ePartition (u v : Fin 26) : (u.val,v.val) ∈ edges ↔
      (u.val,v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (3, 13), (3, 19), (3, 23), (3, 24), (9, 13), (9, 17), (9, 18), (9, 20)] : List (ℕ × ℕ)) ∨
      (u.val,v.val) ∈ ([(2, 14), (2, 20), (2, 24), (2, 25), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) := by
    rw [← ea, ← eb, List.mem_filter, List.mem_filter]
    cases onLine (u.val, v.val) <;> simp
  rw [hEval, Bool.or_eq_true, hAval, hBval]
  constructor
  · rintro (⟨u,v,h,hu,hv⟩ | ⟨u,v,h,hu,hv⟩)
    · exact ⟨u,v,(ePartition u v).mpr (Or.inl h),hu,hv⟩
    · exact ⟨u,v,(ePartition u v).mpr (Or.inr h),hu,hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    rcases (ePartition u v).mp h with h | h
    · exact Or.inl ⟨u,v,h,hu,hv⟩
    · exact Or.inr ⟨u,v,h,hu,hv⟩
