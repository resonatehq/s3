import refinement.trace

namespace Refinement

def astate (tr : Concrete.Trace) : Nat → Abstract.State
  | 0 => Abstract.State.init
  | n + 1 =>
      (Abstract.exec false ((events (tr n).event (tr n).now (tr n).state).map (·, (tr n).now))
        (astate tr n)).2

def evs (tr : Concrete.Trace) (n : Nat) : List Abstract.Event :=
  events (tr n).event (tr n).now (tr n).state ++ [.stutter]

def blocks (tr : Concrete.Trace) (n : Nat) : List Abstract.Frame :=
  frames (tr n).now (astate tr n) (evs tr n)

theorem blocks_pos (tr : Concrete.Trace) (n : Nat) : 0 < (blocks tr n).length := by
  simp [blocks, frames_length, evs]

theorem Inv.init : Inv Concrete.State.init :=
  ⟨fun _ _ h => absurd h (List.not_mem_nil), List.nodup_nil⟩

theorem Equiv.refl (S : Abstract.State) : Equiv S S := ⟨fun _ => rfl, rfl, rfl⟩

theorem invariant (H : Concrete.Hasher) (tr : Concrete.Trace) (valid : Concrete.Valid H tr)
    (init : (tr 0).state = Concrete.State.init) :
    ∀ n, Inv (tr n).state ∧ Equiv (abstract (tr n).state) (astate tr n)
  | 0 => by rw [init]; exact ⟨Inv.init, abstract_init ▸ Equiv.refl _⟩
  | n + 1 => by
      obtain ⟨inv, rel⟩ := invariant H tr valid init n
      obtain ⟨h1, h2, _⟩ := step_sim H (tr n).event (tr n).now (tr n).state (astate tr n) inv rel
      rw [valid.state n]
      exact ⟨h1, h2⟩

theorem blocks_observe (H : Concrete.Hasher) (tr : Concrete.Trace) (valid : Concrete.Valid H tr)
    (init : (tr 0).state = Concrete.State.init) (n : Nat) :
    (blocks tr n).filterMap Abstract.Frame.observe = (Concrete.Frame.observe (tr n)).toList := by
  obtain ⟨inv, rel⟩ := invariant H tr valid init n
  obtain ⟨_, _, h3⟩ := step_sim H (tr n).event (tr n).now (tr n).state (astate tr n) inv rel
  rw [blocks, frames_observe, evs, List.map_append, exec_append]
  simp only [List.map_cons, List.map_nil, exec_cons, Abstract.exec, step_stutter]
  rw [observations_stutter _ _ _ (by rw [exec_length, List.length_map]), h3, ← valid.reply n]

theorem blocks_last (tr : Concrete.Trace) (n : Nat) :
    ((blocks tr n).getLast (List.ne_nil_of_length_pos (blocks_pos tr n))) =
      ⟨astate tr (n + 1), .stutter, .stutter, (tr n).now⟩ := by
  simp only [blocks, evs, frames_append, step_stutter]
  rw [List.getLast_concat]
  rfl

theorem blocks_head (tr : Concrete.Trace) (n : Nat) :
    ((blocks tr n).head (List.ne_nil_of_length_pos (blocks_pos tr n))).state = astate tr n :=
  frames_head _ _ _ _

theorem blocks_head_now (tr : Concrete.Trace) (n : Nat) :
    ((blocks tr n).head (List.ne_nil_of_length_pos (blocks_pos tr n))).now = (tr n).now :=
  frames_head_now _ _ _ _

theorem refines (H : Concrete.Hasher) (tr : Concrete.Trace)
    (valid : Concrete.Valid H tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o := by
  refine ⟨flat (blocks tr) (blocks_pos tr), ?_, ?_, ?_⟩
  · intro m
    refine flat_pairs (P := fun f g =>
      Abstract.step false f.event f.now f.state = (f.reply, g.state) ∧ f.now ≤ g.now)
      (blocks tr) (blocks_pos tr) ?_ ?_ m
    · intro n i h
      exact frames_pairs _ _ _ i h
    · intro n
      rw [blocks_last]
      refine ⟨?_, ?_⟩
      · simp only [step_stutter, blocks_head]
      · show (tr n).now ≤ _
        rw [blocks_head_now]
        exact valid.now n
  · rw [flat_lt _ _ (blocks_pos tr 0)]
    have := blocks_head tr 0
    rw [List.head_eq_getElem] at this
    exact this
  · have hobs : ∀ n, Concrete.observed tr n = Abstract.observed (flat (blocks tr) (blocks_pos tr)) (start (blocks tr) n) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [observed_succ, aobserved_block, ih, blocks_observe H tr valid init]
    intro k o
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨start (blocks tr) n, by rw [← hobs n]; exact hn⟩
    · rintro ⟨M, hM⟩
      refine ⟨M, ?_⟩
      rw [hobs M]
      obtain ⟨t, ht⟩ := aobserved_prefix (flat (blocks tr) (blocks_pos tr)) M (start (blocks tr) M - M)
      have hM' : M + (start (blocks tr) M - M) = start (blocks tr) M := by
        have := start_ge (blocks tr) (blocks_pos tr) M
        omega
      rw [hM'] at ht
      rw [← ht, List.getElem?_append_left]
      · exact hM
      · obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.1 hM
        exact h

end Refinement
