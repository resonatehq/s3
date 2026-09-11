import impl.refinement

namespace Concrete

open Impl (State Obs)
open Commit Refinement

structure Frame where
  state : State
  event : Impl.Step
  reply : Option Obs
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (tr : Trace) : Prop :=
  ∀ t : Nat,
    Impl.step (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).reply = (Impl.step (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr (t + 1)).state = (Impl.step (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

theorem Valid.inv {tr : Trace} (hv : Valid tr) (h0 : (tr 0).state = State.init) :
    ∀ t, Inv (tr t).state ∧ ∃ S, Rel (tr t).state.world S
  | 0 => by rw [h0]; exact ⟨Inv.init, _, Rel.init⟩
  | t + 1 => by
      obtain ⟨hinv, S, hrel⟩ := Valid.inv hv h0 t
      obtain ⟨_, hrel', hinv'⟩ := step_sim (tr t).event (tr t).now (tr t).state S hinv hrel
      rw [hv.state t]
      exact ⟨hinv', _, hrel'⟩

theorem Valid.timers {tr : Trace} (hv : Valid tr) (h0 : (tr 0).state = State.init) (t : Nat) :
    TimerInv (tr t).state.world :=
  (hv.inv h0 t).1.timers

theorem begin_sweep {o : String} {fired now : Nat} {s : State}
    (h : Impl.begin o (.sweep fired) now s ≠ s) :
    (s.world.store.get (.timer fired o)).isSome = true ∧ fired ≤ now := by
  unfold Impl.begin at h
  split at h
  · rename_i hg
    have := hg.2
    simp only [Impl.Work.licensed, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · exact absurd rfl h

theorem Valid.sweep {tr : Trace} (hv : Valid tr) (t : Nat) {o : String} {fired : Nat}
    (he : (tr t).event = .begin o (.sweep fired)) (hne : (tr (t + 1)).state ≠ (tr t).state) :
    ((tr t).state.world.store.get (.timer fired o)).isSome = true ∧ fired ≤ (tr t).now := by
  rw [hv.state t, he] at hne
  exact begin_sweep hne

end Concrete
