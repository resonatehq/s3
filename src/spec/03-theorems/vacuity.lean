import «03-theorems».«corpus»
import «02-abstract».«properties»

namespace Abstract
namespace Vacuity

open Abstract

def badState : State :=
  { objects := [{ id := oid "p",
                  promise := { state := .pending, param := {}, type := .internal,
                               timeoutAt := 1, createdAt := 5 } }] }

theorem legal_body_is_falsifiable :
    (Abstract.Properties.catalogue.all fun l =>
      match l.property with
      | .state f => f 0 badState
      | .trans f => f 0 badState badState) = false := by decide

theorem le_foldl_max : ∀ (m : List Nat) (b : Nat), b ≤ m.foldl Nat.max b
  | [],     b => Nat.le_refl b
  | x :: m, b => Nat.le_trans (Nat.le_max_left b x) (le_foldl_max m (Nat.max b x))

def clockOf (w : List (Event × Nat)) (t : Nat) : Nat :=
  ((w.map Prod.snd).take (t + 1)).foldl Nat.max 0

theorem clockOf_mono (w : List (Event × Nat)) (t : Nat) :
    clockOf w t ≤ clockOf w (t + 1) := by
  unfold clockOf
  have h : (w.map Prod.snd).take (t + 1 + 1)
      = (w.map Prod.snd).take (t + 1) ++ ((w.map Prod.snd)[t + 1]?).toList :=
    List.take_add_one
  rw [h, List.foldl_append]
  exact le_foldl_max _ _

def stepAt (w : List (Event × Nat)) (t : Nat) : Event :=
  match w[t]? with
  | some x => x.1
  | none   => .stutter

def stateAt (mat : Bool) (w : List (Event × Nat)) (s₀ : State) : Nat → State
  | 0     => s₀
  | t + 1 => (step mat (stepAt w t) (clockOf w t) (stateAt mat w s₀ t)).2

def traceOf (mat : Bool) (w : List (Event × Nat)) (s₀ : State) : Trace := fun t =>
  { state := stateAt mat w s₀ t
  , event := stepAt w t
  , reply := (step mat (stepAt w t) (clockOf w t) (stateAt mat w s₀ t)).1
  , now   := clockOf w t }

theorem valid_traceOf (mat : Bool) (w : List (Event × Nat)) (s₀ : State) :
    Valid mat (traceOf mat w s₀) :=
  fun t => ⟨rfl, clockOf_mono w t⟩

theorem traceOf_starts_at_init (mat : Bool) (w : List (Event × Nat)) :
    (traceOf mat w State.init 0).state = State.init := rfl

theorem valid_is_satisfiable (mat : Bool) (w : List (Event × Nat)) :
    ∃ tr : Trace, Valid mat tr ∧ (tr 0).state = State.init :=
  ⟨traceOf mat w State.init, valid_traceOf mat w State.init, rfl⟩

abbrev wit : Trace := traceOf true b1 State.init

theorem witness_clock_moves : (wit 0).now = 100 ∧ (wit 8).now = 230 := by decide

theorem witness_has_two_promises : (wit 9).state.promises.length = 2 := by decide

theorem witness_settles_a_promise :
    (wit 9).state.promises.any (·.state != .pending) = true := by decide

theorem witness_fulfils_a_task :
    (wit 9).state.tasks.any (·.state == .fulfilled) = true := by decide

theorem witness_acquires_a_task :
    (wit 8).state.tasks.any (·.state == .acquired) = true := by decide

theorem witness_registers_a_callback :
    (wit 3).state.promises.any (fun p => !p.callbacks.isEmpty) = true := by decide

theorem witness_suspends_a_task :
    (wit 3).state.tasks.any (·.state == .suspended) = true := by decide

theorem witness_writes_the_outbox :
    (wit 7).state.outbox.isEmpty = false := by decide

open Abstract in
theorem cross_origin_callback_is_refused :
    (run true (promiseRegisterCallback
        { awaited := { origin := "o1", suffix := "a" },
          awaiter := { origin := "o2", suffix := "x" } } 100)
      State.init).1.status = 400 := by decide

open Abstract in
theorem same_origin_callback_passes_the_door :
    (run true (promiseRegisterCallback
        { awaited := { origin := "o1", suffix := "a" },
          awaiter := { origin := "o1", suffix := "x" } } 100)
      State.init).1.status ≠ 400 := by decide

open Abstract in
theorem cross_origin_fence_is_refused :
    (run true (taskFence
        { id := { origin := "o1", suffix := "x" }, version := 1,
          action := .settle { id := { origin := "o2", suffix := "a" },
                              state := .resolved, value := {} } } 100)
      State.init).1.status = 400 := by decide

open Abstract in
theorem cross_origin_suspend_is_refused :
    (run true (taskSuspend
        { id := { origin := "o1", suffix := "x" }, version := 1,
          actions := [{ awaited := { origin := "o2", suffix := "a" },
                        awaiter := { origin := "o1", suffix := "x" } }] } 100)
      State.init).1.status = 400 := by decide

theorem legal_holds_along_witness :
    (List.range 12).all (fun t =>
      Abstract.Properties.catalogue.all fun l =>
        match l.property with
        | .state f => f (wit t).now (wit t).state
        | .trans f => f (wit t).now (wit t).state (wit (t + 1)).state) = true := by decide

theorem b1_length : b1.length = 9 := rfl

theorem stepAt_idle (t : Nat) (h : 9 ≤ t) : stepAt b1 t = Event.stutter := by
  unfold stepAt
  rw [List.getElem?_eq_none (by rw [b1_length]; exact h)]

theorem clock_const (t : Nat) (h : 8 ≤ t) : clockOf b1 t = clockOf b1 8 := by
  unfold clockOf
  rw [List.take_of_length_le (by simp [b1_length]; omega),
      List.take_of_length_le (by simp [b1_length])]

theorem state_const (t : Nat) :
    stateAt true b1 State.init (9 + t) = stateAt true b1 State.init 9 := by
  induction t with
  | zero => rfl
  | succ k ih =>
      show (step true (stepAt b1 (9 + k)) (clockOf b1 (9 + k))
              (stateAt true b1 State.init (9 + k))).2 = _
      rw [stepAt_idle (9 + k) (by omega)]
      exact ih

theorem state_const' (t : Nat) (h : 9 ≤ t) :
    stateAt true b1 State.init t = stateAt true b1 State.init 9 := by
  have := state_const (t - 9)
  rwa [Nat.add_sub_cancel' h] at this

theorem legal_wit : Legal wit := by
  intro t
  by_cases h : t < 12
  · exact List.all_eq_true.mp legal_holds_along_witness t (by simp [List.mem_range]; omega)
  · have h9 : 9 ≤ t := by omega
    show (Abstract.Properties.catalogue.all fun l =>
      match l.property with
      | .state f => f (clockOf b1 t) (stateAt true b1 State.init t)
      | .trans f => f (clockOf b1 t) (stateAt true b1 State.init t)
                      (stateAt true b1 State.init (t + 1))) = true
    rw [clock_const t (by omega), state_const' t h9, state_const' (t + 1) (by omega)]
    exact List.all_eq_true.mp legal_holds_along_witness 9 (by simp)

theorem valid_implies_legal_is_not_vacuous :
    ∃ tr : Trace, Valid true tr ∧ (tr 0).state = State.init ∧ Legal tr
      ∧ (tr 9).state.promises.any (·.state != .pending) = true
      ∧ (tr 9).state.tasks.any (·.state == .fulfilled) = true :=
  ⟨wit, valid_traceOf true b1 State.init, rfl, legal_wit,
   witness_settles_a_promise, witness_fulfils_a_task⟩

end Vacuity
end Abstract
