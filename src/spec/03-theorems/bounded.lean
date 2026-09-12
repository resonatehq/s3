import «03-theorems».«corpus»
import «02-abstract».«properties»

namespace Abstract
namespace Bounded

open Abstract

def sched (tr : Trace) (n : Nat) : List (Event × Nat) :=
  (List.range n).map (fun t => ((tr t).event, (tr t).now))

theorem sched_succ (tr : Trace) (n : Nat) :
    sched tr (n + 1) = sched tr n ++ [((tr n).event, (tr n).now)] := by
  unfold sched
  rw [List.range_succ, List.map_append]
  rfl

theorem exec_snoc (mat : Bool) :
    ∀ (w : List (Event × Nat)) (x : Event × Nat) (s : State),
      (exec mat (w ++ [x]) s).2 = (step mat x.1 x.2 (exec mat w s).2).2
  | [],           _, _ => rfl
  | (st, n) :: w, x, s => exec_snoc mat w x (step mat st n s).2

theorem valid_state_at (mat : Bool) (tr : Trace) (hv : Valid mat tr) :
    ∀ n, (tr n).state = (exec mat (sched tr n) (tr 0).state).2
  | 0     => rfl
  | n + 1 => by
      rw [(hv.state n), sched_succ, exec_snoc, ← valid_state_at mat tr hv n]

theorem valid_state_at_init (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = State.init) (n : Nat) :
    (tr n).state = (exec mat (sched tr n) State.init).2 := by
  rw [valid_state_at mat tr hv n, h0]

def foldAt (now : Nat) (a b : State) : Bool :=
  Abstract.Properties.catalogue.all fun l =>
    match l.property with
    | .state f => f now a
    | .trans f => f now a b

theorem legal_at_is_about_the_schedule (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = State.init) (n : Nat) :
    foldAt (tr n).now (tr n).state (tr (n + 1)).state
      = foldAt (tr n).now (exec mat (sched tr n) State.init).2
                          (exec mat (sched tr (n + 1)) State.init).2 := by
  rw [valid_state_at_init mat tr hv h0 n, valid_state_at_init mat tr hv h0 (n + 1)]

theorem legal_below_of_schedule (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = State.init) (N : Nat)
    (h : ∀ n < N, foldAt (tr n).now (exec mat (sched tr n) State.init).2
                         (exec mat (sched tr (n + 1)) State.init).2 = true) :
    ∀ n < N, foldAt (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n hn
  rw [legal_at_is_about_the_schedule mat tr hv h0 n]
  exact h n hn

def statesOf (mat : Bool) :
    List (Event × Nat) → State → List (Nat × State × State)
  | [],           _ => []
  | (st, n) :: w, s =>
      let s' := (step mat st n s).2
      (n, s, s') :: statesOf mat w s'

def legalRunOf (mat : Bool) (w : List (Event × Nat)) : Bool :=
  (statesOf mat w State.init).all (fun (n, a, b) => foldAt n a b)

theorem tiny_sweep_materialized :
    ((seqsUpToA (kernelsResp.take 3) 2).map instantiateA).all (legalRunOf true) = true := by
  decide

theorem tiny_sweep_projected :
    ((seqsUpToA (kernelsResp.take 3) 2).map instantiateA).all (legalRunOf false) = true := by
  decide

def demoSched : List (Event × Nat) := b1

theorem demo_exec_reaches_fulfilment :
    ((exec true demoSched State.init).2.tasks.any (·.state == .fulfilled)) = true := by
  decide

theorem demo_exec_settles :
    ((exec true demoSched State.init).2.promises.any (·.state != .pending)) = true := by
  decide

end Bounded
end Abstract
