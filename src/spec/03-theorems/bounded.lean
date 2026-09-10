import «03-theorems».«corpus»
import «02-abstract».«properties»

namespace Abstraction
namespace Bounded

open AbstractModel

def sched (tr : Trace) (n : Nat) : List (Step × Nat) :=
  (List.range n).map (fun t => ((tr t).req, (tr t).now))

theorem sched_succ (tr : Trace) (n : Nat) :
    sched tr (n + 1) = sched tr n ++ [((tr n).req, (tr n).now)] := by
  unfold sched
  rw [List.range_succ, List.map_append]
  rfl

theorem runFin_snoc (mat : Bool) :
    ∀ (w : List (Step × Nat)) (x : Step × Nat) (s : ServerState),
      (runFin mat (w ++ [x]) s).2 = (stepOf mat x.1 x.2 (runFin mat w s).2).2
  | [],           _, _ => rfl
  | (st, n) :: w, x, s => runFin_snoc mat w x (stepOf mat st n s).2

theorem valid_state_at (mat : Bool) (tr : Trace) (hv : Valid mat tr) :
    ∀ n, (tr n).state = (runFin mat (sched tr n) (tr 0).state).2
  | 0     => rfl
  | n + 1 => by
      rw [(hv n).2.1, sched_succ, runFin_snoc, ← valid_state_at mat tr hv n]

theorem valid_state_at_init (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) (n : Nat) :
    (tr n).state = (runFin mat (sched tr n) ServerState.init).2 := by
  rw [valid_state_at mat tr hv n, h0]

def foldAt (now : Nat) (a b : ServerState) : Bool :=
  AbstractModel.Properties.catalogue.all fun l =>
    match l.property with
    | .state f => f now a
    | .trans f => f now a b

theorem legal_at_is_about_the_schedule (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) (n : Nat) :
    foldAt (tr n).now (tr n).state (tr (n + 1)).state
      = foldAt (tr n).now (runFin mat (sched tr n) ServerState.init).2
                          (runFin mat (sched tr (n + 1)) ServerState.init).2 := by
  rw [valid_state_at_init mat tr hv h0 n, valid_state_at_init mat tr hv h0 (n + 1)]

theorem legal_below_of_schedule (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) (N : Nat)
    (h : ∀ n < N, foldAt (tr n).now (runFin mat (sched tr n) ServerState.init).2
                         (runFin mat (sched tr (n + 1)) ServerState.init).2 = true) :
    ∀ n < N, foldAt (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n hn
  rw [legal_at_is_about_the_schedule mat tr hv h0 n]
  exact h n hn

def statesOf (mat : Bool) :
    List (Step × Nat) → ServerState → List (Nat × ServerState × ServerState)
  | [],           _ => []
  | (st, n) :: w, s =>
      let s' := (stepOf mat st n s).2
      (n, s, s') :: statesOf mat w s'

def legalRunOf (mat : Bool) (w : List (Step × Nat)) : Bool :=
  (statesOf mat w ServerState.init).all (fun (n, a, b) => foldAt n a b)

theorem tiny_sweep_materialized :
    ((seqsUpToA (kernelsResp.take 3) 2).map instantiateA).all (legalRunOf true) = true := by
  decide

theorem tiny_sweep_projected :
    ((seqsUpToA (kernelsResp.take 3) 2).map instantiateA).all (legalRunOf false) = true := by
  decide

def demoSched : List (Step × Nat) := b1

theorem demo_runFin_reaches_fulfilment :
    ((runFin true demoSched ServerState.init).2.tasks.any (·.state == .fulfilled)) = true := by
  decide

theorem demo_runFin_settles :
    ((runFin true demoSched ServerState.init).2.promises.any (·.state != .pending)) = true := by
  decide

end Bounded
end Abstraction
