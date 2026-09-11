import «03-theorems».«bounded»
import «03-theorems».«trans»

namespace Abstract
namespace Holds

open AbstractModel
open Abstract.Bounded

theorem invariant_along_trace {P : Nat → ServerState → Bool}
    (hinit : ∀ now, P now ServerState.init = true)
    (hstep : ∀ (mat : Bool) (st : Event) (now n' : Nat) (s : ServerState),
               P now s = true → P n' (step mat st now s).2 = true)
    (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) :
    ∀ n, P (tr n).now (tr n).state = true
  | 0     => by rw [h0]; exact hinit _
  | n + 1 => by
      rw [(hv.state n)]
      exact hstep mat (tr n).event (tr n).now (tr (n + 1)).now (tr n).state
        (invariant_along_trace hinit hstep mat tr hv h0 n)

theorem invariant_along_trace_via {S : ServerState → Bool} {P : Nat → ServerState → Bool}
    (hinit : S ServerState.init = true)
    (hstep : ∀ (mat : Bool) (st : Event) (now : Nat) (s : ServerState),
               S s = true → S (step mat st now s).2 = true)
    (himp : ∀ (now : Nat) (s : ServerState), S s = true → P now s = true)
    (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) :
    ∀ n, P (tr n).now (tr n).state = true := by
  have key : ∀ n, S (tr n).state = true := by
    intro n
    induction n with
    | zero => rw [h0]; exact hinit
    | succ k ih => rw [(hv.state k)]; exact hstep mat _ _ _ ih
  exact fun n => himp _ _ (key n)

theorem invariant_along_trace_prop {S : ServerState → Prop} {P : Nat → ServerState → Bool}
    (hinit : S ServerState.init)
    (hstep : ∀ (mat : Bool) (st : Event) (now : Nat) (s : ServerState),
               S s → S (step mat st now s).2)
    (himp : ∀ (now : Nat) (s : ServerState), S s → P now s = true)
    (mat : Bool) (tr : Trace) (hv : Valid mat tr)
    (h0 : (tr 0).state = ServerState.init) :
    ∀ n, P (tr n).now (tr n).state = true := by
  have key : ∀ n, S (tr n).state := by
    intro n
    induction n with
    | zero => rw [h0]; exact hinit
    | succ k ih => rw [(hv.state k)]; exact hstep mat _ _ _ ih
  exact fun n => himp _ _ (key n)

section Along

variable (mat : Bool) (tr : Trace) (hv : Valid mat tr)
  (h0 : (tr 0).state = ServerState.init)

include mat hv h0

open Properties Abstract.Induction Abstract.Stepwise Abstract.Trans

theorem created_at_lte_timeout_at :
    ∀ n, well_formed_promise_created_at_lte_timeout_at (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.created_at_lte_timeout_at_init
    (fun mat st now n' s => Induction.created_at_lte_timeout_at_step mat st now n' s)
    mat tr hv h0

theorem pending_created_before_deadline :
    ∀ n, well_formed_promise_pending_created_before_deadline (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.pending_created_before_deadline_init
    (fun mat st now n' s => Induction.pending_created_before_deadline_step mat st now n' s)
    mat tr hv h0

theorem settled_at_iff_not_pending :
    ∀ n, well_formed_promise_settled_at_iff_not_pending (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.settled_at_iff_not_pending_init
    (fun mat st now n' s => Induction.settled_at_iff_not_pending_step mat st now n' s)
    mat tr hv h0

theorem timedout_is_server_owned :
    ∀ n, well_formed_promise_timedout_is_server_owned (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.timedout_is_server_owned_init
    (fun mat st now n' s => Induction.timedout_is_server_owned_step mat st now n' s)
    mat tr hv h0

theorem settled_at_lte_timeout_at :
    ∀ n, well_formed_promise_settled_at_lte_timeout_at (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.settled_at_lte_timeout_at_init
    (fun mat st now n' s => Induction.settled_at_lte_timeout_at_step mat st now n' s)
    mat tr hv h0

theorem deadline_verdict_matches_timer_tag :
    ∀ n, well_formed_promise_deadline_verdict_matches_timer_tag (tr n).now (tr n).state = true :=
  invariant_along_trace Induction.deadline_verdict_matches_timer_tag_init
    (fun mat st now n' s => Induction.deadline_verdict_matches_timer_tag_step mat st now n' s)
    mat tr hv h0

theorem pending_has_no_value :
    ∀ n, well_formed_promise_pending_has_no_value (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.no_value_unless_settled_init
    Induction.no_value_unless_settled_step
    Induction.pending_has_no_value_of_strengthening mat tr hv h0

theorem deadline_settlement_has_no_value :
    ∀ n, well_formed_promise_deadline_settlement_has_no_value (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.no_value_unless_settled_init
    Induction.no_value_unless_settled_step
    Induction.deadline_settlement_has_no_value_of_strengthening mat tr hv h0

theorem task_acquired_iff_has_pid :
    ∀ n, well_formed_task_acquired_iff_has_pid (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_acquired_iff_has_pid_of_shape mat tr hv h0

theorem task_acquired_iff_has_ttl :
    ∀ n, well_formed_task_acquired_iff_has_ttl (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_acquired_iff_has_ttl_of_shape mat tr hv h0

theorem task_acquired_iff_has_lease_timeout_at :
    ∀ n, well_formed_task_acquired_iff_has_lease_timeout_at (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_acquired_iff_has_lease_timeout_at_of_shape mat tr hv h0

theorem task_pending_iff_has_retry_timeout_at :
    ∀ n, well_formed_task_pending_iff_has_retry_timeout_at (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_pending_iff_has_retry_timeout_at_of_shape mat tr hv h0

theorem task_fulfilled_is_cleared :
    ∀ n, well_formed_task_fulfilled_is_cleared (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_fulfilled_is_cleared_of_shape mat tr hv h0

theorem task_suspended_is_cleared :
    ∀ n, well_formed_task_suspended_is_cleared (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_suspended_is_cleared_of_shape mat tr hv h0

theorem task_halted_is_cleared :
    ∀ n, well_formed_task_halted_is_cleared (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_halted_is_cleared_of_shape mat tr hv h0

theorem task_suspended_has_no_resumes :
    ∀ n, well_formed_task_suspended_has_no_resumes (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_suspended_has_no_resumes_of_shape mat tr hv h0

theorem task_acquired_version_positive :
    ∀ n, well_formed_task_acquired_version_positive (tr n).now (tr n).state = true :=
  invariant_along_trace_via Induction.task_shape_init Induction.task_shape_step
    Induction.task_acquired_version_positive_of_shape mat tr hv h0

theorem store_nodup : ∀ n, StoreNodup (tr n).state := by
  intro n
  induction n with
  | zero => rw [h0]; exact storeNodup_init
  | succ k ih => rw [(hv.state k)]; exact storeNodup_step mat _ _ _ ih

theorem object_ids_unique :
    ∀ n, well_formed_store_object_ids_unique (tr n).now (tr n).state = true :=
  fun n => object_ids_unique_of_nodup _ _ (store_nodup mat tr hv h0 n)

theorem schedule_ids_unique :
    ∀ n, well_formed_store_schedule_ids_unique (tr n).now (tr n).state = true :=
  fun n => schedule_ids_unique_of_nodup _ _ (store_nodup mat tr hv h0 n)

theorem outbox_keys_unique :
    ∀ n, well_formed_store_outbox_keys_unique (tr n).now (tr n).state = true :=
  fun n => outbox_keys_unique_of_nodup _ _ (store_nodup mat tr hv h0 n)

theorem monotone_promise_set_grows :
    ∀ n, Properties.monotone_promise_set_grows (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Stepwise.monotone_promise_set_grows_step mat _ _ _ _

theorem monotone_task_set_grows :
    ∀ n, Properties.monotone_task_set_grows (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Stepwise.monotone_task_set_grows_step mat _ _ _ _ (store_nodup mat tr hv h0 n)

theorem preserved_promise_birth_fields_immutable :
    ∀ n, Properties.preserved_promise_birth_fields_immutable
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_promise_birth_fields_immutable_step mat _ _ _ _
    (store_nodup mat tr hv h0 n).1

theorem preserved_settled_promise_record :
    ∀ n, Properties.preserved_settled_promise_record
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_settled_promise_record_step mat _ _ _ _
    (store_nodup mat tr hv h0 n).1

theorem preserved_promise_state_frozen_once_settled :
    ∀ n, Properties.preserved_promise_state_frozen_once_settled
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_promise_state_frozen_once_settled_step mat _ _ _ _
    (store_nodup mat tr hv h0 n).1

theorem preserved_promise_value_until_settlement :
    ∀ n, Properties.preserved_promise_value_until_settlement
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_promise_value_until_settlement_step mat _ _ _ _
    (store_nodup mat tr hv h0 n).1

theorem preserved_promise_no_duplicate_ids :
    ∀ n, Properties.preserved_promise_no_duplicate_ids
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_promise_no_duplicate_ids_step mat _ _ _ _
    (store_nodup mat tr hv h0 n)

theorem preserved_promise_settlement_is_one_way :
    ∀ n, Properties.preserved_promise_settlement_is_one_way
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.preserved_promise_settlement_is_one_way_step mat _ _ _ _
    (store_nodup mat tr hv h0 n)

theorem monotone_promise_callbacks_grow_while_pending :
    ∀ n, Properties.monotone_promise_callbacks_grow_while_pending
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.monotone_promise_callbacks_grow_while_pending_step mat _ _ _ _
    (store_nodup mat tr hv h0 n)

theorem monotone_promise_listeners_grow_while_pending :
    ∀ n, Properties.monotone_promise_listeners_grow_while_pending
           (tr n).now (tr n).state (tr (n + 1)).state = true := by
  intro n
  rw [(hv.state n)]
  exact Trans.monotone_promise_listeners_grow_while_pending_step mat _ _ _ _
    (store_nodup mat tr hv h0 n)

end Along

section NotInductiveAlone

open AbstractModel

def sneaky : ServerState :=
  { objects := [{ id := oid "p",
                  promise := { state := .pending, param := {},
                               value := { data := some "x", headers := [] },
                               type := .internal, timeoutAt := 10, createdAt := 0 } }] }

theorem sneaky_satisfies_the_entry :
    Properties.well_formed_promise_deadline_settlement_has_no_value 0 sneaky = true := by
  decide

theorem one_step_breaks_it :
    Properties.well_formed_promise_deadline_settlement_has_no_value 20
      (step true (.internal (.promiseTimeout { id := oid "p" })) 20 sneaky).2 = false := by
  decide

theorem sneaky_is_unreachable_because :
    Properties.well_formed_promise_pending_has_no_value 0 sneaky = false := by
  decide

end NotInductiveAlone

end Holds
end Abstract
