import «02-abstract».«state»

namespace AbstractModel
namespace Properties

open ServerModel

inductive Property where

  | state (f : Nat → ServerState → Bool)

  | trans (f : Nat → ServerState → ServerState → Bool)

structure Named where
  name : String
  property : Property

def well_formed_promise_created_at_lte_timeout_at (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.createdAt ≤ p.timeoutAt

def well_formed_promise_pending_created_before_deadline (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.state != .pending || p.createdAt < p.timeoutAt

def well_formed_promise_settled_at_lte_timeout_at (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    match p.settledAt with
    | none => true
    | some x => x ≤ p.timeoutAt

def well_formed_promise_created_at_lte_settled_at (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    match p.settledAt with
    | none => true
    | some x => p.createdAt ≤ x

def well_formed_promise_settled_at_iff_not_pending (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    (p.state != .pending) == p.settledAt.isSome

def well_formed_promise_pending_has_no_value (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.state != .pending || (p.value.data.isNone && p.value.headers.isEmpty)

def well_formed_promise_deadline_verdict_matches_timer_tag (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.settledAt != some p.timeoutAt
      || p.state == (if p.type == .deadline then .resolved else .rejectedTimedout)

def well_formed_promise_deadline_settlement_has_no_value (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.settledAt != some p.timeoutAt
      || (p.value.data.isNone && p.value.headers.isEmpty)

def well_formed_promise_timedout_is_server_owned (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.state != .rejectedTimedout || p.settledAt == some p.timeoutAt

def well_formed_promise_callbacks_unique (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.callbacks.eraseDups.length == p.callbacks.length

def well_formed_promise_listeners_unique (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.listeners.eraseDups.length == p.listeners.length

def well_formed_promise_obligations_require_external (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    (p.callbacks.isEmpty && p.listeners.isEmpty) || p.type.awaitable

def well_formed_promise_awaiter_is_not_self (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o =>
    let p := o.promise
    !p.callbacks.contains o.id

def well_formed_promise_callbacks_same_origin (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o =>
    o.promise.callbacks.all (·.sameOrigin o.id)

def well_formed_promise_created_at_lte_now (now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.createdAt ≤ now

def well_formed_promise_settled_at_lte_now (now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    match p.settledAt with
    | none => true
    | some x => x ≤ now

def well_formed_task_acquired_iff_has_pid (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    (t.state == .acquired) == t.pid.isSome

def well_formed_task_acquired_iff_has_ttl (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    (t.state == .acquired) == t.ttl.isSome

def well_formed_task_acquired_iff_has_lease_timeout_at (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    (t.state == .acquired) == t.leaseTimeoutAt.isSome

def well_formed_task_pending_iff_has_retry_timeout_at (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    (t.state == .pending) == t.retryTimeoutAt.isSome

def well_formed_task_fulfilled_is_cleared (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.state != .fulfilled
      || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone
          && t.resumes.isEmpty)

def well_formed_task_suspended_is_cleared (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.state != .suspended
      || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone)

def well_formed_task_halted_is_cleared (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.state != .halted
      || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone)

def well_formed_task_suspended_has_no_resumes (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.state != .suspended || t.resumes.isEmpty

def well_formed_task_resumes_unique (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.resumes.eraseDups.length == t.resumes.length

def well_formed_task_acquired_version_positive (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t =>
    t.state != .acquired || 1 ≤ t.version

def well_formed_schedule_created_at_lte_next_run_at (_now : Nat) (s : ServerState) : Bool :=
  s.schedules.all fun c =>
    c.createdAt ≤ c.nextRunAt

def well_formed_schedule_created_at_lte_last_run_at (_now : Nat) (s : ServerState) : Bool :=
  s.schedules.all fun c =>
    match c.lastRunAt with
    | none => true
    | some l => c.createdAt ≤ l

def well_formed_schedule_last_run_at_lt_next_run_at (_now : Nat) (s : ServerState) : Bool :=
  s.schedules.all fun c =>
    match c.lastRunAt with
    | none => true
    | some l => l < c.nextRunAt

def well_formed_store_object_ids_unique (_now : Nat) (s : ServerState) : Bool :=
  (s.objects.map (·.id)).eraseDups.length == s.objects.length

def well_formed_store_schedule_ids_unique (_now : Nat) (s : ServerState) : Bool :=
  (s.schedules.map (·.id)).eraseDups.length == s.schedules.length

def well_formed_store_outbox_keys_unique (_now : Nat) (s : ServerState) : Bool :=
  (s.outbox.map (·.key)).eraseDups.length == s.outbox.length

def consistent_task_iff_kind_task (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o =>
    o.task.isSome == o.promise.type.isRunnable

def consistent_settled_promise_has_fulfilled_task (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o =>
    o.promise.state == .pending || o.task.all (·.state == .fulfilled)

def consistent_callback_awaiter_is_targeted (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    p.callbacks.all fun a =>
      s.objects.any (fun q => q.id == a && q.promise.type.isRunnable)

def consistent_outbox_execute_names_existing_task (_now : Nat) (s : ServerState) : Bool :=
  s.outbox.all fun e =>
    match e.message with
    | .execute id _ => s.hasTask id
    | .unblock _    => true

def consistent_outbox_never_ahead (_now : Nat) (s : ServerState) : Bool :=
  s.outbox.all fun e =>
    match e.message with
    | .execute id v =>
        match s.task? id with
        | some t => v ≤ t.version
        | none   => true
    | .unblock _ => true

def consistent_outbox_execute_address_is_target_tag (_now : Nat) (s : ServerState) : Bool :=
  s.outbox.all fun e =>
    match e.message with
    | .execute id _ =>
        match s.promise? id with
        | some p => e.address == p.type.target?.getD ""
        | none   => true
    | .unblock _ => true

def consistent_outbox_unblock_names_settled_promise (_now : Nat) (s : ServerState) : Bool :=
  s.outbox.all fun e =>
    match e.message with
    | .unblock r =>
        r.state != .pending
          && s.objects.any (fun o => o.id == r.id && o.promise.state != .pending)
    | .execute _ _ => true

def consistent_suspended_task_holds_rung (now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o => o.task.all fun t =>
    t.state != .suspended
      || (o.promise.project now).state != .pending
      || s.promises.any (·.callbacks.contains o.id)

def consistent_settled_task_promise_settled (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o => o.task.all fun t =>
    t.state != .fulfilled || o.promise.state != .pending

def preserved_promise_birth_fields_immutable (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none => true
    | some q =>
        q.param.data == p.param.data && q.param.headers == p.param.headers
          && q.type == p.type && q.timeoutAt == p.timeoutAt && q.createdAt == p.createdAt

def preserved_settled_promise_record (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.state == .pending ||
      (match b.promise? o.id with
       | none => false
       | some q =>
           q.state == p.state && q.settledAt == p.settledAt
             && q.value.data == p.value.data && q.value.headers == p.value.headers)

def monotone_promise_set_grows (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => b.objects.any (·.id == o.id)

def monotone_task_set_grows (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => !o.task.isSome || b.hasTask o.id

def monotone_task_version_increases_only_on_acquisition (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        if t.state == .pending && u.state == .acquired then
          u.version == t.version + 1
        else
          u.version == t.version

def preserved_fulfilled_task (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    t.state != .fulfilled ||
      (match b.task? o.id with
       | none => false
       | some u =>
           u.state == .fulfilled && u.version == t.version && u.resumes.isEmpty
             && u.pid.isNone && u.ttl.isNone && u.leaseTimeoutAt.isNone && u.retryTimeoutAt.isNone)

def preserved_no_dead_dispatch (now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    u.state != .pending
      || (match a.task? o.id with
          | some t => t.state == .pending
          | none   => false)
      || (match b.promise? o.id with
          | some p => (p.project now).state == .pending
          | none   => true)

def preserved_execute_only_for_live_task (now : Nat) (a b : ServerState) : Bool :=
  b.outbox.all fun e =>
    match e.message with
    | .unblock _ => true
    | .execute id v =>
        a.outbox.any (fun f =>
          match f.message with
          | .execute id' v' => id' == id && v' == v && f.address == e.address
          | .unblock _ => false)
        || (match b.promise? id with
            | some p => (p.project now).state == .pending
            | none   => true)

def subsetOf {α} [BEq α] (xs ys : List α) : Bool := xs.all ys.contains

def preserved_promise_state_frozen_once_settled (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.state == .pending ||
      (match b.promise? o.id with
       | none => false
       | some q => q.state == p.state)

def preserved_promise_settlement_is_one_way (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    q.state != .pending
      || (match a.promise? o.id with
          | some p => p.state == .pending
          | none   => true)

def consistent_promise_settled_at_moves_with_state (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none => false
    | some q => (q.settledAt != p.settledAt) == (q.state != p.state)

def preserved_promise_value_until_settlement (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none => false
    | some q =>
        q.state != .pending
          || (q.value.data == p.value.data && q.value.headers == p.value.headers)

def preserved_promise_no_duplicate_ids (_now : Nat) (_a b : ServerState) : Bool :=
  (b.objects.map (·.id)).eraseDups.length == b.objects.length

def monotone_promise_callbacks_grow_while_pending (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    q.state != .pending ||
      (match a.promise? o.id with
       | none => q.callbacks.isEmpty
       | some p => subsetOf p.callbacks q.callbacks)

def monotone_promise_callbacks_shrink_once_settled (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    q.state == .pending ||
      (match a.promise? o.id with
       | none => q.callbacks.isEmpty
       | some p => subsetOf q.callbacks p.callbacks)

def monotone_promise_listeners_grow_while_pending (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    q.state != .pending ||
      (match a.promise? o.id with
       | none => q.listeners.isEmpty
       | some p => subsetOf p.listeners q.listeners)

def monotone_promise_listeners_shrink_once_settled (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    q.state == .pending ||
      (match a.promise? o.id with
       | none => q.listeners.isEmpty
       | some p => subsetOf q.listeners p.listeners)

def consistent_promise_state_edge_admissible (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none   => true
    | some q =>
        [ (PromiseState.pending,          PromiseState.pending),
          (PromiseState.pending,          PromiseState.resolved),
          (PromiseState.pending,          PromiseState.rejected),
          (PromiseState.pending,          PromiseState.rejectedCanceled),
          (PromiseState.pending,          PromiseState.rejectedTimedout),
          (PromiseState.resolved,         PromiseState.resolved),
          (PromiseState.rejected,         PromiseState.rejected),
          (PromiseState.rejectedCanceled, PromiseState.rejectedCanceled),
          (PromiseState.rejectedTimedout, PromiseState.rejectedTimedout)
        ].contains (p.state, q.state)

def consistent_task_state_edge_admissible (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none   => true
    | some u =>
        [ (TaskState.pending,   TaskState.pending),
          (TaskState.pending,   TaskState.acquired),
          (TaskState.pending,   TaskState.halted),
          (TaskState.pending,   TaskState.fulfilled),
          (TaskState.acquired,  TaskState.pending),
          (TaskState.acquired,  TaskState.acquired),
          (TaskState.acquired,  TaskState.suspended),
          (TaskState.acquired,  TaskState.halted),
          (TaskState.acquired,  TaskState.fulfilled),
          (TaskState.suspended, TaskState.pending),
          (TaskState.suspended, TaskState.suspended),
          (TaskState.suspended, TaskState.halted),
          (TaskState.suspended, TaskState.fulfilled),
          (TaskState.halted,    TaskState.pending),
          (TaskState.halted,    TaskState.halted),
          (TaskState.halted,    TaskState.fulfilled),
          (TaskState.fulfilled, TaskState.fulfilled)
        ].contains (t.state, u.state)

def preserved_task_acquisition_only_from_pending (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    u.state != .acquired
      || (match a.task? o.id with
          | some t => t.state == .pending || t.state == .acquired
          | none   => true)

def preserved_task_suspension_only_from_acquired (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    u.state != .suspended
      || (match a.task? o.id with
          | some t => t.state == .acquired || t.state == .suspended
          | none   => false)

def preserved_task_halted_only_reenters_via_pending (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    t.state != .halted
      || (match b.task? o.id with
          | none   => false
          | some u => [TaskState.halted, TaskState.pending, TaskState.fulfilled].contains u.state)

def consistent_settlement_fulfils_task (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.state != .pending ||
      (match b.promise? o.id, b.task? o.id with
       | some q, some u => q.state == .pending || u.state == .fulfilled
       | _, _ => true)

def consistent_task_fulfilment_needs_settlement (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    u.state != .fulfilled ||
      (match a.task? o.id with
       | none => true
       | some t =>
           t.state == .fulfilled
             || (match a.promise? o.id, b.promise? o.id with
                 | some p, some q => p.state == .pending && q.state != .pending
                 | _, _ => false))

def consistent_obligation_discharge_requires_settled (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none => true
    | some q =>
        (p.callbacks.all q.callbacks.contains && p.listeners.all q.listeners.contains)
          || q.state != .pending

def consistent_callback_consumption_resumes_awaiter (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.callbacks.all fun x =>
      (match b.promise? o.id with
       | none => true
       | some q => q.callbacks.contains x)
      || (match b.task? x with
          | none => true
          | some u => u.state == .fulfilled || u.resumes.contains o.id)

def consistent_listener_consumption_enqueues_unblock (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.listeners.all fun addr =>
      (match b.promise? o.id with
       | none => true
       | some q => q.listeners.contains addr)
      || (b.outbox.filter (fun e =>
            e.address == addr &&
              (match e.message with
               | .unblock r => r.id == o.id && r.state != .pending
               | .execute _ _ => false))).length == 1

def consistent_wake_follows_callback_consumption (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    match a.task? o.id with
    | none => true
    | some t =>
        !(t.state == .suspended && u.state == .pending)
          || a.objects.any (fun p =>
               p.promise.callbacks.contains o.id
                 && (match b.promise? p.id with
                     | none => false
                     | some q => !q.callbacks.contains o.id)
                 && u.resumes.contains p.id)

def consistent_suspension_registers_callback (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    u.state != .suspended
      || (match a.task? o.id with
          | none => false
          | some t => t.state == .suspended)
      || b.objects.any (fun q =>
           q.promise.callbacks.contains o.id
             && (match a.promise? q.id with
                 | none => true
                 | some p => !p.callbacks.contains o.id)
             && q.promise.state == .pending)

def consistent_task_birth_couples_promise_birth (_now : Nat) (a b : ServerState) : Bool :=
  (b.objects.all fun o => o.task.all fun u =>
     a.hasTask o.id
       || ((!a.objects.any (·.id == o.id))
            && (let q := o.promise
                q.type.isRunnable
                  && (if u.state == .fulfilled then q.state != .pending
                      else q.state == .pending))
            && ((u.state == .pending && u.version == 0)
                || (u.state == .acquired && 1 ≤ u.version)
                || (u.state == .fulfilled && u.version == 0))))
  && (b.objects.all fun o =>
        a.objects.any (·.id == o.id)
          || !o.promise.type.isRunnable
          || o.task.isSome)

def monotone_outbox_keys_never_disappear (_now : Nat) (a b : ServerState) : Bool :=
  a.outbox.all fun e => b.outbox.any (fun f => f.key == e.key)

def consistent_new_execute_matches_task_and_target (_now : Nat) (a b : ServerState) : Bool :=
  b.outbox.all fun f =>
    match f.message with
    | .unblock _ => true
    | .execute id v =>
        a.outbox.any (fun e =>
          match e.message with
          | .execute id' v' => id' == id && v' == v && e.address == f.address
          | .unblock _ => false)
        || ((match b.task? id with
             | some t => t.version == v
             | none   => false)
            && (match b.promise? id with
                | some p => f.address == p.type.target?.getD ""
                | none   => false))

def consistent_new_unblock_carries_stored_record (_now : Nat) (a b : ServerState) : Bool :=
  b.outbox.all fun f =>
    match f.message with
    | .execute _ _ => true
    | .unblock r =>
        a.outbox.any (fun e =>
          match e.message with
          | .unblock r' => e.address == f.address && r'.id == r.id
          | .execute _ _ => false)
        || (r.state != .pending
            && (match b.promise? r.id with
                | some p =>
                    p.state == r.state && p.settledAt == r.settledAt
                      && p.value.data == r.value.data && p.timeoutAt == r.timeoutAt
                      && p.createdAt == r.createdAt
                | none => false))

def consistent_new_unblock_discharges_its_listener (_now : Nat) (a b : ServerState) : Bool :=
  b.outbox.all fun f =>
    match f.message with
    | .execute _ _ => true
    | .unblock r =>
        a.outbox.any (fun e =>
          match e.message with
          | .unblock r' => e.address == f.address && r'.id == r.id
          | .execute _ _ => false)
        || ((a.objects.any fun o => o.id == r.id && o.promise.listeners.contains f.address)
            && (b.objects.all fun o =>
                  o.id != r.id || !o.promise.listeners.contains f.address))

def preserved_schedule_birth_fields_immutable (_now : Nat) (a b : ServerState) : Bool :=
  a.schedules.all fun c =>
    match b.schedules.find? (·.id == c.id) with
    | none => true
    | some d =>
        d.cron == c.cron && d.promiseId == c.promiseId
          && d.promiseTimeout == c.promiseTimeout
          && d.promiseParam.data == c.promiseParam.data
          && d.promiseParam.headers == c.promiseParam.headers
          && d.promiseType == c.promiseType && d.createdAt == c.createdAt

def consistent_task_birth_state (_now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    (a.hasTask o.id)
    || (u.state == .pending && u.retryTimeoutAt.isSome
          && u.pid.isNone && u.ttl.isNone && u.leaseTimeoutAt.isNone && u.resumes.isEmpty)
    || (u.state == .fulfilled && u.retryTimeoutAt.isNone
          && u.pid.isNone && u.ttl.isNone && u.leaseTimeoutAt.isNone && u.resumes.isEmpty)
    || (u.state == .acquired && 1 ≤ u.version && u.retryTimeoutAt.isNone
          && u.pid.isSome && u.ttl.isSome && u.leaseTimeoutAt.isSome && u.resumes.isEmpty)

def consistent_task_lease_released_atomically (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state == .acquired && u.state != .acquired)
        || (u.pid.isNone && u.ttl.isNone && u.leaseTimeoutAt.isNone && u.version == t.version)

def preserved_task_lease_holder_stable (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state == .acquired && u.state == .acquired && u.version == t.version)
        || (u.pid == t.pid && u.ttl == t.ttl)

def consistent_task_lease_fields_move_together (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        (u.pid == t.pid && u.ttl == t.ttl && u.leaseTimeoutAt == t.leaseTimeoutAt)
        || (t.state != .acquired && u.state == .acquired
              && u.pid.isSome && u.ttl.isSome && u.leaseTimeoutAt.isSome)
        || (t.state == .acquired && u.state != .acquired
              && u.pid.isNone && u.ttl.isNone && u.leaseTimeoutAt.isNone)
        || (t.state == .acquired && u.state == .acquired
              && u.pid == t.pid && u.ttl == t.ttl)

def monotone_task_resumes_grow_or_clear (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u => u.resumes.isEmpty || subsetOf t.resumes u.resumes

def consistent_task_resumes_cleared_only_on_dispatch_or_park (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(!t.resumes.isEmpty && u.resumes.isEmpty)
        || u.state == .acquired || u.state == .suspended || u.state == .fulfilled

def consistent_task_acquisition_is_atomic (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state != .acquired && u.state == .acquired)
        || (t.state == .pending && t.version < u.version
              && u.pid.isSome && u.ttl.isSome
              && u.leaseTimeoutAt == some (now + u.ttl.getD 0)
              && u.retryTimeoutAt.isNone && u.resumes.isEmpty)

def consistent_task_lease_deadline_is_now_plus_ttl (now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o => o.task.all fun u =>
    match u.leaseTimeoutAt with
    | none => true
    | some d =>
        d == now + u.ttl.getD 0
        || (match a.task? o.id with
            | some t => t.leaseTimeoutAt == some d && t.ttl == u.ttl && t.state == u.state
            | none   => false)

def consistent_task_pending_entry_arms_retry (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state != .pending && u.state == .pending) || u.retryTimeoutAt == some now

def consistent_task_retry_rearm_only_when_due (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state == .pending && u.state == .pending && u.retryTimeoutAt != t.retryTimeoutAt)
        || (match t.retryTimeoutAt with | some due => decide (due ≤ now) | none => false)

def consistent_task_wake_records_resume (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none => true
    | some u =>
        !(t.state == .suspended && u.state == .pending)
        || (!u.resumes.isEmpty && u.retryTimeoutAt == some now && u.version == t.version)

def consistent_task_state_edge_internal_admissible (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    match b.task? o.id with
    | none   => true
    | some u =>
        [ (TaskState.pending,   TaskState.pending),
          (TaskState.pending,   TaskState.fulfilled),
          (TaskState.acquired,  TaskState.pending),
          (TaskState.acquired,  TaskState.acquired),
          (TaskState.acquired,  TaskState.fulfilled),
          (TaskState.suspended, TaskState.pending),
          (TaskState.suspended, TaskState.suspended),
          (TaskState.suspended, TaskState.fulfilled),
          (TaskState.halted,    TaskState.halted),
          (TaskState.halted,    TaskState.fulfilled),
          (TaskState.fulfilled, TaskState.fulfilled)
        ].contains (t.state, u.state)

def consistent_promise_state_edge_internal_admissible (_now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    match b.promise? o.id with
    | none   => true
    | some q =>
        (p.state == q.state)
          || (p.state == .pending
                && (q.state == .rejectedTimedout || (q.state == .resolved && p.type == .deadline)))

def internalChecks : List Named :=
  [ { name := "consistent_task_state_edge_internal_admissible"
      , property := .trans consistent_task_state_edge_internal_admissible },
    { name := "consistent_promise_state_edge_internal_admissible"
      , property := .trans consistent_promise_state_edge_internal_admissible } ]

def internalFailures (now : Nat) (a b : ServerState) : List String :=
  internalChecks.filterMap fun l =>
    match l.property with
    | .state _ => none
    | .trans f => if f now a b then none else some l.name

def internalWellFormed (now : Nat) (a b : ServerState) : Bool :=
  (internalFailures now a b).isEmpty

def consistent_promise_settlement_stamp (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.state != .pending ||
      (match b.promise? o.id with
       | none => false
       | some q =>
           q.state == .pending
             || (q.settledAt == some now && now < q.timeoutAt
                   && q.state != .rejectedTimedout)
             || (q.settledAt == some q.timeoutAt && q.timeoutAt ≤ now
                   && (if q.type == .deadline then q.state == .resolved
                       else q.state == .rejectedTimedout)
                   && q.value.data == p.value.data
                   && q.value.headers == p.value.headers))

def preserved_timedout_is_server_owned (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o =>
    let p := o.promise
    p.state != .pending
      || (match b.promise? o.id with
          | none   => true
          | some q => q.state != .rejectedTimedout
                        || (p.timeoutAt ≤ now && q.settledAt == some p.timeoutAt))

def consistent_new_promise_born_clean (now : Nat) (a b : ServerState) : Bool :=
  b.objects.all fun o =>
    let q := o.promise
    a.objects.any (·.id == o.id)
      || (q.callbacks.isEmpty && q.listeners.isEmpty
          && q.value.data.isNone && q.value.headers.isEmpty
          && q.createdAt ≤ now
          && ((q.state == .pending && q.settledAt.isNone && q.createdAt < q.timeoutAt)
              || (q.settledAt == some q.timeoutAt && q.createdAt == q.timeoutAt
                  && q.timeoutAt ≤ now
                  && (if q.type == .deadline then q.state == .resolved
                      else q.state == .rejectedTimedout))))

def monotone_task_retry_rearm_advances (now : Nat) (a b : ServerState) : Bool :=
  a.objects.all fun o => o.task.all fun t =>
    t.state != .pending ||
      (match b.task? o.id with
       | none   => true
       | some u => u.state != .pending || u.retryTimeoutAt == t.retryTimeoutAt
                     || (match u.retryTimeoutAt with
                         | some d => now < d
                         | none   => false))

def catalogue : List Named :=
  [ { name := "well_formed_promise_created_at_lte_timeout_at"
      , property := .state well_formed_promise_created_at_lte_timeout_at },
    { name := "well_formed_promise_pending_created_before_deadline"
      , property := .state well_formed_promise_pending_created_before_deadline },
    { name := "well_formed_promise_settled_at_lte_timeout_at"
      , property := .state well_formed_promise_settled_at_lte_timeout_at },
    { name := "well_formed_promise_created_at_lte_settled_at"
      , property := .state well_formed_promise_created_at_lte_settled_at },
    { name := "well_formed_promise_settled_at_iff_not_pending"
      , property := .state well_formed_promise_settled_at_iff_not_pending },
    { name := "well_formed_promise_pending_has_no_value"
      , property := .state well_formed_promise_pending_has_no_value },
    { name := "well_formed_promise_deadline_verdict_matches_timer_tag"
      , property := .state well_formed_promise_deadline_verdict_matches_timer_tag },
    { name := "well_formed_promise_deadline_settlement_has_no_value"
      , property := .state well_formed_promise_deadline_settlement_has_no_value },
    { name := "well_formed_promise_timedout_is_server_owned"
      , property := .state well_formed_promise_timedout_is_server_owned },
    { name := "well_formed_promise_callbacks_unique"
      , property := .state well_formed_promise_callbacks_unique },
    { name := "well_formed_promise_listeners_unique"
      , property := .state well_formed_promise_listeners_unique },
    { name := "well_formed_promise_obligations_require_external"
      , property := .state well_formed_promise_obligations_require_external },
    { name := "well_formed_promise_awaiter_is_not_self"
      , property := .state well_formed_promise_awaiter_is_not_self },
    { name := "well_formed_promise_callbacks_same_origin"
      , property := .state well_formed_promise_callbacks_same_origin },
    { name := "well_formed_promise_created_at_lte_now"
      , property := .state well_formed_promise_created_at_lte_now },
    { name := "well_formed_promise_settled_at_lte_now"
      , property := .state well_formed_promise_settled_at_lte_now },
    { name := "well_formed_task_acquired_iff_has_pid"
      , property := .state well_formed_task_acquired_iff_has_pid },
    { name := "well_formed_task_acquired_iff_has_ttl"
      , property := .state well_formed_task_acquired_iff_has_ttl },
    { name := "well_formed_task_acquired_iff_has_lease_timeout_at"
      , property := .state well_formed_task_acquired_iff_has_lease_timeout_at },
    { name := "well_formed_task_pending_iff_has_retry_timeout_at"
      , property := .state well_formed_task_pending_iff_has_retry_timeout_at },
    { name := "well_formed_task_fulfilled_is_cleared"
      , property := .state well_formed_task_fulfilled_is_cleared },
    { name := "well_formed_task_suspended_is_cleared"
      , property := .state well_formed_task_suspended_is_cleared },
    { name := "well_formed_task_halted_is_cleared"
      , property := .state well_formed_task_halted_is_cleared },
    { name := "well_formed_task_suspended_has_no_resumes"
      , property := .state well_formed_task_suspended_has_no_resumes },
    { name := "well_formed_task_resumes_unique"
      , property := .state well_formed_task_resumes_unique },
    { name := "well_formed_task_acquired_version_positive"
      , property := .state well_formed_task_acquired_version_positive },
    { name := "well_formed_schedule_created_at_lte_next_run_at"
      , property := .state well_formed_schedule_created_at_lte_next_run_at },
    { name := "well_formed_schedule_created_at_lte_last_run_at"
      , property := .state well_formed_schedule_created_at_lte_last_run_at },
    { name := "well_formed_schedule_last_run_at_lt_next_run_at"
      , property := .state well_formed_schedule_last_run_at_lt_next_run_at },
    { name := "well_formed_store_object_ids_unique"
      , property := .state well_formed_store_object_ids_unique },
    { name := "well_formed_store_schedule_ids_unique"
      , property := .state well_formed_store_schedule_ids_unique },
    { name := "well_formed_store_outbox_keys_unique"
      , property := .state well_formed_store_outbox_keys_unique },
    { name := "consistent_task_iff_kind_task"
      , property := .state consistent_task_iff_kind_task },
    { name := "consistent_settled_promise_has_fulfilled_task"
      , property := .state consistent_settled_promise_has_fulfilled_task },
    { name := "consistent_callback_awaiter_is_targeted"
      , property := .state consistent_callback_awaiter_is_targeted },
    { name := "consistent_outbox_execute_names_existing_task"
      , property := .state consistent_outbox_execute_names_existing_task },
    { name := "consistent_outbox_never_ahead"
      , property := .state consistent_outbox_never_ahead },
    { name := "consistent_outbox_execute_address_is_target_tag"
      , property := .state consistent_outbox_execute_address_is_target_tag },
    { name := "consistent_outbox_unblock_names_settled_promise"
      , property := .state consistent_outbox_unblock_names_settled_promise },
    { name := "consistent_settled_task_promise_settled"
      , property := .state consistent_settled_task_promise_settled },
    { name := "consistent_suspended_task_holds_rung"
      , property := .state consistent_suspended_task_holds_rung },
    { name := "preserved_promise_birth_fields_immutable"
      , property := .trans preserved_promise_birth_fields_immutable },
    { name := "preserved_settled_promise_record"
      , property := .trans preserved_settled_promise_record },
    { name := "monotone_promise_set_grows"
      , property := .trans monotone_promise_set_grows },
    { name := "monotone_task_set_grows"
      , property := .trans monotone_task_set_grows },
    { name := "monotone_task_version_increases_only_on_acquisition"
      , property := .trans monotone_task_version_increases_only_on_acquisition },
    { name := "preserved_fulfilled_task"
      , property := .trans preserved_fulfilled_task },
    { name := "preserved_promise_state_frozen_once_settled"
      , property := .trans preserved_promise_state_frozen_once_settled },
    { name := "preserved_promise_settlement_is_one_way"
      , property := .trans preserved_promise_settlement_is_one_way },
    { name := "consistent_promise_settled_at_moves_with_state"
      , property := .trans consistent_promise_settled_at_moves_with_state },
    { name := "preserved_promise_value_until_settlement"
      , property := .trans preserved_promise_value_until_settlement },
    { name := "preserved_promise_no_duplicate_ids"
      , property := .trans preserved_promise_no_duplicate_ids },
    { name := "monotone_promise_callbacks_grow_while_pending"
      , property := .trans monotone_promise_callbacks_grow_while_pending },
    { name := "monotone_promise_callbacks_shrink_once_settled"
      , property := .trans monotone_promise_callbacks_shrink_once_settled },
    { name := "monotone_promise_listeners_grow_while_pending"
      , property := .trans monotone_promise_listeners_grow_while_pending },
    { name := "monotone_promise_listeners_shrink_once_settled"
      , property := .trans monotone_promise_listeners_shrink_once_settled },
    { name := "consistent_promise_state_edge_admissible"
      , property := .trans consistent_promise_state_edge_admissible },
    { name := "consistent_task_state_edge_admissible"
      , property := .trans consistent_task_state_edge_admissible },
    { name := "preserved_task_acquisition_only_from_pending"
      , property := .trans preserved_task_acquisition_only_from_pending },
    { name := "preserved_task_suspension_only_from_acquired"
      , property := .trans preserved_task_suspension_only_from_acquired },
    { name := "preserved_task_halted_only_reenters_via_pending"
      , property := .trans preserved_task_halted_only_reenters_via_pending },
    { name := "consistent_settlement_fulfils_task"
      , property := .trans consistent_settlement_fulfils_task },
    { name := "consistent_task_fulfilment_needs_settlement"
      , property := .trans consistent_task_fulfilment_needs_settlement },
    { name := "consistent_obligation_discharge_requires_settled"
      , property := .trans consistent_obligation_discharge_requires_settled },
    { name := "consistent_callback_consumption_resumes_awaiter"
      , property := .trans consistent_callback_consumption_resumes_awaiter },
    { name := "consistent_listener_consumption_enqueues_unblock"
      , property := .trans consistent_listener_consumption_enqueues_unblock },
    { name := "consistent_wake_follows_callback_consumption"
      , property := .trans consistent_wake_follows_callback_consumption },
    { name := "consistent_suspension_registers_callback"
      , property := .trans consistent_suspension_registers_callback },
    { name := "consistent_task_birth_couples_promise_birth"
      , property := .trans consistent_task_birth_couples_promise_birth },
    { name := "monotone_outbox_keys_never_disappear"
      , property := .trans monotone_outbox_keys_never_disappear },
    { name := "consistent_new_execute_matches_task_and_target"
      , property := .trans consistent_new_execute_matches_task_and_target },
    { name := "consistent_new_unblock_carries_stored_record"
      , property := .trans consistent_new_unblock_carries_stored_record },
    { name := "consistent_new_unblock_discharges_its_listener"
      , property := .trans consistent_new_unblock_discharges_its_listener },
    { name := "preserved_schedule_birth_fields_immutable"
      , property := .trans preserved_schedule_birth_fields_immutable },
    { name := "consistent_task_birth_state"
      , property := .trans consistent_task_birth_state },
    { name := "consistent_task_lease_released_atomically"
      , property := .trans consistent_task_lease_released_atomically },
    { name := "preserved_task_lease_holder_stable"
      , property := .trans preserved_task_lease_holder_stable },
    { name := "consistent_task_lease_fields_move_together"
      , property := .trans consistent_task_lease_fields_move_together },
    { name := "monotone_task_resumes_grow_or_clear"
      , property := .trans monotone_task_resumes_grow_or_clear },
    { name := "consistent_task_resumes_cleared_only_on_dispatch_or_park"
      , property := .trans consistent_task_resumes_cleared_only_on_dispatch_or_park },
    { name := "preserved_no_dead_dispatch"
      , property := .trans preserved_no_dead_dispatch },
    { name := "preserved_execute_only_for_live_task"
      , property := .trans preserved_execute_only_for_live_task },
    { name := "consistent_promise_settlement_stamp"
      , property := .trans consistent_promise_settlement_stamp },
    { name := "preserved_timedout_is_server_owned"
      , property := .trans preserved_timedout_is_server_owned },
    { name := "consistent_new_promise_born_clean"
      , property := .trans consistent_new_promise_born_clean },
    { name := "consistent_task_acquisition_is_atomic"
      , property := .trans consistent_task_acquisition_is_atomic },
    { name := "consistent_task_lease_deadline_is_now_plus_ttl"
      , property := .trans consistent_task_lease_deadline_is_now_plus_ttl },
    { name := "consistent_task_pending_entry_arms_retry"
      , property := .trans consistent_task_pending_entry_arms_retry },
    { name := "consistent_task_retry_rearm_only_when_due"
      , property := .trans consistent_task_retry_rearm_only_when_due },
    { name := "monotone_task_retry_rearm_advances"
      , property := .trans monotone_task_retry_rearm_advances },
    { name := "consistent_task_wake_records_resume"
      , property := .trans consistent_task_wake_records_resume } ]

def legalAt (now : Nat) (a b : ServerState) : Bool :=
  catalogue.all fun l =>
    match l.property with
    | .state f => f now a
    | .trans f => f now a b

def stateHolds (now : Nat) (s : ServerState) : Bool :=
  catalogue.all fun l =>
    match l.property with
    | .state f => f now s
    | .trans _ => true

def stateCount : Nat := (catalogue.filter (fun l => match l.property with | .state _ => true | _ => false)).length
def transCount : Nat := (catalogue.filter (fun l => match l.property with | .trans _ => true | _ => false)).length

def well_formed_task_ttl_positive (_now : Nat) (s : ServerState) : Bool :=
  s.tasks.all fun t => t.state != .acquired || 0 < t.ttl.getD 0

def well_formed_promise_target_is_nonempty (_now : Nat) (s : ServerState) : Bool :=
  s.promises.all fun p =>
    match p.type with
    | .runnable target => !target.isEmpty
    | _                => true

def well_formed_promise_delay_before_deadline (_now : Nat) (s : ServerState) : Bool :=
  s.objects.all fun o =>
    match o.task with
    | some { state := .pending, version := 0, retryTimeoutAt := some due, .. } =>
        due < o.promise.timeoutAt
    | _ => true

def well_formed_config_retry_positive (c : ServerConfig) : Bool :=
  0 < c.retryTimeout

def gaps : List Named :=
  [ { name := "well_formed_task_ttl_positive"
      , property := .state well_formed_task_ttl_positive },
    { name := "well_formed_promise_target_is_nonempty"
      , property := .state well_formed_promise_target_is_nonempty },
    { name := "well_formed_promise_delay_before_deadline"
      , property := .state well_formed_promise_delay_before_deadline } ]

theorem well_formed_promise_record_hides_callbacks
    (p : PromiseObject) (a id : Ident) :
    (p.addCallback a).toRecord id = p.toRecord id := by
  unfold PromiseObject.addCallback
  split <;> rfl

theorem well_formed_promise_record_hides_listeners
    (p : PromiseObject) (a : String) (id : Ident) :
    (p.addListener a).toRecord id = p.toRecord id := by
  unfold PromiseObject.addListener
  split <;> rfl

theorem well_formed_task_record_hides_deadlines
    (t : TaskObject) (e r : Option Nat) (id : Ident) :
    ({ t with leaseTimeoutAt := e, retryTimeoutAt := r } : TaskObject).toRecord id
      = t.toRecord id := rfl

theorem well_formed_task_record_resumes_is_a_count (t : TaskObject) (id : Ident) :
    (t.toRecord id).resumes = t.resumes.length := rfl

end Properties
end AbstractModel
