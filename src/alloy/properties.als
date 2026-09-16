module properties

-- The catalogue's state properties, as in
-- `src/spec/02-abstract/properties.lean`: one predicate per Lean property,
-- same name, same shape, `now` as argument and the state the current
-- instant's; the transition properties relate the current instant to the
-- next.

open types
open state

-- well formed: promises

pred well_formed_promise_created_at_lte_timeout_at [now : Int] {
  all p : storedPromises | p.createdAt <= p.timeoutAt
}

pred well_formed_promise_pending_created_before_deadline [now : Int] {
  all p : storedPromises | p.state != Pending or p.createdAt < p.timeoutAt
}

pred well_formed_promise_settled_at_lte_timeout_at [now : Int] {
  all p : storedPromises | all x : p.settledAt | x <= p.timeoutAt
}

pred well_formed_promise_created_at_lte_settled_at [now : Int] {
  all p : storedPromises | all x : p.settledAt | p.createdAt <= x
}

pred well_formed_promise_settled_at_iff_not_pending [now : Int] {
  all p : storedPromises | (p.state != Pending) iff (some p.settledAt)
}

pred well_formed_promise_pending_has_no_value [now : Int] {
  all p : storedPromises | p.state != Pending or emptyValue[p.value]
}

pred well_formed_promise_deadline_verdict_matches_timer_tag [now : Int] {
  all p : storedPromises |
    p.settledAt != p.timeoutAt
      or p.state = (p.type = Deadline implies Resolved else RejectedTimedout)
}

pred well_formed_promise_deadline_settlement_has_no_value [now : Int] {
  all p : storedPromises | p.settledAt != p.timeoutAt or emptyValue[p.value]
}

pred well_formed_promise_timedout_is_server_owned [now : Int] {
  all p : storedPromises | p.state != RejectedTimedout or p.settledAt = p.timeoutAt
}

-- Callbacks are a set: duplicate free by construction.
pred well_formed_promise_callbacks_unique [now : Int] {
  all p : storedPromises | p.callbacks in Ident
}

-- Listeners are a set: duplicate free by construction.
pred well_formed_promise_listeners_unique [now : Int] {
  all p : storedPromises | p.listeners in Str
}

pred well_formed_promise_obligations_require_external [now : Int] {
  all p : storedPromises | (no p.callbacks and no p.listeners) or p.type in awaitable
}

pred well_formed_promise_awaiter_is_not_self [now : Int] {
  all o : State.objects | o.id not in o.promise.callbacks
}

pred well_formed_promise_callbacks_same_origin [now : Int] {
  all o : State.objects | all a : o.promise.callbacks | sameOrigin[a, o.id]
}

pred well_formed_promise_created_at_lte_now [now : Int] {
  all p : storedPromises | p.createdAt <= now
}

pred well_formed_promise_settled_at_lte_now [now : Int] {
  all p : storedPromises | all x : p.settledAt | x <= now
}

-- well formed: tasks

pred well_formed_task_acquired_iff_has_pid [now : Int] {
  all t : storedTasks | (t.state = Acquired) iff (some t.pid)
}

pred well_formed_task_acquired_iff_has_ttl [now : Int] {
  all t : storedTasks | (t.state = Acquired) iff (some t.ttl)
}

pred well_formed_task_acquired_iff_has_lease_timeout_at [now : Int] {
  all t : storedTasks | (t.state = Acquired) iff (some t.leaseTimeoutAt)
}

pred well_formed_task_pending_iff_has_retry_timeout_at [now : Int] {
  all t : storedTasks | (t.state = TaskPending) iff (some t.retryTimeoutAt)
}

pred well_formed_task_fulfilled_is_cleared [now : Int] {
  all t : storedTasks |
    t.state != Fulfilled
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt
          and no t.resumes)
}

pred well_formed_task_suspended_is_cleared [now : Int] {
  all t : storedTasks |
    t.state != Suspended
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt)
}

pred well_formed_task_halted_is_cleared [now : Int] {
  all t : storedTasks |
    t.state != Halted
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt)
}

pred well_formed_task_suspended_has_no_resumes [now : Int] {
  all t : storedTasks | t.state != Suspended or no t.resumes
}

-- Resumes are a set: duplicate free by construction.
pred well_formed_task_resumes_unique [now : Int] {
  all t : storedTasks | t.resumes in Ident
}

pred well_formed_task_acquired_version_positive [now : Int] {
  all t : storedTasks | t.state != Acquired or 1 <= t.version
}

-- well formed: schedules

pred well_formed_schedule_created_at_lte_next_run_at [now : Int] {
  all c : State.schedules | c.createdAt <= c.nextRunAt
}

pred well_formed_schedule_created_at_lte_last_run_at [now : Int] {
  all c : State.schedules | all l : c.lastRunAt | c.createdAt <= l
}

pred well_formed_schedule_last_run_at_lt_next_run_at [now : Int] {
  all c : State.schedules | all l : c.lastRunAt | l < c.nextRunAt
}

-- well formed: the store

pred well_formed_store_object_ids_unique [now : Int] {
  all disj a, b : State.objects | a.id != b.id
}

pred well_formed_store_schedule_ids_unique [now : Int] {
  all disj a, b : State.schedules | a.id != b.id
}

pred well_formed_store_outbox_keys_unique [now : Int] {
  all disj a, b : State.outbox | not sameKey[a, b]
}

-- consistent

pred consistent_task_iff_kind_task [now : Int] {
  all o : State.objects | (some o.task) iff (o.promise.type in isRunnable)
}

pred consistent_settled_promise_has_fulfilled_task [now : Int] {
  all o : State.objects | o.promise.state = Pending or o.task.state in Fulfilled
}

pred consistent_callback_awaiter_is_targeted [now : Int] {
  all p : storedPromises | all a : p.callbacks |
    some q : State.objects | q.id = a and q.promise.type in isRunnable
}

pred consistent_outbox_execute_names_existing_task [now : Int] {
  all e : State.outbox | e.message in Execute implies hasTask[e.message.taskId]
}

pred consistent_outbox_never_ahead [now : Int] {
  all e : State.outbox | e.message in Execute implies
    all t : task[e.message.taskId] | e.message.version <= t.version
}

pred consistent_outbox_execute_address_is_target_tag [now : Int] {
  all e : State.outbox | e.message in Execute implies
    all p : promise[e.message.taskId] |
      e.address = (p.type in isRunnable implies targetOf[p.type] else EmptyStr)
}

pred consistent_outbox_unblock_names_settled_promise [now : Int] {
  all e : State.outbox | e.message in Unblock implies
    let r = e.message.promise |
      r.state != Pending
        and some o : State.objects | o.id = r.id and o.promise.state != Pending
}

pred consistent_suspended_task_holds_rung [now : Int] {
  all o : State.objects | all t : o.task |
    t.state != Suspended
      or projectedState[o.promise, now] != Pending
      or some p : storedPromises | o.id in p.callbacks
}

pred consistent_settled_task_promise_settled [now : Int] {
  all o : State.objects | all t : o.task |
    t.state != Fulfilled or o.promise.state != Pending
}

-- `stateHolds`: every state property of the catalogue.

pred stateHolds [now : Int] {
  well_formed_promise_created_at_lte_timeout_at[now]
  well_formed_promise_pending_created_before_deadline[now]
  well_formed_promise_settled_at_lte_timeout_at[now]
  well_formed_promise_created_at_lte_settled_at[now]
  well_formed_promise_settled_at_iff_not_pending[now]
  well_formed_promise_pending_has_no_value[now]
  well_formed_promise_deadline_verdict_matches_timer_tag[now]
  well_formed_promise_deadline_settlement_has_no_value[now]
  well_formed_promise_timedout_is_server_owned[now]
  well_formed_promise_callbacks_unique[now]
  well_formed_promise_listeners_unique[now]
  well_formed_promise_obligations_require_external[now]
  well_formed_promise_awaiter_is_not_self[now]
  well_formed_promise_callbacks_same_origin[now]
  well_formed_promise_created_at_lte_now[now]
  well_formed_promise_settled_at_lte_now[now]
  well_formed_task_acquired_iff_has_pid[now]
  well_formed_task_acquired_iff_has_ttl[now]
  well_formed_task_acquired_iff_has_lease_timeout_at[now]
  well_formed_task_pending_iff_has_retry_timeout_at[now]
  well_formed_task_fulfilled_is_cleared[now]
  well_formed_task_suspended_is_cleared[now]
  well_formed_task_halted_is_cleared[now]
  well_formed_task_suspended_has_no_resumes[now]
  well_formed_task_resumes_unique[now]
  well_formed_task_acquired_version_positive[now]
  well_formed_schedule_created_at_lte_next_run_at[now]
  well_formed_schedule_created_at_lte_last_run_at[now]
  well_formed_schedule_last_run_at_lt_next_run_at[now]
  well_formed_store_object_ids_unique[now]
  well_formed_store_schedule_ids_unique[now]
  well_formed_store_outbox_keys_unique[now]
  consistent_task_iff_kind_task[now]
  consistent_settled_promise_has_fulfilled_task[now]
  consistent_callback_awaiter_is_targeted[now]
  consistent_outbox_execute_names_existing_task[now]
  consistent_outbox_never_ahead[now]
  consistent_outbox_execute_address_is_target_tag[now]
  consistent_outbox_unblock_names_settled_promise[now]
  consistent_settled_task_promise_settled[now]
  consistent_suspended_task_holds_rung[now]
}

-- `gaps`: stated, not in the catalogue.

pred well_formed_task_ttl_positive [now : Int] {
  all t : storedTasks | t.state != Acquired or (some t.ttl and 0 < t.ttl)
}

pred well_formed_promise_target_is_nonempty [now : Int] {
  all p : storedPromises | p.type in isRunnable implies targetOf[p.type] != EmptyStr
}

pred well_formed_promise_delay_before_deadline [now : Int] {
  all o : State.objects | all t : o.task |
    (t.state = TaskPending and t.version = 0 and some t.retryTimeoutAt)
      implies t.retryTimeoutAt < o.promise.timeoutAt
}

pred well_formed_config_retry_positive { 0 < ServerConfig.retryTimeout }

pred gapsHold [now : Int] {
  well_formed_task_ttl_positive[now]
  well_formed_promise_target_is_nonempty[now]
  well_formed_promise_delay_before_deadline[now]
  well_formed_config_retry_positive
}

-- Transitions. One predicate per Lean transition property, `f now a b`
-- with `a` the current instant and `b` the next: a lookup on the next
-- instant is the primed lookup, `(promise[i])'`. Where the Lean matches
-- `none` on the next instant's lookup, the empty lookup is quantified
-- over, so `none => true` is `all q : (promise[i])'` and `none => false`
-- adds `some (promise[i])'`.

fun ttlOr0 [t : TaskObject] : one Int { some t.ttl implies t.ttl else 0 }

fun promiseEdges : PromiseState -> PromiseState {
  (Pending -> Pending) + (Pending -> Resolved) + (Pending -> Rejected) +
  (Pending -> RejectedCanceled) + (Pending -> RejectedTimedout) +
  (Resolved -> Resolved) + (Rejected -> Rejected) +
  (RejectedCanceled -> RejectedCanceled) + (RejectedTimedout -> RejectedTimedout)
}

fun taskEdges : TaskState -> TaskState {
  (TaskPending -> TaskPending) + (TaskPending -> Acquired) + (TaskPending -> Halted) +
  (TaskPending -> Fulfilled) + (Acquired -> TaskPending) + (Acquired -> Acquired) +
  (Acquired -> Suspended) + (Acquired -> Halted) + (Acquired -> Fulfilled) +
  (Suspended -> TaskPending) + (Suspended -> Suspended) + (Suspended -> Halted) +
  (Suspended -> Fulfilled) + (Halted -> TaskPending) + (Halted -> Halted) +
  (Halted -> Fulfilled) + (Fulfilled -> Fulfilled)
}

fun internalTaskEdges : TaskState -> TaskState {
  (TaskPending -> TaskPending) + (TaskPending -> Fulfilled) + (Acquired -> TaskPending) +
  (Acquired -> Acquired) + (Acquired -> Fulfilled) + (Suspended -> TaskPending) +
  (Suspended -> Suspended) + (Suspended -> Fulfilled) + (Halted -> Halted) +
  (Halted -> Fulfilled) + (Fulfilled -> Fulfilled)
}

pred preserved_promise_birth_fields_immutable [now : Int] {
  all o : State.objects | let p = o.promise | all q : (promise[o.id])' |
    q.param = p.param and q.type = p.type and q.timeoutAt = p.timeoutAt and
    q.createdAt = p.createdAt
}

pred preserved_settled_promise_record [now : Int] {
  all o : State.objects | let p = o.promise |
    p.state = Pending or
    (some (promise[o.id])' and all q : (promise[o.id])' |
      q.state = p.state and q.settledAt = p.settledAt and q.value = p.value)
}

pred monotone_promise_set_grows [now : Int] {
  all o : State.objects | some (object[o.id])'
}

pred monotone_task_set_grows [now : Int] {
  all o : State.objects | no o.task or some (task[o.id])'
}

pred monotone_task_version_increases_only_on_acquisition [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    (t.state = TaskPending and u.state = Acquired)
      implies u.version = plus[t.version, 1]
      else u.version = t.version
}

pred preserved_fulfilled_task [now : Int] {
  all o : State.objects | all t : o.task |
    t.state != Fulfilled or
    (some (task[o.id])' and all u : (task[o.id])' |
      u.state = Fulfilled and u.version = t.version and no u.resumes and
      no u.pid and no u.ttl and no u.leaseTimeoutAt and no u.retryTimeoutAt)
}

pred preserved_no_dead_dispatch [now : Int] {
  all o : State.objects' | all u : o.task |
    u.state != TaskPending
    or (some task[o.id] and all t : task[o.id] | t.state = TaskPending)
    or (all p : (promise[o.id])' | projectedState[p, now] = Pending)
}

pred preserved_execute_only_for_live_task [now : Int] {
  all e : State.outbox' | e.message in Execute implies
    (e in State.outbox
     or (all p : (promise[e.message.taskId])' | projectedState[p, now] = Pending))
}

pred preserved_promise_state_frozen_once_settled [now : Int] {
  all o : State.objects | let p = o.promise |
    p.state = Pending or
    (some (promise[o.id])' and all q : (promise[o.id])' | q.state = p.state)
}

pred preserved_promise_settlement_is_one_way [now : Int] {
  all o : State.objects' | o.promise.state != Pending or
    (all p : promise[o.id] | p.state = Pending)
}

pred consistent_promise_settled_at_moves_with_state [now : Int] {
  all o : State.objects | let p = o.promise |
    some (promise[o.id])' and all q : (promise[o.id])' |
      (q.settledAt != p.settledAt) iff (q.state != p.state)
}

pred preserved_promise_value_until_settlement [now : Int] {
  all o : State.objects | let p = o.promise |
    some (promise[o.id])' and all q : (promise[o.id])' |
      q.state != Pending or q.value = p.value
}

pred preserved_promise_no_duplicate_ids [now : Int] {
  all disj a, b : State.objects' | a.id != b.id
}

pred monotone_promise_callbacks_grow_while_pending [now : Int] {
  all o : State.objects' | let q = o.promise |
    q.state != Pending or
    (no promise[o.id] implies no q.callbacks
     else all p : promise[o.id] | p.callbacks in q.callbacks)
}

pred monotone_promise_callbacks_shrink_once_settled [now : Int] {
  all o : State.objects' | let q = o.promise |
    q.state = Pending or
    (no promise[o.id] implies no q.callbacks
     else all p : promise[o.id] | q.callbacks in p.callbacks)
}

pred monotone_promise_listeners_grow_while_pending [now : Int] {
  all o : State.objects' | let q = o.promise |
    q.state != Pending or
    (no promise[o.id] implies no q.listeners
     else all p : promise[o.id] | p.listeners in q.listeners)
}

pred monotone_promise_listeners_shrink_once_settled [now : Int] {
  all o : State.objects' | let q = o.promise |
    q.state = Pending or
    (no promise[o.id] implies no q.listeners
     else all p : promise[o.id] | q.listeners in p.listeners)
}

pred consistent_promise_state_edge_admissible [now : Int] {
  all o : State.objects | let p = o.promise | all q : (promise[o.id])' |
    p.state -> q.state in promiseEdges
}

pred consistent_task_state_edge_admissible [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    t.state -> u.state in taskEdges
}

pred preserved_task_acquisition_only_from_pending [now : Int] {
  all o : State.objects' | all u : o.task |
    u.state != Acquired or (all t : task[o.id] | t.state in TaskPending + Acquired)
}

pred preserved_task_suspension_only_from_acquired [now : Int] {
  all o : State.objects' | all u : o.task |
    u.state != Suspended or
    (some task[o.id] and all t : task[o.id] | t.state in Acquired + Suspended)
}

pred preserved_task_halted_only_reenters_via_pending [now : Int] {
  all o : State.objects | all t : o.task |
    t.state != Halted or
    (some (task[o.id])' and all u : (task[o.id])' | u.state in Halted + TaskPending + Fulfilled)
}

pred consistent_settlement_fulfils_task [now : Int] {
  all o : State.objects | let p = o.promise |
    p.state != Pending or
    (all q : (promise[o.id])', u : (task[o.id])' | q.state = Pending or u.state = Fulfilled)
}

pred consistent_task_fulfilment_needs_settlement [now : Int] {
  all o : State.objects' | all u : o.task |
    u.state != Fulfilled or
    (all t : task[o.id] |
      t.state = Fulfilled or
      (some promise[o.id] and some (promise[o.id])' and
       all p : promise[o.id], q : (promise[o.id])' | p.state = Pending and q.state != Pending))
}

pred consistent_obligation_discharge_requires_settled [now : Int] {
  all o : State.objects | let p = o.promise | all q : (promise[o.id])' |
    (p.callbacks in q.callbacks and p.listeners in q.listeners) or q.state != Pending
}

pred consistent_callback_consumption_resumes_awaiter [now : Int] {
  all o : State.objects | let p = o.promise | all x : p.callbacks |
    (all q : (promise[o.id])' | x in q.callbacks)
    or (all u : (task[x])' | u.state = Fulfilled or o.id in u.resumes)
}

pred consistent_listener_consumption_enqueues_unblock [now : Int] {
  all o : State.objects | let p = o.promise | all addr : p.listeners |
    (all q : (promise[o.id])' | addr in q.listeners)
    or one { e : State.outbox' | e.address = addr and e.message in Unblock and
             e.message.promise.id = o.id and e.message.promise.state != Pending }
}

pred consistent_wake_follows_callback_consumption [now : Int] {
  all o : State.objects' | all u : o.task | all t : task[o.id] |
    not (t.state = Suspended and u.state = TaskPending)
    or some p : State.objects |
         o.id in p.promise.callbacks and
         (some (promise[p.id])' and all q : (promise[p.id])' | o.id not in q.callbacks) and
         p.id in u.resumes
}

pred consistent_suspension_registers_callback [now : Int] {
  all o : State.objects' | all u : o.task |
    u.state != Suspended
    or (some task[o.id] and all t : task[o.id] | t.state = Suspended)
    or some q : State.objects' |
         o.id in q.promise.callbacks and
         (all p : promise[q.id] | o.id not in p.callbacks) and
         q.promise.state = Pending
}

pred consistent_task_birth_couples_promise_birth [now : Int] {
  all o : State.objects' | all u : o.task |
    hasTask[o.id]
    or (no object[o.id]
        and (let q = o.promise |
               q.type in isRunnable and
               (u.state = Fulfilled implies q.state != Pending else q.state = Pending))
        and ((u.state = TaskPending and u.version = 0)
             or (u.state = Acquired and 1 <= u.version)
             or (u.state = Fulfilled and u.version = 0)))
  all o : State.objects' |
    some object[o.id] or o.promise.type not in isRunnable or some o.task
}

pred monotone_outbox_keys_never_disappear [now : Int] {
  all e : State.outbox | some f : State.outbox' | sameKey[e, f]
}

pred consistent_new_execute_matches_task_and_target [now : Int] {
  all f : State.outbox' | f.message in Execute implies
    (f in State.outbox
     or (let i = f.message.taskId |
          (some (task[i])' and all t : (task[i])' | t.version = f.message.version)
          and (some (promise[i])' and all p : (promise[i])' |
                 f.address = (p.type in isRunnable implies targetOf[p.type] else EmptyStr))))
}

pred consistent_new_unblock_carries_stored_record [now : Int] {
  all f : State.outbox' | f.message in Unblock implies
    (let r = f.message.promise |
      (some e : State.outbox |
         e.message in Unblock and e.address = f.address and e.message.promise.id = r.id)
      or (r.state != Pending and
          some (promise[r.id])' and all p : (promise[r.id])' |
            p.state = r.state and p.settledAt = r.settledAt and
            p.value.data = r.value.data and p.timeoutAt = r.timeoutAt and
            p.createdAt = r.createdAt))
}

pred consistent_new_unblock_discharges_its_listener [now : Int] {
  all f : State.outbox' | f.message in Unblock implies
    (let r = f.message.promise |
      (some e : State.outbox |
         e.message in Unblock and e.address = f.address and e.message.promise.id = r.id)
      or ((some o : State.objects | o.id = r.id and f.address in o.promise.listeners)
          and (all o : State.objects' | o.id != r.id or f.address not in o.promise.listeners)))
}

pred preserved_schedule_birth_fields_immutable [now : Int] {
  all c : State.schedules | all d : (schedule[c.id])' |
    d.cron = c.cron and d.promiseId = c.promiseId and d.promiseTimeout = c.promiseTimeout and
    d.promiseParam = c.promiseParam and d.promiseType = c.promiseType and
    d.createdAt = c.createdAt
}

pred consistent_task_birth_state [now : Int] {
  all o : State.objects' | all u : o.task |
    hasTask[o.id]
    or (u.state = TaskPending and some u.retryTimeoutAt and no u.pid and no u.ttl and
        no u.leaseTimeoutAt and no u.resumes)
    or (u.state = Fulfilled and no u.retryTimeoutAt and no u.pid and no u.ttl and
        no u.leaseTimeoutAt and no u.resumes)
    or (u.state = Acquired and 1 <= u.version and no u.retryTimeoutAt and some u.pid and
        some u.ttl and some u.leaseTimeoutAt and no u.resumes)
}

pred consistent_task_lease_released_atomically [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state = Acquired and u.state != Acquired)
    or (no u.pid and no u.ttl and no u.leaseTimeoutAt and u.version = t.version)
}

pred preserved_task_lease_holder_stable [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state = Acquired and u.state = Acquired and u.version = t.version)
    or (u.pid = t.pid and u.ttl = t.ttl)
}

pred consistent_task_lease_fields_move_together [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    (u.pid = t.pid and u.ttl = t.ttl and u.leaseTimeoutAt = t.leaseTimeoutAt)
    or (t.state != Acquired and u.state = Acquired and
        some u.pid and some u.ttl and some u.leaseTimeoutAt)
    or (t.state = Acquired and u.state != Acquired and
        no u.pid and no u.ttl and no u.leaseTimeoutAt)
    or (t.state = Acquired and u.state = Acquired and u.pid = t.pid and u.ttl = t.ttl)
}

pred monotone_task_resumes_grow_or_clear [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    no u.resumes or t.resumes in u.resumes
}

pred consistent_task_resumes_cleared_only_on_dispatch_or_park [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (some t.resumes and no u.resumes) or u.state in Acquired + Suspended + Fulfilled
}

pred consistent_task_acquisition_is_atomic [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state != Acquired and u.state = Acquired)
    or (t.state = TaskPending and t.version < u.version and some u.pid and some u.ttl and
        u.leaseTimeoutAt = plus[now, ttlOr0[u]] and no u.retryTimeoutAt and no u.resumes)
}

pred consistent_task_lease_deadline_is_now_plus_ttl [now : Int] {
  all o : State.objects' | all u : o.task | all d : u.leaseTimeoutAt |
    d = plus[now, ttlOr0[u]]
    or (some task[o.id] and all t : task[o.id] |
          t.leaseTimeoutAt = d and t.ttl = u.ttl and t.state = u.state)
}

pred consistent_task_pending_entry_arms_retry [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state != TaskPending and u.state = TaskPending) or u.retryTimeoutAt = now
}

pred consistent_task_retry_rearm_only_when_due [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state = TaskPending and u.state = TaskPending and
         u.retryTimeoutAt != t.retryTimeoutAt)
    or (some t.retryTimeoutAt and t.retryTimeoutAt <= now)
}

pred consistent_task_wake_records_resume [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    not (t.state = Suspended and u.state = TaskPending)
    or (some u.resumes and u.retryTimeoutAt = now and u.version = t.version)
}

pred consistent_task_state_edge_internal_admissible [now : Int] {
  all o : State.objects | all t : o.task | all u : (task[o.id])' |
    t.state -> u.state in internalTaskEdges
}

pred consistent_promise_state_edge_internal_admissible [now : Int] {
  all o : State.objects | let p = o.promise | all q : (promise[o.id])' |
    p.state = q.state or
    (p.state = Pending and
     (q.state = RejectedTimedout or (q.state = Resolved and p.type = Deadline)))
}

pred consistent_promise_settlement_stamp [now : Int] {
  all o : State.objects | let p = o.promise |
    p.state != Pending or
    (some (promise[o.id])' and all q : (promise[o.id])' |
      q.state = Pending
      or (q.settledAt = now and now < q.timeoutAt and q.state != RejectedTimedout)
      or (q.settledAt = q.timeoutAt and q.timeoutAt <= now and
          q.state = (q.type = Deadline implies Resolved else RejectedTimedout) and
          q.value = p.value))
}

pred preserved_timedout_is_server_owned [now : Int] {
  all o : State.objects | let p = o.promise |
    p.state != Pending or
    (all q : (promise[o.id])' |
      q.state != RejectedTimedout or (p.timeoutAt <= now and q.settledAt = p.timeoutAt))
}

pred consistent_new_promise_born_clean [now : Int] {
  all o : State.objects' | let q = o.promise |
    some object[o.id]
    or (no q.callbacks and no q.listeners and emptyValue[q.value] and q.createdAt <= now
        and ((q.state = Pending and no q.settledAt and q.createdAt < q.timeoutAt)
             or (q.settledAt = q.timeoutAt and q.createdAt = q.timeoutAt and
                 q.timeoutAt <= now and
                 q.state = (q.type = Deadline implies Resolved else RejectedTimedout))))
}

pred monotone_task_retry_rearm_advances [now : Int] {
  all o : State.objects | all t : o.task |
    t.state != TaskPending or
    (all u : (task[o.id])' |
      u.state != TaskPending or u.retryTimeoutAt = t.retryTimeoutAt or
      (some u.retryTimeoutAt and now < u.retryTimeoutAt))
}

-- `transHolds`: every transition property of the catalogue, from the
-- current instant to the next. `internalWellFormed`: the two the Lean
-- checks on internal steps only. `legalAt`: the catalogue on a step.

pred transHolds [now : Int] {
  preserved_promise_birth_fields_immutable[now]
  preserved_settled_promise_record[now]
  monotone_promise_set_grows[now]
  monotone_task_set_grows[now]
  monotone_task_version_increases_only_on_acquisition[now]
  preserved_fulfilled_task[now]
  preserved_promise_state_frozen_once_settled[now]
  preserved_promise_settlement_is_one_way[now]
  consistent_promise_settled_at_moves_with_state[now]
  preserved_promise_value_until_settlement[now]
  preserved_promise_no_duplicate_ids[now]
  monotone_promise_callbacks_grow_while_pending[now]
  monotone_promise_callbacks_shrink_once_settled[now]
  monotone_promise_listeners_grow_while_pending[now]
  monotone_promise_listeners_shrink_once_settled[now]
  consistent_promise_state_edge_admissible[now]
  consistent_task_state_edge_admissible[now]
  preserved_task_acquisition_only_from_pending[now]
  preserved_task_suspension_only_from_acquired[now]
  preserved_task_halted_only_reenters_via_pending[now]
  consistent_settlement_fulfils_task[now]
  consistent_task_fulfilment_needs_settlement[now]
  consistent_obligation_discharge_requires_settled[now]
  consistent_callback_consumption_resumes_awaiter[now]
  consistent_listener_consumption_enqueues_unblock[now]
  consistent_wake_follows_callback_consumption[now]
  consistent_suspension_registers_callback[now]
  consistent_task_birth_couples_promise_birth[now]
  monotone_outbox_keys_never_disappear[now]
  consistent_new_execute_matches_task_and_target[now]
  consistent_new_unblock_carries_stored_record[now]
  consistent_new_unblock_discharges_its_listener[now]
  preserved_schedule_birth_fields_immutable[now]
  consistent_task_birth_state[now]
  consistent_task_lease_released_atomically[now]
  preserved_task_lease_holder_stable[now]
  consistent_task_lease_fields_move_together[now]
  monotone_task_resumes_grow_or_clear[now]
  consistent_task_resumes_cleared_only_on_dispatch_or_park[now]
  preserved_no_dead_dispatch[now]
  preserved_execute_only_for_live_task[now]
  consistent_promise_settlement_stamp[now]
  preserved_timedout_is_server_owned[now]
  consistent_new_promise_born_clean[now]
  consistent_task_acquisition_is_atomic[now]
  consistent_task_lease_deadline_is_now_plus_ttl[now]
  consistent_task_pending_entry_arms_retry[now]
  consistent_task_retry_rearm_only_when_due[now]
  monotone_task_retry_rearm_advances[now]
}

pred internalWellFormed [now : Int] {
  consistent_task_state_edge_internal_admissible[now]
  consistent_promise_state_edge_internal_admissible[now]
}

pred legalAt [now : Int] { stateHolds[now] and transHolds[now] }
