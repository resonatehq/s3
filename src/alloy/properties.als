module properties

-- The catalogue's state properties, as in
-- `src/spec/02-abstract/properties.lean`: one predicate per Lean property,
-- same name, same shape, `now` and the state as arguments. The schedule
-- properties are left out with the schedules. The transition properties
-- come with the transitions.

open types
open state

-- well formed: promises

pred well_formed_promise_created_at_lte_timeout_at [now : Int, s : State] {
  all p : promises[s] | p.createdAt <= p.timeoutAt
}

pred well_formed_promise_pending_created_before_deadline [now : Int, s : State] {
  all p : promises[s] | p.state != Pending or p.createdAt < p.timeoutAt
}

pred well_formed_promise_settled_at_lte_timeout_at [now : Int, s : State] {
  all p : promises[s] | all x : p.settledAt | x <= p.timeoutAt
}

pred well_formed_promise_created_at_lte_settled_at [now : Int, s : State] {
  all p : promises[s] | all x : p.settledAt | p.createdAt <= x
}

pred well_formed_promise_settled_at_iff_not_pending [now : Int, s : State] {
  all p : promises[s] | (p.state != Pending) iff (some p.settledAt)
}

pred well_formed_promise_pending_has_no_value [now : Int, s : State] {
  all p : promises[s] | p.state != Pending or emptyValue[p.value]
}

pred well_formed_promise_deadline_verdict_matches_timer_tag [now : Int, s : State] {
  all p : promises[s] |
    p.settledAt != p.timeoutAt
      or p.state = (p.type = Deadline implies Resolved else RejectedTimedout)
}

pred well_formed_promise_deadline_settlement_has_no_value [now : Int, s : State] {
  all p : promises[s] | p.settledAt != p.timeoutAt or emptyValue[p.value]
}

pred well_formed_promise_timedout_is_server_owned [now : Int, s : State] {
  all p : promises[s] | p.state != RejectedTimedout or p.settledAt = p.timeoutAt
}

-- Callbacks are a set: duplicate free by construction.
pred well_formed_promise_callbacks_unique [now : Int, s : State] {
  all p : promises[s] | p.callbacks in Ident
}

-- Listeners are a set: duplicate free by construction.
pred well_formed_promise_listeners_unique [now : Int, s : State] {
  all p : promises[s] | p.listeners in Str
}

pred well_formed_promise_obligations_require_external [now : Int, s : State] {
  all p : promises[s] | (no p.callbacks and no p.listeners) or p.type in awaitable
}

pred well_formed_promise_awaiter_is_not_self [now : Int, s : State] {
  all o : s.objects | o.id not in o.promise.callbacks
}

pred well_formed_promise_callbacks_same_origin [now : Int, s : State] {
  all o : s.objects | all a : o.promise.callbacks | sameOrigin[a, o.id]
}

pred well_formed_promise_created_at_lte_now [now : Int, s : State] {
  all p : promises[s] | p.createdAt <= now
}

pred well_formed_promise_settled_at_lte_now [now : Int, s : State] {
  all p : promises[s] | all x : p.settledAt | x <= now
}

-- well formed: tasks

pred well_formed_task_acquired_iff_has_pid [now : Int, s : State] {
  all t : tasks[s] | (t.state = Acquired) iff (some t.pid)
}

pred well_formed_task_acquired_iff_has_ttl [now : Int, s : State] {
  all t : tasks[s] | (t.state = Acquired) iff (some t.ttl)
}

pred well_formed_task_acquired_iff_has_lease_timeout_at [now : Int, s : State] {
  all t : tasks[s] | (t.state = Acquired) iff (some t.leaseTimeoutAt)
}

pred well_formed_task_pending_iff_has_retry_timeout_at [now : Int, s : State] {
  all t : tasks[s] | (t.state = TaskPending) iff (some t.retryTimeoutAt)
}

pred well_formed_task_fulfilled_is_cleared [now : Int, s : State] {
  all t : tasks[s] |
    t.state != Fulfilled
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt
          and no t.resumes)
}

pred well_formed_task_suspended_is_cleared [now : Int, s : State] {
  all t : tasks[s] |
    t.state != Suspended
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt)
}

pred well_formed_task_halted_is_cleared [now : Int, s : State] {
  all t : tasks[s] |
    t.state != Halted
      or (no t.pid and no t.ttl and no t.leaseTimeoutAt and no t.retryTimeoutAt)
}

pred well_formed_task_suspended_has_no_resumes [now : Int, s : State] {
  all t : tasks[s] | t.state != Suspended or no t.resumes
}

-- Resumes are a set: duplicate free by construction.
pred well_formed_task_resumes_unique [now : Int, s : State] {
  all t : tasks[s] | t.resumes in Ident
}

pred well_formed_task_acquired_version_positive [now : Int, s : State] {
  all t : tasks[s] | t.state != Acquired or 1 <= t.version
}

-- well formed: the store

pred well_formed_store_object_ids_unique [now : Int, s : State] {
  all disj a, b : s.objects | a.id != b.id
}

pred well_formed_store_outbox_keys_unique [now : Int, s : State] {
  all disj a, b : s.outbox | not sameKey[a, b]
}

-- consistent

pred consistent_task_iff_kind_task [now : Int, s : State] {
  all o : s.objects | (some o.task) iff (o.promise.type in isRunnable)
}

pred consistent_settled_promise_has_fulfilled_task [now : Int, s : State] {
  all o : s.objects | o.promise.state = Pending or o.task.state in Fulfilled
}

pred consistent_callback_awaiter_is_targeted [now : Int, s : State] {
  all p : promises[s] | all a : p.callbacks |
    some q : s.objects | q.id = a and q.promise.type in isRunnable
}

pred consistent_outbox_execute_names_existing_task [now : Int, s : State] {
  all e : s.outbox | e.message in Execute implies hasTask[s, e.message.taskId]
}

pred consistent_outbox_never_ahead [now : Int, s : State] {
  all e : s.outbox | e.message in Execute implies
    all t : task[s, e.message.taskId] | e.message.version <= t.version
}

pred consistent_outbox_execute_address_is_target_tag [now : Int, s : State] {
  all e : s.outbox | e.message in Execute implies
    all p : promise[s, e.message.taskId] |
      e.address = (p.type in isRunnable implies targetOf[p.type] else EmptyStr)
}

pred consistent_outbox_unblock_names_settled_promise [now : Int, s : State] {
  all e : s.outbox | e.message in Unblock implies
    let r = e.message.promise |
      r.state != Pending
        and some o : s.objects | o.id = r.id and o.promise.state != Pending
}

pred consistent_suspended_task_holds_rung [now : Int, s : State] {
  all o : s.objects | all t : o.task |
    t.state != Suspended
      or projectedState[o.promise, now] != Pending
      or some p : promises[s] | o.id in p.callbacks
}

pred consistent_settled_task_promise_settled [now : Int, s : State] {
  all o : s.objects | all t : o.task |
    t.state != Fulfilled or o.promise.state != Pending
}

-- `stateHolds`: every state property of the catalogue.

pred stateHolds [now : Int, s : State] {
  well_formed_promise_created_at_lte_timeout_at[now, s]
  well_formed_promise_pending_created_before_deadline[now, s]
  well_formed_promise_settled_at_lte_timeout_at[now, s]
  well_formed_promise_created_at_lte_settled_at[now, s]
  well_formed_promise_settled_at_iff_not_pending[now, s]
  well_formed_promise_pending_has_no_value[now, s]
  well_formed_promise_deadline_verdict_matches_timer_tag[now, s]
  well_formed_promise_deadline_settlement_has_no_value[now, s]
  well_formed_promise_timedout_is_server_owned[now, s]
  well_formed_promise_callbacks_unique[now, s]
  well_formed_promise_listeners_unique[now, s]
  well_formed_promise_obligations_require_external[now, s]
  well_formed_promise_awaiter_is_not_self[now, s]
  well_formed_promise_callbacks_same_origin[now, s]
  well_formed_promise_created_at_lte_now[now, s]
  well_formed_promise_settled_at_lte_now[now, s]
  well_formed_task_acquired_iff_has_pid[now, s]
  well_formed_task_acquired_iff_has_ttl[now, s]
  well_formed_task_acquired_iff_has_lease_timeout_at[now, s]
  well_formed_task_pending_iff_has_retry_timeout_at[now, s]
  well_formed_task_fulfilled_is_cleared[now, s]
  well_formed_task_suspended_is_cleared[now, s]
  well_formed_task_halted_is_cleared[now, s]
  well_formed_task_suspended_has_no_resumes[now, s]
  well_formed_task_resumes_unique[now, s]
  well_formed_task_acquired_version_positive[now, s]
  well_formed_store_object_ids_unique[now, s]
  well_formed_store_outbox_keys_unique[now, s]
  consistent_task_iff_kind_task[now, s]
  consistent_settled_promise_has_fulfilled_task[now, s]
  consistent_callback_awaiter_is_targeted[now, s]
  consistent_outbox_execute_names_existing_task[now, s]
  consistent_outbox_never_ahead[now, s]
  consistent_outbox_execute_address_is_target_tag[now, s]
  consistent_outbox_unblock_names_settled_promise[now, s]
  consistent_settled_task_promise_settled[now, s]
  consistent_suspended_task_holds_rung[now, s]
}

-- `gaps`: stated, not in the catalogue.

pred well_formed_task_ttl_positive [now : Int, s : State] {
  all t : tasks[s] | t.state != Acquired or (some t.ttl and 0 < t.ttl)
}

pred well_formed_promise_target_is_nonempty [now : Int, s : State] {
  all p : promises[s] | p.type in isRunnable implies targetOf[p.type] != EmptyStr
}

pred well_formed_promise_delay_before_deadline [now : Int, s : State] {
  all o : s.objects | all t : o.task |
    (t.state = TaskPending and t.version = 0 and some t.retryTimeoutAt)
      implies t.retryTimeoutAt < o.promise.timeoutAt
}

pred gapsHold [now : Int, s : State] {
  well_formed_task_ttl_positive[now, s]
  well_formed_promise_target_is_nonempty[now, s]
  well_formed_promise_delay_before_deadline[now, s]
}

-- Commands. The runs show the catalogue admits the states it is meant to
-- describe; the checks show consequences the transitions rely on.

run init for 4 but 5 Int, 1 State

run showWellFormed {
  some now : Int, s : State | stateHolds[now, s] and gapsHold[now, s] and #s.objects >= 3
} for 5 but 5 Int, 1 State

run showAcquired {
  some now : Int, s : State | stateHolds[now, s] and gapsHold[now, s]
    and some t : tasks[s] | t.state = Acquired and some t.resumes
} for 4 but 5 Int, 1 State

run showSuspendedAwaiting {
  some now : Int, s : State | stateHolds[now, s] and gapsHold[now, s]
    and some o : s.objects | o.task.state = Suspended and o.promise.state = Pending
} for 4 but 5 Int, 1 State

run showOutbox {
  some now : Int, s : State | stateHolds[now, s] and gapsHold[now, s]
    and some s.outbox.message & Execute and some s.outbox.message & Unblock
} for 5 but 5 Int, 1 State

run showTimedOut {
  some now : Int, s : State | stateHolds[now, s] and gapsHold[now, s]
    and some o : s.objects | o.promise.state = RejectedTimedout and some o.task
} for 4 but 5 Int, 1 State

-- Under unique ids the lookups are functional, as `find?` on the Lean list.
check lookupsAreFunctional {
  all now : Int, s : State | stateHolds[now, s] implies
    all id : Ident | lone object[s, id] and lone promise[s, id] and lone task[s, id]
} for 5 but 5 Int, 1 State

-- A task is in exactly one of its five states and the lease and retry
-- fields tell which.
check leaseAndRetryAreExclusive {
  all now : Int, s : State | stateHolds[now, s] implies
    all t : tasks[s] | no t.leaseTimeoutAt or no t.retryTimeoutAt
} for 5 but 5 Int, 1 State

-- A settled promise shows the same state at every instant, and a pending
-- one before its timeout.
check projectionIsIdentityWhenNotDue {
  all p : PromiseObject, now : Int |
    (p.state != Pending or now < p.timeoutAt) implies projectedState[p, now] = p.state
} for 4 but 5 Int

-- Projecting a pending promise agrees with the deadline verdict the
-- catalogue demands of a settlement stamped at the timeout.
check projectionMatchesVerdict {
  all p, p2 : PromiseObject, now : Int |
    (p.state = Pending and no p.settledAt and projectPromise[p, now, p2]) implies
      (p2.settledAt != p2.timeoutAt
        or p2.state = (p2.type = Deadline implies Resolved else RejectedTimedout))
} for 4 but 5 Int

-- A task viewed next to a settled promise is fulfilled.
check viewFulfils {
  all t, t2 : TaskObject, p : PromiseObject |
    (p.state != Pending and viewTask[t, p, t2]) implies t2.state = Fulfilled
} for 4 but 5 Int

-- The object model's functions are realisable.

run showProjection {
  some o, o2 : Object, now : Int |
    o.promise.state = Pending and o.promise.timeoutAt <= now and some o.task
    and o.task.state = Acquired and projectObject[o, now, o2]
} for 4 but 5 Int, 0 State

run showAddCallback {
  some p, p2 : PromiseObject, a : Ident | a not in p.callbacks and addCallback[p, a, p2]
} for 4 but 5 Int, 0 State

run showRecords {
  some o : Object, r : PromiseRecord, q : TaskRecord |
    some o.task and some o.task.resumes and
    promiseToRecord[o.promise, o.id, r] and taskToRecord[o.task, o.id, q]
} for 4 but 5 Int, 0 State
