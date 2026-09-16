module properties

-- The catalogue's state properties, as in
-- `src/spec/02-abstract/properties.lean`: one predicate per Lean property,
-- same name, same shape, `now` as argument and the state the current
-- instant's. The schedule properties are left out with the schedules.
-- The transition properties come with the transitions.

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

-- well formed: the store

pred well_formed_store_object_ids_unique [now : Int] {
  all disj a, b : State.objects | a.id != b.id
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
  well_formed_store_object_ids_unique[now]
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

-- Commands. The runs show the catalogue admits the states it is meant to
-- describe; the checks show consequences the transitions rely on.

run init for 4 but 5 Int, 1 steps

run showWellFormed {
  some now : Int | stateHolds[now] and gapsHold[now] and #State.objects >= 3
} for 5 but 5 Int, 1 steps

run showAcquired {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some t : storedTasks | t.state = Acquired and some t.resumes
} for 4 but 5 Int, 1 steps

run showSuspendedAwaiting {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some o : State.objects | o.task.state = Suspended and o.promise.state = Pending
} for 4 but 5 Int, 1 steps

run showOutbox {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some State.outbox.message & Execute and some State.outbox.message & Unblock
} for 5 but 5 Int, 1 steps

run showTimedOut {
  some now : Int | stateHolds[now] and gapsHold[now]
    and some o : State.objects | o.promise.state = RejectedTimedout and some o.task
} for 4 but 5 Int, 1 steps

-- Under unique ids the lookups are functional, as `find?` on the Lean list.
check lookupsAreFunctional {
  all now : Int | stateHolds[now] implies
    all id : Ident | lone object[id] and lone promise[id] and lone task[id]
} for 5 but 5 Int, 1 steps

-- A task is in exactly one of its five states and the lease and retry
-- fields tell which.
check leaseAndRetryAreExclusive {
  all now : Int | stateHolds[now] implies
    all t : storedTasks | no t.leaseTimeoutAt or no t.retryTimeoutAt
} for 5 but 5 Int, 1 steps

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
} for 4 but 5 Int, 1 steps

run showAddCallback {
  some p, p2 : PromiseObject, a : Ident | a not in p.callbacks and addCallback[p, a, p2]
} for 4 but 5 Int, 1 steps

run showRecords {
  some o : Object, r : PromiseRecord, q : TaskRecord |
    some o.task and some o.task.resumes and
    promiseToRecord[o.promise, o.id, r] and taskToRecord[o.task, o.id, q]
} for 4 but 5 Int, 1 steps
