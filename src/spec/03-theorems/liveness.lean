import «03-theorems».«properties-step»

namespace Abstract

open AbstractModel (ServerState PromiseObject TaskObject)

def promiseAt (s : ServerState) (id : ServerModel.Ident) : Option PromiseObject :=
  s.promise? id

def taskAt (s : ServerState) (id : ServerModel.Ident) : Option TaskObject :=
  s.task? id

def enabledInternal (st : Event) (now : Nat) (s : ServerState) : Bool :=
  match st with
  | .internal (.promiseTimeout { id := id }) =>
      match promiseAt s id with
      | some p => p.type.awaitable && p.state == .pending && p.timeoutAt ≤ now
      | none   => false
  | .internal (.callback { awaited := id, awaiter := x }) =>
      match promiseAt s id with
      | some p => (p.project now).state != .pending && p.callbacks.contains x
      | none   => false
  | .internal (.listener { awaited := id, address := addr }) =>
      match promiseAt s id with
      | some p => (p.project now).state != .pending && p.listeners.contains addr
      | none   => false
  | .internal (.taskLeaseTimeout { id := id }) =>
      match taskAt s id, promiseAt s id with
      | some t, some p =>
          t.state == .acquired && (t.leaseTimeoutAt.getD (now + 1)) ≤ now
            && (p.project now).state == .pending
      | _, _ => false
  | .internal (.taskRetryTimeout { id := id }) =>
      match taskAt s id, promiseAt s id with
      | some t, some p =>
          t.state == .pending && (t.retryTimeoutAt.getD (now + 1)) ≤ now
            && (p.project now).state == .pending
      | _, _ => false
  | .internal (.scheduleTimeout { schedule := id }) => (s.schedules.find? (·.id == id)).isSome
  | _ => false

def ClockAdvances (tr : Trace) : Prop :=
  ∀ n : Nat, ∃ t : Nat, n ≤ (tr t).now

def WeaklyFairOn (tr : Trace) (family : Event → Bool) : Prop :=
  ∀ st : Event, family st = true →
    ∀ t : Nat,
      (∀ u : Nat, t ≤ u → enabledInternal st (tr u).now (tr u).state = true) →
      ∃ u : Nat, t ≤ u ∧ (tr u).event = st

def isSettlementStep : Event → Bool
  | .internal (.promiseTimeout { id := _ }) => true
  | _     => false

def isCallbackStep : Event → Bool
  | .internal (.callback { awaited := _, awaiter := _ }) => true
  | _       => false

def isListenerStep : Event → Bool
  | .internal (.listener { awaited := _, address := _ }) => true
  | _       => false

def EventuallyEveryExternalPromiseSettles : Prop :=
  ∀ tr : Trace, Valid true tr → ClockAdvances tr → WeaklyFairOn tr isSettlementStep →
    ∀ (t : Nat) (id : ServerModel.Ident),
      (∀ p, promiseAt (tr t).state id = some p → p.type.awaitable = true) →
      (promiseAt (tr t).state id).isSome →
      ∃ u : Nat, t ≤ u ∧
        ∀ p, promiseAt (tr u).state id = some p → p.state ≠ .pending

def EventuallyEveryPromiseReadsSettled : Prop :=
  ∀ tr : Trace, Valid true tr → ClockAdvances tr →
    ∀ (t : Nat) (id : ServerModel.Ident),
      (promiseAt (tr t).state id).isSome →
      ∃ u : Nat, t ≤ u ∧
        ∀ p, promiseAt (tr u).state id = some p →
          (p.project (tr u).now).state ≠ .pending

def EventuallyEveryTaskFulfils : Prop :=
  ∀ tr : Trace, Valid true tr → ClockAdvances tr → WeaklyFairOn tr isSettlementStep →
    ∀ (t : Nat) (id : ServerModel.Ident),
      (taskAt (tr t).state id).isSome →
      ∃ u : Nat, t ≤ u ∧
        ∀ w, taskAt (tr u).state id = some w → w.state = .fulfilled

theorem taskFulfilment_follows_from_promiseSettlement :
    EventuallyEveryExternalPromiseSettles → EventuallyEveryTaskFulfils := by
  sorry

def EventuallyAwaiterResumed : Prop :=
  ∀ tr : Trace, Valid true tr → ClockAdvances tr →
    WeaklyFairOn tr isSettlementStep → WeaklyFairOn tr isCallbackStep →
    ∀ (t : Nat) (a x : ServerModel.Ident),
      (∃ p, promiseAt (tr t).state a = some p ∧
              p.state ≠ .pending ∧ p.callbacks.contains x = true) →
      ∃ u : Nat, t ≤ u ∧
        (∀ p, promiseAt (tr u).state a = some p → p.callbacks.contains x = false) ∧
        (∀ w, taskAt (tr u).state x = some w →
           w.state = .fulfilled ∨ (w.state ≠ .suspended ∧ w.resumes.contains a = true))

def EventuallyListenerNotified : Prop :=
  ∀ tr : Trace, Valid true tr → ClockAdvances tr →
    WeaklyFairOn tr isSettlementStep → WeaklyFairOn tr isListenerStep →
    ∀ (t : Nat) (a : ServerModel.Ident) (addr : String),
      (∃ p, promiseAt (tr t).state a = some p ∧
              p.state ≠ .pending ∧ p.listeners.contains addr = true) →
      ∃ u : Nat, t ≤ u ∧
        (tr u).state.outbox.any (fun e =>
          e.address == addr &&
            (match e.message with
             | .unblock r => r.id == a && r.state != .pending
             | .execute _ _ => false)) = true

def enabledSteps (now : Nat) (s : ServerState) : List Event :=
  s.objects.flatMap fun o =>
    let p := o.promise
    (if enabledInternal (.internal (.promiseTimeout { id := o.id })) now s then [Event.internal (.promiseTimeout { id := o.id })] else [])
      ++ p.callbacks.map (fun x => Event.internal (.callback { awaited := o.id, awaiter := x }))
      ++ p.listeners.map (fun addr => Event.internal (.listener { awaited := o.id, address := addr }))
      ++ (if o.task.isSome ∧ enabledInternal (.internal (.taskLeaseTimeout { id := o.id })) now s then [Event.internal (.taskLeaseTimeout { id := o.id })] else [])
      ++ (if o.task.isSome ∧ enabledInternal (.internal (.taskRetryTimeout { id := o.id })) now s then [Event.internal (.taskRetryTimeout { id := o.id })] else [])

def fireAllEnabled (now : Nat) (s : ServerState) : ServerState :=
  (enabledSteps now s).foldl
    (fun acc st => if enabledInternal st now acc then (step true st now acc).2 else acc) s

def fairRounds : Nat → Nat → ServerState → ServerState
  | 0,     _,   s => s
  | k + 1, now, s => fairRounds k now (fireAllEnabled now s)

def wakeMaterializes (w : List (Event × Nat)) (horizon : Nat) : Bool :=
  let s := fairRounds 6 horizon (exec true w AbstractModel.ServerState.init).2
  s.promises.all fun p =>
    (p.project horizon).state == .pending ||
      (p.callbacks.isEmpty && p.listeners.isEmpty)

def resumeRecorded (w : List (Event × Nat)) (horizon : Nat) : Bool :=
  let s0 := (exec true w AbstractModel.ServerState.init).2
  let s  := fairRounds 6 horizon s0
  s0.objects.all fun o =>
    o.promise.callbacks.all fun x =>
      match taskAt s x with
      | none   => true
      | some u => u.state == .fulfilled
                    || (u.state != .suspended && u.resumes.contains o.id)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def wWake : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "a", timeoutAt := 9000, param := {}, type := extType }), 100),
    (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 9000, param := {}, type := tgtType } }), 100),
    (.external (.taskSuspend { id := oid "x", version := 1, actions := [{ awaited := oid "a", awaiter := oid "x" }] }), 120),
    (.external (.promiseSettle { id := oid "a", state := .resolved, value := {} }), 200) ]

example : wakeMaterializes wWake 300 := by decide
example : resumeRecorded wWake 300 := by decide

def wWakeTimedOut : List (Event × Nat) :=
  [ (.external (.promiseCreate { id := oid "a", timeoutAt := 9000, param := {}, type := extType }), 100),
    (.external (.taskCreate { pid := "p0", ttl := 100, action := { id := oid "x", timeoutAt := 250, param := {}, type := tgtType } }), 100),
    (.external (.taskSuspend { id := oid "x", version := 1, actions := [{ awaited := oid "a", awaiter := oid "x" }] }), 120),
    (.external (.promiseSettle { id := oid "a", state := .resolved, value := {} }), 200) ]

example : wakeMaterializes wWakeTimedOut 300 := by decide
example : resumeRecorded wWakeTimedOut 300 := by decide

theorem wake_requires_fairness :
    ((exec true wWake AbstractModel.ServerState.init).2.promises.any (fun p => p.callbacks.contains (oid "x"))
      && (exec true wWake AbstractModel.ServerState.init).2.tasks.any (fun t => t.state == .suspended)) = true := by
  decide

theorem boundedWakeSweep :
    (((seqsUpToA kernelsResp 3).map instantiateA).all
      (fun w => wakeMaterializes w 9000 && resumeRecorded w 9000)) = true := by
  decide

theorem boundedWakeBattery :
    (battery.all (fun w => wakeMaterializes w 9000 && resumeRecorded w 9000)) = true := by
  decide

end Abstract
