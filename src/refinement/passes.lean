import refinement.store
import «02-abstract».«system»

namespace Chain

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)
open Concrete (Origin Commands Timer)

def promiseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      some (.promiseTimeout ⟨o.id⟩)
    else
      none

def listenerTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      o.promise.listeners.map fun a => .listener ⟨o.id, a⟩
    else
      []

def callbackTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending then
      o.promise.callbacks.map fun w => .callback ⟨o.id, w⟩
    else
      []

def leaseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    let o := o.project now
    match o.task with
    | some t =>
        if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
          some (.taskLeaseTimeout ⟨o.id⟩)
        else
          none
    | none =>
        none

def retryTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.current.objects.filterMap fun o =>
    let o := o.project now
    match o.task, o.promise.type with
    | some t, .runnable _ =>
        if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
          some (.taskRetryTimeout ⟨o.id⟩)
        else
          none
    | _, _ =>
        none

def sweepTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  let c1 := Concrete.promiseTimeouts now org
  let c2 := c1.merge (Concrete.listeners now (c1.doc org))
  let c3 := c2.merge (Concrete.callbacks now (c2.doc org))
  let c4 := c3.merge (Concrete.leaseTimeouts now (c3.doc org))
  promiseTimeoutTriggers now org ++ listenerTriggers now (c1.doc org) ++ callbackTriggers now (c2.doc org)
    ++ leaseTimeoutTriggers now (c3.doc org) ++ retryTimeoutTriggers now (c4.doc org)

end Chain
