import impl.system
import «02-abstract».«system»

namespace Abstract

open Protocol (Request Response)

structure Observation where
  req : Request
  res : Response
  now : Nat

def Frame.observe (f : Frame) : Option Observation :=
  match f.event, f.reply with
  | .external req, .external res =>
      some ⟨req, res, f.now⟩
  | _, _ =>
      none

def observed (tr : Trace) (n : Nat) : List Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace) (k : Nat) (o : Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

end Abstract

namespace Concrete

def Frame.observe (f : Frame) : Option Abstract.Observation :=
  match f.event, f.reply with
  | .external req, .external res =>
      some ⟨req, res, f.now⟩
  | _, _ =>
      none

def observed (tr : Trace) (n : Nat) : List Abstract.Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace) (k : Nat) (o : Abstract.Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

end Concrete

namespace Concrete

def promiseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.objects.filterMap fun o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
      some (.promiseTimeout ⟨o.id⟩)
    else
      none

def listenerTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
      o.promise.listeners.map fun a => .listener ⟨o.id, a⟩
    else
      []

def callbackTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.objects.flatMap fun o =>
    let o := o.project now
    if o.promise.state != .pending then
      o.promise.callbacks.map fun w => .callback ⟨o.id, w⟩
    else
      []

def leaseTimeoutTriggers (now : Nat) (org : Origin) : List Abstract.Trigger :=
  org.objects.filterMap fun o =>
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
  org.objects.filterMap fun o =>
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
  let c1 := promiseTimeouts now org
  let c2 := c1.merge (listeners now c1.put)
  let c3 := c2.merge (callbacks now c2.put)
  let c4 := c3.merge (leaseTimeouts now c3.put)
  promiseTimeoutTriggers now org ++ listenerTriggers now c1.put ++ callbackTriggers now c2.put
    ++ leaseTimeoutTriggers now c3.put ++ retryTimeoutTriggers now c4.put

end Concrete

namespace Refinement

def events : Concrete.Event → Nat → Concrete.State → List Abstract.Event
  | .external req, now, s =>
      match req.origin? with
      | some name =>
          (Concrete.sweepTriggers now (s.origin name)).map .internal ++ [.external req]
      | none =>
          []
  | .internal t, now, s =>
      if (s.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        (Concrete.sweepTriggers now (s.origin t.id.origin)).map .internal
      else
        []
  | .stutter, _, _ =>
      []

def origins (s : Concrete.State) : List Concrete.Origin :=
  s.bucket.filterMap fun
    | (.origin _, .origin org) =>
        some org
    | _ =>
        none

def abstract (s : Concrete.State) : Abstract.State :=
  { objects := (origins s).flatMap (·.objects), schedules := [], outbox := s.outbox }

theorem abstract_init : abstract Concrete.State.init = Abstract.State.init := rfl

def Equiv (S T : Abstract.State) : Prop :=
  (∀ id, S.objects.find? (·.id == id) = T.objects.find? (·.id == id)) ∧
  S.schedules = T.schedules ∧
  S.outbox = T.outbox

structure Inv (s : Concrete.State) : Prop where
  blobs : ∀ name b, (Concrete.Path.origin name, b) ∈ s.bucket →
    ∃ org, b = .origin org ∧ (∀ o ∈ org.objects, o.id.origin = name) ∧ (org.objects.map (·.id)).Nodup

def observations (now : Nat) : List Abstract.Event → List Abstract.Reply → List Abstract.Observation
  | .external req :: evs, .external res :: rs =>
      ⟨req, res, now⟩ :: observations now evs rs
  | _ :: evs, _ :: rs =>
      observations now evs rs
  | _, _ =>
      []


end Refinement
