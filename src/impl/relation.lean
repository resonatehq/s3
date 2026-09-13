import impl.passes

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


namespace Refinement

def events : Concrete.Event → Nat → Concrete.State → List Abstract.Event
  | .external req, now, s =>
      match req.origin? with
      | some name =>
          (Chain.sweepTriggers now (s.origin name)).map .internal ++ [.external req]
      | none =>
          []
  | .internal t, now, s =>
      if (s.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        (Chain.sweepTriggers now (s.origin t.id.origin)).map .internal
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

def WF (org : Concrete.Origin) : Prop :=
  ∀ ob ∈ org.objects, ob.promise.listeners.Nodup ∧ ob.promise.callbacks.Nodup ∧
    ∀ w ∈ ob.promise.callbacks, w ≠ ob.id ∧ w.origin = ob.id.origin

structure Inv (s : Concrete.State) : Prop where
  blobs : ∀ name b, (Concrete.Path.origin name, b) ∈ s.bucket →
    ∃ org, b = .origin org ∧ (∀ o ∈ org.objects, o.id.origin = name) ∧
      (org.objects.map (·.id)).Nodup ∧ WF org
  paths : (s.bucket.map (·.1)).Nodup

def observations (now : Nat) : List Abstract.Event → List Abstract.Reply → List Abstract.Observation
  | .external req :: evs, .external res :: rs =>
      ⟨req, res, now⟩ :: observations now evs rs
  | _ :: evs, _ :: rs =>
      observations now evs rs
  | _, _ =>
      []


end Refinement
