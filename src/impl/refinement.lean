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

namespace Refinement

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

def Inv (s : Concrete.State) : Prop :=
  ∀ name org, s.blob? (.origin name) = some (.origin org) →
    (∀ o ∈ org.objects, o.id.origin = name) ∧ (org.objects.map (·.id)).Nodup

def observations (now : Nat) : List Abstract.Event → List Abstract.Reply → List Abstract.Observation
  | .external req :: evs, .external res :: rs =>
      ⟨req, res, now⟩ :: observations now evs rs
  | _ :: evs, _ :: rs =>
      observations now evs rs
  | _, _ =>
      []

theorem step_sim (H : Concrete.Hasher) (ev : Concrete.Event) (now : Nat)
    (s : Concrete.State) (S : Abstract.State)
    (inv : Inv s) (rel : Equiv (abstract s) S) :
    ∃ evs : List Abstract.Event,
      Inv (Concrete.step H ev now s).2 ∧
      Equiv (abstract (Concrete.step H ev now s).2)
            (Abstract.exec false (evs.map (·, now)) S).2 ∧
      observations now evs (Abstract.exec false (evs.map (·, now)) S).1 =
        (Concrete.Frame.observe ⟨s, ev, (Concrete.step H ev now s).1, now⟩).toList :=
  sorry

theorem refines (H : Concrete.Hasher) (tr : Concrete.Trace)
    (valid : Concrete.Valid H tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o :=
  sorry

end Refinement
