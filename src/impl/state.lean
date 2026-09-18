import types

namespace Concrete

open Protocol (Ident Message OutboxEntry PromiseState TaskState Object PromiseObject TaskObject Request Response)

structure Origin where
  objects : List Object := []
  deriving Repr

inductive TimerKind
  | promiseTimeout
  | taskLeaseTimeout
  | taskRetryTimeout
  deriving Repr, DecidableEq

structure Timer where
  deadline : Nat
  id       : Ident
  kind     : TimerKind
  deriving Repr, DecidableEq

structure Commands where
  arm  : List Timer := []
  org  : Origin
  del  : List Timer := []
  send : List (String × Message) := []
  deriving Repr

def Origin.get (org : Origin) (id : Ident) (now : Nat) : Option Object :=
  (org.objects.find? (·.id == id)).map (·.project now)

def Origin.set (org : Origin) (o : Object) : Origin :=
  if org.objects.any (·.id == o.id) then
    ⟨org.objects.map fun x => if x.id == o.id then o else x⟩
  else
    ⟨org.objects ++ [o]⟩

def _root_.Protocol.TaskObject.timers (t : TaskObject) (id : Ident) : List Timer :=
  match t.state, t.leaseTimeoutAt, t.retryTimeoutAt with
  | .acquired, some dl, _ =>
      [⟨dl, id, .taskLeaseTimeout⟩]
  | .pending, _, some dl =>
      [⟨dl, id, .taskRetryTimeout⟩]
  | _, _, _ =>
      []

def _root_.Protocol.Object.timers (o : Object) : List Timer :=
  (if o.promise.state == .pending ∧ o.promise.type != .internal then [⟨o.promise.timeoutAt, o.id, .promiseTimeout⟩]
   else [])
  ++ (o.task.map (·.timers o.id)).getD []

inductive Path
  | origin (name : String)
  | timer (t : Timer)
  deriving Repr, DecidableEq

inductive Blob
  | origin (org : Origin)
  | timer
  deriving Repr

structure Hasher where
  Hash : Type
  hash : Blob → Hash
  inj  : ∀ a b, hash a = hash b → a = b
  deq  : DecidableEq Hash

attribute [instance] Hasher.deq

inductive Cond (H : Hasher)
  | any
  | absent
  | hash (h : H.Hash)

def Cond.holds {H : Hasher} : Cond H → Option Blob → Bool
  | .any, _ =>
      true
  | .absent, cur =>
      cur.isNone
  | .hash h, cur =>
      cur.map H.hash == some h

def Cond.of (H : Hasher) : Option Blob → Cond H
  | some b =>
      .hash (H.hash b)
  | none =>
      .absent

structure State where
  bucket : List (Path × Blob) := []
  outbox : List OutboxEntry := []
  deriving Repr

def State.init : State := {}

def State.blob? (s : State) (p : Path) : Option Blob :=
  (s.bucket.find? (·.1 == p)).map (·.2)

def State.origin (s : State) (name : String) : Origin :=
  match s.blob? (.origin name) with
  | some (.origin org) =>
      org
  | _ =>
      {}

inductive Effect (H : Hasher)
  | put (path : Path) (blob : Blob) (cond : Cond H)
  | del (path : Path)
  | send (address : String) (msg : Message)

def Effect.apply {H : Hasher} (s : State) : Effect H → Option State
  | .put p b c =>
      if c.holds (s.blob? p) then
        some { s with bucket := (p, b) :: s.bucket.filter (·.1 != p) }
      else
        none
  | .del p =>
      some { s with bucket := s.bucket.filter (·.1 != p) }
  | .send a m =>
      let entry := OutboxEntry.mk a m
      some { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def applyAll {H : Hasher} : State → List (Effect H) → State × Bool
  | s, [] =>
      (s, true)
  | s, e :: es =>
      match e.apply s with
      | some s' =>
          applyAll s' es
      | none =>
          (s, false)

def Commands.effects {H : Hasher} (name : String) (cond : Cond H) (c : Commands) :
    List (Effect H) :=
  c.arm.map (fun t => .put (.timer t) .timer .any)
  ++ [.put (.origin name) (.origin c.org) cond]
  ++ c.del.map (fun t => .del (.timer t))
  ++ c.send.map (fun (a, m) => .send a m)

def run (H : Hasher) (name : String) (f : Origin → α × Commands) (s : State) :
    α × State × Bool :=
  let (a, c) := f (s.origin name)
  let (s', ok) := applyAll s (c.effects name (Cond.of H (s.blob? (.origin name))))
  (a, s', ok)

end Concrete
