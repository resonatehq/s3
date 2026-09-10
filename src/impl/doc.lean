import «02-abstract».«system»
import impl.cas

namespace Impl

open ServerModel (Ident Message OutboxEntry OutboxKey PromiseState TaskState OType)
open AbstractModel (Object PromiseObject TaskObject ServerState)

structure OriginDoc where
  objects : List Object := []

  timerAt : Option Nat := none
  deriving Repr

def OriginDoc.toState (d : OriginDoc) : ServerState := { objects := d.objects }

def OriginDoc.ofState (s : ServerState) (timerAt : Option Nat) : OriginDoc :=
  { objects := s.objects, timerAt := timerAt }

def Object.deadlines (o : Object) : List Nat :=
  (if o.promise.state == .pending
      ∧ (o.promise.otype == .runnable
         ∨ !o.promise.callbacks.isEmpty
         ∨ !o.promise.listeners.isEmpty)
   then [o.promise.timeoutAt] else [])
  ++ (match o.task with
      | some t => t.leaseTimeoutAt.toList ++ t.retryTimeoutAt.toList
      | none   => [])

def OriginDoc.minDeadline (d : OriginDoc) : Option Nat :=
  (d.objects.flatMap Object.deadlines).foldl
    (fun acc x => match acc with
      | none   => some x
      | some m => some (min m x))
    none

inductive Key
  | doc   (origin : String)
  | timer (deadline : Nat) (origin : String)
  deriving DecidableEq, Repr

inductive Blob
  | doc (d : OriginDoc)
  | timer
  deriving Repr

def Key.isTimer : Key → Bool
  | .timer _ _ => true
  | .doc _     => false

def Key.due (now : Nat) : Key → Bool
  | .timer dl _ => dl ≤ now
  | .doc _      => false

structure World where
  store : Cas.Store Key Blob := {}
  wire  : List OutboxEntry := []
  deriving Repr

def World.doc? (w : World) (origin : String) : Option (OriginDoc × Cas.Version) :=
  match w.store.get (.doc origin) with
  | some (.doc d, v) => some (d, v)
  | _                => none

def World.docs (w : World) : List (String × OriginDoc) :=
  w.store.entries.filterMap fun e =>
    match e with
    | (.doc o, _, .doc d) => some (o, d)
    | _                   => none

def World.send (w : World) (address : String) (msg : Message) : World :=
  let entry := OutboxEntry.mk address msg
  { w with wire := entry :: w.wire.filter (fun e => e.key != entry.key) }

def abs (w : World) : ServerState :=
  { objects   := w.docs.flatMap (·.2.objects)
    schedules := []
    outbox    := w.wire }

end Impl
