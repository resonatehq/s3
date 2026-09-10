import impl.origin
import impl.cas

namespace Impl

open ServerModel (Message OutboxEntry)
open AbstractModel (ServerState)

inductive Key
  | origin (origin : String)
  | timer  (deadline : Nat) (origin : String)
  deriving DecidableEq, Repr

inductive Blob
  | origin (o : Origin)
  | timer
  deriving Repr

def Key.isTimer : Key → Bool
  | .timer _ _ => true
  | .origin _  => false

def Key.due (now : Nat) : Key → Bool
  | .timer dl _ => dl ≤ now
  | .origin _   => false

structure World where
  store : Cas.Store Key Blob := {}
  wire  : List OutboxEntry := []
  deriving Repr

def World.origin? (w : World) (origin : String) : Option (Origin × Cas.Version) :=
  match w.store.get (.origin origin) with
  | some (.origin o, v) => some (o, v)
  | _                   => none

def World.origins (w : World) : List (String × Origin) :=
  w.store.entries.filterMap fun e =>
    match e with
    | (.origin n, _, .origin o) => some (n, o)
    | _                         => none

def World.send (w : World) (address : String) (msg : Message) : World :=
  let entry := OutboxEntry.mk address msg
  { w with wire := entry :: w.wire.filter (fun e => e.key != entry.key) }

def abs (w : World) : ServerState :=
  { objects   := w.origins.flatMap (·.2.objects)
    schedules := []
    outbox    := w.wire }

end Impl
