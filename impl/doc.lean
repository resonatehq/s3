import «02-abstract».«system»
import impl.cas

/-!  # The document, the key space, and the world

What the implementation keeps in the bucket, and how to read it back as
a state of the specification.

ONE ORIGIN, ONE OBJECT. Every id has an origin — the part before the
first `:` — and every transition the protocol admits is single-origin:
a callback joins two promises of one origin, a suspension awaits
promises of the task's origin, a fence acts within the task's origin.
So the implementation stores one document per origin, holding every
promise and task of that origin, and commits any transition with ONE
conditional write of that one document. There is no cross-document
transaction, because the protocol never needs one.

The document's rows are the specification's own `Object`s. That is a
choice, and a deliberate one: the S3 backend's `OriginDoc` mirrors the
protocol's promise and task fields one for one (its codec is a
bijection onto them), so nothing is gained by inventing a second row
type and then proving it equal to the first. What the implementation
adds is not a new row but a new STORE — the CAS machine of
`impl/cas.lean` — and that is where the proof obligation lives.

TIMERS ARE KEYS. A deadline the server must wake up for is an empty
object under a timer key carrying the deadline and the origin. The key
IS the value, which is why a timer write is unconditional and
idempotent: arming the same deadline twice writes the same object. One
timer per origin — the minimum of every armed deadline in the document
— and the document records which one, so the next commit can delete
it.

THE WORLD is the bucket plus the wire: the messages the server has
handed to the transport. The specification keeps an outbox in its
state and a message becomes visible to a worker when it is there; the
implementation has no outbox, it sends. The wire is the record of
those sends, in the specification's own outbox discipline (one live
message per key), so that the two can be compared. -/

namespace Impl

open ServerModel (Ident Message OutboxEntry OutboxKey PromiseState TaskState OType)
open AbstractModel (Object PromiseObject TaskObject ServerState)

/-! ## The document -/

/-- One origin's entire state: the unit of every conditional write. -/
structure OriginDoc where
  objects : List Object := []
  /-- The deadline of the timer key currently armed for this origin. -/
  timerAt : Option Nat := none
  deriving Repr

/-- The document as the specification sees it: a state with only these
    objects, no schedules, and an empty outbox. -/
def OriginDoc.toState (d : OriginDoc) : ServerState := { objects := d.objects }

/-- A state back into a document, keeping the armed timer. -/
def OriginDoc.ofState (s : ServerState) (timerAt : Option Nat) : OriginDoc :=
  { objects := s.objects, timerAt := timerAt }

/-- The deadlines an object asks the server to wake up for.

    A pending promise's expiry is armed only when someone is waiting on
    it — a task to fulfil, a callback to fire, a listener to notify. A
    pending promise nobody awaits expires lazily, on the next read that
    touches it, exactly as the SQL backends and the S3 backend do. A
    task's lease and retry deadlines are armed whenever they are set. -/
def Object.deadlines (o : Object) : List Nat :=
  (if o.promise.state == .pending
      ∧ (o.promise.otype == .runnable
         ∨ !o.promise.callbacks.isEmpty
         ∨ !o.promise.listeners.isEmpty)
   then [o.promise.timeoutAt] else [])
  ++ (match o.task with
      | some t => t.leaseTimeoutAt.toList ++ t.retryTimeoutAt.toList
      | none   => [])

/-- The nearest armed deadline of the document, or `none` when nothing is
    armed. This is the one timer key the origin holds. -/
def OriginDoc.minDeadline (d : OriginDoc) : Option Nat :=
  (d.objects.flatMap Object.deadlines).foldl
    (fun acc x => match acc with
      | none   => some x
      | some m => some (min m x))
    none

/-! ## The key space -/

/-- The two kinds of object in the bucket. -/
inductive Key
  | doc   (origin : String)
  | timer (deadline : Nat) (origin : String)
  deriving DecidableEq, Repr

/-- What a key holds. A timer object is empty: the key carries the value. -/
inductive Blob
  | doc (d : OriginDoc)
  | timer
  deriving Repr

def Key.isTimer : Key → Bool
  | .timer _ _ => true
  | .doc _     => false

/-- The timer keys due at or before `now` — what the timer daemon lists. -/
def Key.due (now : Nat) : Key → Bool
  | .timer dl _ => dl ≤ now
  | .doc _      => false

/-! ## The world -/

/-- The bucket and the wire. -/
structure World where
  store : Cas.Store Key Blob := {}
  wire  : List OutboxEntry := []
  deriving Repr

/-- The origin's document and its version, or `none` if the origin has
    never been written. -/
def World.doc? (w : World) (origin : String) : Option (OriginDoc × Cas.Version) :=
  match w.store.get (.doc origin) with
  | some (.doc d, v) => some (d, v)
  | _                => none

/-- Every document in the bucket, with the origin its key names. -/
def World.docs (w : World) : List (String × OriginDoc) :=
  w.store.entries.filterMap fun e =>
    match e with
    | (.doc o, _, .doc d) => some (o, d)
    | _                   => none

/-- Hand a message to the transport. The wire keeps one live message per
    key, exactly as the specification's outbox does (`Effect.apply`),
    so the two can be compared entry for entry. -/
def World.send (w : World) (address : String) (msg : Message) : World :=
  let entry := OutboxEntry.mk address msg
  { w with wire := entry :: w.wire.filter (fun e => e.key != entry.key) }

/-! ## The abstraction

A world, read as a state of the specification: every document's objects,
no schedules, and the wire as the outbox. The order of objects is the
order of the bucket listing, which is not the order the specification's
own `Effect.apply` would have left them in — so the refinement relates
the two by LOOKUP (`find?` by id) rather than by equality. Nothing the
protocol answers depends on the order; `promise.search`, which would,
is not part of this implementation. -/

def abs (w : World) : ServerState :=
  { objects   := w.docs.flatMap (·.2.objects)
    schedules := []
    outbox    := w.wire }

end Impl
