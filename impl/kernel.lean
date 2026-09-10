import impl.monad

/-!  # The kernel — the protocol's transition, run against one document

The decision a commit makes, as a pure function of the snapshot. Nothing
here touches the bucket; that is `transact` at the bottom, and it only
turns the decision into effects.

THE KERNEL IS THE SPECIFICATION. The S3 backend does not have its own
theory of what `promise.settle` means; it has one document per origin
and it applies the protocol's transition to it. So the kernel here does
literally that: it lifts the document to a specification state
(`OriginDoc.toState`), runs the specification's own handler
(`Abstraction.handleExternal`) in the specification's own monad `H`,
and lowers the resulting state back to a document. The response is the
specification's response. There is no second decider to drift.

That is what makes the refinement in `refinement.lean` a theorem about
the STORE rather than about 21 handlers: the handler is shared, so
what has to be shown is that running it against one origin's document
gives the same answer as running it against the whole state — the
frame property the protocol's single-origin discipline was designed to
provide.

THE DRAIN. The specification leaves its six internal steps to fire
whenever they like, one at a time. The implementation has no daemon
per promise; it has one timer per origin, and when the timer fires it
sweeps the document: every deadline that has passed, every obligation
of every settled promise, every task due for re-dispatch, in three
phases, each reading the state the previous left. Each phase is a list
of the specification's own internal steps, run one after another
through the specification's own `handleInternal` — so a drain is not a
new transition but a SEQUENCE of specified ones, committed together.

Every commit drains. A request's commit therefore also settles what has
expired and fans out what has settled, so a document never leaves a
commit with anything due at the commit's instant (when the retry
interval is positive). The S3 backend sweeps only what a request names
and leaves the rest to its tick; sweeping everything is the simpler
invariant and, since each swept step is one the specification could
have taken anyway, it is observationally free.

WHICH ORIGIN. Every request the kernel serves names one origin —
`Request.origin?` — and the transaction is against that origin's
document. A request that names none (a search, a schedule, a heartbeat
across origins) is outside this implementation: the S3 backend's
validators refuse those at the door, and this model does not serve
them. -/

namespace Impl

open ServerModel (Ident Message PromiseState TaskState)
open AbstractModel (Object PromiseObject TaskObject ServerState)
open Equivalence (Request Response)
open Abstraction (InternalStep)

/-! ## The origin a request is about -/

/-- The one origin a request touches, if it touches exactly one.

    A heartbeat is single-origin when every reference shares the first's
    origin; one with no references names nothing and is not served.
    Callbacks, fences and suspensions name the origin of the request's
    subject; the handler itself refuses the cross-origin shapes with 400
    before reading anything else. -/
def _root_.Equivalence.Request.origin? : Request → Option String
  | .promiseGet r              => some r.id.origin
  | .promiseCreate r           => some r.id.origin
  | .promiseSettle r           => some r.id.origin
  | .promiseRegisterCallback r => some r.awaited.origin
  | .promiseRegisterListener r => some r.awaited.origin
  | .promiseSearch _           => none
  | .scheduleGet _             => none
  | .scheduleCreate _          => none
  | .scheduleDelete _          => none
  | .scheduleSearch _          => none
  | .taskGet r                 => some r.id.origin
  | .taskCreate r              => some r.action.id.origin
  | .taskAcquire r             => some r.id.origin
  | .taskFence r               => some r.id.origin
  | .taskHeartbeat r           =>
      match r.tasks with
      | []       => none
      | t :: ts  => if ts.all (fun u => u.id.origin == t.id.origin) then some t.id.origin else none
  | .taskSuspend r             => some r.id.origin
  | .taskFulfill r             => some r.id.origin
  | .taskRelease r             => some r.id.origin
  | .taskHalt r                => some r.id.origin
  | .taskContinue r            => some r.id.origin
  | .taskSearch _              => none

/-! ## Messages -/

/-- The messages a list of specification effects owes the transport. -/
def sendsOf : List AbstractModel.Effect → List (String × Message)
  | []                      => []
  | .setMessage a m :: rest => (a, m) :: sendsOf rest
  | _ :: rest               => sendsOf rest

/-- Whether an optional deadline has passed. -/
def dueAt (now : Nat) : Option Nat → Bool
  | some dl => dl ≤ now
  | none    => false

/-! ## One specification step against a document -/

/-- Run one specification step (external or internal) against the
    document: the response, the new document, and the messages owed. The
    timer field is carried through untouched; `transact` recomputes it. -/
def stepDoc (mat : Bool) (st : Abstraction.Step) (now : Nat) (d : OriginDoc) :
    Response × OriginDoc × List (String × Message) :=
  let (res, fx) := Abstraction.handle st now { state := d.toState, mat := mat }
  (res, OriginDoc.ofState (AbstractModel.applyAll d.toState fx) d.timerAt, sendsOf fx)

/-- A sequence of internal steps, each against the document the previous
    one left. -/
def stepDocs (mat : Bool) (now : Nat) :
    OriginDoc → List InternalStep → OriginDoc × List (String × Message)
  | d, []       => (d, [])
  | d, st :: sts =>
      let (_, d', sends) := stepDoc mat (.internal st) now d
      let (d'', sends') := stepDocs mat now d' sts
      (d'', sends ++ sends')

/-! ## The drain -/

/-- Phase 1 — every deadline that has passed: pending promises past their
    timeout, acquired tasks past their lease. Promises first, so an
    awaiter that is itself expiring is settled before its awaited promise
    fans out. -/
def timeoutSteps (d : OriginDoc) (now : Nat) : List InternalStep :=
  (d.objects.filterMap fun o =>
    if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now
    then some (.promiseTimeout ⟨o.id⟩) else none)
  ++ (d.objects.filterMap fun o =>
    match o.task with
    | some t =>
        if t.state == .acquired ∧ dueAt now t.leaseTimeoutAt
        then some (.taskLeaseTimeout ⟨o.id⟩) else none
    | none => none)

/-- Phase 2 — every obligation of every settled promise: its callbacks,
    in registration order, then its listeners. Only same-origin awaiters
    are drained here; the protocol admits no others (the callback door
    refuses them), and a document is the wrong place to reach across. -/
def obligationSteps (origin : String) (d : OriginDoc) : List InternalStep :=
  d.objects.flatMap fun o =>
    if o.promise.state != .pending then
      (o.promise.callbacks.filterMap fun awaiter =>
        if awaiter.origin == origin
        then some (.callback ⟨o.id, awaiter⟩) else none)
      ++ o.promise.listeners.map (fun a => .listener ⟨o.id, a⟩)
    else []

/-- Phase 3 — every pending task whose retry deadline has passed. Read
    after phase 2, so a task the settlement just fulfilled has no timer
    left to fire, and a task the fan-out just resumed is dispatched now. -/
def retrySteps (d : OriginDoc) (now : Nat) : List InternalStep :=
  d.objects.filterMap fun o =>
    match o.task with
    | some t =>
        if t.state == .pending ∧ dueAt now t.retryTimeoutAt
        then some (.taskRetryTimeout ⟨o.id⟩) else none
    | none => none

/-- The internal steps a sweep of `d` at `now` fires, in order. Each phase
    is computed from the document the previous phase left. -/
def drainSteps (mat : Bool) (origin : String) (d : OriginDoc) (now : Nat) : List InternalStep :=
  let p1 := timeoutSteps d now
  let d1 := (stepDocs mat now d p1).1
  let p2 := obligationSteps origin d1
  let d2 := (stepDocs mat now d1 p2).1
  let p3 := retrySteps d2 now
  p1 ++ p2 ++ p3

/-- The sweep: the drain steps, run. -/
def drain (mat : Bool) (origin : String) (d : OriginDoc) (now : Nat) :
    OriginDoc × List (String × Message) :=
  stepDocs mat now d (drainSteps mat origin d now)

/-! ## The transaction -/

/-- What a transaction is for. -/
inductive Work
  | request (rq : Request)
  /-- The timer daemon's sweep, and the timer key that woke it, if one did. -/
  | sweep (fired : Option Nat)
  deriving Repr

/-- The origin a piece of work is against, if it names one. -/
def Work.origin? (declared : String) : Work → Option String
  | .request rq => rq.origin?
  | .sweep _    => some declared

/-- The decision: the work against the document, then the sweep, then the
    timer the new document needs. Pure — this is what a commit decides;
    `transact` is how it is performed. -/
def decide (mat : Bool) (origin : String) (work : Work) (now : Nat) (old : OriginDoc) :
    Response × OriginDoc × List (String × Message) :=
  let (res, d1, sends1) :=
    match work with
    | .request rq => stepDoc mat (.external rq) now old
    | .sweep _    => (Response.silent, old, [])
  let (d2, sends2) := drain mat origin d1 now
  (res, { d2 with timerAt := d2.minDeadline }, sends1 ++ sends2)

/-- The timer to arm: the new document's, when it differs from the old. -/
def armFx (old new : OriginDoc) : List Effect :=
  if new.timerAt != old.timerAt then
    match new.timerAt with
    | some dl => [.armTimer dl]
    | none    => []
  else []

/-- The timers to clear: the old document's, when it differs from the
    new; and the key that fired, unless the new document re-armed it. -/
def delFx (old new : OriginDoc) (work : Work) : List Effect :=
  (if new.timerAt != old.timerAt then
    match old.timerAt with
    | some dl => [.delTimer dl]
    | none    => []
  else [])
  ++ (match work with
      | .sweep (some fired) => if new.timerAt != some fired then [.delTimer fired] else []
      | _                   => [])

/-- The messages, as effects. -/
def sendFx (sends : List (String × Message)) : List Effect :=
  sends.map fun (a, m) => .send a m

def emitAll : List Effect → C Unit
  | []      => pure ()
  | f :: fs => do emit f; emitAll fs

/-- Decide the work against the snapshot, then emit what the shell
    performs, in the shell's order: arm the new timer, commit the
    document, clear the old timer and the one that fired, send. -/
def transact (mat : Bool) (work : Work) (now : Nat) : C Response := do
  let e ← ask
  let (res, new, sends) := decide mat e.origin work now e.doc
  emitAll (armFx e.doc new)
  putDoc new
  emitAll (delFx e.doc new work)
  emitAll (sendFx sends)
  return res

end Impl
