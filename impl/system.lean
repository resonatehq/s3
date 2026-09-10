import impl.kernel

/-!  # The implementation as a system — transactions, interleaved

The specification's system is a sequence of atomic steps. The
implementation's is not: a commit begins with a read and ends with a
conditional write, and anything may happen in between — another
transaction on the same origin may commit, the timer daemon may sweep.
This file writes that down, so that the refinement can say what the
CAS buys.

A TRANSACTION is a snapshot: the origin, the work, and the document
read (with its version) when the transaction began. It is opened by
`begin` and closed by `commit`. Between the two it sits in
`State.inflight`, seeing nothing.

  `begin origin work`   read the origin's document into a new transaction
  `commit txn`          decide against the snapshot and perform the
                        effects at `now` — the document write CAS'd
                        against the snapshot's version
  `idle`                nothing

A commit whose CAS is refused delivers no answer. The transaction is
gone either way; the shell re-decides by beginning a new one. The
effects that landed before the refusal are exactly the timer PUTs
`transact` emits before `putDoc`, and they are harmless.

The timer daemon is a client of `begin` like any other: a due timer key
is a reason to `begin origin (.sweep (some deadline))`, and the commit
deletes the key. Nothing forces the daemon to be prompt, and nothing
stops a sweep that no key asked for — both are how the specification's
internal steps behave too.

OBSERVATIONS. What a client sees is the answer to a request, at the
instant it was answered. A sweep is silent, a refused commit is
silent, a `begin` is silent. `run` collects the observations of a
finite run; `refinement.lean` shows that every such list is the
observation list of a run of the specification. -/

namespace Impl

open Equivalence (Request Response)

/-- A transaction in flight: what it read, and what it is for. -/
structure Txn where
  origin   : String
  work     : Work
  snapshot : Option (OriginDoc × Cas.Version)
  deriving Repr

structure State where
  world    : World := {}
  inflight : List Txn := []
  deriving Repr

def State.init : State := {}

inductive Step
  | begin  (origin : String) (work : Work)
  | commit (txn : Nat)
  | idle
  deriving Repr

/-- One answered request. -/
structure Obs where
  rq  : Request
  res : Response
  now : Nat
  deriving Repr

/-- Open a transaction: snapshot the origin's document. Work that names
    no single origin, or names a different one, is refused at the door
    and opens nothing. -/
def begin (origin : String) (work : Work) (s : State) : State :=
  if work.origin? origin == some origin then
    { s with inflight := s.inflight ++ [⟨origin, work, s.world.doc? origin⟩] }
  else
    s

/-- Close a transaction: decide at `now` against its snapshot, perform the
    effects. The observation, if the work was a request and the commit
    landed. -/
def commit (mat : Bool) (i : Nat) (now : Nat) (s : State) : Option Obs × State :=
  match s.inflight[i]? with
  | none   => (none, s)
  | some t =>
      let r := runC (transact mat t.work now)
        { origin := t.origin, snapshot := t.snapshot, mat := mat } s.world
      ((match r.1, t.work with
        | some res, .request rq => some ⟨rq, res, now⟩
        | _,        _           => none),
       { world := r.2, inflight := s.inflight.eraseIdx i })

def step (mat : Bool) (st : Step) (now : Nat) (s : State) : Option Obs × State :=
  match st with
  | .begin o w => (none, begin o w s)
  | .commit i  => commit mat i now s
  | .idle      => (none, s)

/-- A finite run: the observations, in order, and the final state. -/
def run (mat : Bool) : List (Step × Nat) → State → List Obs × State
  | [],           s => ([], s)
  | (st, n) :: w, s =>
      let (o, s')    := step mat st n s
      let (os, s'')  := run mat w s'
      (o.toList ++ os, s'')

/-! ## The atomic view

A transaction that begins and commits with nothing in between is one
atomic read-modify-write of the origin's document. `atomic` is that
step, and `commit_accepted_is_atomic` in `refinement.lean` is the
statement that a commit whose CAS is accepted is one — whatever ran
between its `begin` and its `commit`. -/

/-- Decide against the CURRENT document and perform the effects. -/
def atomic (mat : Bool) (origin : String) (work : Work) (now : Nat) (w : World) :
    Option Response × World :=
  let e : Env := { origin := origin, snapshot := w.doc? origin, mat := mat }
  runC (transact mat work now) e w

end Impl
