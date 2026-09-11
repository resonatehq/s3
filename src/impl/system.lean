import impl.kernel

namespace Impl

open Abstract (Request Response Reply)

structure Txn where
  origin   : String
  work     : Work
  snapshot : Option (Origin × Cas.Version)
  deriving Repr

structure State where
  world    : World := {}
  inflight : List Txn := []
  deriving Repr

def State.init : State := {}

inductive Step
  | begin  (origin : String) (work : Work)
  | commit (txn : Nat)
  | stutter
  deriving Repr

structure Obs where
  rq  : Request
  res : Response
  now : Nat
  deriving Repr

def begin (origin : String) (work : Work) (now : Nat) (s : State) : State :=
  if work.origin? origin == some origin ∧ work.licensed origin now s.world = true then
    { s with inflight := s.inflight ++ [⟨origin, work, s.world.origin? origin⟩] }
  else
    s

def commit (i : Nat) (now : Nat) (s : State) : Option Obs × State :=
  match s.inflight[i]? with
  | none   => (none, s)
  | some t =>
      let r := runC (transact t.work now) { origin := t.origin, snapshot := t.snapshot } s.world
      ((match r.1, t.work with
        | some (.external res), .request rq => some ⟨rq, res, now⟩
        | _,                    _           => none),
       { world := r.2, inflight := s.inflight.eraseIdx i })

def step (st : Step) (now : Nat) (s : State) : Option Obs × State :=
  match st with
  | .begin o w => (none, begin o w now s)
  | .commit i  => commit i now s
  | .stutter   => (none, s)

def run : List (Step × Nat) → State → List Obs × State
  | [],           s => ([], s)
  | (st, n) :: w, s =>
      let (o, s')    := step st n s
      let (os, s'')  := run w s'
      (o.toList ++ os, s'')

def atomic (origin : String) (work : Work) (now : Nat) (w : World) : Option Reply × World :=
  runC (transact work now) { origin := origin, snapshot := w.origin? origin } w

end Impl
