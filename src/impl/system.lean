import impl.kernel

namespace Impl

open Abstract (Request Response Reply)

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
  | stutter
  deriving Repr

structure Obs where
  rq  : Request
  res : Response
  now : Nat
  deriving Repr

def begin (origin : String) (work : Work) (s : State) : State :=
  if work.origin? origin == some origin then
    { s with inflight := s.inflight ++ [⟨origin, work, s.world.doc? origin⟩] }
  else
    s

def commit (mat : Bool) (i : Nat) (now : Nat) (s : State) : Option Obs × State :=
  match s.inflight[i]? with
  | none   => (none, s)
  | some t =>
      let r := runC (transact mat t.work now)
        { origin := t.origin, snapshot := t.snapshot, mat := mat } s.world
      ((match r.1, t.work with
        | some (.external res), .request rq => some ⟨rq, res, now⟩
        | _,        _           => none),
       { world := r.2, inflight := s.inflight.eraseIdx i })

def step (mat : Bool) (st : Step) (now : Nat) (s : State) : Option Obs × State :=
  match st with
  | .begin o w => (none, begin o w s)
  | .commit i  => commit mat i now s
  | .stutter   => (none, s)

def run (mat : Bool) : List (Step × Nat) → State → List Obs × State
  | [],           s => ([], s)
  | (st, n) :: w, s =>
      let (o, s')    := step mat st n s
      let (os, s'')  := run mat w s'
      (o.toList ++ os, s'')

def atomic (mat : Bool) (origin : String) (work : Work) (now : Nat) (w : World) :
    Option Reply × World :=
  let e : Env := { origin := origin, snapshot := w.doc? origin, mat := mat }
  runC (transact mat work now) e w

end Impl
