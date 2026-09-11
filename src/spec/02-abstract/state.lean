import types

namespace AbstractModel

open ServerModel (Ident Value PromiseState TaskState PromiseRecord
                  TaskRecord Schedule Message OutboxEntry OutboxKey
                  PromiseCreateReq OType)

structure PromiseObject where
  state     : PromiseState
  param     : Value
  value     : Value       := {}
  type      : OType
  timeoutAt : Nat
  createdAt : Nat
  settledAt : Option Nat  := none
  callbacks : List Ident     := []
  listeners : List String := []
  deriving Repr

def PromiseObject.toRecord (p : PromiseObject) (id : Ident) : PromiseRecord :=
  { id := id, state := p.state, param := p.param, value := p.value,
    type := p.type, timeoutAt := p.timeoutAt, createdAt := p.createdAt,
    settledAt := p.settledAt }

def PromiseObject.addCallback (p : PromiseObject) (awaiterId : Ident) : PromiseObject :=
  if p.callbacks.contains awaiterId then
    p
  else
    { p with callbacks := p.callbacks ++ [awaiterId] }

def PromiseObject.addListener (p : PromiseObject) (address : String) : PromiseObject :=
  if p.listeners.contains address then
    p
  else
    { p with listeners := p.listeners ++ [address] }

def PromiseObject.project (p : PromiseObject) (now : Nat) : PromiseObject :=
  if p.state == .pending ∧ p.timeoutAt ≤ now then
    if p.type == .deadline then
      { p with state := .resolved, settledAt := some p.timeoutAt }
    else
      { p with state := .rejectedTimedout, settledAt := some p.timeoutAt }
  else
    p

structure TaskObject where
  state          : TaskState
  version        : Nat
  ttl            : Option Nat    := none
  pid            : Option String := none
  leaseTimeoutAt : Option Nat    := none
  retryTimeoutAt : Option Nat    := none
  resumes        : List Ident    := []
  deriving Repr

def TaskObject.toRecord (t : TaskObject) (id : Ident) : TaskRecord :=
  { id := id, state := t.state, version := t.version,
    resumes := t.resumes.length, ttl := t.ttl, pid := t.pid }

def TaskObject.fulfill (t : TaskObject) : TaskObject :=
  { t with state := .fulfilled, pid := none, ttl := none,
           leaseTimeoutAt := none, retryTimeoutAt := none, resumes := [] }

def TaskObject.view (t : TaskObject) (p : PromiseObject) : TaskObject :=
  if p.state != .pending ∧ t.state != .fulfilled then t.fulfill else t

structure Object where
  id      : Ident
  promise : PromiseObject
  task    : Option TaskObject := none
  deriving Repr

def Object.project (o : Object) (now : Nat) : Object :=
  let p := o.promise.project now
  { o with promise := p, task := o.task.map (·.view p) }

structure ServerState where
  objects   : List Object      := []
  schedules : List Schedule    := []
  outbox    : List OutboxEntry := []
  deriving Repr

def ServerState.init : ServerState := {}

def ServerState.promises (s : ServerState) : List PromiseObject :=
  s.objects.map (·.promise)

def ServerState.tasks (s : ServerState) : List TaskObject :=
  s.objects.filterMap (·.task)

def ServerState.promise? (s : ServerState) (id : Ident) : Option PromiseObject :=
  (s.objects.find? (·.id == id)).map (·.promise)

def ServerState.task? (s : ServerState) (id : Ident) : Option TaskObject :=
  (s.objects.find? (·.id == id)).bind (·.task)

def ServerState.hasTask (s : ServerState) (id : Ident) : Bool :=
  (s.task? id).isSome

inductive Effect
  | setPromise  (id : Ident) (p : PromiseObject)
  | setTask     (id : Ident) (t : TaskObject)
  | setSchedule (s : Schedule)
  | delSchedule (id : Ident)
  | setMessage  (address : String) (msg : Message)
  deriving Repr

def Object.withPromise (id : Ident) (p : PromiseObject) : Option Object → Object
  | some o => { o with promise := p }
  | none   => { id := id, promise := p }

def Effect.apply (s : ServerState) : Effect → ServerState
  | .setPromise id p =>
      { s with objects := Object.withPromise id p (s.objects.find? (·.id == id))
                            :: s.objects.filter (·.id != id) }
  | .setTask id t =>
      { s with objects := s.objects.map fun o =>
                 if o.id == id then { o with task := some t } else o }
  | .setSchedule c => { s with schedules := c :: s.schedules.filter (·.id != c.id) }
  | .delSchedule i => { s with schedules := s.schedules.filter (·.id != i) }
  | .setMessage a m =>
      let entry := OutboxEntry.mk a m
      { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def applyAll (s : ServerState) : List Effect → ServerState
  | []      => s
  | e :: es => applyAll (e.apply s) es

structure ServerConfig where
  retryTimeout : Nat := 5000
  deriving Repr

structure Env where
  state  : ServerState
  mat    : Bool
  config : ServerConfig := {}

def H (α : Type) : Type := Env → α × List Effect

instance : Monad H where
  pure a   := fun _ => (a, [])
  bind x f := fun e =>
    let (a, w₁) := x e
    let (b, w₂) := f a e
    (b, w₁ ++ w₂)

def ask : H Env := fun e => (e, [])

def emit (f : Effect) : H Unit := fun _ => ((), [f])

def runWith (mat : Bool) (config : ServerConfig) (act : H α) (s : ServerState) :
    α × ServerState :=
  let (a, w) := act { state := s, mat := mat, config := config }
  (a, applyAll s w)

def run (mat : Bool) (act : H α) (s : ServerState) : α × ServerState :=
  runWith mat {} act s

def getObject (id : Ident) : H (Option Object) :=
  return (← ask).state.objects.find? (·.id == id)

def getSchedule (id : Ident) : H (Option Schedule) :=
  return (← ask).state.schedules.find? (·.id == id)

def setPromise (id : Ident) (p : PromiseObject) : H Unit := emit (.setPromise id p)
def setTask (id : Ident) (t : TaskObject) : H Unit := emit (.setTask id t)
def setSchedule (c : Schedule) : H Unit := emit (.setSchedule c)
def delSchedule (id : Ident) : H Unit := emit (.delSchedule id)
def setMessage (a : String) (m : Message) : H Unit := emit (.setMessage a m)

def setSettled (o : Object) (p : PromiseObject) : H Unit := do
  setPromise o.id p
  if p.state != .pending then
    match o.task with
    | some t => if t.state != .fulfilled then setTask o.id t.fulfill
    | none   => pure ()

def createPromise (req : PromiseCreateReq) (now : Nat) : H Object := do
  if req.timeoutAt > now then
    let p : PromiseObject :=
      { state := .pending, param := req.param, type := req.type,
        timeoutAt := req.timeoutAt, createdAt := now }
    setPromise req.id p
    if p.type.isRunnable then
      let due :=
        match req.delay with
        | some d => max d now
        | none => now
      let t : TaskObject := { state := .pending, version := 0, retryTimeoutAt := some due }
      setTask req.id t
      return { id := req.id, promise := p, task := some t }
    else
      return { id := req.id, promise := p }
  else
    let state :=
      if req.type == .deadline then PromiseState.resolved else PromiseState.rejectedTimedout
    let p : PromiseObject :=
      { state := state, param := req.param, type := req.type,
        timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
        settledAt := some req.timeoutAt }
    setPromise req.id p
    if p.type.isRunnable then
      let t : TaskObject := { state := .fulfilled, version := 0 }
      setTask req.id t
      return { id := req.id, promise := p, task := some t }
    else
      return { id := req.id, promise := p }

def materialise (id : Ident) (o o' : Object) : H Unit :=
  (if o'.promise.state != o.promise.state then setPromise id o'.promise else pure ()) >>=
    fun _ =>
      match o.task, o'.task with
      | some t, some u => if u.state != t.state then setTask id u else pure ()
      | _, _ => pure ()

def readObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | none => return none
  | some o =>
      let o' := o.project now
      if (← ask).mat then materialise id o o'
      return some o'

def readTaskObject (id : Ident) (now : Nat) : H (Option Object) := do
  match ← getObject id with
  | none   => return none
  | some o => if o.task.isSome then readObject id now else return none

def createIfAbsent (req : PromiseCreateReq) (now : Nat) : H Unit := do
  match ← readObject req.id now with
  | some _ => pure ()
  | none   => let _ ← createPromise req now

def withMat (mat : Bool) (act : H α) : H α := fun e => act { e with mat := mat }

def touchObject (id : Ident) (now : Nat) : H (Option Object) :=
  withMat true (readObject id now)

def viewObject (id : Ident) (now : Nat) : H (Option Object) :=
  withMat false (readObject id now)

def touchTaskObject (id : Ident) (now : Nat) : H (Option Object) :=
  withMat true (readTaskObject id now)

def viewTaskObject (id : Ident) (now : Nat) : H (Option Object) :=
  withMat false (readTaskObject id now)

end AbstractModel
