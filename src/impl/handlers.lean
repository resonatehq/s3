import impl.origin

namespace Impl.Handlers

open ServerModel
open AbstractModel (Object PromiseObject TaskObject ServerConfig)
open Abstract (Request Response Trigger)

def promiseGet (req : PromiseGetReq) (now : Nat) (o : Origin) (tx : Tx) : PromiseGetRes × Tx :=
  match read o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) => ({ status := 200, promise := some (ob.promise.toRecord ob.id) }, tx)

def promiseCreate (req : PromiseCreateReq) (now : Nat) (o : Origin) (tx : Tx) :
    PromiseCreateRes × Tx :=
  if req.tags.timerTargeted then ({ status := 400, promise := none }, tx) else
  match read o tx req.id now with
  | (some ob, tx) => ({ status := 200, promise := some (ob.promise.toRecord ob.id) }, tx)
  | (none, tx)    =>
      let (ob, tx) := tx.createPromise req now
      ({ status := 200, promise := some (ob.promise.toRecord ob.id) }, tx)

def promiseSettle (req : PromiseSettleReq) (now : Nat) (o : Origin) (tx : Tx) :
    PromiseSettleRes × Tx :=
  if !req.state.settable then ({ status := 400 }, tx) else
  match read o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
      if ob.promise.state == .pending then
        let p := { ob.promise with state := req.state, value := req.value, settledAt := some now }
        ({ status := 200, promise := some (p.toRecord ob.id) }, tx.settle ob p)
      else
        ({ status := 200, promise := some (ob.promise.toRecord ob.id) }, tx)

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) (o : Origin) (tx : Tx) :
    PromiseRegisterCallbackRes × Tx :=
  if req.awaited == req.awaiter then ({ status := 400 }, tx) else
  if !req.awaited.sameOrigin req.awaiter then ({ status := 400 }, tx) else
  match read o tx req.awaited now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some oa, tx) =>
  match read o tx req.awaiter now with
  | (none, tx)    => ({ status := 422 }, tx)
  | (some ow, tx) =>
      if ow.promise.otype != .runnable then ({ status := 422 }, tx) else
      if !oa.promise.otype.awaitable then ({ status := 422 }, tx) else
      if oa.promise.state == .pending then
        let tx := if ow.promise.state == .pending
                  then tx.putPromise oa.id (oa.promise.addCallback req.awaiter) else tx
        ({ status := 200, promise := some (oa.promise.toRecord oa.id) }, tx)
      else
        ({ status := 200, promise := some (oa.promise.toRecord oa.id) }, tx)

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) (o : Origin) (tx : Tx) :
    PromiseRegisterListenerRes × Tx :=
  match read o tx req.awaited now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some oa, tx) =>
      if !oa.promise.otype.awaitable then ({ status := 422 }, tx) else
      if oa.promise.state == .pending then
        ({ status := 200, promise := some (oa.promise.toRecord oa.id) },
         tx.putPromise oa.id (oa.promise.addListener req.address))
      else
        ({ status := 200, promise := some (oa.promise.toRecord oa.id) }, tx)

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) (_o : Origin) (tx : Tx) :
    PromiseSearchRes × Tx :=
  ({ status := 501 }, tx)

def taskGet (req : TaskGetReq) (now : Nat) (o : Origin) (tx : Tx) : TaskGetRes × Tx :=
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t => ({ status := 200, task := some (t.toRecord ob.id) }, tx)

def taskCreate (req : TaskCreateReq) (now : Nat) (o : Origin) (tx : Tx) : TaskCreateRes × Tx :=
  let a := req.action
  if a.tags.otype != .runnable ∨ a.tags.timerTargeted then ({ status := 400 }, tx) else
  match read o tx a.id now with
  | (none, tx) =>
      if a.timeoutAt > now then
        let p : PromiseObject :=
          { state := .pending, param := a.param, tags := a.tags,
            timeoutAt := a.timeoutAt, createdAt := now }
        let tx := tx.putPromise a.id p
        let t : TaskObject :=
          { state := .acquired, version := 1, ttl := some req.ttl, pid := some req.pid,
            leaseTimeoutAt := some (now + req.ttl) }
        ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
         tx.putTask a.id t)
      else
        let st := PromiseState.rejectedTimedout
        let p : PromiseObject :=
          { state := st, param := a.param, tags := a.tags,
            timeoutAt := a.timeoutAt, createdAt := a.timeoutAt, settledAt := some a.timeoutAt }
        let tx := tx.putPromise a.id p
        let t : TaskObject := { state := .fulfilled, version := 0 }
        ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
         tx.putTask a.id t)
  | (some ob, tx) =>
      if ob.promise.otype != .runnable then ({ status := 422 }, tx) else
      match ob.task with
      | none   => ({ status := 409 }, tx)
      | some t =>
          if t.state == .fulfilled then
            ({ status := 200, task := some (t.toRecord ob.id), promise := some (ob.promise.toRecord ob.id) }, tx)
          else if t.state == .pending then
            let t := { t with state := .acquired, version := t.version + 1,
                              ttl := some req.ttl, pid := some req.pid,
                              leaseTimeoutAt := some (now + req.ttl),
                              retryTimeoutAt := none, resumes := [] }
            ({ status := 200, task := some (t.toRecord ob.id), promise := some (ob.promise.toRecord ob.id) },
             tx.putTask ob.id t)
          else
            ({ status := 409 }, tx)

def taskAcquire (req : TaskAcquireReq) (now : Nat) (o : Origin) (tx : Tx) : TaskAcquireRes × Tx :=
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .pending then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      if t.version != req.version then ({ status := 409 }, tx) else
      let t := { t with state := .acquired, version := t.version + 1,
                        ttl := some req.ttl, pid := some req.pid,
                        leaseTimeoutAt := some (now + req.ttl),
                        retryTimeoutAt := none, resumes := [] }
      ({ status := 200, task := some (t.toRecord ob.id), promise := some (ob.promise.toRecord ob.id) },
       tx.putTask ob.id t)

def taskFence (req : TaskFenceReq) (now : Nat) (o : Origin) (tx : Tx) : TaskFenceRes × Tx :=
  if req.action.targetId == req.id then ({ status := 400 }, tx) else
  if !req.action.targetId.sameOrigin req.id then ({ status := 400 }, tx) else
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .acquired then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      if t.version != req.version then ({ status := 409 }, tx) else
      match req.action with
      | .create r =>
          let (res, tx) := promiseCreate r now o tx
          ({ status := 200, action := some (.create res) }, tx)
      | .settle r =>
          let (res, tx) := promiseSettle r now o tx
          ({ status := 200, action := some (.settle res) }, tx)

def heartbeatOne (pid : String) (ref : TaskRef) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match readTask o tx ref.id now with
  | (none, tx)    => tx
  | (some ob, tx) =>
  match ob.task with
  | none   => tx
  | some t =>
      if t.state == .acquired ∧ t.version == ref.version
          ∧ t.pid == some pid ∧ ob.promise.state == .pending then
        tx.putTask ob.id { t with leaseTimeoutAt := some (now + t.ttl.getD 0) }
      else tx

def heartbeatAll (pid : String) (now : Nat) (o : Origin) : List TaskRef → Tx → Tx
  | [],          tx => tx
  | ref :: refs, tx => heartbeatAll pid now o refs (heartbeatOne pid ref now o tx)

def taskHeartbeat (req : TaskHeartbeatReq) (now : Nat) (o : Origin) (tx : Tx) :
    TaskHeartbeatRes × Tx :=
  ({ status := 200 }, heartbeatAll req.pid now o req.tasks tx)

def checkAwaited (now : Nat) (o : Origin) : List PromiseRegisterCallbackReq → Tx → Option Bool × Tx
  | [],             tx => (some false, tx)
  | action :: rest, tx =>
      match read o tx action.awaited now with
      | (none, tx)    => (none, tx)
      | (some oa, tx) =>
          if !oa.promise.otype.awaitable then (none, tx) else
          match checkAwaited now o rest tx with
          | (none, tx)         => (none, tx)
          | (some settled, tx) => (some (settled || oa.promise.state != .pending), tx)

def registerAwaited (awaiter : Ident) (now : Nat) (o : Origin) :
    List PromiseRegisterCallbackReq → Tx → Tx
  | [],             tx => tx
  | action :: rest, tx =>
      match read o tx action.awaited now with
      | (some oa, tx) => registerAwaited awaiter now o rest (tx.putPromise oa.id (oa.promise.addCallback awaiter))
      | (none, tx)    => registerAwaited awaiter now o rest tx

def taskSuspend (req : TaskSuspendReq) (now : Nat) (o : Origin) (tx : Tx) : TaskSuspendRes × Tx :=
  if req.actions.isEmpty then ({ status := 400 }, tx) else
  if req.actions.any (·.awaited == req.id) then ({ status := 400 }, tx) else
  if req.actions.any (fun a => !a.awaited.sameOrigin req.id) then ({ status := 400 }, tx) else
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then ({ status := 400 }, tx) else
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .acquired then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      if t.version != req.version then ({ status := 409 }, tx) else
      match checkAwaited now o req.actions tx with
      | (none, tx)       => ({ status := 422 }, tx)
      | (some true, tx)  => ({ status := 300 }, tx.putTask ob.id { t with resumes := [] })
      | (some false, tx) =>
          let tx := registerAwaited req.id now o req.actions tx
          ({ status := 200 },
           tx.putTask ob.id { t with state := .suspended, pid := none, ttl := none,
                                     leaseTimeoutAt := none, retryTimeoutAt := none, resumes := [] })

def taskFulfill (req : TaskFulfillReq) (now : Nat) (o : Origin) (tx : Tx) : TaskFulfillRes × Tx :=
  if !req.action.state.settable then ({ status := 400 }, tx) else
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .acquired then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      if t.version != req.version then ({ status := 409 }, tx) else
      let p := { ob.promise with state := req.action.state, value := req.action.value,
                                 settledAt := some now }
      ({ status := 200, promise := some (p.toRecord ob.id) }, tx.settle ob p)

def taskRelease (req : TaskReleaseReq) (now : Nat) (o : Origin) (tx : Tx) : TaskReleaseRes × Tx :=
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .acquired then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      if t.version != req.version then ({ status := 409 }, tx) else
      ({ status := 200 },
       tx.putTask ob.id { t with state := .pending, pid := none, ttl := none,
                                 leaseTimeoutAt := none, retryTimeoutAt := some now })

def taskHalt (req : TaskHaltReq) (now : Nat) (o : Origin) (tx : Tx) : TaskHaltRes × Tx :=
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state == .fulfilled then ({ status := 409 }, tx) else
      if t.state == .halted then ({ status := 200 }, tx) else
      ({ status := 200 },
       tx.putTask ob.id { t with state := .halted, pid := none, ttl := none,
                                 leaseTimeoutAt := none, retryTimeoutAt := none })

def taskContinue (req : TaskContinueReq) (now : Nat) (o : Origin) (tx : Tx) : TaskContinueRes × Tx :=
  match readTask o tx req.id now with
  | (none, tx)    => ({ status := 404 }, tx)
  | (some ob, tx) =>
  match ob.task with
  | none   => ({ status := 404 }, tx)
  | some t =>
      if t.state != .halted then ({ status := 409 }, tx) else
      if ob.promise.state != .pending then ({ status := 409 }, tx) else
      ({ status := 200 }, tx.putTask ob.id { t with state := .pending, retryTimeoutAt := some now })

def taskSearch (_req : TaskSearchReq) (_now : Nat) (_o : Origin) (tx : Tx) : TaskSearchRes × Tx :=
  ({ status := 501 }, tx)

def promiseTimeout (req : PromiseTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  (read o tx req.id now).2

def resumeOne (awaited awaiter : Ident) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match readTask o tx awaiter now with
  | (none, tx)    => tx
  | (some ob, tx) =>
  match ob.task with
  | none   => tx
  | some t =>
      match t.state with
      | .suspended =>
          tx.putTask ob.id { t with state := .pending, resumes := [awaited], retryTimeoutAt := some now }
      | .pending | .acquired | .halted =>
          if !(t.resumes.contains awaited) then
            tx.putTask ob.id { t with resumes := t.resumes ++ [awaited] }
          else tx
      | .fulfilled => tx

def callback (req : PromiseRegisterCallbackReq) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match read o tx req.awaited now with
  | (none, tx)    => tx
  | (some ob, tx) =>
      if ob.promise.state == .pending then tx
      else if ob.promise.callbacks.contains req.awaiter then
        let tx := tx.putPromise ob.id { ob.promise with
                                        callbacks := ob.promise.callbacks.filter (· != req.awaiter) }
        resumeOne ob.id req.awaiter now o tx
      else tx

def listener (req : PromiseRegisterListenerReq) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match read o tx req.awaited now with
  | (none, tx)    => tx
  | (some ob, tx) =>
      if ob.promise.state == .pending then tx
      else if ob.promise.listeners.contains req.address then
        let tx := tx.putPromise ob.id { ob.promise with
                                        listeners := ob.promise.listeners.filter (· != req.address) }
        tx.send req.address (.unblock (ob.promise.toRecord ob.id))
      else tx

def leaseTimeout (req : TaskLeaseTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match viewTask o req.id now with
  | none    => tx
  | some ob =>
  match ob.task with
  | none   => tx
  | some t =>
      match t.leaseTimeoutAt with
      | none          => tx
      | some deadline =>
          if t.state == .acquired ∧ deadline ≤ now then
            if ob.promise.state == .pending then
              tx.putTask ob.id { t with state := .pending, pid := none, ttl := none,
                                        leaseTimeoutAt := none, retryTimeoutAt := some now }
            else tx
          else tx

def retryTimeout (req : TaskRetryTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) : Tx :=
  match viewTask o req.id now with
  | none    => tx
  | some ob =>
  match ob.task with
  | none   => tx
  | some t =>
      match t.retryTimeoutAt with
      | none     => tx
      | some due =>
          if t.state == .pending ∧ due ≤ now then
            if ob.promise.state == .pending then
              let tx := tx.putTask ob.id
                { t with retryTimeoutAt := some (now + ({} : ServerConfig).retryTimeout) }
              tx.send ((ob.promise.tags.get? "resonate:target").getD "") (.execute ob.id t.version)
            else tx
          else tx

end Impl.Handlers

namespace Impl.Handle

open ServerModel
open Abstract (Request Response Trigger)

def run (f : Tx → α × Tx) (o : Origin) : α × Commit :=
  let (a, tx) := f (Tx.start o)
  (a, tx.commit o)

def external (req : Request) (now : Nat) (o : Origin) : Response × Commit :=
  match req with
  | .promiseGet              r => run (fun tx => let (a, tx) := Handlers.promiseGet r now o tx; (Response.promiseGet a, tx)) o
  | .promiseCreate           r => run (fun tx => let (a, tx) := Handlers.promiseCreate r now o tx; (Response.promiseCreate a, tx)) o
  | .promiseSettle           r => run (fun tx => let (a, tx) := Handlers.promiseSettle r now o tx; (Response.promiseSettle a, tx)) o
  | .promiseRegisterCallback r => run (fun tx => let (a, tx) := Handlers.promiseRegisterCallback r now o tx; (Response.promiseRegisterCallback a, tx)) o
  | .promiseRegisterListener r => run (fun tx => let (a, tx) := Handlers.promiseRegisterListener r now o tx; (Response.promiseRegisterListener a, tx)) o
  | .promiseSearch           r => run (fun tx => let (a, tx) := Handlers.promiseSearch r now o tx; (Response.promiseSearch a, tx)) o
  | .scheduleGet             _ => run (fun tx => (Response.scheduleGet { status := 501 }, tx)) o
  | .scheduleCreate          _ => run (fun tx => (Response.scheduleCreate { status := 501 }, tx)) o
  | .scheduleDelete          _ => run (fun tx => (Response.scheduleDelete { status := 501 }, tx)) o
  | .scheduleSearch          _ => run (fun tx => (Response.scheduleSearch { status := 501 }, tx)) o
  | .taskGet                 r => run (fun tx => let (a, tx) := Handlers.taskGet r now o tx; (Response.taskGet a, tx)) o
  | .taskCreate              r => run (fun tx => let (a, tx) := Handlers.taskCreate r now o tx; (Response.taskCreate a, tx)) o
  | .taskAcquire             r => run (fun tx => let (a, tx) := Handlers.taskAcquire r now o tx; (Response.taskAcquire a, tx)) o
  | .taskFence               r => run (fun tx => let (a, tx) := Handlers.taskFence r now o tx; (Response.taskFence a, tx)) o
  | .taskHeartbeat           r => run (fun tx => let (a, tx) := Handlers.taskHeartbeat r now o tx; (Response.taskHeartbeat a, tx)) o
  | .taskSuspend             r => run (fun tx => let (a, tx) := Handlers.taskSuspend r now o tx; (Response.taskSuspend a, tx)) o
  | .taskFulfill             r => run (fun tx => let (a, tx) := Handlers.taskFulfill r now o tx; (Response.taskFulfill a, tx)) o
  | .taskRelease             r => run (fun tx => let (a, tx) := Handlers.taskRelease r now o tx; (Response.taskRelease a, tx)) o
  | .taskHalt                r => run (fun tx => let (a, tx) := Handlers.taskHalt r now o tx; (Response.taskHalt a, tx)) o
  | .taskContinue            r => run (fun tx => let (a, tx) := Handlers.taskContinue r now o tx; (Response.taskContinue a, tx)) o
  | .taskSearch              r => run (fun tx => let (a, tx) := Handlers.taskSearch r now o tx; (Response.taskSearch a, tx)) o

def trigger (trg : Trigger) (now : Nat) (o : Origin) : Commit :=
  match trg with
  | .promiseTimeout   r => (Handlers.promiseTimeout r now o (Tx.start o)).commit o
  | .callback         r => (Handlers.callback r now o (Tx.start o)).commit o
  | .listener         r => (Handlers.listener r now o (Tx.start o)).commit o
  | .taskLeaseTimeout r => (Handlers.leaseTimeout r now o (Tx.start o)).commit o
  | .taskRetryTimeout r => (Handlers.retryTimeout r now o (Tx.start o)).commit o
  | .scheduleTimeout  _ => (Tx.start o).commit o

end Impl.Handle
