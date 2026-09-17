import impl.state

namespace Concrete

open Protocol (Ident Message PromiseState TaskState Object PromiseObject TaskObject)
open Protocol (PromiseGetReq PromiseGetRes
                  PromiseCreateReq PromiseCreateRes
                  PromiseSettleReq PromiseSettleRes
                  PromiseRegisterCallbackReq PromiseRegisterCallbackRes
                  PromiseRegisterListenerReq PromiseRegisterListenerRes
                  PromiseSearchReq PromiseSearchRes
                  TaskGetReq TaskGetRes
                  TaskCreateReq TaskCreateRes
                  TaskAcquireReq TaskAcquireRes
                  TaskFenceReq TaskFenceRes
                  TaskHeartbeatReq TaskHeartbeatRes
                  TaskSuspendReq TaskSuspendRes
                  TaskFulfillReq TaskFulfillRes
                  TaskReleaseReq TaskReleaseRes
                  TaskHaltReq TaskHaltRes
                  TaskContinueReq TaskContinueRes
                  TaskSearchReq TaskSearchRes
                  ScheduleGetReq ScheduleGetRes
                  ScheduleCreateReq ScheduleCreateRes
                  ScheduleDeleteReq ScheduleDeleteRes
                  ScheduleSearchReq ScheduleSearchRes)

def promiseGet (now : Nat) (org : Origin) (req : PromiseGetReq) : PromiseGetRes × Commands :=
  match org.get req.id now with
  | none =>
      ({ status := 404 }, { org })
  | some o =>
      ({ status := 200, promise := some (o.promise.toRecord o.id) }, { org })

def promiseCreate (now : Nat) (org : Origin) (req : PromiseCreateReq) : PromiseCreateRes × Commands :=
  match org.get req.id now with
  | some o =>
      ({ status := 200, promise := some (o.promise.toRecord o.id) }, { org })
  | none =>
      if req.timeoutAt > now then
        let p : PromiseObject :=
          { state := .pending, param := req.param, type := req.type,
            timeoutAt := req.timeoutAt, createdAt := now }
        if p.type.isRunnable then
          let due :=
            match req.delay with
            | some d =>
                max d now
            | none =>
                now
          let t : TaskObject := { state := .pending, version := 0, retryTimeoutAt := some due }
          ({ status := 200, promise := some (p.toRecord req.id) },
           { arm := [⟨req.timeoutAt, req.id, .promise⟩, ⟨due, req.id, .retry⟩],
             org := org.set ⟨req.id, p, some t⟩ })
        else
          ({ status := 200, promise := some (p.toRecord req.id) },
           { arm := [⟨req.timeoutAt, req.id, .promise⟩],
             org := org.set ⟨req.id, p, none⟩ })
      else
        let p : PromiseObject :=
          { state := if req.type == .deadline then .resolved else .rejectedTimedout,
            param := req.param, type := req.type,
            timeoutAt := req.timeoutAt, createdAt := req.timeoutAt,
            settledAt := some req.timeoutAt }
        let t : Option TaskObject :=
          if p.type.isRunnable then some { state := .fulfilled, version := 0 } else none
        ({ status := 200, promise := some (p.toRecord req.id) },
         { org := org.set ⟨req.id, p, t⟩ })

def promiseSettle (now : Nat) (org : Origin) (req : PromiseSettleReq) : PromiseSettleRes × Commands :=
  if !req.state.settable then
    ({ status := 400 }, { org })
  else
    match org.get req.id now with
    | none =>
        ({ status := 404 }, { org })
    | some o =>
        if o.promise.state == .pending then
          let p := { o.promise with state := req.state, value := req.value, settledAt := some now }
          ({ status := 200, promise := some (p.toRecord o.id) },
           { org := org.set { o with promise := p,
                                       task := o.task.map fun t =>
                                         if t.state == .fulfilled then t else t.fulfill },
             del := o.timers })
        else
          ({ status := 200, promise := some (o.promise.toRecord o.id) }, { org })

def promiseRegisterCallback (now : Nat) (org : Origin) (req : PromiseRegisterCallbackReq) : PromiseRegisterCallbackRes × Commands :=
  if req.awaited == req.awaiter ∨ !req.awaited.sameOrigin req.awaiter then
    ({ status := 400 }, { org })
  else
    match org.get req.awaited now, org.get req.awaiter now with
    | none, _ =>
        ({ status := 404 }, { org })
    | some _, none =>
        ({ status := 422 }, { org })
    | some awaited, some awaiter =>
        if !awaiter.promise.type.isRunnable ∨ !awaited.promise.type.awaitable then
          ({ status := 422 }, { org })
        else if awaited.promise.state == .pending ∧ awaiter.promise.state == .pending then
          ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) },
           { org := org.set { awaited with promise := awaited.promise.addCallback req.awaiter } })
        else
          ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) }, { org })

def promiseRegisterListener (now : Nat) (org : Origin) (req : PromiseRegisterListenerReq) : PromiseRegisterListenerRes × Commands :=
  match org.get req.awaited now with
  | none =>
      ({ status := 404 }, { org })
  | some awaited =>
      if !awaited.promise.type.awaitable then
        ({ status := 422 }, { org })
      else if awaited.promise.state == .pending then
        ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) },
         { org := org.set { awaited with promise := awaited.promise.addListener req.address } })
      else
        ({ status := 200, promise := some (awaited.promise.toRecord awaited.id) }, { org })

def promiseSearch (_now : Nat) (org : Origin) (_req : PromiseSearchReq) : PromiseSearchRes × Commands :=
  ({ status := 501 }, { org })

def taskGet (now : Nat) (org : Origin) (req : TaskGetReq) : TaskGetRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o.id, ·) with
  | none =>
      ({ status := 404 }, { org })
  | some (id, t) =>
      ({ status := 200, task := some (t.toRecord id) }, { org })

def taskCreate (now : Nat) (org : Origin) (req : TaskCreateReq) : TaskCreateRes × Commands :=
  let a := req.action
  if !a.type.isRunnable then
    ({ status := 400 }, { org })
  else
    match org.get a.id now with
    | none =>
        if a.timeoutAt > now then
          let p : PromiseObject :=
            { state := .pending, param := a.param, type := a.type,
              timeoutAt := a.timeoutAt, createdAt := now }
          let t : TaskObject :=
            { state := .acquired, version := 1, ttl := some req.ttl, pid := some req.pid,
              leaseTimeoutAt := some (now + req.ttl) }
          ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
           { arm := [⟨a.timeoutAt, a.id, .promise⟩, ⟨now + req.ttl, a.id, .lease⟩],
             org := org.set ⟨a.id, p, some t⟩ })
        else
          let p : PromiseObject :=
            { state := .rejectedTimedout, param := a.param, type := a.type,
              timeoutAt := a.timeoutAt, createdAt := a.timeoutAt, settledAt := some a.timeoutAt }
          let t : TaskObject := { state := .fulfilled, version := 0 }
          ({ status := 200, task := some (t.toRecord a.id), promise := some (p.toRecord a.id) },
           { org := org.set ⟨a.id, p, some t⟩ })
    | some o =>
        if !o.promise.type.isRunnable then
          ({ status := 422 }, { org })
        else
          match o.task with
          | none =>
              ({ status := 409 }, { org })
          | some t =>
              if t.state == .fulfilled then
                ({ status := 200, task := some (t.toRecord o.id),
                   promise := some (o.promise.toRecord o.id) }, { org })
              else if t.state == .pending then
                let t' := { t with state := .acquired, version := t.version + 1,
                                   ttl := some req.ttl, pid := some req.pid,
                                   leaseTimeoutAt := some (now + req.ttl),
                                   retryTimeoutAt := none, resumes := [] }
                ({ status := 200, task := some (t'.toRecord o.id),
                   promise := some (o.promise.toRecord o.id) },
                 { arm := [⟨now + req.ttl, o.id, .lease⟩],
                   org := org.set { o with task := some t' },
                   del := t.timers o.id })
              else
                ({ status := 409 }, { org })

def taskAcquire (now : Nat) (org : Origin) (req : TaskAcquireReq) : TaskAcquireRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, { org })
  | some (o, t) =>
      if t.state != .pending ∨ o.promise.state != .pending ∨ t.version != req.version then
        ({ status := 409 }, { org })
      else
        let t' := { t with state := .acquired, version := t.version + 1,
                           ttl := some req.ttl, pid := some req.pid,
                           leaseTimeoutAt := some (now + req.ttl),
                           retryTimeoutAt := none, resumes := [] }
        ({ status := 200, task := some (t'.toRecord o.id), promise := some (o.promise.toRecord o.id) },
         { arm := [⟨now + req.ttl, o.id, .lease⟩],
           org := org.set { o with task := some t' },
           del := t.timers o.id })

def taskFence (now : Nat) (org : Origin) (req : TaskFenceReq) : TaskFenceRes × Commands :=
  if req.action.targetId == req.id ∨ !req.action.targetId.sameOrigin req.id then
    ({ status := 400 }, { org })
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, { org })
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, { org })
        else
          match req.action with
          | .create r =>
              let (res, c) := promiseCreate now org r
              ({ status := 200, action := some (.create res) }, c)
          | .settle r =>
              let (res, c) := promiseSettle now org r
              ({ status := 200, action := some (.settle res) }, c)

def taskHeartbeat (now : Nat) (org : Origin) (req : TaskHeartbeatReq) : TaskHeartbeatRes × Commands :=
  ({ status := 200 },
   req.tasks.foldl (init := { org }) fun c ref =>
     match (org.get ref.id now).bind fun o => o.task.map (o, ·) with
     | none =>
         c
     | some (o, t) =>
         if t.state == .acquired ∧ t.version == ref.version
             ∧ t.pid == some req.pid ∧ o.promise.state == .pending then
           let lease := now + t.ttl.getD 0
           { c with
             arm := c.arm ++ (if t.leaseTimeoutAt == some lease then [] else [⟨lease, o.id, .lease⟩]),
             org := c.org.set { o with task := some { t with leaseTimeoutAt := some lease } },
             del := c.del ++ (if t.leaseTimeoutAt == some lease then [] else t.timers o.id) }
         else
           c)

def taskSuspend (now : Nat) (org : Origin) (req : TaskSuspendReq) : TaskSuspendRes × Commands :=
  let awaitedIds := req.actions.map (·.awaited)
  if req.actions.isEmpty ∨ awaitedIds.contains req.id
      ∨ awaitedIds.any (fun a => !a.sameOrigin req.id)
      ∨ awaitedIds.eraseDups.length != awaitedIds.length then
    ({ status := 400 }, { org })
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, { org })
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, { org })
        else
          let awaited := awaitedIds.map (org.get · now)
          if awaited.any (fun oa => !(oa.map (·.promise.type.awaitable)).getD false) then
            ({ status := 422 }, { org })
          else if awaited.any (fun oa => (oa.map (·.promise.state != .pending)).getD false) then
            ({ status := 300 }, { org := org.set { o with task := some { t with resumes := [] } } })
          else
            let registered := awaited.foldl (init := org) fun d oa =>
              match oa with
              | some oa =>
                  d.set { oa with promise := oa.promise.addCallback req.id }
              | none =>
                  d
            ({ status := 200 },
             { org := registered.set
                 { o with task := some { t with state := .suspended, pid := none, ttl := none,
                                                leaseTimeoutAt := none, retryTimeoutAt := none,
                                                resumes := [] } },
               del := t.timers o.id })

def taskFulfill (now : Nat) (org : Origin) (req : TaskFulfillReq) : TaskFulfillRes × Commands :=
  if !req.action.state.settable then
    ({ status := 400 }, { org })
  else
    match (org.get req.id now).bind fun o => o.task.map (o, ·) with
    | none =>
        ({ status := 404 }, { org })
    | some (o, t) =>
        if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
          ({ status := 409 }, { org })
        else
          let p := { o.promise with state := req.action.state, value := req.action.value,
                                    settledAt := some now }
          ({ status := 200, promise := some (p.toRecord o.id) },
           { org := org.set { o with promise := p,
                                       task := some (if t.state == .fulfilled then t else t.fulfill) },
             del := o.timers })

def taskRelease (now : Nat) (org : Origin) (req : TaskReleaseReq) : TaskReleaseRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, { org })
  | some (o, t) =>
      if t.state != .acquired ∨ o.promise.state != .pending ∨ t.version != req.version then
        ({ status := 409 }, { org })
      else
        ({ status := 200 },
         { arm := [⟨now, o.id, .retry⟩],
           org := org.set { o with task := some { t with state := .pending, pid := none, ttl := none,
                                                           leaseTimeoutAt := none,
                                                           retryTimeoutAt := some now } },
           del := t.timers o.id })

def taskHalt (now : Nat) (org : Origin) (req : TaskHaltReq) : TaskHaltRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, { org })
  | some (o, t) =>
      if t.state == .fulfilled then
        ({ status := 409 }, { org })
      else if t.state == .halted then
        ({ status := 200 }, { org })
      else
        ({ status := 200 },
         { org := org.set { o with task := some { t with state := .halted, pid := none, ttl := none,
                                                           leaseTimeoutAt := none,
                                                           retryTimeoutAt := none } },
           del := t.timers o.id })

def taskContinue (now : Nat) (org : Origin) (req : TaskContinueReq) : TaskContinueRes × Commands :=
  match (org.get req.id now).bind fun o => o.task.map (o, ·) with
  | none =>
      ({ status := 404 }, { org })
  | some (o, t) =>
      if t.state != .halted ∨ o.promise.state != .pending then
        ({ status := 409 }, { org })
      else
        ({ status := 200 },
         { arm := [⟨now, o.id, .retry⟩],
           org := org.set { o with task := some { t with state := .pending, retryTimeoutAt := some now } } })

def taskSearch (_now : Nat) (org : Origin) (_req : TaskSearchReq) : TaskSearchRes × Commands :=
  ({ status := 501 }, { org })

def scheduleGet (_now : Nat) (org : Origin) (_req : ScheduleGetReq) : ScheduleGetRes × Commands :=
  ({ status := 501 }, { org })

def scheduleCreate (_now : Nat) (org : Origin) (_req : ScheduleCreateReq) : ScheduleCreateRes × Commands :=
  ({ status := 501 }, { org })

def scheduleDelete (_now : Nat) (org : Origin) (_req : ScheduleDeleteReq) : ScheduleDeleteRes × Commands :=
  ({ status := 501 }, { org })

def scheduleSearch (_now : Nat) (org : Origin) (_req : ScheduleSearchReq) : ScheduleSearchRes × Commands :=
  ({ status := 501 }, { org })

end Concrete
