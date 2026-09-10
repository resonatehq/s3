import impl.frame

namespace Equiv

open ServerModel AbstractModel
open Impl (Origin Tx)

def env (o : Origin) : AbstractModel.Env := { state := o.toState, mat := true }

def Tx.apply : Tx → List Effect → Tx
  | tx, []                     => tx
  | tx, .setPromise id p :: fx => Tx.apply (tx.putPromise id p) fx
  | tx, .setTask id t :: fx    => Tx.apply (tx.putTask id t) fx
  | tx, .setMessage a m :: fx  => Tx.apply (tx.send a m) fx
  | tx, .setSchedule _ :: fx   => Tx.apply tx fx
  | tx, .delSchedule _ :: fx   => Tx.apply tx fx

theorem Tx.apply_append (tx : Tx) (a b : List Effect) :
    Tx.apply tx (a ++ b) = Tx.apply (Tx.apply tx a) b := by
  induction a generalizing tx with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.cons_append, Tx.apply, ih]

def liftH (act : H α) (o : Origin) (tx : Tx) : α × Tx :=
  ((act (env o)).1, Tx.apply tx (act (env o)).2)

theorem liftH_pure (a : α) (o : Origin) (tx : Tx) : liftH (pure a : H α) o tx = (a, tx) := rfl

theorem liftH_bind (x : H α) (f : α → H β) (o : Origin) (tx : Tx) :
    liftH (x >>= f) o tx = liftH (f (liftH x o tx).1) o (liftH x o tx).2 := by
  simp only [liftH, Frame.bind_apply, Tx.apply_append]

theorem liftH_map (g : α → β) (x : H α) (o : Origin) (tx : Tx) :
    liftH (g <$> x) o tx = (g (liftH x o tx).1, (liftH x o tx).2) := by
  rw [Frame.map_eq, liftH_bind]; rfl

theorem liftH_ite {c : Prop} [Decidable c] (a b : H α) (o : Origin) (tx : Tx) :
    liftH (if c then a else b) o tx = if c then liftH a o tx else liftH b o tx := by
  split <;> rfl

theorem liftH_setPromise (id : Ident) (p : PromiseObject) (o : Origin) (tx : Tx) :
    liftH (setPromise id p) o tx = ((), tx.putPromise id p) := rfl

theorem liftH_setTask (id : Ident) (t : TaskObject) (o : Origin) (tx : Tx) :
    liftH (setTask id t) o tx = ((), tx.putTask id t) := rfl

theorem liftH_setMessage (a : String) (m : Message) (o : Origin) (tx : Tx) :
    liftH (setMessage a m) o tx = ((), tx.send a m) := rfl

theorem liftH_getObject (id : Ident) (o : Origin) (tx : Tx) :
    liftH (getObject id) o tx = (o.find? id, tx) := rfl

theorem liftH_ask (o : Origin) (tx : Tx) : liftH ask o tx = (env o, tx) := rfl

theorem liftH_withMat_true (act : H α) (o : Origin) (tx : Tx) :
    liftH (withMat true act) o tx = liftH act o tx := rfl

theorem fst_ite {c : Prop} [Decidable c] (x y : α × β) : (if c then x else y).1 = if c then x.1 else y.1 := by
  split <;> rfl

theorem snd_ite {c : Prop} [Decidable c] (x y : α × β) : (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

theorem liftH_materialise (id : Ident) (ob ob' : Object) (o : Origin) (tx : Tx) :
    liftH (materialise id ob ob') o tx = ((), tx.materialise id ob ob') := by
  unfold AbstractModel.materialise Tx.materialise
  simp only [liftH_bind, liftH_ite, liftH_setPromise, liftH_pure, snd_ite]
  cases ob.task <;> cases ob'.task
  all_goals first
    | rfl
    | (simp only [liftH_ite, liftH_setTask, liftH_pure]; split <;> rfl)

theorem liftH_readObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (readObject id now) o tx = Impl.read o tx id now := by
  unfold AbstractModel.readObject Impl.read
  simp only [liftH_bind, liftH_getObject]
  cases o.find? id with
  | none => rfl
  | some ob =>
    simp only [liftH_bind, liftH_ask, env, ↓reduceIte, Frame.pure_bind, liftH_materialise, liftH_pure]

theorem liftH_readTaskObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (readTaskObject id now) o tx = Impl.readTask o tx id now := by
  unfold AbstractModel.readTaskObject Impl.readTask
  simp only [liftH_bind, liftH_getObject]
  cases o.find? id with
  | none => rfl
  | some ob =>
    simp only
    split
    · exact liftH_readObject id now o tx
    · rfl

theorem liftH_touchObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (touchObject id now) o tx = Impl.read o tx id now := liftH_readObject id now o tx

theorem liftH_touchTaskObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (touchTaskObject id now) o tx = Impl.readTask o tx id now := liftH_readTaskObject id now o tx

theorem liftH_viewObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (viewObject id now) o tx = (Impl.view o id now, tx) := by
  simp only [liftH, AbstractModel.viewObject, Frame.withMat_apply, Frame.readObject_apply,
    Frame.getObject_apply, Impl.view, Impl.Origin.find?, env, Origin.toState]
  cases o.objects.find? (·.id == id) <;> rfl

theorem liftH_viewTaskObject (id : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (viewTaskObject id now) o tx = (Impl.viewTask o id now, tx) := by
  simp only [liftH, AbstractModel.viewTaskObject, Frame.withMat_apply, Frame.readTaskObject_apply,
    Frame.readObject_apply, Frame.getObject_apply, Impl.viewTask, Impl.view, Impl.Origin.find?, env,
    Origin.toState]
  cases o.objects.find? (·.id == id) with
  | none => rfl
  | some ob =>
    simp only
    split <;> rfl

theorem liftH_createPromise (req : PromiseCreateReq) (now : Nat) (o : Origin) (tx : Tx) :
    liftH (createPromise req now) o tx = tx.createPromise req now := by
  unfold AbstractModel.createPromise Tx.createPromise
  simp only [liftH_ite, liftH_bind, liftH_setPromise, liftH_setTask, liftH_pure]
  split <;> split <;> rfl

theorem liftH_setSettled (ob : Object) (p : PromiseObject) (o : Origin) (tx : Tx) :
    liftH (setSettled ob p) o tx = ((), tx.settle ob p) := by
  rw [Frame.setSettled_eq]
  unfold Tx.settle
  simp only [liftH_bind, liftH_setPromise, liftH_ite]
  split
  · cases ob.task
    · rfl
    · simp only [liftH_ite, liftH_setTask, liftH_pure]; split <;> rfl
  · rfl

section Handlers

open Impl.Handlers

theorem promiseGet_eq (req : PromiseGetReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseGet req now o tx = liftH (AbstractModel.promiseGet req now) o tx := by
  unfold Impl.Handlers.promiseGet AbstractModel.promiseGet
  simp only [liftH_bind, liftH_readObject]
  rcases Impl.read o tx req.id now with ⟨a, tx'⟩
  cases a <;> rfl

theorem promiseCreate_eq (req : PromiseCreateReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseCreate req now o tx = liftH (AbstractModel.promiseCreate req now) o tx := by
  unfold Impl.Handlers.promiseCreate AbstractModel.promiseCreate
  simp only [Frame.pure_bind, liftH_ite, liftH_bind, liftH_readObject, liftH_pure]
  split
  · rfl
  · rcases Impl.read o tx req.id now with ⟨a, tx'⟩
    cases a
    · simp only [liftH_bind, liftH_createPromise, liftH_pure]
    · rfl

theorem promiseSettle_eq (req : PromiseSettleReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseSettle req now o tx = liftH (AbstractModel.promiseSettle req now) o tx := by
  unfold Impl.Handlers.promiseSettle AbstractModel.promiseSettle
  simp only [Frame.pure_bind, liftH_ite, liftH_bind, liftH_readObject, liftH_pure]
  split
  · rfl
  · rcases Impl.read o tx req.id now with ⟨a, tx'⟩
    cases a
    · rfl
    · simp only [liftH_ite, liftH_bind, liftH_setSettled, liftH_pure]
      try (split <;> rfl)

syntax "equiv_simp" : tactic
macro_rules
  | `(tactic| equiv_simp) => `(tactic| simp only [*, Frame.pure_bind, liftH_ite, liftH_bind, liftH_pure,
      liftH_map, liftH_setTask, liftH_setPromise, liftH_setMessage, liftH_setSettled, liftH_createPromise,
      liftH_readObject, liftH_readTaskObject, liftH_touchObject, liftH_touchTaskObject,
      liftH_viewObject, liftH_viewTaskObject, liftH_ask, snd_ite, fst_ite])

syntax "equiv_finish" : tactic
macro_rules
  | `(tactic| equiv_finish) => `(tactic| repeat' (first | rfl | (split <;> (try equiv_simp))))

theorem promiseRegisterCallback_eq (req : PromiseRegisterCallbackReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseRegisterCallback req now o tx = liftH (AbstractModel.promiseRegisterCallback req now) o tx := by
  unfold Impl.Handlers.promiseRegisterCallback AbstractModel.promiseRegisterCallback
  equiv_simp; equiv_finish

theorem promiseRegisterListener_eq (req : PromiseRegisterListenerReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseRegisterListener req now o tx = liftH (AbstractModel.promiseRegisterListener req now) o tx := by
  unfold Impl.Handlers.promiseRegisterListener AbstractModel.promiseRegisterListener
  equiv_simp; equiv_finish

theorem promiseSearch_eq (req : PromiseSearchReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseSearch req now o tx = liftH (AbstractModel.promiseSearch req now) o tx := rfl

theorem taskGet_eq (req : TaskGetReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskGet req now o tx = liftH (AbstractModel.taskGet req now) o tx := by
  unfold Impl.Handlers.taskGet AbstractModel.taskGet
  equiv_simp; equiv_finish

theorem taskCreate_eq (req : TaskCreateReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskCreate req now o tx = liftH (AbstractModel.taskCreate req now) o tx := by
  unfold Impl.Handlers.taskCreate AbstractModel.taskCreate
  equiv_simp; equiv_finish

theorem taskAcquire_eq (req : TaskAcquireReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskAcquire req now o tx = liftH (AbstractModel.taskAcquire req now) o tx := by
  unfold Impl.Handlers.taskAcquire AbstractModel.taskAcquire
  equiv_simp; equiv_finish

theorem taskFence_eq (req : TaskFenceReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskFence req now o tx = liftH (AbstractModel.taskFence req now) o tx := by
  unfold Impl.Handlers.taskFence AbstractModel.taskFence
  equiv_simp
  simp only [promiseCreate_eq, promiseSettle_eq]
  equiv_finish

theorem heartbeatOne_eq (pid : String) (ref : TaskRef) (now : Nat) (o : Origin) (tx : Tx) :
    heartbeatOne pid ref now o tx = (liftH (AbstractModel.heartbeatOne pid ref now) o tx).2 := by
  unfold Impl.Handlers.heartbeatOne AbstractModel.heartbeatOne
  equiv_simp; equiv_finish

theorem heartbeatAll_eq (pid : String) (now : Nat) (o : Origin) :
    ∀ (refs : List TaskRef) (tx : Tx),
      heartbeatAll pid now o refs tx = (liftH (AbstractModel.heartbeatAll pid now refs) o tx).2
  | [], tx => by rw [AbstractModel.heartbeatAll]; rfl
  | ref :: refs, tx => by
      rw [AbstractModel.heartbeatAll]
      simp only [Impl.Handlers.heartbeatAll, liftH_bind, heartbeatOne_eq]
      exact heartbeatAll_eq pid now o refs _

theorem taskHeartbeat_eq (req : TaskHeartbeatReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskHeartbeat req now o tx = liftH (AbstractModel.taskHeartbeat req now) o tx := by
  unfold Impl.Handlers.taskHeartbeat AbstractModel.taskHeartbeat
  simp only [liftH_bind, liftH_pure, heartbeatAll_eq]

theorem checkAwaited_eq (now : Nat) (o : Origin) :
    ∀ (actions : List PromiseRegisterCallbackReq) (tx : Tx),
      checkAwaited now o actions tx = liftH (AbstractModel.checkAwaited now actions) o tx
  | [], tx => by rw [AbstractModel.checkAwaited]; rfl
  | action :: rest, tx => by
      rw [AbstractModel.checkAwaited]
      simp only [Impl.Handlers.checkAwaited, liftH_bind, liftH_readObject]
      rcases Impl.read o tx action.awaited now with ⟨a, tx'⟩
      cases a
      · rfl
      · simp only [liftH_ite, liftH_pure, liftH_bind, checkAwaited_eq now o rest]
        split
        · rfl
        · rcases liftH (AbstractModel.checkAwaited now rest) o tx' with ⟨b, tx''⟩
          cases b <;> rfl

theorem registerAwaited_eq (awaiter : Ident) (now : Nat) (o : Origin) :
    ∀ (actions : List PromiseRegisterCallbackReq) (tx : Tx),
      registerAwaited awaiter now o actions tx =
        (liftH (AbstractModel.registerAwaited awaiter now actions) o tx).2
  | [], tx => by rw [AbstractModel.registerAwaited]; rfl
  | action :: rest, tx => by
      rw [AbstractModel.registerAwaited]
      simp only [Impl.Handlers.registerAwaited, Frame.pure_bind, liftH_bind, liftH_readObject]
      rcases Impl.read o tx action.awaited now with ⟨a, tx'⟩
      cases a
      · exact registerAwaited_eq awaiter now o rest tx'
      · exact registerAwaited_eq awaiter now o rest _

theorem taskSuspend_eq (req : TaskSuspendReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskSuspend req now o tx = liftH (AbstractModel.taskSuspend req now) o tx := by
  unfold Impl.Handlers.taskSuspend AbstractModel.taskSuspend
  equiv_simp
  simp only [checkAwaited_eq, registerAwaited_eq]
  equiv_finish

theorem taskFulfill_eq (req : TaskFulfillReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskFulfill req now o tx = liftH (AbstractModel.taskFulfill req now) o tx := by
  unfold Impl.Handlers.taskFulfill AbstractModel.taskFulfill
  equiv_simp; equiv_finish

theorem taskRelease_eq (req : TaskReleaseReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskRelease req now o tx = liftH (AbstractModel.taskRelease req now) o tx := by
  unfold Impl.Handlers.taskRelease AbstractModel.taskRelease
  equiv_simp; equiv_finish

theorem taskHalt_eq (req : TaskHaltReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskHalt req now o tx = liftH (AbstractModel.taskHalt req now) o tx := by
  unfold Impl.Handlers.taskHalt AbstractModel.taskHalt
  equiv_simp; equiv_finish

theorem taskContinue_eq (req : TaskContinueReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskContinue req now o tx = liftH (AbstractModel.taskContinue req now) o tx := by
  unfold Impl.Handlers.taskContinue AbstractModel.taskContinue
  equiv_simp; equiv_finish

theorem taskSearch_eq (req : TaskSearchReq) (now : Nat) (o : Origin) (tx : Tx) :
    taskSearch req now o tx = liftH (AbstractModel.taskSearch req now) o tx := rfl

open AbstractModel.Internal

theorem promiseTimeout_eq (req : PromiseTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) :
    promiseTimeout req now o tx = (liftH (processPromiseTimeout req now) o tx).2 := by
  unfold Impl.Handlers.promiseTimeout AbstractModel.Internal.processPromiseTimeout
  simp only [liftH_bind, liftH_touchObject, liftH_pure]

theorem resumeOne_eq (awaited awaiter : Ident) (now : Nat) (o : Origin) (tx : Tx) :
    resumeOne awaited awaiter now o tx = (liftH (AbstractModel.Internal.resumeOne awaited awaiter now) o tx).2 := by
  unfold Impl.Handlers.resumeOne AbstractModel.Internal.resumeOne
  equiv_simp; equiv_finish

theorem callback_eq (req : PromiseRegisterCallbackReq) (now : Nat) (o : Origin) (tx : Tx) :
    callback req now o tx = (liftH (processCallback req now) o tx).2 := by
  unfold Impl.Handlers.callback AbstractModel.Internal.processCallback
  equiv_simp
  simp only [resumeOne_eq]
  equiv_finish

theorem listener_eq (req : PromiseRegisterListenerReq) (now : Nat) (o : Origin) (tx : Tx) :
    listener req now o tx = (liftH (processListener req now) o tx).2 := by
  unfold Impl.Handlers.listener AbstractModel.Internal.processListener
  equiv_simp; equiv_finish

theorem leaseTimeout_eq (req : TaskLeaseTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) :
    leaseTimeout req now o tx = (liftH (processLeaseTimeout req now) o tx).2 := by
  unfold Impl.Handlers.leaseTimeout AbstractModel.Internal.processLeaseTimeout
  equiv_simp; equiv_finish

theorem retryTimeout_eq (req : TaskRetryTimeoutReq) (now : Nat) (o : Origin) (tx : Tx) :
    retryTimeout req now o tx = (liftH (processRetryTimeout req now) o tx).2 := by
  unfold Impl.Handlers.retryTimeout AbstractModel.Internal.processRetryTimeout
  equiv_simp; equiv_finish

end Handlers

theorem objects_apply_congr {s s' : ServerState} (h : s.objects = s'.objects) (e : Effect) :
    (e.apply s).objects = (e.apply s').objects := by
  cases e <;> simp only [Effect.apply, h]

theorem objects_applyAll_congr {s s' : ServerState} (h : s.objects = s'.objects) (fx : List Effect) :
    (applyAll s fx).objects = (applyAll s' fx).objects := by
  induction fx generalizing s s' with
  | nil => exact h
  | cons e es ih => exact ih (objects_apply_congr h e)

theorem Tx.apply_origin (tx : Tx) (fx : List Effect) :
    (Tx.apply tx fx).origin = ⟨(applyAll tx.origin.toState fx).objects⟩ := by
  induction fx generalizing tx with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | setPromise id p => simp only [Tx.apply, applyAll, ih]; rfl
    | setTask id t => simp only [Tx.apply, applyAll, ih]; rfl
    | setMessage a m =>
      simp only [Tx.apply, applyAll, ih]
      try exact congrArg Origin.mk (objects_applyAll_congr (s := tx.origin.toState)
        (s' := Effect.apply tx.origin.toState (Effect.setMessage a m)) rfl es)
    | setSchedule c =>
      simp only [Tx.apply, applyAll, ih]
      try exact congrArg Origin.mk (objects_applyAll_congr (s := tx.origin.toState)
        (s' := Effect.apply tx.origin.toState (Effect.setSchedule c)) rfl es)
    | delSchedule i =>
      simp only [Tx.apply, applyAll, ih]
      try exact congrArg Origin.mk (objects_applyAll_congr (s := tx.origin.toState)
        (s' := Effect.apply tx.origin.toState (Effect.delSchedule i)) rfl es)

theorem Tx.apply_sends (tx : Tx) (fx : List Effect) :
    (Tx.apply tx fx).sends = tx.sends ++ Impl.sendsOf fx := by
  induction fx generalizing tx with
  | nil => simp [Tx.apply, Impl.sendsOf]
  | cons e es ih =>
    cases e with
    | setPromise id p => simp only [Tx.apply, Impl.sendsOf, ih]; rfl
    | setTask id t => simp only [Tx.apply, Impl.sendsOf, ih]; rfl
    | setMessage a m => simp only [Tx.apply, Impl.sendsOf, ih, Tx.send, List.append_assoc, List.singleton_append]
    | setSchedule c => simp only [Tx.apply, Impl.sendsOf, ih]
    | delSchedule i => simp only [Tx.apply, Impl.sendsOf, ih]

def specStep (ev : Abstract.Event) (now : Nat) (o : Origin) :
    Abstract.Reply × Origin × List (String × Message) :=
  ((Abstract.handle ev now (env o)).1,
   ⟨(applyAll o.toState (Abstract.handle ev now (env o)).2).objects⟩,
   Impl.sendsOf (Abstract.handle ev now (env o)).2)

theorem Tx.eta (tx : Tx) : tx = { origin := tx.origin, sends := tx.sends } := rfl

theorem Tx.apply_start (o : Origin) (fx : List Effect) :
    Tx.apply (Tx.start o) fx =
      { origin := ⟨(applyAll o.toState fx).objects⟩, sends := Impl.sendsOf fx } := by
  have h1 := Tx.apply_origin (Tx.start o) fx
  have h2 := Tx.apply_sends (Tx.start o) fx
  cases hx : Tx.apply (Tx.start o) fx with
  | mk og sd =>
    rw [hx] at h1 h2
    simp only at h1 h2
    rw [h1, h2]
    rfl

theorem external_eq (req : Abstract.Request) (now : Nat) (o : Origin)
    (h : req.origin?.isSome) :
    (Abstract.Reply.external (Impl.Handle.external req now o).1,
     (Impl.Handle.external req now o).2.put,
     (Impl.Handle.external req now o).2.send) = specStep (.external req) now o := by
  cases req <;> simp only [Abstract.Request.origin?, Option.isSome, Bool.false_eq_true] at h
  all_goals
    simp only [Impl.Handle.external, Impl.Handle.run, Impl.Tx.commit]
    simp only [specStep, Abstract.handle, Abstract.handleExternal, Frame.map_eq, Frame.bind_apply,
      Frame.pure_apply, List.append_nil]
    simp only [promiseGet_eq, promiseCreate_eq, promiseSettle_eq, promiseRegisterCallback_eq,
      promiseRegisterListener_eq, taskGet_eq, taskCreate_eq, taskAcquire_eq, taskFence_eq,
      taskHeartbeat_eq, taskSuspend_eq, taskFulfill_eq, taskRelease_eq, taskHalt_eq, taskContinue_eq,
      liftH, Tx.apply_start]

def _root_.Abstract.Trigger.isSchedule : Abstract.Trigger → Bool
  | .scheduleTimeout _ => true
  | _                  => false

theorem trigger_eq (trg : Abstract.Trigger) (now : Nat) (o : Origin) (h : trg.isSchedule = false) :
    ((Impl.Handle.trigger trg now o).put, (Impl.Handle.trigger trg now o).send) =
      ((specStep (.internal trg) now o).2.1, (specStep (.internal trg) now o).2.2) := by
  cases trg <;> simp only [Abstract.Trigger.isSchedule, Bool.true_eq_false] at h
  all_goals
    simp only [Impl.Handle.trigger, Impl.Tx.commit]
    simp only [specStep, Abstract.handle, Abstract.handleInternal, Frame.bind_apply,
      Frame.pure_apply, List.append_nil]
    simp only [promiseTimeout_eq, callback_eq, listener_eq, leaseTimeout_eq, retryTimeout_eq,
      liftH, Tx.apply_start]

theorem trigger_reply (trg : Abstract.Trigger) (now : Nat) (o : Origin) :
    (specStep (.internal trg) now o).1 = .internal := rfl

end Equiv
