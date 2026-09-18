import refinement.wf

namespace Refinement

open Protocol (Ident Object Request TaskRef)
open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
               PromiseRegisterListenerReq TaskGetReq TaskCreateReq TaskAcquireReq TaskFenceReq
               TaskHeartbeatReq TaskSuspendReq TaskFulfillReq TaskReleaseReq TaskHaltReq TaskContinueReq)
open Concrete (Origin Commands)

def Extends (org d : Origin) : Prop := ∃ new, d.objects = org.objects ++ new

theorem Extends.refl (org : Origin) : Extends org org := ⟨[], (List.append_nil _).symm⟩

theorem Extends.set {org d : Origin} (h : Extends org d) (x : Object) : Extends org (d.set x) := by
  obtain ⟨new, hn⟩ := h
  exact ⟨new ++ [x], by show d.objects ++ [x] = _; rw [hn, List.append_assoc]⟩

theorem Extends.trans {a b c : Origin} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  exact ⟨n1 ++ n2, by rw [e2, e1, List.append_assoc]⟩

theorem promiseGet_extends (now : Nat) (req : PromiseGetReq) (org : Origin) :
    Extends org (Concrete.promiseGet req now org).2.org := by
  unfold Concrete.promiseGet
  split <;> exact Extends.refl _

theorem promiseCreate_extends (now : Nat) (req : PromiseCreateReq) (org : Origin) :
    Extends org (Concrete.promiseCreate req now org).2.org := by
  unfold Concrete.promiseCreate
  split
  · exact Extends.refl _
  · dsimp only
    split
    · split
      · exact (Extends.refl _).set _
      · exact (Extends.refl _).set _
    · exact (Extends.refl _).set _

theorem promiseSettle_extends (now : Nat) (req : PromiseSettleReq) (org : Origin) :
    Extends org (Concrete.promiseSettle req now org).2.org := by
  unfold Concrete.promiseSettle
  split
  · exact Extends.refl _
  · cases org.get req.id now with
    | none => exact Extends.refl _
    | some o =>
        dsimp only
        split
        · exact (Extends.refl _).set _
        · exact Extends.refl _

theorem promiseRegisterCallback_extends (now : Nat) (req : PromiseRegisterCallbackReq) (org : Origin) :
    Extends org (Concrete.promiseRegisterCallback req now org).2.org := by
  unfold Concrete.promiseRegisterCallback
  split
  · exact Extends.refl _
  · cases org.get req.awaited now with
    | none => exact Extends.refl _
    | some awaited =>
        cases org.get req.awaiter now with
        | none => exact Extends.refl _
        | some awaiter =>
            dsimp only
            split
            · exact Extends.refl _
            · split
              · exact (Extends.refl _).set _
              · exact Extends.refl _

theorem promiseRegisterListener_extends (now : Nat) (req : PromiseRegisterListenerReq) (org : Origin) :
    Extends org (Concrete.promiseRegisterListener req now org).2.org := by
  unfold Concrete.promiseRegisterListener
  cases org.get req.awaited now with
  | none => exact Extends.refl _
  | some awaited =>
      dsimp only
      split
      · exact Extends.refl _
      · split
        · exact (Extends.refl _).set _
        · exact Extends.refl _

theorem taskGet_extends (now : Nat) (req : TaskGetReq) (org : Origin) :
    Extends org (Concrete.taskGet req now org).2.org := by
  unfold Concrete.taskGet
  split <;> exact Extends.refl _

theorem taskCreate_extends (now : Nat) (req : TaskCreateReq) (org : Origin) :
    Extends org (Concrete.taskCreate req now org).2.org := by
  unfold Concrete.taskCreate
  dsimp only
  split
  · exact Extends.refl _
  · cases org.get req.action.id now with
    | none =>
        dsimp only
        split
        · exact (Extends.refl _).set _
        · exact (Extends.refl _).set _
    | some o =>
        dsimp only
        split
        · exact Extends.refl _
        · split
          · exact Extends.refl _
          · split
            · exact Extends.refl _
            · split
              · exact (Extends.refl _).set _
              · exact Extends.refl _

theorem taskAcquire_extends (now : Nat) (req : TaskAcquireReq) (org : Origin) :
    Extends org (Concrete.taskAcquire req now org).2.org := by
  unfold Concrete.taskAcquire
  cases org.get req.id now with
  | none => exact Extends.refl _
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Extends.refl _
      | some t =>
          simp only [Option.map_some]
          split
          · exact Extends.refl _
          · exact (Extends.refl _).set _

theorem taskFence_extends (now : Nat) (req : TaskFenceReq) (org : Origin) :
    Extends org (Concrete.taskFence req now org).2.org := by
  unfold Concrete.taskFence
  split
  · exact Extends.refl _
  · cases org.get req.id now with
    | none => exact Extends.refl _
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Extends.refl _
        | some t =>
            simp only [Option.map_some]
            split
            · exact Extends.refl _
            · cases req.action with
              | create r =>
                  rcases hC : Concrete.promiseCreate r now org with ⟨res, c⟩
                  have := promiseCreate_extends now r org
                  rw [hC] at this
                  simp only [hC]
                  exact this
              | settle r =>
                  rcases hC : Concrete.promiseSettle r now org with ⟨res, c⟩
                  have := promiseSettle_extends now r org
                  rw [hC] at this
                  simp only [hC]
                  exact this

theorem hbStep_extends (now : Nat) (org : Origin) (pid : String) :
    ∀ (refs : List TaskRef) (c : Commands), Extends org c.org →
      Extends org (refs.foldl (hbStep now org pid) c).org
  | [], _, hc => hc
  | ref :: refs, c, hc => by
      simp only [List.foldl_cons]
      refine hbStep_extends now org pid refs _ ?_
      unfold hbStep
      cases org.get ref.id now with
      | none => exact hc
      | some o =>
          simp only [Option.bind_some]
          cases o.task with
          | none => exact hc
          | some t =>
              simp only [Option.map_some]
              split
              · exact hc.set _
              · exact hc

theorem taskHeartbeat_extends (now : Nat) (req : TaskHeartbeatReq) (org : Origin) :
    Extends org (Concrete.taskHeartbeat req now org).2.org := by
  rw [taskHeartbeat_eq]
  exact hbStep_extends now org req.pid req.tasks _ (Extends.refl _)

theorem regStep_extends (now : Nat) (org : Origin) (awaiter : Ident) :
    ∀ (ids : List Ident) (d : Origin), Extends org d →
      Extends org ((ids.map (org.get · now)).foldl (regStep awaiter) d)
  | [], _, hd => hd
  | id :: ids, d, hd => by
      simp only [List.map_cons, List.foldl_cons]
      refine regStep_extends now org awaiter ids _ ?_
      unfold regStep
      cases org.get id now with
      | none => exact hd
      | some oa => exact hd.set _

theorem taskSuspend_extends (now : Nat) (req : TaskSuspendReq) (org : Origin) :
    Extends org (Concrete.taskSuspend req now org).2.org := by
  rw [taskSuspend_eq]
  dsimp only
  split
  · exact Extends.refl _
  · cases org.get req.id now with
    | none => exact Extends.refl _
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Extends.refl _
        | some t =>
            simp only [Option.map_some]
            split
            · exact Extends.refl _
            · split
              · exact Extends.refl _
              · split
                · exact (Extends.refl _).set _
                · exact (regStep_extends now org req.id _ org (Extends.refl _)).set _

theorem taskFulfill_extends (now : Nat) (req : TaskFulfillReq) (org : Origin) :
    Extends org (Concrete.taskFulfill req now org).2.org := by
  unfold Concrete.taskFulfill
  split
  · exact Extends.refl _
  · cases org.get req.id now with
    | none => exact Extends.refl _
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Extends.refl _
        | some t =>
            simp only [Option.map_some]
            split
            · exact Extends.refl _
            · exact (Extends.refl _).set _

theorem taskRelease_extends (now : Nat) (req : TaskReleaseReq) (org : Origin) :
    Extends org (Concrete.taskRelease req now org).2.org := by
  unfold Concrete.taskRelease
  cases org.get req.id now with
  | none => exact Extends.refl _
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Extends.refl _
      | some t =>
          simp only [Option.map_some]
          split
          · exact Extends.refl _
          · exact (Extends.refl _).set _

theorem taskHalt_extends (now : Nat) (req : TaskHaltReq) (org : Origin) :
    Extends org (Concrete.taskHalt req now org).2.org := by
  unfold Concrete.taskHalt
  cases org.get req.id now with
  | none => exact Extends.refl _
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Extends.refl _
      | some t =>
          simp only [Option.map_some]
          split
          · exact Extends.refl _
          · split
            · exact Extends.refl _
            · exact (Extends.refl _).set _

theorem taskContinue_extends (now : Nat) (req : TaskContinueReq) (org : Origin) :
    Extends org (Concrete.taskContinue req now org).2.org := by
  unfold Concrete.taskContinue
  cases org.get req.id now with
  | none => exact Extends.refl _
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Extends.refl _
      | some t =>
          simp only [Option.map_some]
          split
          · exact Extends.refl _
          · exact (Extends.refl _).set _

theorem handleExternal_extends (now : Nat) (req : Request) (org : Origin) :
    Extends org (Concrete.handleExternal req now org).2.org := by
  cases req with
  | promiseGet r =>
      rcases hC : Concrete.promiseGet r now org with ⟨res, c⟩
      have := promiseGet_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseCreate r =>
      rcases hC : Concrete.promiseCreate r now org with ⟨res, c⟩
      have := promiseCreate_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseSettle r =>
      rcases hC : Concrete.promiseSettle r now org with ⟨res, c⟩
      have := promiseSettle_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseRegisterCallback r =>
      rcases hC : Concrete.promiseRegisterCallback r now org with ⟨res, c⟩
      have := promiseRegisterCallback_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseRegisterListener r =>
      rcases hC : Concrete.promiseRegisterListener r now org with ⟨res, c⟩
      have := promiseRegisterListener_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | promiseSearch r => exact Extends.refl _
  | scheduleGet r => exact Extends.refl _
  | scheduleCreate r => exact Extends.refl _
  | scheduleDelete r => exact Extends.refl _
  | scheduleSearch r => exact Extends.refl _
  | taskGet r =>
      rcases hC : Concrete.taskGet r now org with ⟨res, c⟩
      have := taskGet_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskCreate r =>
      rcases hC : Concrete.taskCreate r now org with ⟨res, c⟩
      have := taskCreate_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskAcquire r =>
      rcases hC : Concrete.taskAcquire r now org with ⟨res, c⟩
      have := taskAcquire_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskFence r =>
      rcases hC : Concrete.taskFence r now org with ⟨res, c⟩
      have := taskFence_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskHeartbeat r =>
      rcases hC : Concrete.taskHeartbeat r now org with ⟨res, c⟩
      have := taskHeartbeat_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskSuspend r =>
      rcases hC : Concrete.taskSuspend r now org with ⟨res, c⟩
      have := taskSuspend_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskFulfill r =>
      rcases hC : Concrete.taskFulfill r now org with ⟨res, c⟩
      have := taskFulfill_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskRelease r =>
      rcases hC : Concrete.taskRelease r now org with ⟨res, c⟩
      have := taskRelease_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskHalt r =>
      rcases hC : Concrete.taskHalt r now org with ⟨res, c⟩
      have := taskHalt_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskContinue r =>
      rcases hC : Concrete.taskContinue r now org with ⟨res, c⟩
      have := taskContinue_extends now r org
      rw [hC] at this
      simp only [Concrete.handleExternal, hC]
      exact this
  | taskSearch r => exact Extends.refl _

theorem sweep_extends (now : Nat) (org : Origin) : Extends org (Concrete.sweep now org).org :=
  ⟨_, rfl⟩

theorem handle_extends (ev : Concrete.Event) (now : Nat) (org : Origin) :
    Extends org (Concrete.handle ev now org).2.org := by
  cases ev with
  | external req =>
      show Extends org ((Concrete.sweep now org).merge
        (Concrete.handleExternal req now (Concrete.sweep now org).org).2).org
      exact (sweep_extends now org).trans (handleExternal_extends now req _)
  | internal _ => exact sweep_extends now org
  | stutter => exact Extends.refl org

end Refinement
