import refinement.cache

namespace Refinement

open Protocol (Ident Object PromiseObject TaskObject Request)
open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
                  PromiseRegisterListenerReq TaskGetReq TaskCreateReq TaskAcquireReq TaskFenceReq
                  TaskHeartbeatReq TaskSuspendReq TaskFulfillReq TaskReleaseReq TaskHaltReq TaskContinueReq
                  TaskRef)
open Concrete (Origin Commands Timer Path Blob)

def Armed (s : Concrete.State) : Prop :=
  ∀ t : Timer, (s.blob? (.timer t)).isSome = true → t.kind = .promiseTimeout →
    ∃ o ∈ (s.origin t.id.origin).objects, o.id = t.id ∧ o.promise.type ≠ .internal

theorem Armed.init : Armed Concrete.State.init := by
  intro t ht _
  simp [Concrete.State.init, Concrete.State.blob?] at ht

def KeepDoc (org d : Origin) : Prop :=
  ∀ o ∈ org.current.objects, ∃ o' ∈ d.current.objects, o'.id = o.id ∧ o'.promise.type = o.promise.type

theorem KeepDoc.refl (org : Origin) : KeepDoc org org := fun o ho => ⟨o, ho, rfl, rfl⟩

theorem KeepDoc.trans {a b c : Origin} (h1 : KeepDoc a b) (h2 : KeepDoc b c) : KeepDoc a c := by
  intro o ho
  obtain ⟨o', ho', hi, ht⟩ := h1 o ho
  obtain ⟨o'', ho'', hi', ht'⟩ := h2 o' ho'
  exact ⟨o'', ho'', hi'.trans hi, ht'.trans ht⟩

theorem mem_set_self (org : Origin) (x : Object) : x ∈ (org.set x).current.objects := by
  rw [current_set]
  show x ∈ replace org.current.objects x
  unfold replace
  split
  · rename_i h
    obtain ⟨o, ho, he⟩ := List.any_eq_true.1 h
    exact List.mem_map.2 ⟨o, ho, by simp [he]⟩
  · simp

theorem mem_set_of_ne {org : Origin} {x o : Object} (ho : o ∈ org.current.objects) (hne : o.id ≠ x.id) :
    o ∈ (org.set x).current.objects := by
  rw [current_set]
  show o ∈ replace org.current.objects x
  unfold replace
  split
  · exact List.mem_map.2 ⟨o, ho, by simp [hne]⟩
  · simp [ho]

theorem KeepDoc.set {org d : Origin} (hd : KeepDoc org d) {x : Object}
    (hty : ∀ o ∈ org.current.objects, o.id = x.id → o.promise.type = x.promise.type) : KeepDoc org (d.set x) := by
  intro o ho
  by_cases e : o.id = x.id
  · exact ⟨x, mem_set_self d x, e.symm, (hty o ho e).symm⟩
  · obtain ⟨o', ho', hi, ht⟩ := hd o ho
    exact ⟨o', mem_set_of_ne ho' (fun h => e (hi.symm.trans h)), hi, ht⟩

structure Keep (org : Origin) (c : Commands) : Prop where
  arm : ∀ t ∈ c.arm, t.kind = .promiseTimeout → ∃ o ∈ (c.doc org).current.objects, o.id = t.id ∧ o.promise.type ≠ .internal
  doc : KeepDoc org (c.doc org)

theorem Keep.id (org : Origin) : Keep org {} :=
  ⟨fun _ ht => absurd ht List.not_mem_nil, by rw [doc_empty]; exact KeepDoc.refl org⟩

theorem Keep.merge {org : Origin} {c d : Commands} (hc : Keep org c) (hd : Keep (c.doc org) d) :
    Keep org (c.merge d) := by
  refine ⟨fun t ht hk => ?_, fun o ho => by rw [current_merge]; exact hc.doc.trans hd.doc o ho⟩
  rw [current_merge]
  have ht' : t ∈ c.arm.filter (· ∉ d.del) ++ d.arm := ht
  rcases List.mem_append.1 ht' with ht | ht
  · obtain ⟨o, ho, hi, hty⟩ := hc.arm t (List.mem_filter.1 ht).1 hk
    obtain ⟨o', ho', hi', hty'⟩ := hd.doc o ho
    exact ⟨o', ho', hi'.trans hi, fun h => hty (hty'.symm.trans h)⟩
  · exact hd.arm t ht hk

theorem task_timers_kind {tk : TaskObject} {id : Ident} {t : Timer} (ht : t ∈ tk.timers id) :
    t.kind ≠ .promiseTimeout := by
  unfold Protocol.TaskObject.timers at ht
  split at ht
  · rw [List.mem_singleton] at ht; subst ht; simp
  · rw [List.mem_singleton] at ht; subst ht; simp
  · simp at ht

theorem timers_kind {o : Object} {t : Timer} (ht : t ∈ o.timers) (hk : t.kind = .promiseTimeout) :
    t.id = o.id ∧ o.promise.type ≠ .internal := by
  unfold Protocol.Object.timers at ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · split at ht
    · rename_i hc
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨rfl, by simpa using hc.2⟩
    · simp at ht
  · cases htk : o.task with
    | none => rw [htk] at ht; simp at ht
    | some tk =>
        rw [htk] at ht
        simp only [Option.map_some, Option.getD_some] at ht
        exact absurd hk (task_timers_kind ht)

theorem project_type (p : PromiseObject) (n : Nat) : (p.project n).type = p.type := by
  unfold PromiseObject.project
  split <;> (try split) <;> rfl

theorem addCallback_type (p : PromiseObject) (w : Ident) : (p.addCallback w).type = p.type := by
  unfold PromiseObject.addCallback; split <;> rfl

theorem addListener_type (p : PromiseObject) (a : String) : (p.addListener a).type = p.type := by
  unfold PromiseObject.addListener; split <;> rfl

theorem type_of_get {org : Origin} {id : Ident} {now : Nat} {o : Object}
    (hf : org.get id now = some o) {x : Object} (hx : x.id = o.id) (hxt : x.promise.type = o.promise.type) :
    ∀ o' ∈ org.current.objects, o'.id = x.id → o'.promise.type = x.promise.type := by
  obtain ⟨ob, hfind, rfl⟩ := get_some hf
  obtain ⟨hob, -⟩ := find_mem hfind
  intro o' ho' he
  have : o' = ob := eq_of_id_nodup (current_nodup org) ho' hob (he.trans hx)
  subst this
  rw [hxt]
  exact (project_type o'.promise now).symm

theorem type_of_none {org : Origin} {id : Ident} {now : Nat} (hf : org.get id now = none) {x : Object}
    (hx : x.id = id) : ∀ o' ∈ org.current.objects, o'.id = x.id → o'.promise.type = x.promise.type := by
  intro o' ho' he
  exfalso
  rw [get_eq] at hf
  have hfind : Origin.find org id = none := by
    cases h : Origin.find org id with
    | none => rfl
    | some _ => rw [h] at hf; cases hf
  unfold Origin.find at hfind
  exact (List.find?_eq_none.1 hfind o' ho') (by simp [he, hx])

theorem Keep.one {org : Origin} {x : Object}
    (hty : ∀ o ∈ org.current.objects, o.id = x.id → o.promise.type = x.promise.type)
    {A D : List Timer} {S : List (String × Protocol.Message)}
    (harm : ∀ t ∈ A, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal) :
    Keep org { arm := A, add := [x], del := D, send := S } :=
  ⟨fun t ht hk => ⟨x, mem_set_self org x, (harm t ht hk).1.symm, (harm t ht hk).2⟩, (KeepDoc.refl org).set hty⟩

theorem Keep.add {org : Origin} {l : List Object} (hd : KeepDoc org (org.add l)) {x : Object}
    (hty : ∀ o ∈ org.current.objects, o.id = x.id → o.promise.type = x.promise.type)
    {A D : List Timer} {S : List (String × Protocol.Message)}
    (harm : ∀ t ∈ A, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal) :
    Keep org { arm := A, add := l ++ [x], del := D, send := S } := by
  have hdoc : ({ arm := A, add := l ++ [x], del := D, send := S } : Commands).doc org = (org.add l).set x :=
    add_snoc org l x
  refine ⟨fun t ht hk => ?_, ?_⟩
  · rw [hdoc]
    exact ⟨x, mem_set_self _ x, (harm t ht hk).1.symm, (harm t ht hk).2⟩
  · rw [hdoc]
    exact hd.set hty

theorem Keep.of_current {org : Origin} {c : Commands} (h : Keep org.current c) : Keep org c := by
  have hd : (c.doc org.current).current = (c.doc org).current := current_add_current org c.add
  refine ⟨fun t ht hk => ?_, fun o ho => ?_⟩
  · rw [← hd]
    exact h.arm t ht hk
  · rw [← hd]
    exact h.doc o (by rw [current_current]; exact ho)

theorem noarm {x : Object} : ∀ t ∈ ([] : List Timer), t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht => absurd ht List.not_mem_nil

theorem taskarm {x : Object} {tk : TaskObject} {id : Ident} :
    ∀ t ∈ tk.timers id, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht hk => absurd hk (task_timers_kind ht)

theorem objarm {x : Object} : ∀ t ∈ x.timers, t.kind = .promiseTimeout → t.id = x.id ∧ x.promise.type ≠ .internal :=
  fun _ ht hk => timers_kind ht hk

theorem promiseGet_keep {org : Origin} (now : Nat) (req : PromiseGetReq) : Keep org (Concrete.promiseGet req now org).2 := by
  unfold Concrete.promiseGet
  split <;> exact Keep.id org

theorem promiseCreate_keep {org : Origin} (now : Nat) (req : PromiseCreateReq) : Keep org (Concrete.promiseCreate req now org).2 := by
  unfold Concrete.promiseCreate
  split
  · exact Keep.id org
  · rename_i hf
    dsimp only
    split
    · split
      · exact Keep.one (type_of_none hf (by rfl)) objarm
      · exact Keep.one (type_of_none hf (by rfl)) objarm
    · exact Keep.one (type_of_none hf (by rfl)) noarm

theorem promiseSettle_keep {org : Origin} (now : Nat) (req : PromiseSettleReq) : Keep org (Concrete.promiseSettle req now org).2 := by
  unfold Concrete.promiseSettle
  split
  · exact Keep.id org
  · split
    · exact Keep.id org
    · rename_i hf
      split
      · exact Keep.one (type_of_get hf (by rfl) (by rfl)) noarm
      · exact Keep.id org

theorem promiseRegisterCallback_keep {org : Origin} (now : Nat) (req : PromiseRegisterCallbackReq) :
    Keep org (Concrete.promiseRegisterCallback req now org).2 := by
  unfold Concrete.promiseRegisterCallback
  split
  · exact Keep.id org
  · split
    · exact Keep.id org
    · exact Keep.id org
    · rename_i hA _
      split
      · exact Keep.id org
      · split
        · exact Keep.one (type_of_get hA (by rfl) (by exact addCallback_type _ _)) noarm
        · exact Keep.id org

theorem promiseRegisterListener_keep {org : Origin} (now : Nat) (req : PromiseRegisterListenerReq) :
    Keep org (Concrete.promiseRegisterListener req now org).2 := by
  unfold Concrete.promiseRegisterListener
  split
  · exact Keep.id org
  · rename_i hf
    split
    · exact Keep.id org
    · split
      · exact Keep.one (type_of_get hf (by rfl) (by exact addListener_type _ _)) noarm
      · exact Keep.id org

theorem taskGet_keep {org : Origin} (now : Nat) (req : TaskGetReq) : Keep org (Concrete.taskGet req now org).2 := by
  unfold Concrete.taskGet
  split <;> exact Keep.id org

theorem taskCreate_keep {org : Origin} (now : Nat) (req : TaskCreateReq) : Keep org (Concrete.taskCreate req now org).2 := by
  unfold Concrete.taskCreate
  dsimp only
  split
  · exact Keep.id org
  · split
    · rename_i hf
      split
      · exact Keep.one (type_of_none hf (by rfl)) objarm
      · exact Keep.one (type_of_none hf (by rfl)) noarm
    · rename_i hf
      split
      · exact Keep.id org
      · split
        · exact Keep.id org
        · split
          · exact Keep.id org
          · split
            · exact Keep.one (type_of_get hf (by rfl) (by rfl)) taskarm
            · exact Keep.id org

theorem taskAcquire_keep {org : Origin} (now : Nat) (req : TaskAcquireReq) : Keep org (Concrete.taskAcquire req now org).2 := by
  unfold Concrete.taskAcquire
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.one (type_of_get hf (by rfl) (by rfl)) taskarm

theorem taskFence_keep {org : Origin} (now : Nat) (req : TaskFenceReq) : Keep org (Concrete.taskFence req now org).2 := by
  unfold Concrete.taskFence
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · split
              · exact promiseCreate_keep now _
              · exact promiseSettle_keep now _

theorem hbStep_keep {org : Origin} (now : Nat) (pid : String) : ∀ (refs : List TaskRef) (c : Commands),
    (∀ t ∈ c.arm, t.kind ≠ .promiseTimeout) → KeepDoc org (c.doc org) →
    (∀ t ∈ (refs.foldl (hbStep now org pid) c).arm, t.kind ≠ .promiseTimeout) ∧
      KeepDoc org ((refs.foldl (hbStep now org pid) c).doc org)
  | [], _, ha, hd => ⟨ha, hd⟩
  | ref :: refs, c, ha, hd => by
      rw [List.foldl_cons]
      refine hbStep_keep now pid refs _ ?_ ?_
      · unfold hbStep
        cases hf : org.get ref.id now with
        | none => exact ha
        | some o =>
            simp only [Option.bind_some]
            cases o.task with
            | none => exact ha
            | some t =>
                simp only [Option.map_some]
                split
                · intro tm htm
                  simp only [List.mem_append] at htm
                  rcases htm with htm | htm
                  · exact ha tm htm
                  · split at htm
                    · simp at htm
                    · exact task_timers_kind htm
                · exact ha
      · unfold hbStep
        cases hf : org.get ref.id now with
        | none => exact hd
        | some o =>
            simp only [Option.bind_some]
            cases o.task with
            | none => exact hd
            | some t =>
                simp only [Option.map_some]
                split
                · dsimp only [Commands.doc]
                  rw [add_snoc]
                  exact hd.set (type_of_get hf (by rfl) (by rfl))
                · exact hd

theorem taskHeartbeat_keep {org : Origin} (now : Nat) (req : TaskHeartbeatReq) : Keep org (Concrete.taskHeartbeat req now org).2 := by
  rw [taskHeartbeat_eq]
  obtain ⟨ha, hd⟩ := hbStep_keep now req.pid req.tasks {} (fun t ht => absurd ht List.not_mem_nil)
    (by rw [doc_empty]; exact KeepDoc.refl org)
  exact ⟨fun t ht hk => absurd hk (ha t ht), hd⟩

theorem regStep_keep {org : Origin} (now : Nat) (awaiter : Ident) : ∀ (ids : List Ident) (adds : List Object),
    KeepDoc org (org.add adds) → KeepDoc org (org.add ((ids.map (org.get · now)).foldl (regStep awaiter) adds))
  | [], _, hd => hd
  | id :: ids, adds, hd => by
      simp only [List.map_cons, List.foldl_cons]
      refine regStep_keep now awaiter ids _ ?_
      unfold regStep
      cases hf : org.get id now with
      | none => exact hd
      | some oa =>
          dsimp only
          rw [add_snoc]
          exact hd.set (type_of_get hf (by rfl) (by exact addCallback_type _ _))

theorem taskSuspend_keep {org : Origin} (now : Nat) (req : TaskSuspendReq) : Keep org (Concrete.taskSuspend req now org).2 := by
  rw [taskSuspend_eq]
  dsimp only
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · split
              · exact Keep.id org
              · split
                · exact Keep.one (type_of_get hf (by rfl) (by rfl)) noarm
                · exact Keep.add (regStep_keep now req.id _ [] (by rw [add_nil]; exact KeepDoc.refl org))
                    (type_of_get hf (by rfl) (by rfl)) noarm

theorem taskFulfill_keep {org : Origin} (now : Nat) (req : TaskFulfillReq) : Keep org (Concrete.taskFulfill req now org).2 := by
  unfold Concrete.taskFulfill
  split
  · exact Keep.id org
  · cases hf : org.get req.id now with
    | none => exact Keep.id org
    | some o =>
        simp only [Option.bind_some]
        cases o.task with
        | none => exact Keep.id org
        | some t =>
            simp only [Option.map_some]
            split
            · exact Keep.id org
            · exact Keep.one (type_of_get hf (by rfl) (by rfl)) noarm

theorem taskRelease_keep {org : Origin} (now : Nat) (req : TaskReleaseReq) : Keep org (Concrete.taskRelease req now org).2 := by
  unfold Concrete.taskRelease
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.one (type_of_get hf (by rfl) (by rfl)) taskarm

theorem taskHalt_keep {org : Origin} (now : Nat) (req : TaskHaltReq) : Keep org (Concrete.taskHalt req now org).2 := by
  unfold Concrete.taskHalt
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · split
            · exact Keep.id org
            · exact Keep.one (type_of_get hf (by rfl) (by rfl)) noarm

theorem taskContinue_keep {org : Origin} (now : Nat) (req : TaskContinueReq) : Keep org (Concrete.taskContinue req now org).2 := by
  unfold Concrete.taskContinue
  cases hf : org.get req.id now with
  | none => exact Keep.id org
  | some o =>
      simp only [Option.bind_some]
      cases o.task with
      | none => exact Keep.id org
      | some t =>
          simp only [Option.map_some]
          split
          · exact Keep.id org
          · exact Keep.one (type_of_get hf (by rfl) (by rfl)) taskarm

theorem handleExternal_keep {org : Origin} (now : Nat) (req : Request) : Keep org (Concrete.handleExternal req now org).2 := by
  cases req with
  | promiseGet r => exact promiseGet_keep now r
  | promiseCreate r => exact promiseCreate_keep now r
  | promiseSettle r => exact promiseSettle_keep now r
  | promiseRegisterCallback r => exact promiseRegisterCallback_keep now r
  | promiseRegisterListener r => exact promiseRegisterListener_keep now r
  | promiseSearch _ => exact Keep.id org
  | scheduleGet _ => exact Keep.id org
  | scheduleCreate _ => exact Keep.id org
  | scheduleDelete _ => exact Keep.id org
  | scheduleSearch _ => exact Keep.id org
  | taskGet r => exact taskGet_keep now r
  | taskCreate r => exact taskCreate_keep now r
  | taskAcquire r => exact taskAcquire_keep now r
  | taskFence r => exact taskFence_keep now r
  | taskHeartbeat r => exact taskHeartbeat_keep now r
  | taskSuspend r => exact taskSuspend_keep now r
  | taskFulfill r => exact taskFulfill_keep now r
  | taskRelease r => exact taskRelease_keep now r
  | taskHalt r => exact taskHalt_keep now r
  | taskContinue r => exact taskContinue_keep now r
  | taskSearch _ => exact Keep.id org

theorem Keep.step {org : Origin} {c c' : Commands} (h : Keep org c) {ob x : Object}
    (hob : ob ∈ (c.doc org).current.objects) (hadd : c'.add = c.add ++ [x]) (hx : x.id = ob.id)
    (hty : x.promise.type = ob.promise.type) (harm : ∀ t ∈ c'.arm, t.kind = .promiseTimeout → t ∈ c.arm) :
    Keep org c' := by
  have hdoc : c'.doc org = (c.doc org).set x := by
    unfold Commands.doc
    rw [hadd]
    exact add_snoc org c.add x
  have hnd := current_nodup (c.doc org)
  have hsame : ∀ o ∈ (c.doc org).current.objects, o.id = x.id → o = ob := fun o ho e =>
    eq_of_id_nodup hnd ho hob (e.trans hx)
  refine ⟨fun t ht hk => ?_, fun o ho => ?_⟩
  · rw [hdoc]
    obtain ⟨o, ho, hi, hot⟩ := h.arm t (harm t ht hk) hk
    by_cases e : o.id = x.id
    · refine ⟨x, mem_set_self _ x, hx.trans (hsame o ho e ▸ hi), ?_⟩
      rw [hty, ← hsame o ho e]
      exact hot
    · exact ⟨o, mem_set_of_ne ho e, hi, hot⟩
  · rw [hdoc]
    refine h.doc.set (fun o' ho' he => ?_) o ho
    obtain ⟨o'', ho'', hi, ht⟩ := h.doc o' ho'
    rw [← ht, hsame o'' ho'' (hi.trans he), hty]

theorem Keep.fold {α : Type} {org : Origin} (step : Commands → α → Commands) :
    ∀ (l : List α), (∀ c a, a ∈ l → Keep org c → Keep org (step c a)) →
      ∀ c, Keep org c → Keep org (l.foldl step c)
  | [], _, _, h => h
  | a :: l, hstep, c, h => by
      rw [List.foldl_cons]
      exact Keep.fold step l (fun c a ha => hstep c a (List.mem_cons_of_mem _ ha)) _
        (hstep c a (List.mem_cons_self ..) h)

theorem Keep.pass {org : Origin} (step : Commands → Object → Commands)
    (hstep : ∀ c o, o ∈ org.current.objects → Keep org c → Keep org (step c o)) :
    Keep org (org.current.objects.foldl step {}) :=
  Keep.fold step _ (fun c o ho h => hstep c o ho h) {} (Keep.id org)

theorem Keep.step_of {org : Origin} {c c' : Commands} (h : Keep org c) {o : Object} (ho : o ∈ org.current.objects)
    {x : Object} (hadd : c'.add = c.add ++ [x]) (hx : x.id = o.id) (hty : x.promise.type = o.promise.type)
    (harm : ∀ t ∈ c'.arm, t.kind = .promiseTimeout → t ∈ c.arm) : Keep org c' := by
  obtain ⟨ob, hob, hi, ht⟩ := h.doc o ho
  exact h.step hob hadd (hx.trans hi.symm) (hty.trans ht.symm) harm

theorem promiseTimeouts_keep (now : Nat) (org : Origin) : Keep org (Concrete.promiseTimeouts now org) := by
  rw [promiseTimeouts_eq]
  refine Keep.pass _ fun c o ho h => ?_
  unfold ptStep
  split
  · exact h.step_of ho rfl (project_id o now) (project_type o.promise now) fun t ht _ => ht
  · exact h

theorem listeners_keep (now : Nat) (org : Origin) : Keep org (Concrete.listeners now org) := by
  rw [listeners_eq]
  refine Keep.pass _ fun c o ho h => ?_
  simp only [lsBulk]
  split
  · exact h.step_of ho rfl (project_id o now) (project_type o.promise now) fun t ht _ => ht
  · exact h

theorem resumeOne_keep {org : Origin} {c : Commands} (h : Keep org c) (now : Nat) (awaited awaiter : Ident) :
    Keep org (Concrete.resumeOne now awaited org c awaiter) := by
  unfold Concrete.resumeOne
  cases hg : (c.doc org).get awaiter now with
  | none => exact h
  | some w =>
      obtain ⟨ob, hf, rfl⟩ := get_some hg
      obtain ⟨hob, -⟩ := find_mem hf
      simp only [Option.bind_some]
      cases (ob.project now).task with
      | none => exact h
      | some t =>
          simp only [Option.map_some]
          split
          · exact h.step hob rfl (project_id ob now) (project_type ob.promise now) fun t ht hk => by
              rcases List.mem_append.1 ht with ht | ht
              · exact ht
              · rw [List.mem_singleton] at ht
                subst ht
                cases hk
          all_goals (try split) <;> exact h.step hob rfl (project_id ob now) (project_type ob.promise now) fun t ht _ => ht

theorem callbacks_keep (now : Nat) (org : Origin) : Keep org (Concrete.callbacks now org) := by
  rw [callbacks_eq]
  refine Keep.pass _ fun c o _ h => ?_
  simp only [cbOuterOld]
  split
  · refine Keep.fold _ _ (fun c awaiter _ h => ?_) c h
    unfold cbStepOld
    split
    · rename_i cur hg
      obtain ⟨ob, hf, rfl⟩ := get_some hg
      obtain ⟨hob, -⟩ := find_mem hf
      refine resumeOne_keep ?_ now _ awaiter
      exact h.step hob rfl (project_id ob now) (project_type ob.promise now) fun t ht _ => ht
    · exact h
  · exact h

theorem leaseTimeouts_keep (now : Nat) (org : Origin) : Keep org (Concrete.leaseTimeouts now org) := by
  rw [leaseTimeouts_eq]
  refine Keep.pass _ fun c o ho h => ?_
  simp only [ltStep]
  split
  · split
    · exact h.step_of ho rfl (project_id o now) (project_type o.promise now) fun t ht hk => by
        rcases List.mem_append.1 ht with ht | ht
        · exact ht
        · rw [List.mem_singleton] at ht
          subst ht
          cases hk
    · exact h
  · exact h

theorem retryTimeouts_keep (now : Nat) (org : Origin) : Keep org (Concrete.retryTimeouts now org) := by
  rw [retryTimeouts_eq]
  refine Keep.pass _ fun c o ho h => ?_
  simp only [rtStep]
  split
  · split
    · exact h.step_of ho rfl (project_id o now) (project_type o.promise now) fun t ht hk => by
        rcases List.mem_append.1 ht with ht | ht
        · exact ht
        · rw [List.mem_singleton] at ht
          subst ht
          cases hk
    · exact h
  all_goals exact h

theorem sweep_keep (now : Nat) (org : Origin) : Keep org (Concrete.sweep now org) :=
  ((((promiseTimeouts_keep now org).merge (listeners_keep now _)).merge (callbacks_keep now _)).merge
    (leaseTimeouts_keep now _)).merge (retryTimeouts_keep now _)

theorem handle_keep (org : Origin) (now : Nat) (ev : Concrete.Event) : Keep org (Concrete.handle ev now org).2 := by
  cases ev with
  | external req =>
      show Keep org ((Concrete.sweep now org).merge
        (Concrete.handleExternal req now ((Concrete.sweep now org).doc org).current).2)
      exact (sweep_keep now org).merge (Keep.of_current (handleExternal_keep now req))
  | internal _ => exact sweep_keep now org
  | stutter => exact Keep.id org

theorem blob?_add_timer {H : Concrete.Hasher} {s s' : Concrete.State} {name : String} {part : List Object}
    {c : Concrete.Cond H} (h : (Concrete.Effect.add name part c).apply s = some s') (t : Timer) :
    s'.blob? (.timer t) = s.blob? (.timer t) := by
  simp only [Concrete.Effect.apply] at h
  split at h
  · cases h
    rw [blob?_eq, blob?_eq]
    simp [blobIn_put]
  · cases h

theorem applyAll_blob_source {H : Concrete.Hasher} :
    ∀ (es : List (Concrete.Effect H)) (s : Concrete.State) (t : Timer),
      ((Concrete.applyAll s es).1.blob? (.timer t)).isSome = true →
      (s.blob? (.timer t)).isSome = true ∨ ∃ b c, Concrete.Effect.put (.timer t) b c ∈ es
  | [], _, _, h => Or.inl h
  | e :: es, s, t, h => by
      simp only [Concrete.applyAll] at h
      cases he : e.apply s with
      | none =>
          rw [he] at h
          simp only at h
          exact Or.inl h
      | some s1 =>
          rw [he] at h
          simp only at h
          rcases applyAll_blob_source es s1 t h with h1 | ⟨b, c, hm⟩
          · cases e with
            | put q b c =>
                by_cases hpq : Path.timer t = q
                · subst hpq
                  exact Or.inr ⟨b, c, List.mem_cons_self ..⟩
                · rw [Concrete.blob?_put_other he hpq] at h1
                  exact Or.inl h1
            | add name part c =>
                rw [blob?_add_timer he] at h1
                exact Or.inl h1
            | del q =>
                simp only [Concrete.Effect.apply, Option.some.injEq] at he
                subst he
                simp only [blob?_eq, blobIn_del] at h1
                split at h1
                · simp at h1
                · exact Or.inl h1
            | send a m =>
                simp only [Concrete.Effect.apply, Option.some.injEq] at he
                subst he
                exact Or.inl h1
          · exact Or.inr ⟨b, c, List.mem_cons_of_mem _ hm⟩

theorem arm_of_put {H : Concrete.Hasher} {cfg : Concrete.Config} {name : String} {parts : List (List Object)}
    {cond : Concrete.Cond H} {objects : List Object} {c : Commands} {t : Timer} {b : Blob} {cd : Concrete.Cond H}
    (h : Concrete.Effect.put (.timer t) b cd ∈ c.effects (Concrete.write H cfg name parts cond objects)) :
    t ∈ c.arm := by
  unfold Concrete.write at h
  split at h <;>
    simp only [Concrete.Commands.effects, List.mem_append, List.mem_map, List.mem_singleton] at h <;>
    rcases h with ((⟨t', ht', heq⟩ | heq) | ⟨_, _, heq⟩) | ⟨⟨a, m⟩, _, heq⟩ <;> cases heq
  · exact ht'
  · exact ht'

theorem Armed.run (H : Concrete.Hasher) (cfg : Concrete.Config) (name : String) (c : Commands) (s : Concrete.State)
    (hs : Armed s) (hk : Keep (s.origin name) c)
    (horig : ∀ o ∈ (c.doc (s.origin name)).current.objects, o.id.origin = name) :
    Armed (Concrete.applyAll s (c.effects (Concrete.write H cfg name (s.parts name)
      (Concrete.Cond.of H (s.blob? (.origin name))) c.add))).1 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := run_state H cfg name c s
  rw [view_next] at h1
  intro t ht hk'
  rcases applyAll_blob_source _ s t ht with hold | ⟨b, cd, hm⟩
  · obtain ⟨o, ho, hoi, hot⟩ := hs t hold hk'
    by_cases e : t.id.origin = name
    · rw [e] at ho ⊢
      rw [h1]
      have ho' : o ∈ (s.origin name).current.objects := by rw [origin_current]; exact ho
      obtain ⟨o', ho', hi, hty⟩ := hk.doc o ho'
      exact ⟨o', ho', hi.trans hoi, fun h => hot (hty.symm.trans h)⟩
    · rw [State.origin_eq, h2 _ e, ← State.origin_eq s t.id.origin]
      exact ⟨o, ho, hoi, hot⟩
  · obtain ⟨o, ho, hoi, hot⟩ := hk.arm t (arm_of_put hm) hk'
    have e : t.id.origin = name := by rw [← hoi]; exact horig o ho
    rw [e, h1]
    exact ⟨o, ho, hoi, hot⟩

theorem Armed.step (H : Concrete.Hasher) (cfg : Concrete.Config) (ev : Concrete.Event) (now : Nat) {s : Concrete.State}
    (inv' : Inv (Concrete.step H cfg ev now s).2) (hs : Armed s) :
    Armed (Concrete.step H cfg ev now s).2 := by
  cases ev with
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [Concrete.step, ho]
          exact hs
      | some name =>
          have hst : (Concrete.step H cfg (.external req) now s).2 =
              (Concrete.run H cfg name (fun org => Concrete.handle (.external req) now org) s).2.1 := by
            rw [Concrete.step, ho]
          rw [hst] at inv' ⊢
          rw [run_snd] at inv' ⊢
          refine Armed.run H cfg name _ s hs (handle_keep _ now _) ?_
          have := (inv'.origin_props name).1
          have h1 := (run_state H cfg name (Concrete.handle (.external req) now (s.origin name)).2 s).1
          rw [view_next] at h1
          rw [h1] at this
          exact this
  | internal t =>
      by_cases hl : (s.blob? (.timer t)).isSome = true ∧ t.deadline ≤ now
      · have hst : (Concrete.step H cfg (.internal t) now s).2 =
            (Concrete.run H cfg t.id.origin (fun org => Concrete.handle (.internal t) now org) s).2.1 := by
          rw [Concrete.step, if_pos hl]
        rw [hst] at inv' ⊢
        rw [run_snd] at inv' ⊢
        refine Armed.run H cfg t.id.origin _ s hs (handle_keep _ now _) ?_
        have := (inv'.origin_props t.id.origin).1
        have h1 := (run_state H cfg t.id.origin (Concrete.handle (.internal t) now (s.origin t.id.origin)).2 s).1
        rw [view_next] at h1
        rw [h1] at this
        exact this
      · rw [Concrete.step, if_neg hl]
        exact hs
  | stutter => exact hs

theorem armed (H : Concrete.Hasher) (cfg : Concrete.Config) (tr : Concrete.Trace) (valid : Concrete.Valid H cfg tr)
    (init : (tr 0).state = Concrete.State.init) : ∀ n, Armed (tr n).state
  | 0 => by rw [init]; exact Armed.init
  | n + 1 => by
      have inv' := (invariant H cfg tr valid init (n + 1)).1
      rw [valid.state n] at inv' ⊢
      exact Armed.step H cfg _ _ inv' (armed H cfg tr valid init n)

end Refinement
