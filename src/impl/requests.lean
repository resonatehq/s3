import impl.lookup

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin Commands)

structure Sim (o : String) (org : Origin) (S : Abstract.State) {α : Type}
    (r : α × List Abstract.Effect) (res : α) (c : Commands) : Prop where
  res   : r.1 = res
  fx    : Fx o r.2
  loc   : Local o c.put (Abstract.applyAll S r.2)
  send  : sendsOf r.2 = c.send
  orig  : (∀ ob ∈ org.objects, ob.id.origin = o) → ∀ ob ∈ c.put.objects, ob.id.origin = o
  nodup : (org.objects.map (·.id)).Nodup → (c.put.objects.map (·.id)).Nodup

theorem find_write_at {org : Origin} {x : Object} {id : Ident} (hx : x.id = id) :
    Origin.find (org.write x) id = some x := by
  rw [← hx]; exact find_write_same org x

theorem Sim.skip {o : String} {org : Origin} {S : Abstract.State} {α : Type} (hL : Local o org S)
    (a : α) : Sim o org S (a, []) a { put := org } :=
  ⟨rfl, trivial, hL, rfl, fun h => h, fun h => h⟩

theorem Local_setPromise {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {p : PromiseObject} {x : Object} (hx : x.id = id)
    (h : Abstract.Object.withPromise id p (Origin.find org id) = x) :
    Local o (org.write x) (Abstract.applyAll S [.setPromise id p]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setPromise_same, hL _ hid', h, find_write_at hx]
  · rw [find_setPromise_other _ _ _ _ e, find_write_other _ _ _ (hx ▸ e), hL _ hid']

theorem Local_setPromise_setTask {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {p : PromiseObject} {t : TaskObject} {x : Object} (hx : x.id = id)
    (h : { Abstract.Object.withPromise id p (Origin.find org id) with task := some t } = x) :
    Local o (org.write x) (Abstract.applyAll S [.setPromise id p, .setTask id t]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setTask, if_pos rfl, find_setPromise_same, hL _ hid', find_write_at hx, Option.map_some]
    rw [← h]
  · rw [find_setTask, if_neg e, find_setPromise_other _ _ _ _ e, find_write_other _ _ _ (hx ▸ e),
        hL _ hid']

theorem Local_setTask {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    {id : Ident} (hid : id.origin = o) {t : TaskObject} {x : Object} (hx : x.id = id)
    (h : (Origin.find org id).map (fun ob => { ob with task := some t }) = some x) :
    Local o (org.write x) (Abstract.applyAll S [.setTask id t]) := by
  intro id' hid'
  simp only [Abstract.applyAll]
  by_cases e : id' = id
  · subst e
    rw [find_setTask, if_pos rfl, hL _ hid', h, find_write_at hx]
  · rw [find_setTask, if_neg e, find_write_other _ _ _ (hx ▸ e), hL _ hid']

theorem Local_sends {o : String} {org : Origin} {S : Abstract.State} (fx : List Abstract.Effect)
    (sends : List (String × Message))
    (h : Local o org (Abstract.applyAll S fx)) :
    Local o org (Abstract.applyAll S (fx ++ sends.map fun (a, m) => .setMessage a m)) := by
  intro id hid
  rw [applyAll_append]
  have : ∀ (T : Abstract.State) (l : List (String × Message)),
      find (Abstract.applyAll T (l.map fun (a, m) => Abstract.Effect.setMessage a m)) id = find T id := by
    intro T l
    induction l generalizing T with
    | nil => rfl
    | cons x xs ih => obtain ⟨a, m⟩ := x; simp only [List.map_cons, Abstract.applyAll]; rw [ih, find_setMessage]
  rw [this]
  exact h id hid

theorem orig_write {o : String} {org : Origin} {x : Object} (hx : x.id.origin = o) :
    (∀ ob ∈ org.objects, ob.id.origin = o) → ∀ ob ∈ (org.write x).objects, ob.id.origin = o :=
  fun h => write_derived h hx

theorem find_orig {org : Origin} {id : Ident} {ob : Object}
    (h : Origin.find org id = some ob) : ob.id = id := (find_mem h).2

theorem get_some {org : Origin} {id : Ident} {now : Nat} {x : Object}
    (h : org.get id now = some x) : ∃ ob, Origin.find org id = some ob ∧ x = ob.project now := by
  rw [get_eq] at h
  cases hf : Origin.find org id with
  | none => rw [hf] at h; cases h
  | some ob => rw [hf] at h; exact ⟨ob, rfl, (Option.some.inj h).symm⟩

open Protocol (PromiseGetReq PromiseCreateReq PromiseSettleReq PromiseRegisterCallbackReq
               PromiseRegisterListenerReq PromiseSearchReq)

theorem promiseGet_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseGetReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseGet req now (env S))
      (Concrete.promiseGet now org req).1 (Concrete.promiseGet now org req).2 := by
  unfold Abstract.promiseGet Concrete.promiseGet
  simp only [bind_apply, readObject_false, get_eq, hL req.id hid]
  cases Origin.find org req.id with
  | none => exact Sim.skip hL _
  | some ob => exact Sim.skip hL _

theorem promiseCreate_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseCreateReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseCreate req now (env S))
      (Concrete.promiseCreate now org req).1 (Concrete.promiseCreate now org req).2 := by
  unfold Abstract.promiseCreate Concrete.promiseCreate
  simp only [bind_apply, readObject_false, get_eq, hL req.id hid]
  cases hf : Origin.find org req.id with
  | some ob => exact Sim.skip hL _
  | none =>
      cases hdel : req.delay <;>
      simp only [Option.map_none, Abstract.createPromise, bind_apply, pure_apply, hdel] <;>
      by_cases h1 : req.timeoutAt > now <;>
      by_cases h2 : req.type.isRunnable = true <;>
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] <;>
      first
        | exact ⟨rfl, ⟨hid, hid, trivial⟩,
            Local_setPromise_setTask hL hid rfl (by simp [hf, Abstract.Object.withPromise]),
            rfl, orig_write hid, write_nodup⟩
        | exact ⟨rfl, ⟨hid, trivial⟩,
            Local_setPromise hL hid rfl (by simp [hf, Abstract.Object.withPromise]),
            rfl, orig_write hid, write_nodup⟩

theorem settable_ne_pending {st : PromiseState} (h : st.settable = true) : (st != .pending) = true := by
  cases st <;> simp_all [Protocol.PromiseState.settable]

theorem project_pending_eq {ob : Object} {now : Nat}
    (h : ((ob.project now).promise.state == PromiseState.pending) = true) : ob.project now = ob :=
  project_pending_id ob now (by simpa using h)

theorem promiseSettle_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (now : Nat) (req : PromiseSettleReq) (hid : req.id.origin = o) :
    Sim o org S (Abstract.promiseSettle req now (env S))
      (Concrete.promiseSettle now org req).1 (Concrete.promiseSettle now org req).2 := by
  unfold Abstract.promiseSettle Concrete.promiseSettle
  by_cases hs : req.state.settable = true
  · have hs' : (!req.state.settable) = false := by simp [hs]
    simp only [hs', Bool.false_eq_true, ↓reduceIte, bind_apply, readObject_false, get_eq, hL req.id hid]
    cases hf : Origin.find org req.id with
    | none => exact Sim.skip hL _
    | some ob =>
        simp only [Option.map_some]
        by_cases hp : ((ob.project now).promise.state == PromiseState.pending) = true
        · have heq := project_pending_eq hp
          rw [heq] at hp ⊢
          simp only [hp, ↓reduceIte, Abstract.setSettled, bind_apply, setPromise_apply,
            settable_ne_pending hs, pure_apply]
          have hob := find_orig hf
          have hido : ob.id.origin = o := hob ▸ hid
          cases ht : ob.task with
          | none =>
              refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_write hido, write_nodup⟩
              exact Local_setPromise hL hido rfl (by rw [hob, hf]; simp [Abstract.Object.withPromise, ht, hob])
          | some t =>
              by_cases hft : (t.state != TaskState.fulfilled) = true
              · have hft' : t.state ≠ TaskState.fulfilled := by simpa using hft
                simp only [hft, ↓reduceIte, setTask_apply]
                refine ⟨rfl, ⟨hido, hido, trivial⟩, ?_, rfl, orig_write hido, write_nodup⟩
                exact Local_setPromise_setTask hL hido rfl
                  (by rw [hob, hf]; simp [Abstract.Object.withPromise, hob, hft'])
              · have hft' : t.state = TaskState.fulfilled := by simpa using hft
                simp only [hft, Bool.false_eq_true, ↓reduceIte, pure_apply]
                refine ⟨rfl, ⟨hido, trivial⟩, ?_, rfl, orig_write hido, write_nodup⟩
                exact Local_setPromise hL hido rfl
                  (by rw [hob, hf]; simp [Abstract.Object.withPromise, ht, hob, hft'])
        · have hp' : ((ob.project now).promise.state == PromiseState.pending) = false := by simpa using hp
          simp only [hp', Bool.false_eq_true, ↓reduceIte, pure_apply]
          exact Sim.skip hL _
  · have hs' : (!req.state.settable) = true := by simpa using hs
    simp only [hs', ↓reduceIte, pure_apply]
    exact Sim.skip hL _

end Refinement
