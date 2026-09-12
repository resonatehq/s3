import «03-theorems».«entries»

namespace Abstract

open Protocol (PromiseObject TaskObject Object)
namespace Stepwise

open Abstract

theorem find?_self_of_nodup {α κ} [BEq κ] [LawfulBEq κ] (key : α → κ) :
    ∀ (l : List α), (l.map key).Nodup → ∀ (x : α), x ∈ l →
      l.find? (fun y => key y == key x) = some x
  | [],     _,   x, hx => absurd hx (by simp)
  | c :: l, hnd, x, hx => by
      simp only [List.map_cons] at hnd
      have hnc := List.nodup_cons.mp hnd
      by_cases hk : (key c == key x) = true
      · have hxc : x = c := by
          rcases List.mem_cons.mp hx with rfl | hxl
          · rfl
          · exact absurd (by
              refine List.mem_map.mpr ⟨x, hxl, ?_⟩
              exact (eq_of_beq hk).symm) hnc.1
        simp [List.find?_cons, hk, hxc]
      · have hxl : x ∈ l := by
          rcases List.mem_cons.mp hx with rfl | h
          · exact absurd (by simp) hk
          · exact h
        simp only [List.find?_cons, hk, if_false]
        exact find?_self_of_nodup key l hnc.2 x hxl

theorem any_id_upsert {α κ} [BEq κ] [LawfulBEq κ] (idOf : α → κ) (x : α) (l : List α) (id : κ)
    (h : l.any (fun y => idOf y == id) = true) :
    (x :: l.filter (fun y => idOf y != idOf x)).any (fun y => idOf y == id) = true := by
  obtain ⟨y, hy, hyid⟩ := List.any_eq_true.mp h
  by_cases hx : (idOf x == id) = true
  · simp [List.any_cons, hx]
  · refine List.any_eq_true.mpr ⟨y, ?_, hyid⟩
    simp only [List.mem_cons]
    refine Or.inr (List.mem_filter.mpr ⟨hy, ?_⟩)
    simp only [bne_iff_ne, ne_eq]
    intro hc
    exact absurd (hc ▸ hyid) hx

theorem any_id_map (m : Object → Object) (hm : ∀ o, (m o).id = o.id) (id : Protocol.Ident) :
    ∀ l : List Object, l.any (·.id == id) = true → (l.map m).any (·.id == id) = true
  | [],     h => h
  | a :: l, h => by
      simp only [List.map_cons, List.any_cons, hm a] at *
      cases hb : (a.id == id) with
      | true  => simp [hb]
      | false => simp only [hb, Bool.false_or] at *; exact any_id_map m hm id l h

theorem find?_map_id (m : Object → Object) (hm : ∀ o, (m o).id = o.id) (id : Protocol.Ident) :
    ∀ l : List Object,
      (l.map m).find? (·.id == id) = (l.find? (·.id == id)).map m
  | []     => rfl
  | a :: l => by
      simp only [List.map_cons, List.find?_cons, hm a]
      cases hb : (a.id == id) with
      | true  => simp [hb]
      | false => simp [hb, find?_map_id m hm id l]

theorem setTask_id (i : Protocol.Ident) (t : TaskObject) (o : Object) :
    (if o.id == i then { o with task := some t } else o).id = o.id := by
  split <;> rfl

theorem setTask_promise (i : Protocol.Ident) (t : TaskObject) (o : Object) :
    (if o.id == i then { o with task := some t } else o).promise = o.promise := by
  split <;> rfl

theorem withPromise_find?_id (s : State) (i : Protocol.Ident) (p : PromiseObject) :
    (Object.withPromise i p (s.objects.find? (·.id == i))).id = i := by
  unfold Object.withPromise
  cases h : s.objects.find? (·.id == i) with
  | none   => rfl
  | some o => exact eq_of_beq (by simpa using List.find?_some h)

theorem any_id_upsert' (x : Object) (k : Protocol.Ident) (hk : x.id = k) (l : List Object)
    (id : Protocol.Ident) (h : l.any (·.id == id) = true) :
    ((x :: l.filter (fun y => y.id != k)).any (·.id == id)) = true := by
  subst hk; exact any_id_upsert (·.id) x l id h

theorem find?_upsert' (x : Object) (k : Protocol.Ident) (hk : x.id = k) (l : List Object)
    (id : Protocol.Ident) :
    (x :: l.filter (fun y => y.id != k)).find? (·.id == id)
      = if (x.id == id) = true then some x else l.find? (·.id == id) := by
  subst hk; exact Lookup.find?_upsert (·.id) x l id

theorem object_id_apply (f : Effect) (s : State) (id : Protocol.Ident)
    (h : s.objects.any (·.id == id) = true) :
    (f.apply s).objects.any (·.id == id) = true := by
  cases f with
  | setPromise i p =>
      exact any_id_upsert' _ i (withPromise_find?_id s i p) s.objects id h
  | setTask i t    => exact any_id_map _ (setTask_id i t) id s.objects h
  | setSchedule _ | delSchedule _ | setMessage _ _ =>
      simpa [Effect.apply] using h

theorem object_id_applyAll :
    ∀ (w : List Effect) (s : State) (id : Protocol.Ident),
      s.objects.any (·.id == id) = true → (applyAll s w).objects.any (·.id == id) = true
  | [],      _, _,  h => h
  | f :: fs, s, id, h => object_id_applyAll fs (f.apply s) id (object_id_apply f s id h)

theorem promise?_setPromise (s : State) (i : Protocol.Ident) (p : PromiseObject) (id : Protocol.Ident) :
    (Effect.apply s (Effect.setPromise i p)).promise? id
      = if (i == id) = true then some p else s.promise? id := by
  have hw := withPromise_find?_id s i p
  show ((Object.withPromise i p (s.objects.find? (·.id == i))
           :: s.objects.filter (fun z => z.id != i)).find? (·.id == id)).map (·.promise) = _
  rw [find?_upsert' _ i hw s.objects id, hw]
  by_cases hy : (i == id) = true
  · rw [if_pos hy, if_pos hy]
    unfold Object.withPromise
    cases s.objects.find? (·.id == i) <;> rfl
  · rw [if_neg hy, if_neg hy]; rfl

theorem promise?_setTask (s : State) (i : Protocol.Ident) (t : TaskObject) (id : Protocol.Ident) :
    (Effect.apply s (Effect.setTask i t)).promise? id = s.promise? id := by
  show ((s.objects.map (fun o => if o.id == i then { o with task := some t } else o)).find?
          (·.id == id)).map (·.promise)
        = (s.objects.find? (·.id == id)).map (·.promise)
  rw [find?_map_id _ (setTask_id i t) id]
  cases s.objects.find? (·.id == id) with
  | none   => rfl
  | some o => simp only [Option.map_some]; split <;> rfl

theorem find?_applyAll_promise :
    ∀ (w : List Effect) (s : State) (id : Protocol.Ident),
      (applyAll s w).promise? id = s.promise? id
      ∨ ∃ p, Effect.setPromise id p ∈ w ∧ (applyAll s w).promise? id = some p
  | [],      _, _  => Or.inl rfl
  | f :: fs, s, id => by
      rw [show applyAll s (f :: fs) = applyAll (f.apply s) fs from rfl]
      rcases find?_applyAll_promise fs (f.apply s) id with h | ⟨x, hx, hfind⟩
      · rw [h]
        cases f with
        | setPromise i p =>
            rw [promise?_setPromise]
            by_cases hy : (i == id) = true
            · have : i = id := eq_of_beq hy
              subst this
              exact Or.inr ⟨p, by simp, by rw [if_pos hy]⟩
            · exact Or.inl (by rw [if_neg hy])
        | setTask i t => exact Or.inl (promise?_setTask s i t id)
        | setSchedule _ | delSchedule _ | setMessage _ _ => exact Or.inl rfl
      · exact Or.inr ⟨x, by simp [hx], hfind⟩

theorem eraseDupsBy_loop_length {α} [BEq α] [LawfulBEq α] :
    ∀ (as bs : List α), as.Nodup → (∀ a ∈ as, a ∉ bs) →
      (List.eraseDupsBy.loop (· == ·) as bs).length = bs.length + as.length
  | [],      bs, _,   _      => by simp [List.eraseDupsBy.loop]
  | a :: as, bs, hnd, hdisj => by
      have hab : bs.any (a == ·) = false := by
        cases hcase : bs.any (fun x => a == x) with
        | false => rfl
        | true =>
            obtain ⟨b, hb, heq⟩ := List.any_eq_true.mp hcase
            exact absurd (by simpa [eq_of_beq heq] using hb) (hdisj a (by simp))
      have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
      have hna : a ∉ as := (List.nodup_cons.mp hnd).1
      have hdisj' : ∀ x ∈ as, x ∉ (a :: bs) := by
        intro x hx hmem
        rcases List.mem_cons.mp hmem with rfl | hb
        · exact hna hx
        · exact hdisj x (by simp [hx]) hb
      have ih := eraseDupsBy_loop_length as (a :: bs) hnd' hdisj'
      simp only [List.eraseDupsBy.loop, hab]
      simp only [ih, List.length_cons]
      omega

theorem eraseDups_length_of_nodup {α} [BEq α] [LawfulBEq α] (l : List α) (h : l.Nodup) :
    l.eraseDups.length = l.length := by
  have := eraseDupsBy_loop_length l [] h (by simp)
  simpa [List.eraseDups, List.eraseDupsBy] using this

theorem nodup_upsert {α κ} [BEq κ] [LawfulBEq κ] (key : α → κ) (x : α) (l : List α)
    (h : (l.map key).Nodup) :
    (((x :: l.filter (fun y => key y != key x)).map key).Nodup) := by
  simp only [List.map_cons]
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨y, hy, hyid⟩ := List.mem_map.mp hmem
    have hne := (List.mem_filter.mp hy).2
    simp only [bne_iff_ne, ne_eq] at hne
    exact hne hyid
  · exact List.Nodup.sublist (List.Sublist.map key List.filter_sublist) h

theorem nodup_upsert' (x : Object) (k : Protocol.Ident) (hk : x.id = k) (l : List Object)
    (h : (l.map (·.id)).Nodup) :
    (((x :: l.filter (fun y => y.id != k)).map (·.id)).Nodup) := by
  subst hk; exact nodup_upsert (·.id) x l h

theorem nodup_filter {α κ} (key : α → κ) (p : α → Bool) (l : List α)
    (h : (l.map key).Nodup) : ((l.filter p).map key).Nodup :=
  List.Nodup.sublist (List.Sublist.map key List.filter_sublist) h

def StoreNodup (s : State) : Prop :=
  (s.objects.map (·.id)).Nodup ∧ (s.schedules.map (·.id)).Nodup
    ∧ (s.outbox.map (·.key)).Nodup

theorem nodup_map_id (m : Object → Object) (hm : ∀ o, (m o).id = o.id) (l : List Object)
    (h : (l.map (·.id)).Nodup) : ((l.map m).map (·.id)).Nodup := by
  have : (l.map m).map (·.id) = l.map (·.id) := by
    simp [List.map_map, Function.comp_def, hm]
  rw [this]; exact h

theorem storeNodup_apply (f : Effect) (s : State) (h : StoreNodup s) :
    StoreNodup (f.apply s) := by
  obtain ⟨h1, h3, h4⟩ := h
  cases f with
  | setPromise i p => exact ⟨nodup_upsert' _ i (withPromise_find?_id s i p) _ h1, h3, h4⟩
  | setTask i t    => exact ⟨nodup_map_id _ (setTask_id i t) _ h1, h3, h4⟩
  | setSchedule x  => exact ⟨h1, nodup_upsert _ x _ h3, h4⟩
  | delSchedule i  => exact ⟨h1, nodup_filter _ _ _ h3, h4⟩
  | setMessage a m => exact ⟨h1, h3, nodup_upsert _ _ _ h4⟩

theorem storeNodup_applyAll :
    ∀ (w : List Effect) (s : State), StoreNodup s → StoreNodup (applyAll s w)
  | [],      _, h => h
  | f :: fs, s, h => storeNodup_applyAll fs (f.apply s) (storeNodup_apply f s h)

theorem storeNodup_init : StoreNodup State.init :=
  ⟨List.nodup_nil, List.nodup_nil, List.nodup_nil⟩

theorem storeNodup_step (mat : Bool) (st : Event) (now : Nat) (s : State)
    (h : StoreNodup s) : StoreNodup (step mat st now s).2 :=
  storeNodup_applyAll _ s h

section Entries

open Properties

theorem task?_setPromise (s : State) (i : Protocol.Ident) (p : PromiseObject) (id : Protocol.Ident) :
    (Effect.apply s (Effect.setPromise i p)).task? id = s.task? id := by
  have hw := withPromise_find?_id s i p
  show ((Object.withPromise i p (s.objects.find? (·.id == i))
           :: s.objects.filter (fun z => z.id != i)).find? (·.id == id)).bind (·.task)
        = (s.objects.find? (·.id == id)).bind (·.task)
  rw [find?_upsert' _ i hw s.objects id, hw]
  by_cases hi : (i == id) = true
  · rw [if_pos hi, show id = i from (eq_of_beq hi).symm]
    unfold Object.withPromise
    cases s.objects.find? (·.id == i) <;> rfl
  · rw [if_neg hi]

theorem task?_setTask_isSome (s : State) (i : Protocol.Ident) (t : TaskObject) (id : Protocol.Ident)
    (h : (s.task? id).isSome = true) :
    ((Effect.apply s (Effect.setTask i t)).task? id).isSome = true := by
  show (((s.objects.map (fun o => if o.id == i then { o with task := some t } else o)).find?
          (·.id == id)).bind (·.task)).isSome = true
  rw [find?_map_id _ (setTask_id i t) id]
  unfold State.task? at h
  cases hfo : s.objects.find? (·.id == id) with
  | none   => rw [hfo] at h; simp at h
  | some o =>
      rw [hfo] at h
      simp only [Option.map_some, Option.bind_some] at h ⊢
      split
      · simp
      · exact h

theorem hasTask_apply (f : Effect) (s : State) (id : Protocol.Ident)
    (h : s.hasTask id = true) : (f.apply s).hasTask id = true := by
  unfold State.hasTask at *
  cases f with
  | setPromise i p => rw [task?_setPromise]; exact h
  | setTask i t    => exact task?_setTask_isSome s i t id h
  | setSchedule _ | delSchedule _ | setMessage _ _ => exact h

theorem hasTask_applyAll :
    ∀ (w : List Effect) (s : State) (id : Protocol.Ident),
      s.hasTask id = true → (applyAll s w).hasTask id = true
  | [],      _, _,  h => h
  | f :: fs, s, id, h => hasTask_applyAll fs (f.apply s) id (hasTask_apply f s id h)

theorem monotone_promise_set_grows_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    monotone_promise_set_grows n' s (step mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  show (step mat st now s).2.objects.any (·.id == o.id) = true
  exact object_id_applyAll _ s o.id (List.any_eq_true.mpr ⟨o, ho, by simp⟩)

theorem monotone_task_set_grows_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) (hnd : StoreNodup s) :
    monotone_task_set_grows n' s (step mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  cases hto : o.task with
  | none => simp [hto]
  | some t =>
      have hpre : s.hasTask o.id = true := by
        unfold State.hasTask State.task?
        rw [find?_self_of_nodup (·.id) s.objects hnd.1 o ho]
        simp [hto]
      show (!(some t).isSome || (step mat st now s).2.hasTask o.id) = true
      simp only [Option.isSome_some, Bool.not_true, Bool.false_or]
      exact hasTask_applyAll _ s o.id hpre

theorem object_ids_unique_of_nodup (now : Nat) (s : State) (h : StoreNodup s) :
    well_formed_store_object_ids_unique now s = true := by
  simp [well_formed_store_object_ids_unique, eraseDups_length_of_nodup _ h.1]

theorem schedule_ids_unique_of_nodup (now : Nat) (s : State) (h : StoreNodup s) :
    well_formed_store_schedule_ids_unique now s = true := by
  simp [well_formed_store_schedule_ids_unique, eraseDups_length_of_nodup _ h.2.1]

theorem outbox_keys_unique_of_nodup (now : Nat) (s : State) (h : StoreNodup s) :
    well_formed_store_outbox_keys_unique now s = true := by
  simp [well_formed_store_outbox_keys_unique, eraseDups_length_of_nodup _ h.2.2]

end Entries

end Stepwise
end Abstract
