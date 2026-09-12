import impl.wf

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject Request Response)
open Concrete (Origin Commands Path Blob)

def originOf? : Option Blob → Origin
  | some (.origin org) => org
  | _ => {}

theorem State.origin_eq (s : Concrete.State) (name : String) :
    s.origin name = originOf? (s.blob? (.origin name)) := by
  unfold Concrete.State.origin originOf?
  cases s.blob? (.origin name) with
  | none => rfl
  | some b => cases b <;> rfl

def blobOrig : Path × Blob → Option Origin
  | (.origin _, .origin org) => some org
  | _ => none

theorem origins_eq (s : Concrete.State) : origins s = s.bucket.filterMap blobOrig := rfl

def Owned (l : List (Path × Blob)) : Prop :=
  ∀ name b, (Path.origin name, b) ∈ l → ∃ org, b = .origin org ∧ ∀ o ∈ org.objects, o.id.origin = name

theorem Owned.tail {x : Path × Blob} {l : List (Path × Blob)} (h : Owned (x :: l)) : Owned l :=
  fun n b hb => h n b (List.mem_cons_of_mem _ hb)

theorem find?_objects_none {org : Origin} {name : String} (horg : ∀ o ∈ org.objects, o.id.origin = name)
    {id : Ident} (hne : name ≠ id.origin) : org.objects.find? (·.id == id) = none := by
  rw [List.find?_eq_none]
  intro o ho
  have := horg o ho
  simp only [beq_iff_eq]
  intro e
  exact hne (this ▸ e ▸ rfl)

theorem find_flat_none (id : Ident) : ∀ (l : List (Path × Blob)), Owned l →
    Path.origin id.origin ∉ l.map (·.1) →
    ((l.filterMap blobOrig).flatMap (·.objects)).find? (·.id == id) = none
  | [], _, _ => rfl
  | (p, b) :: l, hb, hnot => by
      simp only [List.map_cons, List.mem_cons, not_or] at hnot
      cases p with
      | timer t =>
          simp only [List.filterMap_cons, blobOrig]
          exact find_flat_none id l hb.tail hnot.2
      | origin name =>
          obtain ⟨org, rfl, horg⟩ := hb name b (List.mem_cons_self ..)
          have hne : name ≠ id.origin := fun e => hnot.1 (by rw [e])
          simp only [List.filterMap_cons, blobOrig, List.flatMap_cons, List.find?_append,
            find?_objects_none horg hne, Option.none_or]
          exact find_flat_none id l hb.tail hnot.2

theorem find_flat (id : Ident) : ∀ (l : List (Path × Blob)), Owned l → (l.map (·.1)).Nodup →
    ((l.filterMap blobOrig).flatMap (·.objects)).find? (·.id == id) =
      Origin.find (originOf? ((l.find? (·.1 == Path.origin id.origin)).map (·.2))) id
  | [], _, _ => rfl
  | (p, b) :: l, hb, hnd => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases p with
      | timer t =>
          have hne : ((Path.timer t, b).1 == Path.origin id.origin) = false := by simp
          simp only [List.filterMap_cons, blobOrig, List.find?_cons, hne]
          exact find_flat id l hb.tail hnd.2
      | origin name =>
          obtain ⟨org, rfl, horg⟩ := hb name b (List.mem_cons_self ..)
          by_cases e : name = id.origin
          · subst e
            simp only [List.filterMap_cons, blobOrig, List.flatMap_cons, List.find?_append, List.find?_cons,
              beq_self_eq_true, Option.map_some, originOf?, find_flat_none id l hb.tail hnd.1, Option.or_none]
            rfl
          · have hf : ((Path.origin name, Blob.origin org).1 == Path.origin id.origin) = false := by
              simpa using e
            simp only [List.filterMap_cons, blobOrig, List.flatMap_cons, List.find?_append, List.find?_cons,
              hf, find?_objects_none horg e, Option.none_or]
            exact find_flat id l hb.tail hnd.2

theorem find_abstract {s : Concrete.State} (inv : Inv s) (id : Ident) :
    find (abstract s) id = Origin.find (s.origin id.origin) id := by
  show ((origins s).flatMap (·.objects)).find? (·.id == id) = _
  rw [State.origin_eq, origins_eq]
  unfold Concrete.State.blob?
  exact find_flat id s.bucket
    (fun n b h => let ⟨org, hb, ho, _, _⟩ := inv.blobs n b h; ⟨org, hb, ho⟩) inv.paths

theorem Inv.origin_props {s : Concrete.State} (inv : Inv s) (name : String) :
    (∀ o ∈ (s.origin name).objects, o.id.origin = name) ∧
    ((s.origin name).objects.map (·.id)).Nodup ∧ WF (s.origin name) := by
  rw [State.origin_eq]
  unfold Concrete.State.blob?
  cases hf : s.bucket.find? (·.1 == Path.origin name) with
  | none =>
      simp only [Option.map_none, originOf?]
      exact ⟨fun o ho => by simp at ho, List.nodup_nil, fun ob hob => by simp at hob⟩
  | some x =>
      have hmem := List.mem_of_find?_eq_some hf
      have hx : x.1 = Path.origin name := by simpa using List.find?_some hf
      obtain ⟨p, b⟩ := x
      simp only at hx
      subst hx
      obtain ⟨org, rfl, horg, hnd, hwf⟩ := inv.blobs name b hmem
      exact ⟨horg, hnd, hwf⟩

theorem Local_of_rel {s : Concrete.State} {S : Abstract.State} (inv : Inv s) (rel : Equiv (abstract s) S)
    (name : String) : Local name (s.origin name) S := by
  intro id hid
  have h1 : find S id = find (abstract s) id := (rel.1 id).symm
  rw [h1, find_abstract inv id, hid]

def blobIn (bk : List (Path × Blob)) (q : Path) : Option Blob := (bk.find? (·.1 == q)).map (·.2)

theorem blob?_eq (s : Concrete.State) (q : Path) : s.blob? q = blobIn s.bucket q := rfl

theorem find?_filter_path (bk : List (Path × Blob)) (p q : Path) (h : q ≠ p) :
    (bk.filter (·.1 != p)).find? (·.1 == q) = bk.find? (·.1 == q) := by
  induction bk with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.1 = q
      · have h1 : (x.1 == q) = true := by simpa using hx
        have h2 : (x.1 != p) = true := by simpa [hx] using h
        simp [h1, h2]
      · have h1 : (x.1 == q) = false := by simpa using hx
        by_cases hp : x.1 = p
        · have h2 : (x.1 != p) = false := by simpa using hp
          simp [h1, h2, ih]
        · have h2 : (x.1 != p) = true := by simpa using hp
          simp [h1, h2, ih]

theorem blobIn_put (bk : List (Path × Blob)) (p q : Path) (b : Blob) :
    blobIn ((p, b) :: bk.filter (·.1 != p)) q = if q = p then some b else blobIn bk q := by
  unfold blobIn
  by_cases e : q = p
  · subst e; simp
  · have h1 : ((p, b).1 == q) = false := by simpa using Ne.symm e
    simp only [List.find?_cons, h1, if_neg e]
    rw [find?_filter_path _ _ _ e]

theorem blobIn_del (bk : List (Path × Blob)) (p q : Path) :
    blobIn (bk.filter (·.1 != p)) q = if q = p then none else blobIn bk q := by
  unfold blobIn
  by_cases e : q = p
  · subst e
    rw [if_pos rfl]
    have : (bk.filter (·.1 != q)).find? (·.1 == q) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp only [List.mem_filter] at hx
      simpa using hx.2
    rw [this]; rfl
  · rw [if_neg e, find?_filter_path _ _ _ e]

theorem nodup_put {bk : List (Path × Blob)} (h : (bk.map (·.1)).Nodup) (p : Path) (b : Blob) :
    (((p, b) :: bk.filter (·.1 != p)).map (·.1)).Nodup := by
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map (fun x : Path × Blob => x.1) List.filter_sublist).nodup h⟩
  intro hm
  simp only [List.mem_map, List.mem_filter] at hm
  obtain ⟨x, ⟨_, hx⟩, hxp⟩ := hm
  simp [hxp] at hx

theorem nodup_del {bk : List (Path × Blob)} (h : (bk.map (·.1)).Nodup) (p : Path) :
    ((bk.filter (·.1 != p)).map (·.1)).Nodup :=
  (List.Sublist.map (fun x : Path × Blob => x.1) List.filter_sublist).nodup h

structure Same (s s' : Concrete.State) : Prop where
  blob  : ∀ m, s'.blob? (.origin m) = s.blob? (.origin m)
  out   : s'.outbox = s.outbox
  mem   : ∀ m b, (Path.origin m, b) ∈ s'.bucket → (Path.origin m, b) ∈ s.bucket
  nodup : (s.bucket.map (·.1)).Nodup → (s'.bucket.map (·.1)).Nodup

theorem Same.refl (s : Concrete.State) : Same s s := ⟨fun _ => rfl, rfl, fun _ _ h => h, fun h => h⟩

theorem Same.trans {s t u : Concrete.State} (h1 : Same s t) (h2 : Same t u) : Same s u :=
  ⟨fun m => (h2.blob m).trans (h1.blob m), h2.out.trans h1.out, fun m b h => h1.mem m b (h2.mem m b h),
   fun h => h2.nodup (h1.nodup h)⟩

variable {H : Concrete.Hasher}

theorem same_put_timer {s s' : Concrete.State} {t : Concrete.Timer} {c : Concrete.Cond H}
    (h : (Concrete.Effect.put (Path.timer t) Blob.timer c).apply s = some s') : Same s s' := by
  simp only [Concrete.Effect.apply] at h
  split at h
  · cases h
    refine ⟨fun m => ?_, rfl, fun m b hm => ?_, fun hn => nodup_put hn _ _⟩
    · rw [blob?_eq, blob?_eq]
      simp only [blobIn_put]
      rw [if_neg (by simp)]
    · simp only [List.mem_cons, List.mem_filter] at hm
      rcases hm with hm | ⟨hm, _⟩
      · cases hm
      · exact hm
  · cases h

theorem same_del_timer (s : Concrete.State) (t : Concrete.Timer) :
    Same s { s with bucket := s.bucket.filter (·.1 != Path.timer t) } := by
  refine ⟨fun m => ?_, rfl, fun m b hm => ?_, fun hn => nodup_del hn _⟩
  · rw [blob?_eq, blob?_eq]
    simp only [blobIn_del]
    rw [if_neg (by simp)]
  · simp only [List.mem_filter] at hm
    exact hm.1

def TimerFx : Concrete.Effect H → Prop
  | .put (.timer _) .timer .any => True
  | .del (.timer _) => True
  | _ => False

theorem timers_phase : ∀ (es : List (Concrete.Effect H)) (s : Concrete.State), (∀ e ∈ es, TimerFx e) →
    (Concrete.applyAll s es).2 = true ∧ Same s (Concrete.applyAll s es).1
  | [], s, _ => ⟨rfl, Same.refl s⟩
  | e :: es, s, h => by
      have he := h e (List.mem_cons_self ..)
      have hes : ∀ e ∈ es, TimerFx e := fun e he => h e (List.mem_cons_of_mem _ he)
      cases e with
      | put p b c =>
          cases p with
          | origin _ => exact False.elim he
          | timer t =>
              cases b with
              | origin _ => exact False.elim he
              | timer =>
                  cases c with
                  | any =>
                      have hs : (Concrete.Effect.put (H := H) (Path.timer t) Blob.timer .any).apply s =
                          some { s with bucket := (Path.timer t, Blob.timer) :: s.bucket.filter (·.1 != Path.timer t) } := by
                        simp [Concrete.Effect.apply, Concrete.Cond.holds]
                      simp only [Concrete.applyAll, hs]
                      obtain ⟨h1, h2⟩ := timers_phase es _ hes
                      exact ⟨h1, (same_put_timer hs).trans h2⟩
                  | absent => exact False.elim he
                  | hash _ => exact False.elim he
      | del p =>
          cases p with
          | origin _ => exact False.elim he
          | timer t =>
              simp only [Concrete.applyAll, Concrete.Effect.apply]
              obtain ⟨h1, h2⟩ := timers_phase es _ hes
              exact ⟨h1, (same_del_timer s t).trans h2⟩
      | send _ _ => exact False.elim he

theorem sends_phase : ∀ (ms : List (String × Message)) (s : Concrete.State),
    (Concrete.applyAll s (ms.map fun (a, m) => Concrete.Effect.send (H := H) a m)).2 = true ∧
    (Concrete.applyAll s (ms.map fun (a, m) => Concrete.Effect.send (H := H) a m)).1.bucket = s.bucket ∧
    (Concrete.applyAll s (ms.map fun (a, m) => Concrete.Effect.send (H := H) a m)).1.outbox =
      sendsFold s.outbox ms
  | [], s => ⟨rfl, rfl, rfl⟩
  | (a, m) :: ms, s => by
      simp only [List.map_cons, Concrete.applyAll, Concrete.Effect.apply, sendsFold]
      exact sends_phase ms _

theorem origin_put {s s' : Concrete.State} {name : String} {org : Origin} {c : Concrete.Cond H}
    (h : (Concrete.Effect.put (Path.origin name) (Blob.origin org) c).apply s = some s') :
    s'.blob? (.origin name) = some (.origin org) ∧
    (∀ m, m ≠ name → s'.blob? (.origin m) = s.blob? (.origin m)) ∧
    s'.outbox = s.outbox ∧
    (∀ m b, (Path.origin m, b) ∈ s'.bucket → (m = name ∧ b = .origin org) ∨ (Path.origin m, b) ∈ s.bucket) ∧
    ((s.bucket.map (·.1)).Nodup → (s'.bucket.map (·.1)).Nodup) := by
  simp only [Concrete.Effect.apply] at h
  split at h
  · cases h
    refine ⟨?_, fun m hm => ?_, rfl, fun m b hm => ?_, fun hn => nodup_put hn _ _⟩
    · rw [blob?_eq]; simp [blobIn_put]
    · rw [blob?_eq, blob?_eq]; simp [blobIn_put, hm]
    · simp only [List.mem_cons, List.mem_filter] at hm
      rcases hm with hm | ⟨hm, _⟩
      · cases hm; exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr hm
  · cases h

theorem run_state (H : Concrete.Hasher) (name : String) (c : Commands) (s : Concrete.State) :
    (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.blob? (.origin name)
      = some (.origin c.put) ∧
    (∀ m, m ≠ name →
      (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.blob? (.origin m)
        = s.blob? (.origin m)) ∧
    (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.outbox
      = sendsFold s.outbox c.send ∧
    (∀ m b, (Path.origin m, b) ∈
        (Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.bucket →
      (m = name ∧ b = .origin c.put) ∨ (Path.origin m, b) ∈ s.bucket) ∧
    ((s.bucket.map (·.1)).Nodup →
      ((Concrete.applyAll s (c.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1.bucket.map (·.1)).Nodup) := by
  unfold Commands.effects
  obtain ⟨hA, sameA⟩ := timers_phase (H := H) (c.arm.map fun t => .put (.timer t) .timer .any) s
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  obtain ⟨s1, hs1⟩ : ∃ s1, Concrete.applyAll s (c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) = (s1, true) :=
    ⟨_, Prod.ext rfl hA⟩
  rw [hs1] at sameA
  simp only at sameA
  have hhold : (Concrete.Cond.of H (s.blob? (.origin name))).holds (s1.blob? (.origin name)) = true := by
    rw [sameA.blob]; exact Concrete.Cond.of_holds _
  have hP : (Concrete.Effect.put (H := H) (.origin name) (.origin c.put) (Concrete.Cond.of H (s.blob? (.origin name)))).apply s1 =
      some { s1 with bucket := (Path.origin name, Blob.origin c.put) :: s1.bucket.filter (·.1 != Path.origin name) } := by
    simp [Concrete.Effect.apply, hhold]
  obtain ⟨s2, hs2⟩ : ∃ s2, (Concrete.Effect.put (H := H) (.origin name) (.origin c.put) (Concrete.Cond.of H (s.blob? (.origin name)))).apply s1 = some s2 :=
    ⟨_, hP⟩
  obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := origin_put hs2
  obtain ⟨hD, sameD⟩ := timers_phase (H := H) (c.del.map fun t => .del (.timer t)) s2
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  obtain ⟨s3, hs3⟩ : ∃ s3, Concrete.applyAll s2 (c.del.map fun t => Concrete.Effect.del (H := H) (.timer t)) = (s3, true) :=
    ⟨_, Prod.ext rfl hD⟩
  rw [hs3] at sameD
  simp only at sameD
  obtain ⟨hS, hS1, hS2⟩ := sends_phase (H := H) c.send s3
  have e1 : Concrete.applyAll s ((c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) ++
      [Concrete.Effect.put (.origin name) (.origin c.put) (Concrete.Cond.of H (s.blob? (.origin name)))]) = (s2, true) := by
    rw [Concrete.applyAll_append, hs1, if_pos rfl]
    simp only [Concrete.applyAll, hs2]
  have e2 : Concrete.applyAll s ((c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) ++
      [Concrete.Effect.put (.origin name) (.origin c.put) (Concrete.Cond.of H (s.blob? (.origin name)))] ++
      c.del.map fun t => Concrete.Effect.del (.timer t)) = (s3, true) := by
    rw [Concrete.applyAll_append, e1, if_pos rfl]
    exact hs3
  rw [Concrete.applyAll_append, e2, if_pos rfl]
  refine ⟨?_, fun m hm => ?_, ?_, fun m b hm => ?_, fun hn => ?_⟩
  · rw [blob?_eq, hS1, ← blob?_eq, sameD.blob, hP1]
  · rw [blob?_eq, hS1, ← blob?_eq, sameD.blob, hP2 m hm, sameA.blob]
  · rw [hS2, sameD.out, hP3, sameA.out]
  · rw [hS1] at hm
    rcases hP4 m b (sameD.mem m b hm) with h | h
    · exact Or.inl h
    · exact Or.inr (sameA.mem m b h)
  · rw [hS1]
    exact sameD.nodup (hP5 (sameA.nodup hn))

theorem Sim.map' {o : String} {org : Origin} {S : Abstract.State} {α β : Type}
    {r : α × List Abstract.Effect} {res : α} {c : Commands} (f : α → β) (h : Sim o org S r res c) :
    Sim o org S (f r.1, r.2) (f res) c :=
  ⟨by rw [h.res], h.fx, h.loc, h.send, h.orig, h.nodup⟩

theorem handleExternal_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S) (now : Nat)
    (req : Request) (h : req.origin? = some o) :
    Sim o org S (Abstract.handleExternal req now (env S))
      (Concrete.handleExternal now org req).1 (Concrete.handleExternal now org req).2 := by
  cases req with
  | promiseGet r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.promiseGet now org r with ⟨res, c⟩
      have hs := promiseGet_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | promiseCreate r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.promiseCreate now org r with ⟨res, c⟩
      have hs := promiseCreate_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | promiseSettle r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.promiseSettle now org r with ⟨res, c⟩
      have hs := promiseSettle_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | promiseRegisterCallback r =>
      have hid : r.awaited.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.promiseRegisterCallback now org r with ⟨res, c⟩
      have hs := promiseRegisterCallback_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | promiseRegisterListener r =>
      have hid : r.awaited.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.promiseRegisterListener now org r with ⟨res, c⟩
      have hs := promiseRegisterListener_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | promiseSearch r => simp [Protocol.Request.origin?] at h
  | scheduleGet r => simp [Protocol.Request.origin?] at h
  | scheduleCreate r => simp [Protocol.Request.origin?] at h
  | scheduleDelete r => simp [Protocol.Request.origin?] at h
  | scheduleSearch r => simp [Protocol.Request.origin?] at h
  | taskGet r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskGet now org r with ⟨res, c⟩
      have hs := taskGet_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskCreate r =>
      have hid : r.action.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskCreate now org r with ⟨res, c⟩
      have hs := taskCreate_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskAcquire r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskAcquire now org r with ⟨res, c⟩
      have hs := taskAcquire_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskFence r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskFence now org r with ⟨res, c⟩
      have hs := taskFence_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskHeartbeat r =>
      have hid : ∀ ref ∈ r.tasks, ref.id.origin = o := by
        simp only [Protocol.Request.origin?] at h
        cases hts : r.tasks with
        | nil => simp [hts] at h
        | cons t ts =>
            simp only [hts] at h
            by_cases hall : (ts.all (·.id.origin == t.id.origin)) = true
            · simp only [hall, ↓reduceIte, Option.some.injEq] at h
              intro ref href
              rcases List.mem_cons.1 href with rfl | href
              · exact h
              · rw [← h]; simpa using List.all_eq_true.1 hall ref href
            · have hall' : (ts.all (·.id.origin == t.id.origin)) = false := by simpa using hall
              simp [hall'] at h
      rcases hC : Concrete.taskHeartbeat now org r with ⟨res, c⟩
      have hs := taskHeartbeat_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskSuspend r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskSuspend now org r with ⟨res, c⟩
      have hs := taskSuspend_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskFulfill r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskFulfill now org r with ⟨res, c⟩
      have hs := taskFulfill_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskRelease r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskRelease now org r with ⟨res, c⟩
      have hs := taskRelease_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskHalt r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskHalt now org r with ⟨res, c⟩
      have hs := taskHalt_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskContinue r =>
      have hid : r.id.origin = o := by simpa [Protocol.Request.origin?] using h
      rcases hC : Concrete.taskContinue now org r with ⟨res, c⟩
      have hs := taskContinue_sim hL now r hid
      rw [hC] at hs
      simp only [Abstract.handleExternal, map_apply, Concrete.handleExternal, hC]
      exact Sim.map' _ hs
  | taskSearch r => simp [Protocol.Request.origin?] at h

theorem step_external_eq (req : Request) (now : Nat) (T : Abstract.State) :
    Abstract.step false (.external req) now T =
      (.external (Abstract.handleExternal req now (env T)).1,
       Abstract.applyAll T (Abstract.handleExternal req now (env T)).2) := by
  show Abstract.run false (Abstract.handle (.external req) now) T = _
  rw [run_eq]
  simp only [Abstract.handle, map_apply]

theorem exec_internal_events (l : List Abstract.Trigger) (now : Nat) (S : Abstract.State) :
    Abstract.exec false ((l.map Abstract.Event.internal).map (·, now)) S =
      (l.map fun _ => Abstract.Reply.internal, execI l now S) := by
  rw [List.map_map]
  have : ((fun x => (x, now)) ∘ Abstract.Event.internal) = fun t => (Abstract.Event.internal t, now) := rfl
  rw [this]
  exact Prod.ext (exec_internal_replies l now S) rfl

theorem exec_external_events (l : List Abstract.Trigger) (req : Request) (now : Nat) (S : Abstract.State) :
    Abstract.exec false ((l.map Abstract.Event.internal ++ [Abstract.Event.external req]).map (·, now)) S =
      (l.map (fun _ => Abstract.Reply.internal) ++
        [(Abstract.step false (.external req) now (execI l now S)).1],
       (Abstract.step false (.external req) now (execI l now S)).2) := by
  rw [List.map_append, exec_append, exec_internal_events]
  simp only [List.map_cons, List.map_nil, exec_cons, Abstract.exec]

theorem observations_internal (now : Nat) : ∀ (l : List Abstract.Trigger) (evs : List Abstract.Event)
    (rs : List Abstract.Reply),
    observations now (l.map .internal ++ evs) (l.map (fun _ => .internal) ++ rs) = observations now evs rs
  | [], _, _ => rfl
  | t :: l, evs, rs => by
      simp only [List.map_cons, List.cons_append]
      exact observations_internal now l evs rs

theorem SwInv.equiv {o : String} {s s' : Concrete.State} {S : Abstract.State} {c : Commands}
    {T : Abstract.State} (inv : Inv s) (rel : Equiv (abstract s) S) (h : SwInv o S c T)
    (inv' : Inv s')
    (h1 : s'.blob? (.origin o) = some (.origin c.put))
    (h2 : ∀ m, m ≠ o → s'.blob? (.origin m) = s.blob? (.origin m))
    (h3 : s'.outbox = sendsFold s.outbox c.send) :
    Equiv (abstract s') T := by
  refine ⟨fun id => ?_, ?_, ?_⟩
  · show find (abstract s') id = find T id
    rw [find_abstract inv' id]
    by_cases e : id.origin = o
    · rw [e, State.origin_eq, h1, h.loc id e]
      rfl
    · rw [State.origin_eq, h2 _ e, ← State.origin_eq, h.other id e, ← find_abstract inv id]
      exact rel.1 id
  · show [] = T.schedules
    rw [h.sch, ← rel.2.1]
    rfl
  · show s'.outbox = T.outbox
    rw [h3, h.out, ← rel.2.2]
    rfl

theorem Inv.of_run {s s' : Concrete.State} {o : String} {org : Origin} (inv : Inv s)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup) (hwf : WF org)
    (hmem : ∀ m b, (Path.origin m, b) ∈ s'.bucket → (m = o ∧ b = .origin org) ∨ (Path.origin m, b) ∈ s.bucket)
    (hnd : (s.bucket.map (·.1)).Nodup → (s'.bucket.map (·.1)).Nodup) : Inv s' := by
  refine ⟨fun m b hb => ?_, hnd inv.paths⟩
  rcases hmem m b hb with ⟨rfl, rfl⟩ | hb'
  · exact ⟨org, rfl, horig, hnodup, hwf⟩
  · exact inv.blobs m b hb'

theorem step_sim (H : Concrete.Hasher) (ev : Concrete.Event) (now : Nat)
    (s : Concrete.State) (S : Abstract.State)
    (inv : Inv s) (rel : Equiv (abstract s) S) :
    Inv (Concrete.step H ev now s).2 ∧
    Equiv (abstract (Concrete.step H ev now s).2)
          (Abstract.exec false ((events ev now s).map (·, now)) S).2 ∧
    observations now (events ev now s) (Abstract.exec false ((events ev now s).map (·, now)) S).1 =
      (Concrete.Frame.observe ⟨s, ev, (Concrete.step H ev now s).1, now⟩).toList := by
  cases ev with
  | stutter =>
      exact ⟨inv, rel, rfl⟩
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [Concrete.step, events, ho, Abstract.exec, List.map_nil]
          exact ⟨inv, rel, rfl⟩
      | some name =>
          have hL := Local_of_rel inv rel name
          obtain ⟨horig, hnd, hwf⟩ := inv.origin_props name
          have hsw := sweep_sim hL horig hnd hwf now
          rcases hC : Concrete.handleExternal now (Concrete.sweep now (s.origin name)).put req with ⟨res, c⟩
          have hsim := handleExternal_sim hsw.loc now req ho
          rw [hC] at hsim
          have hwf' := handleExternal_wf hsw.wf now req
          rw [hC] at hwf'
          have hfin : SwInv name S ((Concrete.sweep now (s.origin name)).merge c)
              (Abstract.applyAll (execI (Concrete.sweepTriggers now (s.origin name)) now S)
                (Abstract.handleExternal req now (env (execI (Concrete.sweepTriggers now (s.origin name)) now S))).2) :=
            hsw.step _ hsim.fx hsim.loc (by rw [hsim.send]; rfl) (hsim.orig hsw.orig) (hsim.nodup hsw.nodup) hwf'
          have hhandle : Concrete.handle now (s.origin name) (.external req) =
              (.external res, (Concrete.sweep now (s.origin name)).merge c) := by
            simp only [Concrete.handle, hC]
          have hok := Concrete.applyAll_accepted (H := H) s name ((Concrete.sweep now (s.origin name)).merge c)
          have hst := run_state H name ((Concrete.sweep now (s.origin name)).merge c) s
          rcases hR : Concrete.applyAll s (((Concrete.sweep now (s.origin name)).merge c).effects name
            (Concrete.Cond.of H (s.blob? (.origin name)))) with ⟨s', ok⟩
          rw [hR] at hok hst
          simp only at hok hst
          subst hok
          obtain ⟨h1, h2, h3, h4, h5⟩ := hst
          have hstep : Concrete.step H (.external req) now s = (.external res, s') := by
            simp only [Concrete.step, ho, Concrete.run, hhandle, hR, ↓reduceIte]
          rw [hstep, events, ho, exec_external_events, step_external_eq]
          simp only
          have inv' : Inv s' := Inv.of_run inv hfin.orig hfin.nodup hfin.wf h4 h5
          refine ⟨inv', SwInv.equiv inv rel hfin inv' h1 h2 h3, ?_⟩
          rw [observations_internal, hsim.res]
          rfl
  | internal t =>
      by_cases hl : (s.blob? (.timer t)).isSome = true ∧ t.deadline ≤ now
      · have hL := Local_of_rel inv rel t.id.origin
        obtain ⟨horig, hnd, hwf⟩ := inv.origin_props t.id.origin
        have hsw := sweep_sim hL horig hnd hwf now
        have hhandle : Concrete.handle now (s.origin t.id.origin) (.internal t) =
            (.internal, Concrete.sweep now (s.origin t.id.origin)) := rfl
        have hok := Concrete.applyAll_accepted (H := H) s t.id.origin (Concrete.sweep now (s.origin t.id.origin))
        have hst := run_state H t.id.origin (Concrete.sweep now (s.origin t.id.origin)) s
        rcases hR : Concrete.applyAll s ((Concrete.sweep now (s.origin t.id.origin)).effects t.id.origin
          (Concrete.Cond.of H (s.blob? (.origin t.id.origin)))) with ⟨s', ok⟩
        rw [hR] at hok hst
        simp only at hok hst
        subst hok
        obtain ⟨h1, h2, h3, h4, h5⟩ := hst
        have hstep : Concrete.step H (.internal t) now s = (.internal, s') := by
          simp only [Concrete.step, hl, and_self, ↓reduceIte, Concrete.run, hhandle, hR]
        rw [hstep, events, if_pos hl, exec_internal_events]
        simp only
        have inv' : Inv s' := Inv.of_run inv hsw.orig hsw.nodup hsw.wf h4 h5
        refine ⟨inv', SwInv.equiv inv rel hsw inv' h1 h2 h3, ?_⟩
        have := observations_internal now (Concrete.sweepTriggers now (s.origin t.id.origin)) [] []
        simp only [List.append_nil] at this
        rw [this]
        rfl
      · have hstep : Concrete.step H (.internal t) now s = (.stutter, s) := by
          simp only [Concrete.step, hl, ↓reduceIte]
        rw [hstep, events, if_neg hl]
        exact ⟨inv, rel, rfl⟩

end Refinement
