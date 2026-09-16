import impl.refinement

namespace Concrete

structure Cached (H : Hasher) where
  state : State := {}
  cache : List (String × Origin × H.Hash) := []

def Cached.init (H : Hasher) : Cached H := {}

def Cached.read {H : Hasher} (cs : Cached H) (name : String) : Origin × Cond H :=
  match cs.cache.find? (·.1 == name) with
  | some (_, org, etag) =>
      (org, .hash etag)
  | none =>
      (cs.state.origin name, Cond.of H (cs.state.blob? (.origin name)))

def Cached.forget {H : Hasher} (cs : Cached H) (name : String) : List (String × Origin × H.Hash) :=
  cs.cache.filter (·.1 != name)

def attempt (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (org, cond) := cs.read name
  let (a, c) := f org
  let (s', ok) := applyAll cs.state (c.effects name cond)
  let etag := H.hash (.origin c.put)
  (a, { state := s', cache := if ok then (name, c.put, etag) :: cs.forget name else cs.forget name }, ok)

def runCached (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (a, cs', ok) := attempt H name f cs
  if ok then (a, cs', ok) else attempt H name f cs'

def stepCached (H : Hasher) (ev : Event) (now : Nat) (cs : Cached H) : Reply × Cached H :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (r, cs', ok) := runCached H name (fun org => handle now org ev) cs
          (if ok then r else .stutter, cs')
      | none =>
          (.stutter, cs)
  | .internal t =>
      if (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, cs', ok) := runCached H t.id.origin (fun org => handle now org ev) cs
        (if ok then r else .stutter, cs')
      else
        (.stutter, cs)
  | .stutter =>
      (.stutter, cs)

namespace Cached

structure Frame (H : Hasher) where
  state : Cached H
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace (H : Hasher) := Nat → Frame H

def Valid (H : Hasher) (tr : Trace H) : Prop :=
  ∀ t : Nat,
    stepCached H (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

variable {H : Hasher}

def Frame.proj (f : Frame H) : Concrete.Frame :=
  ⟨f.state.state, f.event, f.reply, f.now⟩

def Frame.observe (f : Frame H) : Option Abstract.Observation :=
  f.proj.observe

def observed (tr : Trace H) (n : Nat) : List Abstract.Observation :=
  ((List.range n).map tr).filterMap Frame.observe

def nth (tr : Trace H) (k : Nat) (o : Abstract.Observation) : Prop :=
  ∃ n, (observed tr n)[k]? = some o

def proj (tr : Trace H) : Concrete.Trace :=
  fun n => (tr n).proj

end Cached

end Concrete

namespace Refinement

open Concrete (Cached Hasher Origin Blob Path Commands Event attempt runCached stepCached)

def Sound {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name org etag, (name, org, etag) ∈ cs.cache →
    cs.state.blob? (.origin name) = some (.origin org) ∧ H.hash (.origin org) = etag

def Tagged {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name org etag, (name, org, etag) ∈ cs.cache → H.hash (.origin org) = etag

def Agree {H : Hasher} (cs : Cached H) (name : String) : Prop :=
  cs.read name = (cs.state.origin name, Concrete.Cond.of H (cs.state.blob? (.origin name)))

def Docs (s s' : Concrete.State) : Prop :=
  (∀ m, s'.blob? (.origin m) = s.blob? (.origin m)) ∧ s'.outbox = s.outbox

theorem Sound.init (H : Hasher) : Sound (Cached.init H) :=
  fun _ _ _ h => (List.not_mem_nil h).elim

theorem Docs.refl (s : Concrete.State) : Docs s s := ⟨fun _ => rfl, rfl⟩

theorem read_sound {H : Hasher} {cs : Cached H} (h : Sound cs) (name : String) : Agree cs name := by
  unfold Agree Cached.read
  cases hf : cs.cache.find? (·.1 == name) with
  | none => rfl
  | some p =>
      obtain ⟨n, org, etag⟩ := p
      have hn : n = name := by simpa using List.find?_some hf
      subst hn
      obtain ⟨hb, he⟩ := h n org etag (List.mem_of_find?_eq_some hf)
      show (org, Concrete.Cond.hash etag) = (cs.state.origin n, Concrete.Cond.of H (cs.state.blob? (.origin n)))
      unfold Concrete.State.origin
      simp only [hb, Concrete.Cond.of, he]

theorem read_absent {H : Hasher} {cs : Cached H} {name : String}
    (h : ∀ org etag, (name, org, etag) ∉ cs.cache) : Agree cs name := by
  unfold Agree Cached.read
  have hf : cs.cache.find? (·.1 == name) = none := by
    refine List.find?_eq_none.2 fun x hx => ?_
    obtain ⟨n, org, etag⟩ := x
    intro hn
    have hn' : n = name := by simpa using hn
    subst hn'
    exact h org etag hx
  rw [hf]

theorem read_cases {H : Hasher} (cs : Cached H) (name : String) :
    Agree cs name ∨ ∃ org etag, (name, org, etag) ∈ cs.cache ∧ cs.read name = (org, .hash etag) := by
  unfold Agree Cached.read
  cases hf : cs.cache.find? (·.1 == name) with
  | none => exact Or.inl rfl
  | some p =>
      obtain ⟨n, org, etag⟩ := p
      have hn : n = name := by simpa using List.find?_some hf
      subst hn
      exact Or.inr ⟨org, etag, List.mem_of_find?_eq_some hf, rfl⟩

theorem read_of_hit {H : Hasher} {cs : Cached H} (ht : Tagged cs) {name : String} {org : Origin} {etag : H.Hash}
    (hm : (name, org, etag) ∈ cs.cache) (hr : cs.read name = (org, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = true) :
    Agree cs name := by
  have he := ht name org etag hm
  have hb : cs.state.blob? (.origin name) = some (.origin org) := by
    rw [← he] at hh
    exact (Concrete.Cond.of_holds_iff (.origin org) _).1 hh
  unfold Agree
  rw [hr]
  unfold Concrete.State.origin
  simp only [hb, Concrete.Cond.of, he]

theorem read_true {H : Hasher} {cs : Cached H} (ht : Tagged cs) {name : String}
    (hh : (cs.read name).2.holds (cs.state.blob? (.origin name)) = true) : Agree cs name := by
  rcases read_cases cs name with hr | ⟨org, etag, hm, hr⟩
  · exact hr
  · rw [hr] at hh
    simp only at hh
    exact read_of_hit ht hm hr hh

theorem forget_not_mem {H : Hasher} {cs : Cached H} {name : String} {org : Origin} {etag : H.Hash} :
    (name, org, etag) ∉ cs.forget name := by
  intro hm
  have := (List.mem_filter.1 hm).2
  simp at this

theorem run_fst {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (s : Concrete.State) :
    (Concrete.run H name f s).1 = (f (s.origin name)).1 := by
  simp only [Concrete.run]

theorem run_snd {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (s : Concrete.State) :
    (Concrete.run H name f s).2.1 =
      (Concrete.applyAll s ((f (s.origin name)).2.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1 := by
  simp only [Concrete.run]

theorem attempt_of_read {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (hr : Agree cs name) :
    (attempt H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    (attempt H name f cs).2.1 =
      { state := (Concrete.run H name f cs.state).2.1,
        cache := (name, (f (cs.state.origin name)).2.put, H.hash (.origin (f (cs.state.origin name)).2.put)) ::
          cs.forget name } ∧
    (attempt H name f cs).2.2 = true := by
  unfold Agree at hr
  simp only [attempt, Concrete.run, hr]
  rcases hf : f (cs.state.origin name) with ⟨a, c⟩
  have hok := Concrete.applyAll_accepted (H := H) cs.state name c
  rcases hA : Concrete.applyAll cs.state (c.effects name (Concrete.Cond.of H (cs.state.blob? (.origin name))))
    with ⟨s', ok⟩
  rw [hA] at hok
  simp only at hok
  subst hok
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem attempt_cache {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    ∃ c : Commands, (attempt H name f cs).2.1.cache =
      if (attempt H name f cs).2.2 then (name, c.put, H.hash (.origin c.put)) :: cs.forget name
      else cs.forget name := by
  unfold attempt
  rcases hr : cs.read name with ⟨org, cond⟩
  simp only
  exact ⟨(f org).2, rfl⟩

theorem attempt_tagged {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Tagged cs) : Tagged (attempt H name f cs).2.1 := by
  obtain ⟨c, hc⟩ := attempt_cache H name f cs
  intro m org etag hm
  rw [hc] at hm
  split at hm
  · simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · rfl
    · exact h m org etag (List.mem_filter.1 hm).1
  · exact h m org etag (List.mem_filter.1 hm).1

theorem applyAll_cons_refused {H : Hasher} (s : Concrete.State) (p : Path) (b : Blob) (cond : Concrete.Cond H)
    (rest : List (Concrete.Effect H)) (h : cond.holds (s.blob? p) = false) :
    Concrete.applyAll s (Concrete.Effect.put p b cond :: rest) = (s, false) := by
  have hP : (Concrete.Effect.put (H := H) p b cond).apply s = none := by
    simp [Concrete.Effect.apply, h]
  simp only [Concrete.applyAll, hP]

theorem applyAll_refused (H : Hasher) (s : Concrete.State) (name : String) (c : Commands) (cond : Concrete.Cond H)
    (h : cond.holds (s.blob? (.origin name)) = false) :
    (Concrete.applyAll s (c.effects name cond)).2 = false ∧ Same s (Concrete.applyAll s (c.effects name cond)).1 := by
  unfold Commands.effects
  obtain ⟨hA, sameA⟩ := timers_phase (H := H) (c.arm.map fun t => .put (.timer t) .timer .any) s
    (by intro e he; simp only [List.mem_map] at he; obtain ⟨t, _, rfl⟩ := he; trivial)
  obtain ⟨s1, hs1⟩ : ∃ s1, Concrete.applyAll s (c.arm.map fun t => Concrete.Effect.put (H := H) (.timer t) .timer .any) = (s1, true) :=
    ⟨_, Prod.ext rfl hA⟩
  rw [hs1] at sameA
  simp only at sameA
  simp only [List.append_assoc, List.singleton_append]
  rw [Concrete.applyAll_append, hs1, if_pos rfl]
  have hh : cond.holds (s1.blob? (.origin name)) = false := by rw [sameA.blob, h]
  show (Concrete.applyAll s1 _).2 = false ∧ Same s (Concrete.applyAll s1 _).1
  rw [List.cons_append, applyAll_cons_refused s1 _ _ _ _ hh]
  exact ⟨rfl, sameA⟩

theorem attempt_miss {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    {org : Origin} {etag : H.Hash} (hr : cs.read name = (org, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = false) :
    (attempt H name f cs).2.2 = false ∧
    Same cs.state (attempt H name f cs).2.1.state ∧
    ∀ org' etag', (name, org', etag') ∉ (attempt H name f cs).2.1.cache := by
  simp only [attempt, hr]
  rcases hf : f org with ⟨a, c⟩
  obtain ⟨hA, same⟩ := applyAll_refused H cs.state name c (.hash etag) hh
  rcases hAA : Concrete.applyAll cs.state (c.effects name (.hash etag)) with ⟨s', ok⟩
  rw [hAA] at hA same
  simp only at hA same
  subst hA
  refine ⟨rfl, same, fun org' etag' hm => ?_⟩
  have hm' : (name, org', etag') ∈ cs.forget name := hm
  exact forget_not_mem hm'

theorem attempt_dichotomy {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (ht : Tagged cs) :
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = true →
      (attempt H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
      (attempt H name f cs).2.1.state = (Concrete.run H name f cs.state).2.1 ∧
      (attempt H name f cs).2.2 = true) ∧
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = false →
      (attempt H name f cs).2.2 = false ∧
      Same cs.state (attempt H name f cs).2.1.state ∧
      ∀ org etag, (name, org, etag) ∉ (attempt H name f cs).2.1.cache) := by
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := attempt_of_read H name f (read_true ht hh)
    exact ⟨h1, by rw [h2], h3⟩
  · rcases read_cases cs name with hr | ⟨org, etag, hm, hr⟩
    · unfold Agree at hr
      rw [hr] at hh
      simp only at hh
      rw [Concrete.Cond.of_holds] at hh
      cases hh
    · rw [hr] at hh
      simp only at hh
      exact attempt_miss H name f hr hh

theorem runCached_of_ok {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H)
    (h : (attempt H name f cs).2.2 = true) : runCached H name f cs = attempt H name f cs := by
  unfold runCached
  rcases hA : attempt H name f cs with ⟨a, cs', ok⟩
  rw [hA] at h
  simp only at h
  subst h
  rfl

theorem run_docs {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {s s' : Concrete.State}
    (h : Same s s') :
    (Concrete.run H name f s').1 = (Concrete.run H name f s).1 ∧
    Docs (Concrete.run H name f s).2.1 (Concrete.run H name f s').2.1 := by
  have horg : s'.origin name = s.origin name := by
    rw [State.origin_eq, State.origin_eq, h.blob]
  obtain ⟨h1, h2, h3, -, -⟩ := run_state H name (f (s.origin name)).2 s
  obtain ⟨h1', h2', h3', -, -⟩ := run_state H name (f (s'.origin name)).2 s'
  rw [horg] at h1' h2' h3'
  refine ⟨by rw [run_fst, run_fst, horg], fun m => ?_, ?_⟩
  · rw [run_snd, run_snd, horg]
    by_cases hm : m = name
    · subst hm; rw [h1, h1']
    · rw [h2 m hm, h2' m hm, h.blob]
  · rw [run_snd, run_snd, horg, h3, h3', h.out]

theorem agree_after {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (s : Concrete.State)
    (rest : List (String × Origin × H.Hash)) :
    Agree ({ state := (Concrete.run H name f s).2.1,
             cache := (name, (f (s.origin name)).2.put, H.hash (.origin (f (s.origin name)).2.put)) :: rest } : Cached H)
      name := by
  unfold Agree Cached.read
  simp only [List.find?_cons, beq_self_eq_true]
  obtain ⟨h1, -, -, -, -⟩ := run_state H name (f (s.origin name)).2 s
  show ((f (s.origin name)).2.put, Concrete.Cond.hash (H.hash (.origin (f (s.origin name)).2.put))) =
    (Concrete.State.origin (Concrete.run H name f s).2.1 name,
      Concrete.Cond.of H ((Concrete.run H name f s).2.1.blob? (.origin name)))
  rw [State.origin_eq (Concrete.run H name f s).2.1 name, run_snd, h1]
  rfl

theorem runCached_any {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (ht : Tagged cs) :
    (runCached H name f cs).2.2 = true ∧
    (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    Docs (Concrete.run H name f cs.state).2.1 (runCached H name f cs).2.1.state ∧
    Tagged (runCached H name f cs).2.1 ∧
    Agree (runCached H name f cs).2.1 name := by
  have hd := attempt_dichotomy H name f ht
  cases hh : (cs.read name).2.holds (cs.state.blob? (.origin name)) with
  | true =>
      have hr := read_true ht hh
      obtain ⟨h1, h2, h3⟩ := attempt_of_read H name f hr
      rw [runCached_of_ok H name f cs h3, h2]
      refine ⟨h3, h1, ?_, ?_, agree_after H name f cs.state _⟩
      · exact Docs.refl _
      · rw [← h2]; exact attempt_tagged H name f ht
  | false =>
      obtain ⟨hok, hsame, hnot⟩ := hd.2 hh
      have htag' : Tagged (attempt H name f cs).2.1 := attempt_tagged H name f ht
      have hr' : Agree (attempt H name f cs).2.1 name := read_absent hnot
      obtain ⟨h1, h2, h3⟩ := attempt_of_read H name f hr'
      obtain ⟨hf, hdocs⟩ := run_docs H name f hsame
      have hrun : runCached H name f cs = attempt H name f (attempt H name f cs).2.1 := by
        unfold runCached
        rcases hA : attempt H name f cs with ⟨a, cs', ok⟩
        rw [hA] at hok
        simp only at hok
        subst hok
        rfl
      rw [hrun, h2]
      refine ⟨h3, h1.trans hf, hdocs, ?_, agree_after H name f _ _⟩
      rw [← h2]
      exact attempt_tagged H name f htag'

theorem runCached_eq {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Sound cs) :
    (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    (runCached H name f cs).2.1.state = (Concrete.run H name f cs.state).2.1 ∧
    (runCached H name f cs).2.2 = (Concrete.run H name f cs.state).2.2 := by
  obtain ⟨h1, h2, h3⟩ := attempt_of_read H name f (read_sound h name)
  rw [runCached_of_ok H name f cs h3, h2, h3, Concrete.run_accepted]
  exact ⟨h1, rfl, rfl⟩

theorem runCached_sound {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Sound cs) : Sound (runCached H name f cs).2.1 := by
  obtain ⟨-, h2, h3⟩ := attempt_of_read H name f (read_sound h name)
  rw [runCached_of_ok H name f cs h3, h2, run_snd]
  intro m org etag hm
  obtain ⟨hb1, hb2, -, -, -⟩ := run_state H name (f (cs.state.origin name)).2 cs.state
  simp only [List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | hm
  · exact ⟨hb1, rfl⟩
  · obtain ⟨hmem, hne⟩ := List.mem_filter.1 hm
    have hne' : m ≠ name := by simpa using hne
    obtain ⟨hb, he⟩ := h m org etag hmem
    refine ⟨?_, he⟩
    show (Concrete.applyAll _ _).1.blob? (.origin m) = _
    rw [hb2 m hne']
    exact hb

theorem stepCached_eq (H : Hasher) (ev : Event) (now : Nat) {cs : Cached H} (h : Sound cs) :
    (stepCached H ev now cs).1 = (Concrete.step H ev now cs.state).1 ∧
    (stepCached H ev now cs).2.state = (Concrete.step H ev now cs.state).2 ∧
    Sound (stepCached H ev now cs).2 := by
  cases ev with
  | external req =>
      cases ho : req.origin? with
      | none =>
          simp only [stepCached, Concrete.step, ho]
          exact ⟨trivial, trivial, h⟩
      | some name =>
          simp only [stepCached, Concrete.step, ho]
          have heq := runCached_eq H name (fun org => Concrete.handle now org (.external req)) h
          have hs := runCached_sound H name (fun org => Concrete.handle now org (.external req)) h
          rcases hR : runCached H name (fun org => Concrete.handle now org (.external req)) cs with ⟨r, cs', ok⟩
          rcases hS : Concrete.run H name (fun org => Concrete.handle now org (.external req)) cs.state
            with ⟨r', s', ok'⟩
          rw [hR, hS] at heq
          rw [hR] at hs
          simp only at heq hs
          obtain ⟨rfl, h2, rfl⟩ := heq
          exact ⟨rfl, h2, hs⟩
  | internal t =>
      simp only [stepCached, Concrete.step]
      split
      · have heq := runCached_eq H t.id.origin (fun org => Concrete.handle now org (.internal t)) h
        have hs := runCached_sound H t.id.origin (fun org => Concrete.handle now org (.internal t)) h
        rcases hR : runCached H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs with ⟨r, cs', ok⟩
        rcases hS : Concrete.run H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs.state
          with ⟨r', s', ok'⟩
        rw [hR, hS] at heq
        rw [hR] at hs
        simp only at heq hs
        obtain ⟨rfl, h2, rfl⟩ := heq
        exact ⟨rfl, h2, hs⟩
      · exact ⟨rfl, rfl, h⟩
  | stutter =>
      exact ⟨rfl, rfl, h⟩

theorem stepCached_any (H : Hasher) (now : Nat) (req : Protocol.Request) (name : String)
    (ho : req.origin? = some name) {cs : Cached H} (ht : Tagged cs) :
    (stepCached H (.external req) now cs).1 = (Concrete.step H (.external req) now cs.state).1 ∧
    Docs (Concrete.step H (.external req) now cs.state).2 (stepCached H (.external req) now cs).2.state ∧
    Tagged (stepCached H (.external req) now cs).2 ∧
    Agree (stepCached H (.external req) now cs).2 name := by
  simp only [stepCached, Concrete.step, ho]
  have ha := runCached_any H name (fun org => Concrete.handle now org (.external req)) ht
  have hok' := Concrete.run_accepted (H := H) name (fun org => Concrete.handle now org (.external req)) cs.state
  rcases hR : runCached H name (fun org => Concrete.handle now org (.external req)) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H name (fun org => Concrete.handle now org (.external req)) cs.state with ⟨r', s', ok'⟩
  rw [hR, hS] at ha
  rw [hS] at hok'
  simp only at ha hok'
  obtain ⟨rfl, rfl, hdocs, htag, hagree⟩ := ha
  subst hok'
  exact ⟨rfl, hdocs, htag, hagree⟩

theorem stepCached_any_timer (H : Hasher) (now : Nat) (t : Concrete.Timer) {cs : Cached H}
    (hl : (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now) (ht : Tagged cs) :
    (stepCached H (.internal t) now cs).1 = (Concrete.step H (.internal t) now cs.state).1 ∧
    Docs (Concrete.step H (.internal t) now cs.state).2 (stepCached H (.internal t) now cs).2.state ∧
    Tagged (stepCached H (.internal t) now cs).2 ∧
    Agree (stepCached H (.internal t) now cs).2 t.id.origin := by
  simp only [stepCached, Concrete.step]
  rw [if_pos hl, if_pos hl]
  have ha := runCached_any H t.id.origin (fun org => Concrete.handle now org (.internal t)) ht
  have hok' := Concrete.run_accepted (H := H) t.id.origin (fun org => Concrete.handle now org (.internal t)) cs.state
  rcases hR : runCached H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs.state
    with ⟨r', s', ok'⟩
  rw [hR, hS] at ha
  rw [hS] at hok'
  simp only at ha hok'
  obtain ⟨rfl, rfl, hdocs, htag, hagree⟩ := ha
  subst hok'
  exact ⟨rfl, hdocs, htag, hagree⟩

theorem sound_all {H : Hasher} {tr : Cached.Trace H} (hv : Cached.Valid H tr) (h0 : (tr 0).state = Cached.init H) :
    ∀ n, Sound (tr n).state
  | 0 => by rw [h0]; exact Sound.init H
  | n + 1 => by
      have hst : (tr (n + 1)).state = (stepCached H (tr n).event (tr n).now (tr n).state).2 := by
        rw [(hv n).1]
      rw [hst]
      exact (stepCached_eq H _ _ (sound_all hv h0 n)).2.2

theorem proj_valid {H : Hasher} {tr : Cached.Trace H} (hv : Cached.Valid H tr) (h0 : (tr 0).state = Cached.init H) :
    Concrete.Valid H (Cached.proj tr) := by
  intro n
  obtain ⟨h1, h2, -⟩ := stepCached_eq H (tr n).event (tr n).now (sound_all hv h0 n)
  have hr : (tr n).reply = (stepCached H (tr n).event (tr n).now (tr n).state).1 := by rw [(hv n).1]
  have hs : (tr (n + 1)).state = (stepCached H (tr n).event (tr n).now (tr n).state).2 := by rw [(hv n).1]
  refine ⟨?_, (hv n).2⟩
  show Concrete.step H (tr n).event (tr n).now (tr n).state.state = ((tr n).reply, (tr (n + 1)).state.state)
  rw [hr, hs, h1, h2]

theorem observed_proj {H : Hasher} (tr : Cached.Trace H) (n : Nat) :
    Concrete.observed (Cached.proj tr) n = Cached.observed tr n := by
  unfold Concrete.observed Cached.observed Cached.proj
  rw [List.filterMap_map, List.filterMap_map]
  rfl

theorem nth_proj {H : Hasher} (tr : Cached.Trace H) (k : Nat) (o : Abstract.Observation) :
    Cached.nth tr k o ↔ Concrete.nth (Cached.proj tr) k o := by
  unfold Cached.nth Concrete.nth
  simp only [observed_proj]

theorem refinesCached (H : Hasher) (tr : Cached.Trace H)
    (valid : Cached.Valid H tr) (init : (tr 0).state = Cached.init H) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Cached.nth tr k o ↔ Abstract.nth tr' k o := by
  have hinit : (Cached.proj tr 0).state = Concrete.State.init := by
    show (tr 0).state.state = _
    rw [init]
    rfl
  obtain ⟨tr', h1, h2, h3⟩ := refines H (Cached.proj tr) (proj_valid valid init) hinit
  exact ⟨tr', h1, h2, fun k o => (nth_proj tr k o).trans (h3 k o)⟩

end Refinement
