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

def runCached (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    α × Cached H × Bool :=
  let (org, cond) := cs.read name
  let (a, c) := f org
  let (s', ok) := applyAll cs.state (c.effects name cond)
  let etag := H.hash (.origin c.put)
  (a, { state := s', cache := if ok then (name, c.put, etag) :: cs.forget name else cs.forget name }, ok)

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

open Concrete (Cached Hasher Origin Blob Path Commands Event runCached stepCached)

def Sound {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name org etag, (name, org, etag) ∈ cs.cache →
    cs.state.blob? (.origin name) = some (.origin org) ∧ H.hash (.origin org) = etag

theorem Sound.init (H : Hasher) : Sound (Cached.init H) :=
  fun _ _ _ h => (List.not_mem_nil h).elim

theorem read_sound {H : Hasher} {cs : Cached H} (h : Sound cs) (name : String) :
    cs.read name = (cs.state.origin name, Concrete.Cond.of H (cs.state.blob? (.origin name))) := by
  unfold Cached.read
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

theorem run_snd {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (s : Concrete.State) :
    (Concrete.run H name f s).2.1 =
      (Concrete.applyAll s ((f (s.origin name)).2.effects name (Concrete.Cond.of H (s.blob? (.origin name))))).1 := by
  simp only [Concrete.run]

theorem runCached_eq {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Sound cs) :
    (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    (runCached H name f cs).2.1.state = (Concrete.run H name f cs.state).2.1 ∧
    (runCached H name f cs).2.2 = (Concrete.run H name f cs.state).2.2 := by
  simp only [runCached, Concrete.run, read_sound h]
  rcases hf : f (cs.state.origin name) with ⟨a, c⟩
  rcases hA : Concrete.applyAll cs.state (c.effects name (Concrete.Cond.of H (cs.state.blob? (.origin name))))
    with ⟨s', ok⟩
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem runCached_state {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Sound cs) :
    (runCached H name f cs).2.1 =
      { state := (Concrete.run H name f cs.state).2.1,
        cache := (name, (f (cs.state.origin name)).2.put, H.hash (.origin (f (cs.state.origin name)).2.put)) ::
          cs.forget name } := by
  simp only [runCached, Concrete.run, read_sound h]
  rcases hf : f (cs.state.origin name) with ⟨a, c⟩
  have hok := Concrete.applyAll_accepted (H := H) cs.state name c
  rcases hA : Concrete.applyAll cs.state (c.effects name (Concrete.Cond.of H (cs.state.blob? (.origin name))))
    with ⟨s', ok⟩
  rw [hA] at hok
  simp only at hok
  subst hok
  rfl

theorem runCached_sound {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Sound cs) : Sound (runCached H name f cs).2.1 := by
  rw [runCached_state H name f h, run_snd]
  intro m org etag hm
  obtain ⟨h1, h2, -, -, -⟩ := run_state H name (f (cs.state.origin name)).2 cs.state
  simp only [List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | hm
  · exact ⟨h1, rfl⟩
  · obtain ⟨hmem, hne⟩ := List.mem_filter.1 hm
    have hne' : m ≠ name := by simpa using hne
    obtain ⟨hb, he⟩ := h m org etag hmem
    refine ⟨?_, he⟩
    show (Concrete.applyAll _ _).1.blob? (.origin m) = _
    rw [h2 m hne']
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

def Tagged {H : Hasher} (cs : Cached H) : Prop :=
  ∀ name org etag, (name, org, etag) ∈ cs.cache → H.hash (.origin org) = etag

theorem Sound.tagged {H : Hasher} {cs : Cached H} (h : Sound cs) : Tagged cs :=
  fun name org etag hm => (h name org etag hm).2

theorem forget_not_mem {H : Hasher} {cs : Cached H} {name : String} {org : Origin} {etag : H.Hash} :
    (name, org, etag) ∉ cs.forget name := by
  intro hm
  have := (List.mem_filter.1 hm).2
  simp at this

theorem runCached_cache {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) (cs : Cached H) :
    ∃ c : Commands, (runCached H name f cs).2.1.cache =
      if (runCached H name f cs).2.2 then (name, c.put, H.hash (.origin c.put)) :: cs.forget name
      else cs.forget name := by
  unfold runCached
  rcases hr : cs.read name with ⟨org, cond⟩
  simp only
  exact ⟨(f org).2, rfl⟩

theorem runCached_tagged {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (h : Tagged cs) : Tagged (runCached H name f cs).2.1 := by
  obtain ⟨c, hc⟩ := runCached_cache H name f cs
  intro m org etag hm
  rw [hc] at hm
  split at hm
  · simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · rfl
    · exact h m org etag (List.mem_filter.1 hm).1
  · exact h m org etag (List.mem_filter.1 hm).1

theorem read_cases {H : Hasher} (cs : Cached H) (name : String) :
    cs.read name = (cs.state.origin name, Concrete.Cond.of H (cs.state.blob? (.origin name))) ∨
    ∃ org etag, (name, org, etag) ∈ cs.cache ∧ cs.read name = (org, .hash etag) := by
  unfold Cached.read
  cases hf : cs.cache.find? (·.1 == name) with
  | none => exact Or.inl rfl
  | some p =>
      obtain ⟨n, org, etag⟩ := p
      have hn : n = name := by simpa using List.find?_some hf
      subst hn
      exact Or.inr ⟨org, etag, List.mem_of_find?_eq_some hf, rfl⟩

theorem runCached_of_read {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (hr : cs.read name = (cs.state.origin name, Concrete.Cond.of H (cs.state.blob? (.origin name)))) :
    (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
    (runCached H name f cs).2.1.state = (Concrete.run H name f cs.state).2.1 ∧
    (runCached H name f cs).2.2 = true := by
  simp only [runCached, Concrete.run, hr]
  rcases hf : f (cs.state.origin name) with ⟨a, c⟩
  have hok := Concrete.applyAll_accepted (H := H) cs.state name c
  rcases hA : Concrete.applyAll cs.state (c.effects name (Concrete.Cond.of H (cs.state.blob? (.origin name))))
    with ⟨s', ok⟩
  rw [hA] at hok
  simp only at hok
  subst hok
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem read_of_hit {H : Hasher} {cs : Cached H} (ht : Tagged cs) {name : String} {org : Origin} {etag : H.Hash}
    (hm : (name, org, etag) ∈ cs.cache) (hr : cs.read name = (org, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = true) :
    cs.read name = (cs.state.origin name, Concrete.Cond.of H (cs.state.blob? (.origin name))) := by
  have he := ht name org etag hm
  have hb : cs.state.blob? (.origin name) = some (.origin org) := by
    rw [← he] at hh
    exact (Concrete.Cond.of_holds_iff (.origin org) _).1 hh
  rw [hr]
  unfold Concrete.State.origin
  simp only [hb, Concrete.Cond.of, he]

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

theorem runCached_miss {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    {org : Origin} {etag : H.Hash} (hr : cs.read name = (org, .hash etag))
    (hh : (Concrete.Cond.hash etag : Concrete.Cond H).holds (cs.state.blob? (.origin name)) = false) :
    (runCached H name f cs).2.2 = false ∧
    Same cs.state (runCached H name f cs).2.1.state ∧
    ∀ org' etag', (name, org', etag') ∉ (runCached H name f cs).2.1.cache := by
  simp only [runCached, hr]
  rcases hf : f org with ⟨a, c⟩
  obtain ⟨hA, same⟩ := applyAll_refused H cs.state name c (.hash etag) hh
  rcases hAA : Concrete.applyAll cs.state (c.effects name (.hash etag)) with ⟨s', ok⟩
  rw [hAA] at hA same
  simp only at hA same
  subst hA
  refine ⟨rfl, same, fun org' etag' hm => ?_⟩
  have hm' : (name, org', etag') ∈ cs.forget name := hm
  exact forget_not_mem hm'

theorem runCached_dichotomy {α : Type} (H : Hasher) (name : String) (f : Origin → α × Commands) {cs : Cached H}
    (ht : Tagged cs) :
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = true →
      (runCached H name f cs).1 = (Concrete.run H name f cs.state).1 ∧
      (runCached H name f cs).2.1.state = (Concrete.run H name f cs.state).2.1 ∧
      (runCached H name f cs).2.2 = true) ∧
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = false →
      (runCached H name f cs).2.2 = false ∧
      Same cs.state (runCached H name f cs).2.1.state ∧
      ∀ org etag, (name, org, etag) ∉ (runCached H name f cs).2.1.cache) := by
  rcases read_cases cs name with hr | ⟨org, etag, hm, hr⟩
  · refine ⟨fun _ => runCached_of_read H name f hr, fun hh => ?_⟩
    rw [hr] at hh
    simp only at hh
    rw [Concrete.Cond.of_holds] at hh
    cases hh
  · refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [hr] at hh
      simp only at hh
      exact runCached_of_read H name f (read_of_hit ht hm hr hh)
    · rw [hr] at hh
      simp only at hh
      exact runCached_miss H name f hr hh

theorem stepCached_dichotomy (H : Hasher) (now : Nat) (req : Protocol.Request) (name : String)
    (ho : req.origin? = some name) {cs : Cached H} (ht : Tagged cs) :
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = true →
      (stepCached H (.external req) now cs).1 = (Concrete.step H (.external req) now cs.state).1 ∧
      (stepCached H (.external req) now cs).2.state = (Concrete.step H (.external req) now cs.state).2) ∧
    ((cs.read name).2.holds (cs.state.blob? (.origin name)) = false →
      (stepCached H (.external req) now cs).1 = .stutter ∧
      Same cs.state (stepCached H (.external req) now cs).2.state ∧
      ∀ org etag, (name, org, etag) ∉ (stepCached H (.external req) now cs).2.cache) := by
  simp only [stepCached, Concrete.step, ho]
  have hd := runCached_dichotomy H name (fun org => Concrete.handle now org (.external req)) ht
  have hok' := Concrete.run_accepted (H := H) name (fun org => Concrete.handle now org (.external req)) cs.state
  rcases hR : runCached H name (fun org => Concrete.handle now org (.external req)) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H name (fun org => Concrete.handle now org (.external req)) cs.state with ⟨r', s', ok'⟩
  rw [hR, hS] at hd
  rw [hS] at hok'
  simp only at hd hok'
  subst hok'
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨rfl, h2, rfl⟩ := hd.1 hh
    exact ⟨rfl, h2⟩
  · obtain ⟨rfl, hsame, hnot⟩ := hd.2 hh
    exact ⟨rfl, hsame, hnot⟩

theorem stepCached_dichotomy_timer (H : Hasher) (now : Nat) (t : Concrete.Timer) {cs : Cached H}
    (hl : (cs.state.blob? (.timer t)).isSome ∧ t.deadline ≤ now) (ht : Tagged cs) :
    ((cs.read t.id.origin).2.holds (cs.state.blob? (.origin t.id.origin)) = true →
      (stepCached H (.internal t) now cs).1 = (Concrete.step H (.internal t) now cs.state).1 ∧
      (stepCached H (.internal t) now cs).2.state = (Concrete.step H (.internal t) now cs.state).2) ∧
    ((cs.read t.id.origin).2.holds (cs.state.blob? (.origin t.id.origin)) = false →
      (stepCached H (.internal t) now cs).1 = .stutter ∧
      Same cs.state (stepCached H (.internal t) now cs).2.state ∧
      ∀ org etag, (t.id.origin, org, etag) ∉ (stepCached H (.internal t) now cs).2.cache) := by
  simp only [stepCached, Concrete.step]
  rw [if_pos hl, if_pos hl]
  have hd := runCached_dichotomy H t.id.origin (fun org => Concrete.handle now org (.internal t)) ht
  have hok' := Concrete.run_accepted (H := H) t.id.origin (fun org => Concrete.handle now org (.internal t)) cs.state
  rcases hR : runCached H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs with ⟨r, cs', ok⟩
  rcases hS : Concrete.run H t.id.origin (fun org => Concrete.handle now org (.internal t)) cs.state
    with ⟨r', s', ok'⟩
  rw [hR, hS] at hd
  rw [hS] at hok'
  simp only at hd hok'
  subst hok'
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨rfl, h2, rfl⟩ := hd.1 hh
    exact ⟨rfl, h2⟩
  · obtain ⟨rfl, hsame, hnot⟩ := hd.2 hh
    exact ⟨rfl, hsame, hnot⟩

end Refinement
