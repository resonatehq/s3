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

end Refinement
