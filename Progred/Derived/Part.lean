import Progred.Derived.Forms

/-!
A part of the document, drawn by derivative: an entry of the root
notebook, the end of its entries, or the whole root. A part's tree is of a
seed: where it starts, how the value there is drawn, and the value. A part
is drawn with what of the editor's state is its own: the selection if
it's in the part, and the values its evaluations' errors are about.
-/

open Deui

namespace Progred.Derived

open Display (Entry Hint)

/-- What a part's tree is of. An entry is held as a list of the one, so
its node is the list's element, and the part's own node draws the place to
add an entry before it. A root with no value is a hole. -/
def seed : Entry → Seed
  | .entry p v => ⟨Display.entriesPath, .entry p, .list [(p, v)]⟩
  | .end_ => ⟨Display.entriesPath, .end_, .list []⟩
  | .whole (some v) => ⟨[], .value false, v⟩
  | .whole none => ⟨[], .label, .blob []⟩

/-- A part's edit, as its seed's: a write within an entry is a write a
step further in, in the list that holds it; one that replaces the part's
whole value is another seed. -/
def seedEdits (e : Entry) : Entry.Edit → List Seed.Edit
  | .replace e' => [.replace (seed e')]
  | .write [] w => [.replace (seed (Entry.Edit.apply (.write [] w) e))]
  | .write (r :: rest) w =>
    match e with
    | .entry p _ => [.write (.element p :: r :: rest) w]
    | .whole (some _) => [.write (r :: rest) w]
    | _ => []

/-- A write within the one element of a list is the list of that element
written. -/
theorem written_within (p : Position) (v : Value) (r : Step) (rest : List Step) (w : Option Value) :
    (Value.list [(p, v)]).written (.element p :: r :: rest) w = .list [(p, v.written (r :: rest) w)] := by
  have hstep : (Value.list [(p, v)]).step? (.element p) = some v := by simp [Value.step?]
  cases hp : v.put (r :: rest) w with
  | none =>
    have : (Value.list [(p, v)]).put (.element p :: r :: rest) w = none := by
      cases w <;> simp_all [Value.put, Value.set, Value.without, bind, Option.bind]
    simp [Value.written, hp, this]
  | some c' =>
    have : (Value.list [(p, v)]).put (.element p :: r :: rest) w = some (.list [(p, c')]) := by
      cases w <;> simp_all [Value.put, Value.set, Value.without, bind, Option.bind, Value.setStep, Value.setElement]
    simp [Value.written, hp, this]

theorem seedEdits_ok (e : Entry) (d : Entry.Edit) : run Seeds (seedEdits e d) (seed e) = seed (d.apply e) := by
  cases d with
  | replace e' => rfl
  | write rel w =>
    cases rel with
    | nil => rfl
    | cons r rest =>
      cases e with
      | end_ => rfl
      | whole root => cases root <;> rfl
      | entry p v =>
        show ({ seed (.entry p v) with value := (Value.list [(p, v)]).written (.element p :: r :: rest) w } : Seed) = _
        rw [written_within]
        rfl

/-- A run of a part's edits, as its seed's. -/
def seedRun : Entry → List Entry.Edit → List Seed.Edit
  | _, [] => []
  | e, d :: ds => seedEdits e d ++ seedRun (d.apply e) ds

theorem seedRun_ok : ∀ (ds : List Entry.Edit) (e : Entry),
    run Seeds (seedRun e ds) (seed e) = seed (run Entry.edits ds e)
  | [], _ => rfl
  | d :: ds, e => by
    show run Seeds (seedEdits e d ++ seedRun (d.apply e) ds) (seed e) = seed (run Entry.edits ds (d.apply e))
    rw [run_append, seedEdits_ok, seedRun_ok ds (d.apply e)]

/-! ## What a part is drawn with -/

/-- Whether a selection is in a part, or the part in it, or it's of an
entry being added that the part draws. -/
def within (e : Entry) (sel : Selection) : Bool := (⟨e, ⟨[]⟩, [], false, []⟩ : Display.Item).touches sel

mutual
/-- The values the errors of a value's evaluations are about, by path. -/
def failingIn (results : List (Value × Outcome)) (path : Path) : Value → List Path
  | .record fields =>
    (if (Value.record fields).kind? == some Kinds.evaluation then
      match ((Value.record fields).field? Kinds.expression).bind fun e => (results.find? (·.1 == e)).map (·.2) with
      | some (.failed _ (some rel)) => [path ++ [.key Kinds.expression] ++ rel]
      | _ => []
    else []) ++ failingFields results path fields
  | .list items => failingItems results path items
  | _ => []

def failingFields (results : List (Value × Outcome)) (path : Path) : List (CellId × Value) → List Path
  | [] => []
  | (l, x) :: rest => failingIn results (path ++ [.key l]) x ++ failingFields results path rest

def failingItems (results : List (Value × Outcome)) (path : Path) : List (Position × Value) → List Path
  | [] => []
  | (p, x) :: rest => failingIn results (path ++ [.element p]) x ++ failingItems results path rest
end

/-- The values a part's evaluations' errors are about: none, without
looking, when no error is about a value. -/
def failing (results : List (Value × Outcome)) (s : Seed) : List Path :=
  if results.any fun r => match r.2 with | .failed _ (some _) => true | _ => false then
    failingIn results s.path s.value
  else []

/-- What of the editor's state a part is drawn with. -/
def narrow (e : Entry) (seen : Display.Seen) : Display.Seen :=
  { seen with selection := seen.selection.filter (within e), named := [],
              failing := failing seen.results (seed e) }

/-- A part, as its seed under what it's drawn with. It keeps the part. -/
def seeded : Cached (prod Under (runs Entry.edits)) (prod Under (runs Seeds)) where
  Cache := Entry
  f a := (((narrow a.2 a.1.1, a.1.2), seed a.2), a.2)
  df e d := (((narrow (run Entry.edits d.2 e) d.1.1, d.1.2), seedRun e d.2), run Entry.edits d.2 e)

theorem seeded_ok : seeded.ok := by
  intro a d
  show (((narrow (run Entry.edits d.2 a.2) d.1.1, run cellsEdits d.1.2 a.1.2), run Seeds (seedRun a.2 d.2) (seed a.2)),
      run Entry.edits d.2 a.2) = _
  rw [seedRun_ok]
  rfl

/-- A part's lines, seededLines its seed. -/
def seededLines : Cached (prod Under (runs Entry.edits)) Lines := compose seeded lines

theorem seededLines_ok : seededLines.ok := compose_ok _ _ seeded_ok lines_ok

/-- Whether a part is drawn with the same by two states: most keystrokes
are in another part, and this is all that part does about them. -/
def sameFor (e : Entry) (seen seen' : Display.Seen) : Bool :=
  seen'.ribbon == seen.ribbon && equal seen'.folds seen.folds && equal seen'.results seen.results &&
    equal seen'.layouts seen.layouts &&
    decide (seen'.selection.filter (within e) = seen.selection.filter (within e))

theorem narrow_same (e : Entry) (seen seen' : Display.Seen) (h : sameFor e seen seen' = true) :
    narrow e seen' = narrow e seen := by
  simp only [sameFor, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, hres⟩, hl⟩, hs⟩ := h
  simp only [narrow, hr, equal_sound _ _ hf, equal_sound _ _ hres, equal_sound _ _ hl, hs]

/-- A part's lines, as an incremental function of what parts are drawn
under and the part. It keeps what it was last drawn with: an edit that
writes no definition, doesn't edit the part and leaves what the part is
drawn with as it was, gives no edit and asks nothing further. -/
def part : Cached (prod Under (runs Entry.edits)) Lines where
  Cache := Display.Seen × seededLines.Cache
  f a := ((seededLines.f a).1, (a.1.1, (seededLines.f a).2))
  df k d :=
    if d.1.2.isEmpty && d.2.isEmpty && sameFor k.2.1 k.1 d.1.1 then ([], (d.1.1, k.2))
    else ((seededLines.df k.2 d).1, (d.1.1, (seededLines.df k.2 d).2))

/-- A part's lines seededLines its seed depend on the state only by what the
part is drawn with. -/
theorem seededLines_narrow (seen seen' : Display.Seen) (cells : Cells) (e : Entry) (h : narrow e seen' = narrow e seen) :
    seededLines.f ((seen', cells), e) = seededLines.f ((seen, cells), e) := by
  simp only [seededLines, compose, seeded, h]

theorem part_ok : part.ok := by
  intro a d
  obtain ⟨⟨seen, cells⟩, e⟩ := a
  obtain ⟨⟨seen', ces⟩, ds⟩ := d
  have law := seededLines_ok ((seen, cells), e) ((seen', ces), ds)
  show (Lines.apply _ (seededLines.f ((seen, cells), e)).1, _) = ((seededLines.f _).1, (seen', (seededLines.f _).2))
  simp only [part]
  cases hq : (ces.isEmpty && ds.isEmpty && sameFor (seededLines.f ((seen, cells), e)).2.1 seen seen') with
  | true =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hq
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq
    subst h1
    subst h2
    have same : seededLines.f ((seen', cells), e) = seededLines.f ((seen, cells), e) :=
      seededLines_narrow seen seen' cells e (narrow_same e seen seen' h3)
    simp only [ite_true]
    show ((seededLines.f ((seen, cells), e)).1, (seen', (seededLines.f ((seen, cells), e)).2)) =
      ((seededLines.f ((seen', cells), e)).1, (seen', (seededLines.f ((seen', cells), e)).2))
    rw [same]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have l1 := congrArg Prod.fst law
    have l2 := congrArg Prod.snd law
    simp only at l1 l2
    exact Prod.ext l1 (Prod.ext rfl l2)

/-- A part's lines, from nothing. -/
def partLines (seen : Display.Seen) (cells : Cells) (e : Entry) : List Line :=
  (lines.f ((narrow e seen, cells), seed e)).1

theorem part_lines (seen : Display.Seen) (cells : Cells) (e : Entry) :
    (part.f ((seen, cells), e)).1 = partLines seen cells e := rfl

/-- The document's lines, part by part, from nothing. -/
def docLines (d : Document) (seen : Display.Seen) : List (List Line) :=
  (Display.entries d.root).map (partLines seen d.cells)

end Progred.Derived
