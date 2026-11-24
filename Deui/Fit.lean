import Deui.Text
import Deui.Combine

/-!
Fitting: laying out a tree of frames as text. A frame has a doc, which says
how its own pieces and its kids may go: side by side, one under another,
indented, or the first of two ways that fits the ribbon. Laying a frame out
gives its tokens in reading order, its kids' among its own.

It's kept as it's laid: each frame with where it started, its own tokens,
and each kid as it was laid there. So when one frame is replaced, only the
frames above it are walked again, each taking its other kids as they stand;
and what comes out is a splice of the text where the frame's tokens are, or,
where a frame above it now fits differently, of that frame's.
-/

namespace Deui.Fit

open Deui Deui.Text

/-- How a frame's pieces may be laid out. -/
inductive Doc (S : Type) where
  | text (s : S)
  /-- Side by side: each part starts where the one before ended; a part's
  later lines start at the row's base column. -/
  | row (parts : List (Doc S))
  /-- One under another. -/
  | col (parts : List (Doc S))
  | indent (n : Nat) (d : Doc S)
  /-- Its later lines start `n` columns further in; its first starts where
  it would. -/
  | hang (n : Nat) (d : Doc S)
  /-- `flat` if it's one line and ends within the ribbon, else `stacked`. -/
  | alt (flat stacked : Doc S)
  /-- The frame's kid at a position. -/
  | slot (i : Nat)
  deriving Inhabited

/-- A frame: its own doc, and its kids, which the doc places by position. -/
inductive Frame (S : Type) where
  | node (doc : Doc S) (kids : List (Frame S))
  deriving Inhabited

/-- What a piece measures: its width in columns, and the piece that's `n`
columns of nothing. -/
structure Measure (S : Type) where
  width : S → Nat
  blank : Nat → S

variable {S : Type}

/-! ## Whether a doc fits on the line -/

mutual
/-- Where a doc ends if it's laid on one line from `used`, if that's within
`limit`. It stops as soon as it's past, so it costs the ribbon and not the
doc. `kid` says the same of a kid. -/
def Doc.flat (w : S → Nat) (kid : Nat → Nat → Nat → Option Nat) (limit : Nat) : Doc S → Nat → Option Nat
  | .text s, used => if used + w s ≤ limit then some (used + w s) else none
  | .row parts, used => Doc.flatAll w kid limit parts used
  | .col [], used => some used
  | .col [d], used => Doc.flat w kid limit d used
  | .col (_ :: _ :: _), _ => none
  | .indent n d, used => if used + n ≤ limit then Doc.flat w kid limit d (used + n) else none
  | .hang _ d, used => Doc.flat w kid limit d used
  | .alt flat _, used => Doc.flat w kid limit flat used
  | .slot i, used => kid i limit used

def Doc.flatAll (w : S → Nat) (kid : Nat → Nat → Nat → Option Nat) (limit : Nat) : List (Doc S) → Nat → Option Nat
  | [], used => some used
  | d :: ds, used =>
    match Doc.flat w kid limit d used with
    | some next => Doc.flatAll w kid limit ds next
    | none => none
end

mutual
def Frame.flat (w : S → Nat) : Frame S → Nat → Nat → Option Nat
  | .node doc kids, limit, used =>
    let flats := (Frame.flats w kids).toArray
    Doc.flat w (fun i l u => match flats[i]? with
      | some g => g l u
      | none => some u) limit doc used

def Frame.flats (w : S → Nat) : List (Frame S) → List (Nat → Nat → Option Nat)
  | [] => []
  | k :: ks => Frame.flat w k :: Frame.flats w ks
end

/-! ## Laying out -/

mutual
/-- A frame as it was laid out: the frame, where it started and its base
column, its own tokens with each kid as it was laid among them, the column
it ended at, and its size. -/
inductive Kept (S : Type) where
  | node (frame : Frame S) (first col : Nat) (items : List (Item S)) (stop : Nat) (extent : Extent)

inductive Item (S : Type) where
  | token (t : Token S)
  | kid (i : Nat) (kept : Kept S)
end

def Kept.frame : Kept S → Frame S
  | .node f _ _ _ _ _ => f
def Kept.first : Kept S → Nat
  | .node _ f _ _ _ _ => f
def Kept.col : Kept S → Nat
  | .node _ _ c _ _ _ => c
def Kept.items : Kept S → List (Item S)
  | .node _ _ _ is _ _ => is
def Kept.stop : Kept S → Nat
  | .node _ _ _ _ s _ => s
def Kept.extent : Kept S → Extent
  | .node _ _ _ _ _ e => e

def Item.extent : Item S → Extent
  | .token (.cell _) => ⟨0, 1⟩
  | .token (.line _) => ⟨1, 0⟩
  | .kid _ k => k.extent

/-- The size of items, one after another. -/
def extents : List (Item S) → Extent
  | [] => Extent.zero
  | i :: is => i.extent + extents is

mutual
/-- A kept frame's tokens, before others. -/
def Kept.onto : Kept S → List (Token S) → List (Token S)
  | .node _ _ _ items _ _, acc => Item.onto items acc

def Item.onto : List (Item S) → List (Token S) → List (Token S)
  | [], acc => acc
  | .token t :: is, acc => t :: Item.onto is acc
  | .kid _ k :: is, acc => Kept.onto k (Item.onto is acc)
end

/-- A kept frame's tokens, in reading order. -/
def Kept.tokens (k : Kept S) : List (Token S) := k.onto []

/-- Items' tokens, in reading order. -/
def tokensOf (is : List (Item S)) : List (Token S) := Item.onto is []

/-- What a walk of a doc gives: its items, where it ended, and the state
it passed along. -/
structure Laid (S σ : Type) where
  items : List (Item S)
  stop : Nat
  state : σ

mutual
/-- A doc's items, laid from the column `first` with later lines from
`base`. `kid` lays a kid where the doc puts it, passing a state along:
laying out from nothing passes none, and laying out again passes what was
kept. -/
def Doc.lay {σ : Type} (m : Measure S) (ribbon : Nat) (fits : Nat → Nat → Nat → Option Nat)
    (kid : Nat → Nat → Nat → σ → Option (Kept S) × σ) : Doc S → Nat → Nat → σ → Laid S σ
  | .text s, _, first, st => ⟨[.token (.cell s)], first + m.width s, st⟩
  | .row parts, base, first, st => Doc.layRow m ribbon fits kid parts base first st
  | .col [], _, first, st => ⟨[], first, st⟩
  | .col (d :: rest), base, first, st =>
    let a := Doc.lay m ribbon fits kid d base first st
    let b := Doc.layCol m ribbon fits kid rest base a.stop a.state
    ⟨a.items ++ b.items, b.stop, b.state⟩
  | .indent n d, base, first, st =>
    let a := Doc.lay m ribbon fits kid d (base + n) (first + n) st
    ⟨.token (.cell (m.blank n)) :: a.items, a.stop, a.state⟩
  | .hang n d, base, first, st => Doc.lay m ribbon fits kid d (base + n) first st
  | .alt flat stacked, base, first, st =>
    if (Doc.flat m.width fits ribbon flat first).isSome then Doc.lay m ribbon fits kid flat base first st
    else Doc.lay m ribbon fits kid stacked base first st
  | .slot i, base, first, st =>
    match kid i first base st with
    | (some k, st') => ⟨[.kid i k], k.stop, st'⟩
    | (none, st') => ⟨[], first, st'⟩

/-- Parts side by side. -/
def Doc.layRow {σ : Type} (m : Measure S) (ribbon : Nat) (fits : Nat → Nat → Nat → Option Nat)
    (kid : Nat → Nat → Nat → σ → Option (Kept S) × σ) : List (Doc S) → Nat → Nat → σ → Laid S σ
  | [], _, first, st => ⟨[], first, st⟩
  | d :: ds, base, first, st =>
    let a := Doc.lay m ribbon fits kid d base first st
    let b := Doc.layRow m ribbon fits kid ds base a.stop a.state
    ⟨a.items ++ b.items, b.stop, b.state⟩

/-- Parts under what came before: each on a new line at the base column. -/
def Doc.layCol {σ : Type} (m : Measure S) (ribbon : Nat) (fits : Nat → Nat → Nat → Option Nat)
    (kid : Nat → Nat → Nat → σ → Option (Kept S) × σ) : List (Doc S) → Nat → Nat → σ → Laid S σ
  | [], _, stop, st => ⟨[], stop, st⟩
  | d :: ds, base, _, st =>
    let a := Doc.lay m ribbon fits kid d base base st
    let b := Doc.layCol m ribbon fits kid ds base a.stop a.state
    ⟨.token (.line base) :: (a.items ++ b.items), b.stop, b.state⟩
end

mutual
/-- A frame laid out from nothing, from the column `first` with later lines
from `col`. -/
def Frame.lay (m : Measure S) (ribbon : Nat) : Frame S → Nat → Nat → Kept S
  | .node doc kids, first, col =>
    let flats := (Frame.flats m.width kids).toArray
    let lays := (Frame.lays m ribbon kids).toArray
    let r := Doc.lay m ribbon
      (fun i l u => match flats[i]? with
        | some g => g l u
        | none => some u)
      (fun i f c (_ : Unit) => ((lays[i]?).map fun g => g f c, ())) doc col first ()
    .node (.node doc kids) first col r.items r.stop (extents r.items)

def Frame.lays (m : Measure S) (ribbon : Nat) : List (Frame S) → List (Nat → Nat → Kept S)
  | [] => []
  | k :: ks => Frame.lay m ribbon k :: Frame.lays m ribbon ks
end

/-! ## Edits -/

/-- Where a kid of a reshaped frame comes from: a kid the frame had, by
where it was, or a new frame. -/
inductive Source (S : Type) where
  | kept (j : Nat)
  | fresh (f : Frame S)

/-- The frame a source is, among the kids a frame had. -/
def Source.frame (olds : List (Frame S)) : Source S → Frame S
  | .kept j => (olds[j]?).getD (.node (.row []) [])
  | .fresh f => f

/-- An edit of a frame tree, at a path of kids: a frame replaced; or
reshaped, with a new doc and its kids each one it had or a new one. -/
inductive Edit (S : Type) where
  | replace (f : Frame S)
  | kid (i : Nat) (e : Edit S)
  | reshape (doc : Doc S) (kids : List (Source S))

def Edit.apply : Edit S → Frame S → Frame S
  | .replace f, _ => f
  | .kid i e, .node doc kids => .node doc (kids.modify i (Edit.apply e))
  | .reshape doc sources, .node _ kids => .node doc (sources.map (Source.frame kids))

abbrev edits (S : Type) : EditStructure := ⟨Frame S, Edit S, Edit.apply⟩

/-! ## Laying out, kid by kid -/

/-- Whether a kid fits, by where it is among the kids. -/
def kidFits (w : S → Nat) (kids : List (Frame S)) (i limit used : Nat) : Option Nat :=
  match kids[i]? with
  | some k => Frame.flat w k limit used
  | none => some used

/-- A kid laid out from nothing, by where it is among the kids. -/
def kidLay (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (i first col : Nat) (_ : Unit) :
    Option (Kept S) × Unit :=
  ((kids[i]?).map fun k => Frame.lay m ribbon k first col, ())

theorem Frame.flats_eq (w : S → Nat) (kids : List (Frame S)) : Frame.flats w kids = kids.map (Frame.flat w) := by
  induction kids with
  | nil => simp [Frame.flats]
  | cons k ks ih => simp [Frame.flats, ih]

theorem Frame.lays_eq (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) :
    Frame.lays m ribbon kids = kids.map (Frame.lay m ribbon) := by
  induction kids with
  | nil => simp [Frame.lays]
  | cons k ks ih => simp [Frame.lays, ih]

/-- A frame laid out is its doc walked, each kid laid out from nothing. -/
theorem Frame.lay_node (m : Measure S) (ribbon : Nat) (doc : Doc S) (kids : List (Frame S)) (first col : Nat) :
    Frame.lay m ribbon (.node doc kids) first col =
      .node (.node doc kids) first col
        (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc col first ()).items
        (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc col first ()).stop
        (extents (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc col first ()).items) := by
  have hf : (fun i l u => match (Frame.flats m.width kids).toArray[i]? with
      | some g => g l u
      | none => some u) = kidFits m.width kids := by
    funext i l u
    simp only [kidFits, List.getElem?_toArray, Frame.flats_eq, List.getElem?_map]
    cases kids[i]? <;> rfl
  have hl : (fun i f c (_ : Unit) => (((Frame.lays m ribbon kids).toArray[i]?).map fun g => g f c, ())) =
      kidLay m ribbon kids := by
    funext i f c u
    simp only [kidLay, List.getElem?_toArray, Frame.lays_eq, List.getElem?_map]
    cases kids[i]? <;> rfl
  simp only [Frame.lay, hf, hl]

theorem Frame.lay_first (m : Measure S) (ribbon : Nat) (fr : Frame S) (first col : Nat) :
    (Frame.lay m ribbon fr first col).first = first := by
  cases fr with
  | node doc kids => rw [Frame.lay_node]; rfl

theorem Frame.lay_col (m : Measure S) (ribbon : Nat) (fr : Frame S) (first col : Nat) :
    (Frame.lay m ribbon fr first col).col = col := by
  cases fr with
  | node doc kids => rw [Frame.lay_node]; rfl

/-! ## Two walks that agree -/

section
variable {σ τ : Type} (m : Measure S) (ribbon : Nat) (fits : Nat → Nat → Nat → Option Nat)
  (h : Nat → Nat → Nat → σ → Option (Kept S) × σ) (g : Nat → Nat → Nat → τ → Option (Kept S) × τ)
  (R : σ → τ → Prop)

/-- Two walks gave the same items and ended at the same column, their
states still related. -/
def Agree (a : Laid S σ) (b : Laid S τ) : Prop := a.items = b.items ∧ a.stop = b.stop ∧ R a.state b.state

mutual
/-- Two ways of laying kids that give the same kid wherever their states
are related give the same walk. -/
theorem Doc.lay_agree (hk : ∀ i f c s t, R s t → (h i f c s).1 = (g i f c t).1 ∧ R (h i f c s).2 (g i f c t).2) :
    ∀ (doc : Doc S) (base first : Nat) (s : σ) (t : τ), R s t →
      Agree R (Doc.lay m ribbon fits h doc base first s) (Doc.lay m ribbon fits g doc base first t)
  | .text _, _, _, _, _, hr => ⟨rfl, rfl, hr⟩
  | .row parts, base, first, s, t, hr => by
    simp only [Doc.lay]
    exact Doc.layRow_agree hk parts base first s t hr
  | .col [], _, _, _, _, hr => ⟨rfl, rfl, hr⟩
  | .col (d :: rest), base, first, s, t, hr => by
    obtain ⟨a1, a2, a3⟩ := Doc.lay_agree hk d base first s t hr
    obtain ⟨b1, b2, b3⟩ := Doc.layCol_agree hk rest base (Doc.lay m ribbon fits g d base first t).stop _ _ a3
    simp only [Doc.lay]
    rw [a2]
    exact ⟨by simp only [a1, b1], b2, b3⟩
  | .indent n d, base, first, s, t, hr => by
    obtain ⟨a1, a2, a3⟩ := Doc.lay_agree hk d (base + n) (first + n) s t hr
    simp only [Doc.lay]
    exact ⟨by simp only [a1], a2, a3⟩
  | .hang n d, base, first, s, t, hr => by
    simp only [Doc.lay]
    exact Doc.lay_agree hk d (base + n) first s t hr
  | .alt flat stacked, base, first, s, t, hr => by
    simp only [Doc.lay]
    split
    · exact Doc.lay_agree hk flat base first s t hr
    · exact Doc.lay_agree hk stacked base first s t hr
  | .slot i, base, first, s, t, hr => by
    obtain ⟨k1, k2⟩ := hk i first base s t hr
    simp only [Doc.lay]
    rcases hh : h i first base s with ⟨x, s'⟩
    rcases hg : g i first base t with ⟨y, t'⟩
    rw [hh, hg] at k1 k2
    simp only at k1 k2
    subst k1
    cases x with
    | some k => exact ⟨rfl, rfl, k2⟩
    | none => exact ⟨rfl, rfl, k2⟩

theorem Doc.layRow_agree (hk : ∀ i f c s t, R s t → (h i f c s).1 = (g i f c t).1 ∧ R (h i f c s).2 (g i f c t).2) :
    ∀ (parts : List (Doc S)) (base first : Nat) (s : σ) (t : τ), R s t →
      Agree R (Doc.layRow m ribbon fits h parts base first s) (Doc.layRow m ribbon fits g parts base first t)
  | [], _, _, _, _, hr => ⟨rfl, rfl, hr⟩
  | d :: ds, base, first, s, t, hr => by
    obtain ⟨a1, a2, a3⟩ := Doc.lay_agree hk d base first s t hr
    obtain ⟨b1, b2, b3⟩ := Doc.layRow_agree hk ds base (Doc.lay m ribbon fits g d base first t).stop _ _ a3
    simp only [Doc.layRow]
    rw [a2]
    exact ⟨by simp only [a1, b1], b2, b3⟩

theorem Doc.layCol_agree (hk : ∀ i f c s t, R s t → (h i f c s).1 = (g i f c t).1 ∧ R (h i f c s).2 (g i f c t).2) :
    ∀ (parts : List (Doc S)) (base stop : Nat) (s : σ) (t : τ), R s t →
      Agree R (Doc.layCol m ribbon fits h parts base stop s) (Doc.layCol m ribbon fits g parts base stop t)
  | [], _, _, _, _, hr => ⟨rfl, rfl, hr⟩
  | d :: ds, base, stop, s, t, hr => by
    obtain ⟨a1, a2, a3⟩ := Doc.lay_agree hk d base base s t hr
    obtain ⟨b1, b2, b3⟩ := Doc.layCol_agree hk ds base (Doc.lay m ribbon fits g d base base t).stop _ _ a3
    simp only [Doc.layCol]
    rw [a2]
    exact ⟨by simp only [a1, b1], b2, b3⟩
end

end

/-! ## What a walk's kids are, and its size -/

section
variable {σ : Type} (m : Measure S) (ribbon : Nat) (fits : Nat → Nat → Nat → Option Nat)
  (h : Nat → Nat → Nat → σ → Option (Kept S) × σ)

mutual
/-- Every kid among a walk's items is one that `kid` gave. -/
theorem Doc.lay_kids : ∀ (doc : Doc S) (base first : Nat) (s : σ) (i : Nat) (k : Kept S),
    Item.kid i k ∈ (Doc.lay m ribbon fits h doc base first s).items → ∃ f c s', (h i f c s').1 = some k
  | .text _, _, _, _, _, _, hm => by simp [Doc.lay] at hm
  | .row parts, base, first, s, i, k, hm => by
    simp only [Doc.lay] at hm
    exact Doc.layRow_kids parts base first s i k hm
  | .col [], _, _, _, _, _, hm => by simp [Doc.lay] at hm
  | .col (d :: rest), base, first, s, i, k, hm => by
    simp only [Doc.lay, List.mem_append] at hm
    rcases hm with hm | hm
    · exact Doc.lay_kids d base first s i k hm
    · exact Doc.layCol_kids rest base _ _ i k hm
  | .indent n d, base, first, s, i, k, hm => by
    simp only [Doc.lay, List.mem_cons, reduceCtorEq, false_or] at hm
    exact Doc.lay_kids d (base + n) (first + n) s i k hm
  | .hang n d, base, first, s, i, k, hm => by
    simp only [Doc.lay] at hm
    exact Doc.lay_kids d (base + n) first s i k hm
  | .alt flat stacked, base, first, s, i, k, hm => by
    simp only [Doc.lay] at hm
    split at hm
    · exact Doc.lay_kids flat base first s i k hm
    · exact Doc.lay_kids stacked base first s i k hm
  | .slot j, base, first, s, i, k, hm => by
    simp only [Doc.lay] at hm
    rcases hh : h j first base s with ⟨x, s'⟩
    rw [hh] at hm
    cases x with
    | some k' =>
      simp only [List.mem_cons, Item.kid.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨first, base, s, by rw [hh]⟩
    | none => simp at hm

theorem Doc.layRow_kids : ∀ (parts : List (Doc S)) (base first : Nat) (s : σ) (i : Nat) (k : Kept S),
    Item.kid i k ∈ (Doc.layRow m ribbon fits h parts base first s).items → ∃ f c s', (h i f c s').1 = some k
  | [], _, _, _, _, _, hm => by simp [Doc.layRow] at hm
  | d :: ds, base, first, s, i, k, hm => by
    simp only [Doc.layRow, List.mem_append] at hm
    rcases hm with hm | hm
    · exact Doc.lay_kids d base first s i k hm
    · exact Doc.layRow_kids ds base _ _ i k hm

theorem Doc.layCol_kids : ∀ (parts : List (Doc S)) (base stop : Nat) (s : σ) (i : Nat) (k : Kept S),
    Item.kid i k ∈ (Doc.layCol m ribbon fits h parts base stop s).items → ∃ f c s', (h i f c s').1 = some k
  | [], _, _, _, _, _, hm => by simp [Doc.layCol] at hm
  | d :: ds, base, stop, s, i, k, hm => by
    simp only [Doc.layCol, List.mem_cons, reduceCtorEq, false_or, List.mem_append] at hm
    rcases hm with hm | hm
    · exact Doc.lay_kids d base base s i k hm
    · exact Doc.layCol_kids ds base _ _ i k hm
end

end

mutual
theorem Kept.onto_eq : ∀ (k : Kept S) (acc : List (Token S)), k.onto acc = k.onto [] ++ acc
  | .node _ _ _ items _ _, acc => by
    simp only [Kept.onto]
    exact Item.onto_eq items acc

theorem Item.onto_eq : ∀ (is : List (Item S)) (acc : List (Token S)), Item.onto is acc = Item.onto is [] ++ acc
  | [], acc => by simp [Item.onto]
  | .token t :: is, acc => by
    simp only [Item.onto, List.cons_append]
    rw [Item.onto_eq is acc]
  | .kid _ k :: is, acc => by
    simp only [Item.onto]
    rw [Kept.onto_eq k (Item.onto is acc), Kept.onto_eq k (Item.onto is []), Item.onto_eq is acc, List.append_assoc]
end

theorem tokensOf_nil : tokensOf ([] : List (Item S)) = [] := by simp [tokensOf, Item.onto]

theorem tokensOf_token (t : Token S) (is : List (Item S)) : tokensOf (.token t :: is) = t :: tokensOf is := by
  simp [tokensOf, Item.onto]

theorem tokensOf_kid (i : Nat) (k : Kept S) (is : List (Item S)) :
    tokensOf (.kid i k :: is) = k.tokens ++ tokensOf is := by
  simp only [tokensOf, Kept.tokens, Item.onto]
  rw [Kept.onto_eq]

theorem Kept.tokens_node (fr : Frame S) (f c : Nat) (items : List (Item S)) (stop : Nat) (e : Extent) :
    (Kept.node fr f c items stop e).tokens = tokensOf items := by
  simp [Kept.tokens, tokensOf, Kept.onto]

theorem extent_cell (c : S) (ts : List (Token S)) : extent (Token.cell c :: ts) = ⟨0, 1⟩ + extent ts :=
  extent_append [Token.cell c] ts

theorem extent_line (n : Nat) (ts : List (Token S)) : extent (Token.line n :: ts) = ⟨1, 0⟩ + extent ts :=
  extent_append [Token.line n] ts

/-- Items' size is their tokens', if each kid's is. -/
theorem extents_ok (is : List (Item S)) (h : ∀ i k, Item.kid i k ∈ is → k.extent = Text.extent k.tokens) :
    extents is = Text.extent (tokensOf is) := by
  induction is with
  | nil => rfl
  | cons it is ih =>
    have ih' := ih fun i k hk => h i k (List.mem_cons_of_mem _ hk)
    cases it with
    | token t =>
      rw [tokensOf_token]
      cases t with
      | cell c => rw [extent_cell, ← ih']; rfl
      | line n => rw [extent_line, ← ih']; rfl
    | kid i k =>
      rw [tokensOf_kid, extent_append, ← ih', ← h i k (List.mem_cons_self ..)]
      rfl

/-- A kid that laying out from nothing gave is a frame among the kids,
laid out where it stands. -/
theorem kidLay_some (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (i f c : Nat) (u : Unit)
    (k : Kept S) (h : (kidLay m ribbon kids i f c u).1 = some k) :
    ∃ fr, kids[i]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col := by
  simp only [kidLay, Option.map_eq_some_iff] at h
  obtain ⟨fr, hfr, rfl⟩ := h
  exact ⟨fr, hfr, by rw [Frame.lay_first, Frame.lay_col]⟩

mutual
/-- A frame laid out keeps the size of its tokens. -/
theorem Frame.lay_extent (m : Measure S) (ribbon : Nat) : ∀ (fr : Frame S) (f c : Nat),
    (Frame.lay m ribbon fr f c).extent = Text.extent (Frame.lay m ribbon fr f c).tokens
  | .node doc kids, f, c => by
    rw [Frame.lay_node, Kept.tokens_node]
    show extents _ = _
    refine extents_ok _ fun i k hk => ?_
    obtain ⟨f', c', u, hs⟩ := Doc.lay_kids m ribbon _ _ doc c f () i k hk
    obtain ⟨fr, hfr, hkk⟩ := kidLay_some m ribbon kids i f' c' u k hs
    rw [hkk]
    exact Frame.lays_extent m ribbon kids i fr hfr _ _

theorem Frame.lays_extent (m : Measure S) (ribbon : Nat) : ∀ (kids : List (Frame S)) (i : Nat) (fr : Frame S),
    kids[i]? = some fr → ∀ (f c : Nat),
      (Frame.lay m ribbon fr f c).extent = Text.extent (Frame.lay m ribbon fr f c).tokens
  | [], _, _, h, _, _ => by simp at h
  | k :: _, 0, fr, h, f, c => by
    have e : k = fr := by simpa using h
    exact e ▸ Frame.lay_extent m ribbon k f c
  | _ :: ks, i + 1, fr, h, f, c => Frame.lays_extent m ribbon ks i fr (by simpa using h) f c
end

/-! ## Laying out again -/

/-- A kept item made ready for its frame to be walked again: a token as it
is, or a kid, by where it was among the kids, with what it's laid as now
and the splices that take its tokens there. -/
inductive Ready (S : Type) where
  | token (t : Token S)
  | kid (j : Nat) (old new : Kept S) (splices : List (Splice S))

/-- The first kid that was at `j` among ready items, if it stood where a
kid is now to stand: what it's laid as now, and the items after it. -/
def find (j first col : Nat) : List (Ready S) → Option (Kept S × List (Ready S))
  | [] => none
  | .token _ :: rest => find j first col rest
  | .kid j' old new _ :: rest =>
    if j' = j then (if old.first = first ∧ old.col = col then some (new, rest) else none)
    else find j first col rest

/-- A kid for a walk, from what was kept: if the kid was one the frame had
(`origin` says where), and it stood where this is to stand, as it's laid
now; else laid out from nothing. -/
def reuse (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (origin : Nat → Option Nat)
    (i first col : Nat) (ready : List (Ready S)) : Option (Kept S) × List (Ready S) :=
  match (origin i).bind fun j => find j first col ready with
  | some found => (some found.1, found.2)
  | none => ((kids[i]?).map fun fr => Frame.lay m ribbon fr first col, ready)

/-- Whether two tokens are the same: at once if their cells are the one
object, as a doc's own are from one walk to the next. -/
def sameToken [DecidableEq S] : Token S → Token S → Bool
  | .cell a, .cell b => withPtrEq a b (fun _ => decide (a = b)) (by intro h; simp [h])
  | .line n, .line n' => n == n'
  | _, _ => false

theorem sameToken_sound [DecidableEq S] (a b : Token S) (h : sameToken a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [sameToken, withPtrEq]

/-- Whether an item of a walk is what a ready item is now: the same token,
or the kid it was, standing where it stood. -/
def alike [DecidableEq S] (origin : Nat → Option Nat) : Ready S → Item S → Bool
  | .token t, .token t' => sameToken t t'
  | .kid j _ new _, .kid i k => origin i == some j && new.first == k.first && new.col == k.col
  | _, _ => false

/-- The items a walk has in common with what was kept, from the front, and
what's left of each. -/
def strip [DecidableEq S] (origin : Nat → Option Nat) :
    List (Ready S) → List (Item S) → (List (Ready S) × List (Item S)) × (List (Ready S) × List (Item S))
  | r :: rs, it :: is =>
    if alike origin r it then
      let rest := strip origin rs is
      ((r :: rest.1.1, it :: rest.1.2), rest.2)
    else (([], []), (r :: rs, it :: is))
  | rs, is => (([], []), (rs, is))

def Ready.old1 : Ready S → List (Token S)
  | .token t => [t]
  | .kid _ old _ _ => old.tokens

def Ready.new1 : Ready S → List (Token S)
  | .token t => [t]
  | .kid _ _ new _ => new.tokens

def Item.tokens1 : Item S → List (Token S)
  | .token t => [t]
  | .kid _ k => k.tokens

/-- The tokens ready items had, and have now. -/
def olds (rs : List (Ready S)) : List (Token S) := rs.flatMap Ready.old1

def news (rs : List (Ready S)) : List (Token S) := rs.flatMap Ready.new1

/-- The size ready items had. -/
def oldExtents : List (Ready S) → Extent
  | [] => Extent.zero
  | .token t :: rs => (Item.token t).extent + oldExtents rs
  | .kid _ old _ _ :: rs => old.extent + oldExtents rs

/-- The kids' splices, each moved past what's before its kid, from `off`. -/
def fine : Extent → List (Ready S) → List (Splice S)
  | _, [] => []
  | off, .token t :: rs => fine (off + (Item.token t).extent) rs
  | off, .kid _ _ new sp :: rs => sp.map (Splice.shift off) ++ fine (off + new.extent) rs

/-- The splices that take a frame's tokens to a walk's. What the walk has
in common with what was kept, from the front and from the end, is left,
but for the splices of a kid within it; what's between is taken out, and
the walk's put in. -/
def mend [DecidableEq S] (origin : Nat → Option Nat) (ready : List (Ready S)) (items : List (Item S)) :
    List (Splice S) :=
  let front := strip origin ready items
  let back := strip origin front.2.1.reverse front.2.2.reverse
  let between := back.2.1.reverse
  let put := back.2.2.reverse
  fine Extent.zero front.1.1 ++
    (if between.isEmpty && put.isEmpty then []
      else [⟨extents front.1.2, oldExtents between, tokensOf put⟩]) ++
    fine (extents front.1.2 + extents put) back.1.1.reverse

/-- A kept item made ready: a kid at `i` laid again by `relay`, any other
as it stands. -/
def readied [DecidableEq S] (relay : Kept S → List (Splice S) × Kept S) (i : Nat) : Item S → Ready S
  | .token t => .token t
  | .kid j k =>
    if j = i then
      let made := relay k
      .kid j k made.2 made.1
    else .kid j k k []

/-- A kept item made ready, as it stands. -/
def Item.ready : Item S → Ready S
  | .token t => .token t
  | .kid j k => .kid j k k []

/-- A frame walked again, with its kids as they're kept where they can be:
what's kept for it, and the splices that take its tokens there. -/
def rewalk [DecidableEq S] (m : Measure S) (ribbon : Nat) (doc : Doc S) (kids : List (Frame S))
    (origin : Nat → Option Nat) (first col : Nat) (ready : List (Ready S)) : List (Splice S) × Kept S :=
  let w := Doc.lay m ribbon (kidFits m.width kids) (reuse m ribbon kids origin) doc col first ready
  (mend origin ready w.items, .node (.node doc kids) first col w.items w.stop (extents w.items))

/-- Where the kid at a position of a reshaped frame was, if it was one the
frame had. -/
def Source.origin (sources : Array (Source S)) (had : Nat) (i : Nat) : Option Nat :=
  match sources[i]? with
  | some (.kept j) => if j < had then some j else none
  | _ => none

/-- A kept frame after an edit, and the splices that take its tokens
there. A frame replaced is laid out from nothing, where it stood. A frame
above it, or one reshaped, is walked again with its kids as they're kept;
what comes out as it was is left, and what doesn't is spliced. -/
def Kept.relay [DecidableEq S] (m : Measure S) (ribbon : Nat) : Edit S → Kept S → List (Splice S) × Kept S
  | .replace f, k =>
    let made := Frame.lay m ribbon f k.first k.col
    ([⟨Extent.zero, k.extent, made.tokens⟩], made)
  | .kid i e, .node (.node doc kids) first col items _ _ =>
    rewalk m ribbon doc (kids.modify i (Edit.apply e)) some first col
      (items.map (readied (Kept.relay m ribbon e) i))
  | .reshape doc sources, .node (.node _ kids) first col items _ _ =>
    rewalk m ribbon doc (sources.map (Source.frame kids)) (Source.origin sources.toArray kids.length) first col
      (items.map Item.ready)

/-- A ready item is sound: its kid, as it's laid now, is the frame that
kid is now (`was` says, by where the kid was) laid out from nothing where
it stood, and its splices take the old tokens to the new. -/
def Ready.Sound (m : Measure S) (ribbon : Nat) (was : Nat → Option (Frame S)) : Ready S → Prop
  | .token _ => True
  | .kid j old new sp =>
    ∃ fr, was j = some fr ∧ new = Frame.lay m ribbon fr old.first old.col ∧ Takes sp old.tokens new.tokens ∧
      old.extent = Text.extent old.tokens

theorem find_ok (m : Measure S) (ribbon : Nat) (was : Nat → Option (Frame S)) (j first col : Nat) :
    ∀ (ready : List (Ready S)) (k : Kept S) (rest : List (Ready S)), (∀ r ∈ ready, r.Sound m ribbon was) →
      find j first col ready = some (k, rest) →
      (∃ fr, was j = some fr ∧ k = Frame.lay m ribbon fr first col) ∧ ∀ r ∈ rest, r.Sound m ribbon was
  | [], _, _, _, h => by simp [find] at h
  | .token _ :: more, k, rest, hs, h => by
    simp only [find] at h
    exact find_ok m ribbon was j first col more k rest (fun r hr => hs r (List.mem_cons_of_mem _ hr)) h
  | .kid j' old new sp :: more, k, rest, hs, h => by
    simp only [find] at h
    split at h
    · next hj =>
      subst hj
      split at h
      · next hc =>
        obtain ⟨rfl, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨fr, hfr, hnew, _⟩ := hs (.kid j' old new sp) (List.mem_cons_self ..)
        exact ⟨⟨fr, hfr, hnew⟩, fun r hr => hs r (List.mem_cons_of_mem _ hr)⟩
      · cases h
    · exact find_ok m ribbon was j first col more k rest (fun r hr => hs r (List.mem_cons_of_mem _ hr)) h

/-- Reusing what's kept gives what laying out from nothing gives. -/
theorem reuse_ok (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (origin : Nat → Option Nat)
    (was : Nat → Option (Frame S)) (horigin : ∀ i j, origin i = some j → kids[i]? = was j) (i first col : Nat)
    (ready : List (Ready S)) (hs : ∀ r ∈ ready, r.Sound m ribbon was) :
    (reuse m ribbon kids origin i first col ready).1 = (kidLay m ribbon kids i first col ()).1 ∧
      ∀ r ∈ (reuse m ribbon kids origin i first col ready).2, r.Sound m ribbon was := by
  unfold reuse
  cases ho : origin i with
  | none => exact ⟨rfl, hs⟩
  | some j =>
    simp only [Option.bind_some]
    cases hf : find j first col ready with
    | none => exact ⟨rfl, hs⟩
    | some found =>
      obtain ⟨k, rest⟩ := found
      obtain ⟨⟨fr, hfr, hk⟩, hrest⟩ := find_ok m ribbon was j first col ready k rest hs hf
      refine ⟨?_, hrest⟩
      simp [kidLay, horigin i j ho, hfr, hk]

theorem tokensOf_flatMap (is : List (Item S)) : tokensOf is = is.flatMap Item.tokens1 := by
  induction is with
  | nil => simp [tokensOf_nil]
  | cons it is ih =>
    cases it with
    | token t => simp [tokensOf_token, Item.tokens1, ih]
    | kid i k => simp [tokensOf_kid, Item.tokens1, ih]

/-- An item of a walk that's alike a sound ready item has its tokens. -/
theorem alike_tokens [DecidableEq S] (m : Measure S) (ribbon : Nat) (kids : List (Frame S))
    (origin : Nat → Option Nat) (was : Nat → Option (Frame S))
    (horigin : ∀ i j, origin i = some j → kids[i]? = was j) (r : Ready S) (it : Item S)
    (hs : r.Sound m ribbon was)
    (hk : ∀ i k, it = Item.kid i k → ∃ fr, kids[i]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col)
    (h : alike origin r it = true) : r.new1 = it.tokens1 := by
  cases r with
  | token t =>
    cases it with
    | token t' => simp only [alike] at h; simp [Ready.new1, Item.tokens1, sameToken_sound t t' h]
    | kid i k => simp [alike] at h
  | kid j old new sp =>
    cases it with
    | token t' => simp [alike] at h
    | kid i k =>
      simp only [alike, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨ho, hf⟩, hc⟩ := h
      obtain ⟨fr, hfr, hnew, _⟩ := hs
      obtain ⟨fr', hfr', hkk⟩ := hk i k rfl
      have e : fr' = fr := by
        rw [horigin i j ho, hfr] at hfr'
        exact (Option.some.inj hfr').symm
      have : k = new := by rw [hkk, e, ← hf, ← hc, hnew, Frame.lay_first, Frame.lay_col]
      simp [Ready.new1, Item.tokens1, this]

/-- What `strip` takes off the front is the front of each, and the items
taken off have the tokens the ready ones have now. -/
theorem strip_ok [DecidableEq S] (m : Measure S) (ribbon : Nat) (kids : List (Frame S))
    (origin : Nat → Option Nat) (was : Nat → Option (Frame S))
    (horigin : ∀ i j, origin i = some j → kids[i]? = was j) :
    ∀ (rs : List (Ready S)) (is : List (Item S)), (∀ r ∈ rs, r.Sound m ribbon was) →
      (∀ i k, Item.kid i k ∈ is → ∃ fr, kids[i]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col) →
      rs = (strip origin rs is).1.1 ++ (strip origin rs is).2.1 ∧
        is = (strip origin rs is).1.2 ++ (strip origin rs is).2.2 ∧
        (strip origin rs is).1.1.map Ready.new1 = (strip origin rs is).1.2.map Item.tokens1
  | [], is, _, _ => by simp [strip]
  | r :: rs, [], _, _ => by simp [strip]
  | r :: rs, it :: is, hs, hk => by
    simp only [strip]
    split
    · next h =>
      obtain ⟨h1, h2, h3⟩ := strip_ok m ribbon kids origin was horigin rs is
        (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (fun i k hm => hk i k (List.mem_cons_of_mem _ hm))
      have ht := alike_tokens m ribbon kids origin was horigin r it (hs r (List.mem_cons_self ..))
        (fun i k e => hk i k (e ▸ List.mem_cons_self ..)) h
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.cons_append]; rw [← h1]
      · simp only [List.cons_append]; rw [← h2]
      · simp only [List.map_cons, ht, h3]
    · simp

theorem oldExtents_ok (m : Measure S) (ribbon : Nat) (was : Nat → Option (Frame S)) :
    ∀ (rs : List (Ready S)), (∀ r ∈ rs, r.Sound m ribbon was) → oldExtents rs = Text.extent (olds rs)
  | [], _ => rfl
  | .token t :: rs, hs => by
    have ih := oldExtents_ok m ribbon was rs fun r hr => hs r (List.mem_cons_of_mem _ hr)
    show (Item.token t).extent + oldExtents rs = Text.extent ([t] ++ olds rs)
    rw [extent_append, ih]
    cases t <;> rfl
  | .kid j old new sp :: rs, hs => by
    have ih := oldExtents_ok m ribbon was rs fun r hr => hs r (List.mem_cons_of_mem _ hr)
    obtain ⟨_, _, _, _, hext⟩ := hs (.kid j old new sp) (List.mem_cons_self ..)
    show old.extent + oldExtents rs = Text.extent (old.tokens ++ olds rs)
    rw [extent_append, ih, hext]

theorem fine_takes (m : Measure S) (ribbon : Nat) (was : Nat → Option (Frame S)) :
    ∀ (ready : List (Ready S)), (∀ r ∈ ready, r.Sound m ribbon was) → ∀ (P : List (Token S)),
      Takes (fine (Text.extent P) ready) (P ++ olds ready) (P ++ news ready)
  | [], _, P => Takes.none _
  | .token t :: rs, hs, P => by
    have ih := fine_takes m ribbon was rs (fun r hr => hs r (List.mem_cons_of_mem _ hr)) (P ++ [t])
    have e : Text.extent (P ++ [t]) = Text.extent P + (Item.token t).extent := by
      rw [extent_append]
      cases t <;> rfl
    rw [e] at ih
    simpa [fine, olds, news, Ready.old1, Ready.new1] using ih
  | .kid j old new sp :: rs, hs, P => by
    obtain ⟨fr, _, hnew, hT, _⟩ := hs (.kid j old new sp) (List.mem_cons_self ..)
    have ih := fine_takes m ribbon was rs (fun r hr => hs r (List.mem_cons_of_mem _ hr)) (P ++ new.tokens)
    have e : Text.extent (P ++ new.tokens) = Text.extent P + new.extent := by
      rw [extent_append, hnew, Frame.lay_extent]
    rw [e] at ih
    have first := Takes.inside sp old.tokens new.tokens hT P (olds rs)
    have both := Takes.then_ _ _ _ _ _ first (by simpa [olds, news] using ih)
    simpa [fine, olds, news, Ready.old1, Ready.new1] using both

/-- Mending is right: its splices take what was kept to the walk. -/
theorem mend_takes [DecidableEq S] (m : Measure S) (ribbon : Nat) (kids : List (Frame S))
    (origin : Nat → Option Nat) (was : Nat → Option (Frame S))
    (horigin : ∀ i j, origin i = some j → kids[i]? = was j) (ready : List (Ready S)) (items : List (Item S))
    (hs : ∀ r ∈ ready, r.Sound m ribbon was)
    (hk : ∀ i k, Item.kid i k ∈ items → ∃ fr, kids[i]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col) :
    Takes (mend origin ready items) (olds ready) (tokensOf items) := by
  obtain ⟨f1, f2, f3⟩ := strip_ok m ribbon kids origin was horigin ready items hs hk
  -- What's left of each, from the end.
  have hs1 : ∀ r ∈ (strip origin ready items).2.1.reverse, r.Sound m ribbon was := by
    intro r hr
    exact hs r (by rw [f1]; exact List.mem_append_right _ (List.mem_reverse.mp hr))
  have hk1 : ∀ i k, Item.kid i k ∈ (strip origin ready items).2.2.reverse →
      ∃ fr, kids[i]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col := by
    intro i k hm
    exact hk i k (by rw [f2]; exact List.mem_append_right _ (List.mem_reverse.mp hm))
  obtain ⟨b1, b2, b3⟩ := strip_ok m ribbon kids origin was horigin _ _ hs1 hk1
  simp only [mend]
  generalize hfront : strip origin ready items = front at f1 f2 f3 b1 b2 b3 hs1 hk1 ⊢
  generalize hback : strip origin front.2.1.reverse front.2.2.reverse = back at b1 b2 b3 ⊢
  have r1 : front.2.1 = back.2.1.reverse ++ back.1.1.reverse := by
    have := congrArg List.reverse b1
    simpa using this
  have i1 : front.2.2 = back.2.2.reverse ++ back.1.2.reverse := by
    have := congrArg List.reverse b2
    simpa using this
  have q3 : back.1.1.reverse.map Ready.new1 = back.1.2.reverse.map Item.tokens1 := by
    rw [List.map_reverse, List.map_reverse, b3]
  -- Soundness of each run of ready items, and the sizes of the walk's.
  have sp : ∀ r ∈ front.1.1, r.Sound m ribbon was := fun r hr => hs r (by rw [f1]; exact List.mem_append_left _ hr)
  have sm : ∀ r ∈ back.2.1.reverse, r.Sound m ribbon was := fun r hr =>
    hs r (by rw [f1, r1]; exact List.mem_append_right _ (List.mem_append_left _ hr))
  have sq : ∀ r ∈ back.1.1.reverse, r.Sound m ribbon was := fun r hr =>
    hs r (by rw [f1, r1]; exact List.mem_append_right _ (List.mem_append_right _ hr))
  have kext : ∀ (is : List (Item S)), (∀ x ∈ is, x ∈ items) → extents is = Text.extent (tokensOf is) := by
    intro is sub
    refine extents_ok is fun i k hm => ?_
    obtain ⟨fr, _, hkk⟩ := hk i k (sub _ hm)
    rw [hkk, Frame.lay_extent]
  have subp : ∀ x ∈ front.1.2, x ∈ items := fun x hx => by rw [f2]; exact List.mem_append_left _ hx
  have subm : ∀ x ∈ back.2.2.reverse, x ∈ items := fun x hx => by
    rw [f2, i1]; exact List.mem_append_right _ (List.mem_append_left _ hx)
  -- The tokens, as the three runs.
  have tp : tokensOf front.1.2 = news front.1.1 := by
    rw [tokensOf_flatMap, news, List.flatMap_def, List.flatMap_def, f3]
  have tq : tokensOf back.1.2.reverse = news back.1.1.reverse := by
    rw [tokensOf_flatMap, news, List.flatMap_def, List.flatMap_def, q3]
  have told : olds ready = olds front.1.1 ++ (olds back.2.1.reverse ++ olds back.1.1.reverse) := by
    conv => lhs; rw [f1, r1]
    simp [olds]
  have tnew : tokensOf items = news front.1.1 ++ (tokensOf back.2.2.reverse ++ news back.1.1.reverse) := by
    conv => lhs; rw [f2, i1]
    rw [← tp, ← tq]
    simp [tokensOf_flatMap]
  rw [told, tnew]
  -- The front: its kids' splices.
  have t1 : Takes (fine Extent.zero front.1.1)
      (olds front.1.1 ++ (olds back.2.1.reverse ++ olds back.1.1.reverse))
      (news front.1.1 ++ (olds back.2.1.reverse ++ olds back.1.1.reverse)) := by
    have h := fine_takes m ribbon was front.1.1 sp []
    have h' := Takes.before _ _ _ h (olds back.2.1.reverse ++ olds back.1.1.reverse)
    simpa [extent_nil] using h'
  -- What's between: taken out, and the walk's put in.
  have t2 : Takes (if back.2.1.reverse.isEmpty && back.2.2.reverse.isEmpty then []
        else [⟨extents front.1.2, oldExtents back.2.1.reverse, tokensOf back.2.2.reverse⟩])
      (news front.1.1 ++ (olds back.2.1.reverse ++ olds back.1.1.reverse))
      (news front.1.1 ++ (tokensOf back.2.2.reverse ++ olds back.1.1.reverse)) := by
    split
    · next hem =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hem
      rw [hem.1, hem.2]
      simpa [olds, tokensOf_nil] using Takes.none (C := S) _
    · have h := Takes.inside _ _ _ (Takes.whole (olds back.2.1.reverse) (tokensOf back.2.2.reverse))
        (news front.1.1) (olds back.1.1.reverse)
      rw [kext front.1.2 subp, tp, oldExtents_ok m ribbon was _ sm]
      simpa [Splice.shift, Extent.add_zero] using h
  -- The end: its kids' splices, past the front and what's put in.
  have t3 : Takes (fine (extents front.1.2 + extents back.2.2.reverse) back.1.1.reverse)
      (news front.1.1 ++ (tokensOf back.2.2.reverse ++ olds back.1.1.reverse))
      (news front.1.1 ++ (tokensOf back.2.2.reverse ++ news back.1.1.reverse)) := by
    have h := fine_takes m ribbon was back.1.1.reverse sq (news front.1.1 ++ tokensOf back.2.2.reverse)
    have e : Text.extent (news front.1.1 ++ tokensOf back.2.2.reverse) =
        extents front.1.2 + extents back.2.2.reverse := by
      rw [extent_append, ← tp, ← kext front.1.2 subp, ← kext _ subm]
    rw [e] at h
    simpa [List.append_assoc] using h
  exact Takes.then_ _ _ _ _ _ (Takes.then_ _ _ _ _ _ t1 t2) t3

theorem olds_readied [DecidableEq S] (relay : Kept S → List (Splice S) × Kept S) (i : Nat) (items : List (Item S)) :
    olds (items.map (readied relay i)) = tokensOf items := by
  rw [tokensOf_flatMap]
  induction items with
  | nil => rfl
  | cons it is ih =>
    simp only [olds, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases it with
    | token t => rfl
    | kid j k => by_cases hj : j = i <;> simp [readied, hj, Ready.old1, Item.tokens1]

theorem olds_ready (items : List (Item S)) : olds (items.map Item.ready) = tokensOf items := by
  rw [tokensOf_flatMap]
  induction items with
  | nil => rfl
  | cons it is ih =>
    simp only [olds, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases it <;> rfl

theorem Frame.lay_frame (m : Measure S) (ribbon : Nat) (fr : Frame S) (first col : Nat) :
    (Frame.lay m ribbon fr first col).frame = fr := by
  cases fr with
  | node doc kids => rw [Frame.lay_node]; rfl

/-- Walking a frame again is right: what's kept is the frame laid out from
nothing, and the splices take what was kept there. -/
theorem rewalk_ok [DecidableEq S] (m : Measure S) (ribbon : Nat) (doc : Doc S) (kids : List (Frame S))
    (origin : Nat → Option Nat) (was : Nat → Option (Frame S))
    (horigin : ∀ i j, origin i = some j → kids[i]? = was j) (first col : Nat) (ready : List (Ready S))
    (hs : ∀ r ∈ ready, r.Sound m ribbon was) :
    (rewalk m ribbon doc kids origin first col ready).2 = Frame.lay m ribbon (.node doc kids) first col ∧
      Takes (rewalk m ribbon doc kids origin first col ready).1 (olds ready)
        (Frame.lay m ribbon (.node doc kids) first col).tokens := by
  obtain ⟨hitems, hstop, _⟩ := Doc.lay_agree m ribbon (kidFits m.width kids) (reuse m ribbon kids origin)
    (kidLay m ribbon kids) (fun s (_ : Unit) => ∀ r ∈ s, r.Sound m ribbon was)
    (fun j f' c' s _ hs' => reuse_ok m ribbon kids origin was horigin j f' c' s hs') doc col first _ () hs
  have hk : ∀ j k, Item.kid j k ∈ (Doc.lay m ribbon (kidFits m.width kids) (reuse m ribbon kids origin) doc col
      first ready).items → ∃ fr, kids[j]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col := by
    intro j k hm
    rw [hitems] at hm
    obtain ⟨f', c', u, hs'⟩ := Doc.lay_kids m ribbon _ _ doc col first () j k hm
    exact kidLay_some m ribbon _ j f' c' u k hs'
  have ht := mend_takes m ribbon kids origin was horigin ready _ hs hk
  rw [Frame.lay_node, Kept.tokens_node]
  simp only [rewalk]
  refine ⟨by rw [hitems, hstop], ?_⟩
  rw [← hitems]
  exact ht

/-- Laying out again is right: what's kept after an edit is the edited
frame laid out from nothing, and the splices take the tokens there,
wherever they sit. -/
theorem Kept.relay_ok [DecidableEq S] (m : Measure S) (ribbon : Nat) : ∀ (e : Edit S) (fr : Frame S) (f c : Nat),
    (Kept.relay m ribbon e (Frame.lay m ribbon fr f c)).2 = Frame.lay m ribbon (e.apply fr) f c ∧
      Takes (Kept.relay m ribbon e (Frame.lay m ribbon fr f c)).1 (Frame.lay m ribbon fr f c).tokens
        (Frame.lay m ribbon (e.apply fr) f c).tokens
  | .replace f', fr, f, c => by
    simp only [Kept.relay, Edit.apply, Frame.lay_first, Frame.lay_col]
    refine ⟨trivial, ?_⟩
    rw [Frame.lay_extent]
    exact Takes.whole _ _
  | .kid i e, .node doc kids, f, c => by
    rw [Frame.lay_node, Kept.tokens_node]
    simp only [Edit.apply, Kept.relay]
    -- The kept items, ready for the kids as they are now.
    have hready : ∀ r ∈ (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
        (readied (Kept.relay m ribbon e) i),
        r.Sound m ribbon (fun j => (kids.modify i (Edit.apply e))[j]?) := by
      intro r hr
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hr
      cases it with
      | token t => exact True.intro
      | kid j k =>
        obtain ⟨f', c', u, hs⟩ := Doc.lay_kids m ribbon _ _ doc c f () j k hit
        obtain ⟨frj, hfr, hkk⟩ := kidLay_some m ribbon kids j f' c' u k hs
        have hext : k.extent = Text.extent k.tokens := by rw [hkk, Frame.lay_extent]
        by_cases hj : j = i
        · subst hj
          have ih := Kept.relay_ok m ribbon e frj k.first k.col
          rw [← hkk] at ih
          simp only [readied, ite_true]
          exact ⟨Edit.apply e frj, by simp [hfr], ih.1, by rw [ih.1]; exact ih.2, hext⟩
        · simp only [readied, hj, ite_false]
          refine ⟨frj, ?_, hkk, Takes.none _, hext⟩
          simp [hfr, Ne.symm hj]
    have h := rewalk_ok m ribbon doc (kids.modify i (Edit.apply e)) some
      (fun j => (kids.modify i (Edit.apply e))[j]?) (fun a b hab => by cases hab; rfl) f c _ hready
    rw [olds_readied] at h
    exact h
  | .reshape doc' sources, .node doc kids, f, c => by
    rw [Frame.lay_node, Kept.tokens_node]
    simp only [Edit.apply, Kept.relay]
    have hready : ∀ r ∈ (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
        Item.ready, r.Sound m ribbon (fun j => kids[j]?) := by
      intro r hr
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hr
      cases it with
      | token t => exact True.intro
      | kid j k =>
        obtain ⟨f', c', u, hs⟩ := Doc.lay_kids m ribbon _ _ doc c f () j k hit
        obtain ⟨frj, hfr, hkk⟩ := kidLay_some m ribbon kids j f' c' u k hs
        exact ⟨frj, hfr, hkk, Takes.none _, by rw [hkk, Frame.lay_extent]⟩
    have horigin : ∀ i j, Source.origin sources.toArray kids.length i = some j →
        (sources.map (Source.frame kids))[i]? = kids[j]? := by
      intro i j h
      simp only [Source.origin, List.getElem?_toArray] at h
      cases hsi : sources[i]? with
      | none => simp [hsi] at h
      | some src =>
        rw [hsi] at h
        cases src with
        | fresh fr => simp at h
        | kept j' =>
          simp only at h
          split at h
          · next hlt =>
            cases h
            simp [hsi, Source.frame, List.getElem?_eq_getElem hlt]
          · cases h
    have h := rewalk_ok m ribbon doc' (sources.map (Source.frame kids))
      (Source.origin sources.toArray kids.length) (fun j => kids[j]?) horigin f c _ hready
    rw [olds_ready] at h
    exact h

/-! ## Edits of kids -/

theorem modify_append_cons {α : Type} (pre : List α) (x : α) (post : List α) (f : α → α) :
    (pre ++ x :: post).modify pre.length f = pre ++ f x :: post := by
  induction pre with
  | nil => rfl
  | cons y ys ih => simp [List.modify_succ_cons, ih]

/-- A run of edits of one kid. -/
theorem run_kid (doc : Doc S) (pre : List (Frame S)) (x : Frame S) (post : List (Frame S)) (es : List (Edit S)) :
    run (edits S) (es.map (.kid pre.length)) (.node doc (pre ++ x :: post)) =
      .node doc (pre ++ run (edits S) es x :: post) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    show run (edits S) (es.map (.kid pre.length)) (Edit.apply (.kid pre.length e) (.node doc (pre ++ x :: post))) = _
    simp only [Edit.apply, modify_append_cons]
    exact ih (Edit.apply e x)

/-- Each kid's own run of edits, one kid after another, takes a frame's
kids each to what its run makes of it. -/
theorem run_kids {α : Type} (doc : Doc S) (old new : α → Frame S) (es : α → List (Edit S)) :
    ∀ (xs : List α) (pre : List (Frame S)), (∀ x ∈ xs, run (edits S) (es x) (old x) = new x) →
      run (edits S) ((xs.zipIdx pre.length).flatMap fun p => (es p.1).map (.kid p.2))
          (.node doc (pre ++ xs.map old)) =
        .node doc (pre ++ xs.map new)
  | [], _, _ => rfl
  | x :: xs, pre, h => by
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_cons]
    rw [run_append, run_kid, h x (List.mem_cons_self ..)]
    have ih := run_kids doc old new es xs (pre ++ [new x]) fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc,
      List.cons_append, List.nil_append] at ih
    exact ih

/-! ## Fitting, as an incremental function -/

/-- A kept frame after a run of edits. -/
def relays [DecidableEq S] (m : Measure S) (ribbon : Nat) : List (Edit S) → Kept S → List (Splice S) × Kept S
  | [], k => ([], k)
  | e :: es, k =>
    let made := Kept.relay m ribbon e k
    let rest := relays m ribbon es made.2
    (made.1 ++ rest.1, rest.2)

theorem relays_ok [DecidableEq S] (m : Measure S) (ribbon : Nat) : ∀ (es : List (Edit S)) (fr : Frame S) (f c : Nat),
    (relays m ribbon es (Frame.lay m ribbon fr f c)).2 = Frame.lay m ribbon (run (edits S) es fr) f c ∧
      Takes (relays m ribbon es (Frame.lay m ribbon fr f c)).1 (Frame.lay m ribbon fr f c).tokens
        (Frame.lay m ribbon (run (edits S) es fr) f c).tokens
  | [], _, _, _ => ⟨rfl, Takes.none _⟩
  | e :: es, fr, f, c => by
    obtain ⟨h1, h2⟩ := Kept.relay_ok m ribbon e fr f c
    simp only [relays, h1]
    obtain ⟨r1, r2⟩ := relays_ok m ribbon es (Edit.apply e fr) f c
    exact ⟨r1, Takes.then_ _ _ _ _ _ h2 r2⟩

/-- Fitting's derivative: the same ribbon lays out again what the edits
reach; a new one lays everything out. -/
def fit.df [DecidableEq S] (m : Measure S) (ribbon : Nat) (kept : Kept S) (ribbon' : Nat) (es : List (Edit S)) :
    List (Splice S) × (Nat × Kept S) :=
  if ribbon' = ribbon then
    let made := relays m ribbon es kept
    (made.1, (ribbon, made.2))
  else
    let made := Frame.lay m ribbon' (run (edits S) es kept.frame) 0 0
    ([⟨Extent.zero, kept.extent, made.tokens⟩], (ribbon', made))

/-- A frame tree laid out as text within a ribbon, as an incremental
function of the ribbon and the tree. A frame replaced costs the frames
above it, each walked once; a new ribbon lays everything out again. -/
def fit [DecidableEq S] (m : Measure S) : Cached (prod (latest Nat) (runs (edits S))) (runs (Text.edits S)) where
  Cache := Nat × Kept S
  f a :=
    let made := Frame.lay m a.1 a.2 0 0
    (lines made.tokens, (a.1, made))
  df k d := fit.df m k.1 k.2 d.1 d.2

/-- Fitting's derivative is right: its splices take the text to the edited
tree's, and what it keeps is what laying that out from nothing keeps. -/
theorem fit_ok [DecidableEq S] (m : Measure S) : (fit m).ok := by
  intro a d
  have key : ∀ (ribbon ribbon' : Nat) (fr : Frame S) (es : List (Edit S)),
      (run (Text.edits S) (fit.df m ribbon (Frame.lay m ribbon fr 0 0) ribbon' es).1
          (lines (Frame.lay m ribbon fr 0 0).tokens), (fit.df m ribbon (Frame.lay m ribbon fr 0 0) ribbon' es).2) =
        (lines (Frame.lay m ribbon' (run (edits S) es fr) 0 0).tokens,
          (ribbon', Frame.lay m ribbon' (run (edits S) es fr) 0 0)) := by
    intro ribbon ribbon' fr es
    by_cases hr : ribbon' = ribbon
    · subst hr
      obtain ⟨h1, h2⟩ := relays_ok m ribbon' es fr 0 0
      simp only [fit.df, ite_true, h1]
      rw [Takes.lines _ _ _ h2]
    · simp only [fit.df, hr, ite_false, Frame.lay_frame]
      rw [Frame.lay_extent]
      have := Takes.lines _ _ _ (Takes.whole (Frame.lay m ribbon fr 0 0).tokens
        (Frame.lay m ribbon' (run (edits S) es fr) 0 0).tokens)
      rw [this]
  exact key a.1 d.1 a.2 d.2

end Deui.Fit
