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

/-- An edit of a frame tree: a frame replaced, at a path of kids. -/
inductive Edit (S : Type) where
  | replace (f : Frame S)
  | kid (i : Nat) (e : Edit S)

def Edit.apply : Edit S → Frame S → Frame S
  | .replace f, _ => f
  | .kid i e, .node doc kids => .node doc (kids.modify i (Edit.apply e))

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
is, or a kid, with what it's laid as now and the splices that take its
tokens there. -/
inductive Ready (S : Type) where
  | token (t : Token S)
  | kid (i : Nat) (old new : Kept S) (splices : List (Splice S))

/-- A kid for a walk, from what was kept: the next kid kept, if it's this
one and stood where this is to stand; else laid out from nothing. -/
def reuse (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (i first col : Nat) :
    List (Ready S) → Option (Kept S) × List (Ready S)
  | [] => ((kids[i]?).map fun k => Frame.lay m ribbon k first col, [])
  | .token _ :: rest => reuse m ribbon kids i first col rest
  | .kid j old new _ :: rest =>
    if j = i ∧ old.first = first ∧ old.col = col then (some new, rest)
    else ((kids[i]?).map fun k => Frame.lay m ribbon k first col, rest)

/-- Whether two tokens are the same: at once if their cells are the one
object, as a doc's own are from one walk to the next. -/
def sameToken [DecidableEq S] : Token S → Token S → Bool
  | .cell a, .cell b => withPtrEq a b (fun _ => decide (a = b)) (by intro h; simp [h])
  | .line n, .line n' => n == n'
  | _, _ => false

theorem sameToken_sound [DecidableEq S] (a b : Token S) (h : sameToken a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [sameToken, withPtrEq]

/-- Whether a walk came out as what was kept, kid for kid and token for
token: then nothing of the frame's own has changed. -/
def alike [DecidableEq S] : List (Ready S) → List (Item S) → Bool
  | [], [] => true
  | .token t :: rs, .token t' :: is => sameToken t t' && alike rs is
  | .kid j _ new _ :: rs, .kid j' k :: is =>
    j == j' && new.first == k.first && new.col == k.col && alike rs is
  | _, _ => false

/-- The kids' splices, each moved past what's before its kid, from `off`. -/
def fine : Extent → List (Ready S) → List (Splice S)
  | _, [] => []
  | off, .token t :: rs => fine (off + (Item.token t).extent) rs
  | off, .kid _ _ new sp :: rs => sp.map (Splice.shift off) ++ fine (off + new.extent) rs

/-- A kept item made ready: a kid at `i` laid again by `relay`, any other
as it stands. -/
def readied [DecidableEq S] (relay : Kept S → List (Splice S) × Kept S) (i : Nat) : Item S → Ready S
  | .token t => .token t
  | .kid j k =>
    if j = i then
      let made := relay k
      .kid j k made.2 made.1
    else .kid j k k []

/-- A kept frame after an edit, and the splices that take its tokens
there. A frame replaced is laid out from nothing, where it stood. Above
it, each frame is walked again with its kids as they're kept; if it comes
out as it was but for the kid that changed, the kid's splices are all, and
otherwise its tokens are replaced whole. -/
def Kept.relay [DecidableEq S] (m : Measure S) (ribbon : Nat) : Edit S → Kept S → List (Splice S) × Kept S
  | .replace f, k =>
    let made := Frame.lay m ribbon f k.first k.col
    ([⟨Extent.zero, k.extent, made.tokens⟩], made)
  | .kid i e, .node (.node doc kids) first col items _ ext =>
    let ready := items.map (readied (Kept.relay m ribbon e) i)
    let kids' := kids.modify i (Edit.apply e)
    let w := Doc.lay m ribbon (kidFits m.width kids') (reuse m ribbon kids') doc col first ready
    let kept := Kept.node (.node doc kids') first col w.items w.stop (extents w.items)
    if alike ready w.items then (fine Extent.zero ready, kept)
    else ([⟨Extent.zero, ext, tokensOf w.items⟩], kept)

/-- A ready item is sound for the kids as they are now: its kid, as it's
laid now, is that kid laid out from nothing where it stood, and its
splices take the old tokens to the new. -/
def Ready.Sound (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) : Ready S → Prop
  | .token _ => True
  | .kid j old new sp =>
    ∃ fr, kids[j]? = some fr ∧ new = Frame.lay m ribbon fr old.first old.col ∧ Takes sp old.tokens new.tokens

/-- Reusing what's kept gives what laying out from nothing gives. -/
theorem reuse_ok (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) (i first col : Nat) :
    ∀ (s : List (Ready S)), (∀ r ∈ s, r.Sound m ribbon kids) →
      (reuse m ribbon kids i first col s).1 = (kidLay m ribbon kids i first col ()).1 ∧
        ∀ r ∈ (reuse m ribbon kids i first col s).2, r.Sound m ribbon kids
  | [], _ => ⟨rfl, by simp [reuse]⟩
  | .token _ :: rest, hs => by
    simp only [reuse]
    exact reuse_ok m ribbon kids i first col rest fun r hr => hs r (List.mem_cons_of_mem _ hr)
  | .kid j old new sp :: rest, hs => by
    simp only [reuse]
    split
    · next hc =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      obtain ⟨fr, hfr, hnew, _⟩ := hs (.kid j old new sp) (List.mem_cons_self ..)
      exact ⟨by simp [kidLay, hfr, hnew], fun r hr => hs r (List.mem_cons_of_mem _ hr)⟩
    · exact ⟨rfl, fun r hr => hs r (List.mem_cons_of_mem _ hr)⟩

/-- The tokens ready items had, and have now. -/
def olds : List (Ready S) → List (Token S)
  | [] => []
  | .token t :: rs => t :: olds rs
  | .kid _ old _ _ :: rs => old.tokens ++ olds rs

def news : List (Ready S) → List (Token S)
  | [] => []
  | .token t :: rs => t :: news rs
  | .kid _ _ new _ :: rs => new.tokens ++ news rs

theorem alike_news [DecidableEq S] (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) :
    ∀ (ready : List (Ready S)) (items : List (Item S)), (∀ r ∈ ready, r.Sound m ribbon kids) →
      (∀ j k, Item.kid j k ∈ items → ∃ fr, kids[j]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col) →
      alike ready items = true → tokensOf items = news ready
  | [], [], _, _, _ => by simp [tokensOf_nil, news]
  | [], _ :: _, _, _, h => by simp [alike] at h
  | .token t :: rs, [], _, _, h => by simp [alike] at h
  | .token t :: rs, .kid _ _ :: is, _, _, h => by simp [alike] at h
  | .kid _ _ _ _ :: rs, [], _, _, h => by simp [alike] at h
  | .kid _ _ _ _ :: rs, .token _ :: is, _, _, h => by simp [alike] at h
  | .token t :: rs, .token t' :: is, hs, hk, h => by
    simp only [alike, Bool.and_eq_true] at h
    rw [tokensOf_token, news, ← sameToken_sound t t' h.1,
      alike_news m ribbon kids rs is (fun r hr => hs r (List.mem_cons_of_mem _ hr))
        (fun j k hm => hk j k (List.mem_cons_of_mem _ hm)) h.2]
  | .kid j old new sp :: rs, .kid j' k :: is, hs, hk, h => by
    simp only [alike, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, hf⟩, hc⟩, hrest⟩ := h
    obtain ⟨fr, hfr, hnew, _⟩ := hs (.kid j old new sp) (List.mem_cons_self ..)
    obtain ⟨fr', hfr', hkk⟩ := hk j k (List.mem_cons_self ..)
    have e : fr' = fr := by rw [hfr] at hfr'; exact (Option.some.inj hfr').symm
    have hk' : k = new := by
      rw [hkk, e, ← hf, ← hc, hnew, Frame.lay_first, Frame.lay_col]
    rw [tokensOf_kid, news, hk',
      alike_news m ribbon kids rs is (fun r hr => hs r (List.mem_cons_of_mem _ hr))
        (fun j k hm => hk j k (List.mem_cons_of_mem _ hm)) hrest]

theorem fine_takes (m : Measure S) (ribbon : Nat) (kids : List (Frame S)) :
    ∀ (ready : List (Ready S)), (∀ r ∈ ready, r.Sound m ribbon kids) → ∀ (P : List (Token S)),
      Takes (fine (Text.extent P) ready) (P ++ olds ready) (P ++ news ready)
  | [], _, P => Takes.none _
  | .token t :: rs, hs, P => by
    have ih := fine_takes m ribbon kids rs (fun r hr => hs r (List.mem_cons_of_mem _ hr)) (P ++ [t])
    have e : Text.extent (P ++ [t]) = Text.extent P + (Item.token t).extent := by
      rw [extent_append]
      cases t <;> rfl
    rw [e] at ih
    simpa [fine, olds, news] using ih
  | .kid j old new sp :: rs, hs, P => by
    obtain ⟨fr, _, hnew, hT⟩ := hs (.kid j old new sp) (List.mem_cons_self ..)
    have ih := fine_takes m ribbon kids rs (fun r hr => hs r (List.mem_cons_of_mem _ hr)) (P ++ new.tokens)
    have e : Text.extent (P ++ new.tokens) = Text.extent P + new.extent := by
      rw [extent_append, hnew, Frame.lay_extent]
    rw [e] at ih
    have first := Takes.inside sp old.tokens new.tokens hT P (olds rs)
    have both := Takes.then_ _ _ _ _ _ first (by simpa using ih)
    simpa [fine, olds, news] using both

theorem olds_readied [DecidableEq S] (relay : Kept S → List (Splice S) × Kept S) (i : Nat) (items : List (Item S)) :
    olds (items.map (readied relay i)) = tokensOf items := by
  induction items with
  | nil => simp [olds, tokensOf_nil]
  | cons it is ih =>
    cases it with
    | token t => simp [readied, olds, tokensOf_token, ih]
    | kid j k =>
      by_cases hj : j = i <;> simp [readied, hj, olds, tokensOf_kid, ih]

theorem Frame.lay_frame (m : Measure S) (ribbon : Nat) (fr : Frame S) (first col : Nat) :
    (Frame.lay m ribbon fr first col).frame = fr := by
  cases fr with
  | node doc kids => rw [Frame.lay_node]; rfl

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
    have hold := Frame.lay_extent m ribbon (.node doc kids) f c
    rw [Frame.lay_node] at hold ⊢
    rw [Kept.tokens_node] at hold ⊢
    simp only [Edit.apply]
    rw [Frame.lay_node, Kept.tokens_node]
    -- The kept items, ready for the kids as they are now.
    have hready : ∀ r ∈ (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
        (readied (Kept.relay m ribbon e) i), r.Sound m ribbon (kids.modify i (Edit.apply e)) := by
      intro r hr
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hr
      cases it with
      | token t => exact True.intro
      | kid j k =>
        obtain ⟨f', c', u, hs⟩ := Doc.lay_kids m ribbon _ _ doc c f () j k hit
        obtain ⟨frj, hfr, hkk⟩ := kidLay_some m ribbon kids j f' c' u k hs
        by_cases hj : j = i
        · subst hj
          have ih := Kept.relay_ok m ribbon e frj k.first k.col
          rw [← hkk] at ih
          simp only [readied, ite_true]
          exact ⟨Edit.apply e frj, by simp [hfr], ih.1, by rw [ih.1]; exact ih.2⟩
        · simp only [readied, hj, ite_false]
          refine ⟨frj, ?_, hkk, Takes.none _⟩
          simp [hfr, Ne.symm hj]
    -- Walking with what's kept is walking from nothing.
    have hw := Doc.lay_agree m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
      (reuse m ribbon (kids.modify i (Edit.apply e))) (kidLay m ribbon (kids.modify i (Edit.apply e)))
      (fun s (_ : Unit) => ∀ r ∈ s, r.Sound m ribbon (kids.modify i (Edit.apply e)))
      (fun j f' c' s _ hs => reuse_ok m ribbon _ j f' c' s hs) doc c f _ () hready
    obtain ⟨hitems, hstop, _⟩ := hw
    simp only [Kept.relay]
    have hkept : Kept.node (.node doc (kids.modify i (Edit.apply e))) f c
        (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
          (reuse m ribbon (kids.modify i (Edit.apply e))) doc c f
          ((Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
            (readied (Kept.relay m ribbon e) i))).items
        (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
          (reuse m ribbon (kids.modify i (Edit.apply e))) doc c f
          ((Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
            (readied (Kept.relay m ribbon e) i))).stop
        (extents (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
          (reuse m ribbon (kids.modify i (Edit.apply e))) doc c f
          ((Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
            (readied (Kept.relay m ribbon e) i))).items) =
        Kept.node (.node doc (kids.modify i (Edit.apply e))) f c
          (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
            (kidLay m ribbon (kids.modify i (Edit.apply e))) doc c f ()).items
          (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
            (kidLay m ribbon (kids.modify i (Edit.apply e))) doc c f ()).stop
          (extents (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
            (kidLay m ribbon (kids.modify i (Edit.apply e))) doc c f ()).items) := by
      rw [hitems, hstop]
    split
    · next hal =>
      refine ⟨hkept, ?_⟩
      have hk : ∀ j k, Item.kid j k ∈ (Doc.lay m ribbon (kidFits m.width (kids.modify i (Edit.apply e)))
          (reuse m ribbon (kids.modify i (Edit.apply e))) doc c f
          ((Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items.map
            (readied (Kept.relay m ribbon e) i))).items →
          ∃ fr, (kids.modify i (Edit.apply e))[j]? = some fr ∧ k = Frame.lay m ribbon fr k.first k.col := by
        intro j k hm
        rw [hitems] at hm
        obtain ⟨f', c', u, hs⟩ := Doc.lay_kids m ribbon _ _ doc c f () j k hm
        exact kidLay_some m ribbon _ j f' c' u k hs
      have hn := alike_news m ribbon _ _ _ hready hk hal
      have ht : Takes (fine Extent.zero _) ([] ++ olds _) ([] ++ news _) := fine_takes m ribbon _ _ hready []
      rw [olds_readied] at ht
      rw [← hitems, hn]
      simpa using ht
    · refine ⟨hkept, ?_⟩
      rw [← hitems]
      have : (Kept.node (.node doc kids) f c
          (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items
          (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).stop
          (extents (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items)).extent =
          extents (Doc.lay m ribbon (kidFits m.width kids) (kidLay m ribbon kids) doc c f ()).items := rfl
      rw [this] at hold
      rw [hold]
      exact Takes.whole _ _

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
