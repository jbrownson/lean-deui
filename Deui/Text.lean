import Deui.Spans

/-!
Text: lines of cells, made from tokens in reading order, each a cell or the
start of a new line. A text is edited by a splice: so much taken out at a
place, and tokens put in. The place is lines down and cells along, so a
splice costs the lines above it and no more; and what makes it right is
that the lines of tokens joined are the lines of each, joined: a splice at
the end of `A`, taking out the size of `M`, turns the lines of `A ++ M ++ B`
into the lines of `A ++ M' ++ B`.
-/

namespace Deui.Text

open Deui

/-- What text is made of, in reading order. -/
inductive Token (C : Type) where
  | cell (c : C)
  /-- The start of a new line, indented. -/
  | line (indent : Nat)

/-- A line: how far it's indented, and its cells. A text's first line has
no indent of its own: it starts where the text does. -/
structure Line (C : Type) where
  indent : Nat
  cells : List C
  deriving DecidableEq, Repr

variable {C : Type}

/-- Lines, as all but the last and the last, with a cell put first. -/
def lead (c : C) : List (Line C) × Line C → List (Line C) × Line C
  | ([], a) => ([], ⟨a.indent, c :: a.cells⟩)
  | (x :: xs, a) => (⟨x.indent, c :: x.cells⟩ :: xs, a)

/-- And with a new line begun first: what was the first line is indented. -/
def broken (n : Nat) : List (Line C) × Line C → List (Line C) × Line C
  | ([], a) => ([⟨0, []⟩], ⟨n, a.cells⟩)
  | (x :: xs, a) => (⟨0, []⟩ :: ⟨n, x.cells⟩ :: xs, a)

/-- The lines of tokens: all but the last, and the last. -/
def parts : List (Token C) → List (Line C) × Line C
  | [] => ([], ⟨0, []⟩)
  | .cell c :: ts => lead c (parts ts)
  | .line n :: ts => broken n (parts ts)

/-- The lines of tokens. Never empty: no tokens is one empty line. -/
def lines (ts : List (Token C)) : List (Line C) := (parts ts).1 ++ [(parts ts).2]

/-- A size, or a place: lines down, and cells along the last line. -/
structure Extent where
  lines : Nat
  last : Nat
  deriving DecidableEq, Repr

/-- One size after another: the lines of both, and the cells along the last
line, which are the second's unless it has no line of its own. -/
def Extent.add (a b : Extent) : Extent :=
  ⟨a.lines + b.lines, if b.lines = 0 then a.last + b.last else b.last⟩

instance : Add Extent := ⟨Extent.add⟩

def Extent.zero : Extent := ⟨0, 0⟩

/-- The size of tokens: how many lines they start, and the cells after the
last start. -/
def extent (ts : List (Token C)) : Extent := ⟨(parts ts).1.length, (parts ts).2.cells.length⟩

/-- A line with the first of some lines run on at its end. -/
def fuse (a : Line C) : List (Line C) → List (Line C)
  | [] => [a]
  | c :: cs => ⟨a.indent, a.cells ++ c.cells⟩ :: cs

/-- Lines with cells run on at the end of the last. -/
def endWith (post : List C) : List (Line C) → List (Line C)
  | [] => []
  | [l] => [⟨l.indent, l.cells ++ post⟩]
  | l :: ls => l :: endWith post ls

/-- A splice: at `start`, `gone` is taken out and `put` goes in. -/
structure Splice (C : Type) where
  start : Extent
  gone : Extent
  put : List (Token C)

/-- The lines a splice puts where the ones it reaches were: the cells
before it on its first line, what it puts in, and the cells after it on
its last. -/
def Splice.middle (s : Splice C) (ls : List (Line C)) : List (Line C) :=
  let first := (ls[s.start.lines]?).getD ⟨0, []⟩
  let last := (ls[s.start.lines + s.gone.lines]?).getD ⟨0, []⟩
  let post := last.cells.drop (if s.gone.lines = 0 then s.start.last + s.gone.last else s.gone.last)
  fuse ⟨first.indent, first.cells.take s.start.last⟩ (endWith post (lines s.put))

/-- The lines after a splice. -/
def Splice.apply (s : Splice C) (ls : List (Line C)) : List (Line C) :=
  ls.take s.start.lines ++ s.middle ls ++ ls.drop (s.start.lines + s.gone.lines + 1)

/-- Text's edits: splices. -/
abbrev edits (C : Type) : EditStructure := ⟨List (Line C), Splice C, Splice.apply⟩

/-- A splice moved to sit after something of a size. -/
def Splice.shift (by_ : Extent) (s : Splice C) : Splice C := { s with start := by_ + s.start }

/-! ## The lines of tokens joined -/

/-- The lines of tokens begin with a line that has no indent. -/
theorem lines_cons (ts : List (Token C)) : ∃ b bs, lines ts = ⟨0, b⟩ :: bs := by
  induction ts with
  | nil => exact ⟨[], [], rfl⟩
  | cons t ts ih =>
    obtain ⟨b, bs, h⟩ := ih
    unfold lines at h ⊢
    cases t with
    | cell c =>
      rcases hp : parts ts with ⟨_ | ⟨x, xs⟩, a⟩
      · rw [hp] at h
        simp only [List.nil_append, List.cons.injEq] at h
        exact ⟨c :: b, [], by simp [parts, hp, lead, h.1]⟩
      · rw [hp] at h
        simp only [List.cons_append, List.cons.injEq] at h
        exact ⟨c :: b, xs ++ [a], by simp [parts, hp, lead, h.1]⟩
    | line n =>
      rcases hp : parts ts with ⟨_ | ⟨x, xs⟩, a⟩
      · exact ⟨[], [⟨n, a.cells⟩], by simp [parts, hp, broken]⟩
      · exact ⟨[], ⟨n, x.cells⟩ :: xs ++ [a], by simp [parts, hp, broken]⟩

/-- The lines of tokens joined: the first's, with the second's first line
run on at the end of its last. -/
theorem lines_append (xs ys : List (Token C)) :
    lines (xs ++ ys) = (parts xs).1 ++ fuse (parts xs).2 (lines ys) := by
  obtain ⟨b, bs, hy⟩ := lines_cons ys
  induction xs with
  | nil => simp [parts, hy, fuse]
  | cons t ts ih =>
    rw [hy] at ih ⊢
    unfold lines at ih ⊢
    cases t with
    | cell c =>
      rcases hp : parts ts with ⟨_ | ⟨u, us⟩, a⟩
      · rw [hp] at ih
        rcases hq : parts (ts ++ ys) with ⟨_ | ⟨v, vs⟩, z⟩
        · rw [hq] at ih
          simp only [List.nil_append, fuse, List.cons.injEq] at ih
          simp [parts, hp, hq, lead, fuse, ih.1, ← ih.2]
        · rw [hq] at ih
          simp only [List.nil_append, fuse, List.cons_append, List.cons.injEq] at ih
          simp [parts, hp, hq, lead, fuse, ih.1, ih.2]
      · rw [hp] at ih
        rcases hq : parts (ts ++ ys) with ⟨_ | ⟨v, vs⟩, z⟩
        · rw [hq] at ih
          have := congrArg List.length ih
          simp [fuse] at this
        · rw [hq] at ih
          simp only [List.cons_append, List.cons.injEq] at ih
          simp [parts, hp, hq, lead, ih.1, ih.2]
    | line n =>
      rcases hp : parts ts with ⟨_ | ⟨u, us⟩, a⟩
      · rw [hp] at ih
        rcases hq : parts (ts ++ ys) with ⟨_ | ⟨v, vs⟩, z⟩
        · rw [hq] at ih
          simp only [List.nil_append, fuse, List.cons.injEq] at ih
          simp [parts, hp, hq, broken, fuse, ih.1, ← ih.2]
        · rw [hq] at ih
          simp only [List.nil_append, fuse, List.cons_append, List.cons.injEq] at ih
          simp [parts, hp, hq, broken, fuse, ih.1, ih.2]
      · rw [hp] at ih
        rcases hq : parts (ts ++ ys) with ⟨_ | ⟨v, vs⟩, z⟩
        · rw [hq] at ih
          have := congrArg List.length ih
          simp [fuse] at this
        · rw [hq] at ih
          simp only [List.cons_append, List.cons.injEq] at ih
          simp [parts, hp, hq, broken, ih.1, ih.2]

theorem append_singleton_inj {α : Type} (xs ys : List α) (a b : α) (h : xs ++ [a] = ys ++ [b]) :
    xs = ys ∧ a = b := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

/-- The parts of tokens joined. -/
theorem parts_append (xs ys : List (Token C)) :
    parts (xs ++ ys) =
      match (parts ys).1 with
      | [] => ((parts xs).1, ⟨(parts xs).2.indent, (parts xs).2.cells ++ (parts ys).2.cells⟩)
      | y :: rest => ((parts xs).1 ++ ⟨(parts xs).2.indent, (parts xs).2.cells ++ y.cells⟩ :: rest, (parts ys).2) := by
  have h := lines_append xs ys
  unfold lines at h
  rcases hy : parts ys with ⟨_ | ⟨y, rest⟩, z⟩
  · rw [hy] at h
    simp only [List.nil_append, fuse] at h
    obtain ⟨h1, h2⟩ := append_singleton_inj _ _ _ _ h
    exact Prod.ext h1 h2
  · rw [hy] at h
    simp only [List.cons_append, fuse] at h
    have h' : (parts (xs ++ ys)).1 ++ [(parts (xs ++ ys)).2] =
        ((parts xs).1 ++ ⟨(parts xs).2.indent, (parts xs).2.cells ++ y.cells⟩ :: rest) ++ [z] := by
      rw [h]; simp
    obtain ⟨h1, h2⟩ := append_singleton_inj _ _ _ _ h'
    exact Prod.ext h1 h2

/-- The size of tokens joined is the size of each, one after another. -/
theorem extent_append (xs ys : List (Token C)) : extent (xs ++ ys) = extent xs + extent ys := by
  show extent (xs ++ ys) = Extent.add (extent xs) (extent ys)
  unfold extent Extent.add
  rw [parts_append]
  rcases hy : parts ys with ⟨_ | ⟨y, rest⟩, z⟩
  · simp
  · simp

theorem Extent.add_assoc (a b c : Extent) : a + b + c = a + (b + c) := by
  show Extent.add (Extent.add a b) c = Extent.add a (Extent.add b c)
  unfold Extent.add
  by_cases hc : c.lines = 0 <;> by_cases hb : b.lines = 0 <;> simp [hc, hb] <;> omega

theorem Extent.zero_add (a : Extent) : Extent.zero + a = a := by
  show Extent.add Extent.zero a = a
  unfold Extent.add Extent.zero
  cases a with
  | mk l k => by_cases h : l = 0 <;> simp [h]

theorem extent_nil : extent ([] : List (Token C)) = Extent.zero := rfl

theorem endWith_snoc (post : List C) (xs : List (Line C)) (m : Line C) :
    endWith post (xs ++ [m]) = xs ++ [⟨m.indent, m.cells ++ post⟩] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons x2 xs =>
      show x :: endWith post (x2 :: xs ++ [m]) = _
      rw [ih]; rfl

theorem fuse_snoc (a : Line C) (zs : List (Line C)) (l : Line C) (bs : List (Line C)) :
    fuse a (zs ++ [l]) ++ bs = fuse a (zs ++ l :: bs) := by
  cases zs <;> simp [fuse]

theorem drop_length_add {α : Type} (xs ys : List α) (k : Nat) :
    (xs ++ ys).drop (xs.length + k) = ys.drop k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have e : (x :: xs).length + k = (xs.length + k) + 1 := by simp; omega
    rw [e]
    exact ih

/-- A splice is right: at the end of `A`, taking out the size of `M` and
putting in `M'`, it turns the lines of `A ++ M ++ B` into the lines of
`A ++ M' ++ B`. -/
theorem splice_ok (A M M' B : List (Token C)) :
    Splice.apply ⟨extent A, extent M, M'⟩ (lines (A ++ (M ++ B))) = lines (A ++ (M' ++ B)) := by
  rcases hA : parts A with ⟨xa, a⟩
  rcases hM : parts M with ⟨xm, m⟩
  rcases hM' : parts M' with ⟨xm', m'⟩
  obtain ⟨b, bs, hB⟩ := lines_cons B
  have R : lines (A ++ (M' ++ B)) = xa ++ fuse a (xm' ++ ⟨m'.indent, m'.cells ++ b⟩ :: bs) := by
    rw [lines_append, lines_append, hA, hM', hB]; rfl
  have put : lines M' = xm' ++ [m'] := by simp [lines, hM']
  have eA : extent A = ⟨xa.length, a.cells.length⟩ := by simp [extent, hA]
  have eM : extent M = ⟨xm.length, m.cells.length⟩ := by simp [extent, hM]
  rw [R, eA, eM]
  cases xm with
  | nil =>
    have L : lines (A ++ (M ++ B)) = xa ++ ⟨a.indent, a.cells ++ (m.cells ++ b)⟩ :: bs := by
      rw [lines_append, lines_append, hA, hM, hB]; rfl
    rw [L]
    simp only [Splice.apply, Splice.middle, put, endWith_snoc, List.length_nil, Nat.add_zero, ite_true,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.take_left']
    have hd : List.drop (xa.length + 1) (xa ++ ⟨a.indent, a.cells ++ (m.cells ++ b)⟩ :: bs) = bs := by
      rw [drop_length_add]; rfl
    have hpost : List.drop (a.cells.length + m.cells.length) (a.cells ++ (m.cells ++ b)) = b := by
      rw [drop_length_add]; simp
    rw [hd, List.append_assoc, fuse_snoc, hpost]
  | cons y ys =>
    have L : lines (A ++ (M ++ B)) =
        xa ++ ⟨a.indent, a.cells ++ y.cells⟩ :: (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs) := by
      rw [lines_append, lines_append, hA, hM, hB]; rfl
    rw [L]
    have hne : (ys.length + 1 = 0) = False := by simp
    have hfirst : (xa ++ ⟨a.indent, a.cells ++ y.cells⟩ :: (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs))[xa.length]? =
        some ⟨a.indent, a.cells ++ y.cells⟩ := by simp
    have hlast : (xa ++ ⟨a.indent, a.cells ++ y.cells⟩ :: (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs))[
        xa.length + (ys.length + 1)]? = some ⟨m.indent, m.cells ++ b⟩ := by
      rw [List.getElem?_append_right (by omega)]
      simp
    have hd : List.drop (xa.length + (ys.length + 1) + 1)
        (xa ++ ⟨a.indent, a.cells ++ y.cells⟩ :: (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs)) = bs := by
      have e : xa.length + (ys.length + 1) + 1 = xa.length + (ys.length + 2) := by omega
      rw [e, drop_length_add]
      show List.drop (ys.length + 1) (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs) = bs
      rw [drop_length_add]
      rfl
    have ht : List.take xa.length
        (xa ++ ⟨a.indent, a.cells ++ y.cells⟩ :: (ys ++ ⟨m.indent, m.cells ++ b⟩ :: bs)) = xa := by simp
    simp only [Splice.apply, Splice.middle, put, endWith_snoc, List.length_cons, hne, ite_false, hfirst, hlast,
      Option.getD_some, hd, ht]
    have hpost : List.drop m.cells.length (m.cells ++ b) = b := by simp
    have hpre : List.take a.cells.length (a.cells ++ y.cells) = a.cells := by simp
    rw [hpost, hpre, List.append_assoc, fuse_snoc]

/-! ## Making lines without going deep -/

/-- One token taken, from the end: the cells of the line being made, and
the lines after it. -/
def lines.step (t : Token C) (p : List C × List (Line C)) : List C × List (Line C) :=
  match t with
  | .cell c => (c :: p.1, p.2)
  | .line n => ([], ⟨n, p.1⟩ :: p.2)

/-- The lines of tokens, taken from the end: as `lines`, without a call for
each token one inside another. -/
def linesFolded (ts : List (Token C)) : List (Line C) :=
  let p := ts.foldr lines.step ([], [])
  ⟨0, p.1⟩ :: p.2

@[csimp] theorem lines_eq_folded : @lines = @linesFolded := by
  funext C ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold lines at ih ⊢
    unfold linesFolded at ih ⊢
    rw [List.foldr_cons]
    rcases hp : parts ts with ⟨_ | ⟨x, xs⟩, a⟩ <;> rw [hp] at ih
    · simp only [List.nil_append, List.cons.injEq] at ih
      cases t with
      | cell c => simp [parts, hp, lead, lines.step, ih.1, ← ih.2]
      | line n => simp [parts, hp, broken, lines.step, ih.1, ← ih.2]
    · simp only [List.cons_append, List.cons.injEq] at ih
      cases t with
      | cell c => simp [parts, hp, lead, lines.step, ih.1, ← ih.2]
      | line n => simp [parts, hp, broken, lines.step, ih.1, ← ih.2]

/-! ## Splices, wherever the tokens sit -/

theorem Extent.add_zero (a : Extent) : a + Extent.zero = a := by
  show Extent.add a Extent.zero = a
  simp [Extent.add, Extent.zero]

/-- A run of splices takes tokens `T` to `T'` wherever they sit: whatever
comes before and after, the splices, moved past what's before, take the
lines of the whole to the lines of the whole with `T'` in `T`'s place. -/
def Takes (sp : List (Splice C)) (T T' : List (Token C)) : Prop :=
  ∀ A B, run (edits C) (sp.map (Splice.shift (extent A))) (lines (A ++ (T ++ B))) = lines (A ++ (T' ++ B))

theorem Takes.none (T : List (Token C)) : Takes [] T T := fun _ _ => rfl

/-- One splice that takes all of `T` out and puts `T'` in. -/
theorem Takes.whole (T T' : List (Token C)) : Takes [⟨Extent.zero, extent T, T'⟩] T T' := by
  intro A B
  show Splice.apply (Splice.shift (extent A) ⟨Extent.zero, extent T, T'⟩) (lines (A ++ (T ++ B))) = _
  simp only [Splice.shift, Extent.add_zero]
  exact splice_ok A T T' B

/-- Splices that take `X` to `X'`, moved past `P`, take `P ++ X ++ Q` to
`P ++ X' ++ Q`. -/
theorem Takes.inside (sp : List (Splice C)) (X X' : List (Token C)) (h : Takes sp X X') (P Q : List (Token C)) :
    Takes (sp.map (Splice.shift (extent P))) (P ++ (X ++ Q)) (P ++ (X' ++ Q)) := by
  intro A B
  have e : ∀ Y : List (Token C), A ++ ((P ++ (Y ++ Q)) ++ B) = (A ++ P) ++ (Y ++ (Q ++ B)) := by
    intro Y; simp
  have m : (sp.map (Splice.shift (extent P))).map (Splice.shift (extent A)) =
      sp.map (Splice.shift (extent (A ++ P))) := by
    rw [List.map_map]
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, Splice.shift, extent_append, Extent.add_assoc]
  rw [e, e, m]
  exact h (A ++ P) (Q ++ B)

/-- Splices that take `T` to `T'` take them there with something after. -/
theorem Takes.before (sp : List (Splice C)) (T T' : List (Token C)) (h : Takes sp T T') (Q : List (Token C)) :
    Takes sp (T ++ Q) (T' ++ Q) := by
  intro A B
  have := h A (Q ++ B)
  simpa using this

/-- One run of splices then another. -/
theorem Takes.then_ (sp sp' : List (Splice C)) (T T' T'' : List (Token C)) (h : Takes sp T T')
    (h' : Takes sp' T' T'') : Takes (sp ++ sp') T T'' := by
  intro A B
  rw [List.map_append, run_append, h A B]
  exact h' A B

/-- At the start, with nothing around, the splices take the lines to the lines. -/
theorem Takes.lines (sp : List (Splice C)) (T T' : List (Token C)) (h : Takes sp T T') :
    run (edits C) sp (lines T) = lines T' := by
  have := h [] []
  simp only [List.nil_append, List.append_nil] at this
  have m : sp.map (Splice.shift (extent ([] : List (Token C)))) = sp := by
    conv => rhs; rw [← List.map_id sp]
    refine List.map_congr_left fun s _ => ?_
    simp [Splice.shift, extent_nil, Extent.zero_add]
  rwa [m] at this

/-! ## Lines as a list -/

/-- The edits to the list of lines that a splice makes: the lines it
reaches replaced, one for one while both last, the rest put in or taken
out. -/
def rows.df (ls : List (Line C)) (s : Splice C) : List (Lists.Edit.of (whole (plain (Line C)))) :=
  Lists.swaps (ls.take s.start.lines).length ((ls.drop s.start.lines).take (s.gone.lines + 1)) (s.middle ls)

/-- A text's lines as a list, edited line by line. -/
def rows : Inc (edits C) (runs (Lists.editStructure (whole (plain (Line C))))) := ⟨id, rows.df⟩

theorem rows_ok : (rows (C := C)).ok := by
  intro ls s
  show Lists.patch (whole (plain (Line C))) (rows.df ls s) ls = Splice.apply s ls
  have e : ls = ls.take s.start.lines ++ (ls.drop s.start.lines).take (s.gone.lines + 1) ++
      ls.drop (s.start.lines + s.gone.lines + 1) := by
    rw [List.append_assoc]
    have : ls.drop (s.start.lines + s.gone.lines + 1) = (ls.drop s.start.lines).drop (s.gone.lines + 1) := by
      rw [List.drop_drop, Nat.add_assoc]
    rw [this, List.take_append_drop, List.take_append_drop]
  have h := Lists.swaps_ok (ls.take s.start.lines) ((ls.drop s.start.lines).take (s.gone.lines + 1)) (s.middle ls)
    (ls.drop (s.start.lines + s.gone.lines + 1))
  rw [← e] at h
  exact h

end Deui.Text
