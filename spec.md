# The canonical hypergraph — foundation spec for redundant compute

## Status, printed on the spec

This spec is settled intent, as dictated by Chris on
2026-11-19 (the ruling of 15:43 PST, the steering of
15:37 PST, and the heads-up of 15:46 PST). It is the
foundation document of the redundant compute program,
re-founded. It is not implemented behavior: no code and
no proof in this lane, and no existing repo implements
it. It is not verified behavior: nothing in it has been
checked by a gate. The claims listed in section 13 are
proposed semantics — exact statements the rebuild must
prove — at exactly that strength.

Four states are kept distinct throughout: settled
intent, proposed semantics, implemented behavior,
verified behavior. The definitions in sections 2 to 12
are settled intent about the model's shape: the rebuild
implements exactly these definitions or it implements a
different model. Where a genuine choice was left open by
the ruling, the choice taken is named in place and
collected in section 14. No silent ambiguity is left:
a point not decided here is named as not decided, with
its owner.

Reading rules. Plain words name the model's notions.
Quoted forms in code blocks are the exact forms a Lean
development must take: type names are single words,
field names are single words, and no name in those
blocks uses an underscore, a camel form, or a mashed
compound. Foreign names quoted from other repos keep
their own spelling and are evidence, not models.

## 1. The one model, in one paragraph

There is one hypergraph. It is the total equivalence
graph of equivalent terms: its edges are sets of
equivalent symbolic expressions, at the minimum
resolution, where the symbol is the finest grain. It is
bound, at any resolution time, only by the finite
resolved upper bound taken through the only lattice
(section 4). Resolution levels differ; they are all
appended to this same graph and reconciled on it, never
kept as separate graphs per level (section 7). Resolved
information is appended only; nothing resolved is ever
removed, split, renamed, or rewritten, and drift is
excluded by that construction (section 8). Colorings,
qualifications across software, across qualification,
and across intent, and every proof in the program, are
constructed from this one graph and from nothing else
(sections 9 and 12). The scope of what is resolved
widens incrementally with available compute — trivial
first order expressions first, wider forms as compute
allows — under rules that never change the model
(section 3).

## 2. Symbols and terms

### 2.1 Symbols

A symbol is an atom of the model: indivisible at every
resolution the model admits. The symbol is the finest
grain. No resolution splits a symbol, and no two
distinct symbols are the same symbol.

Lean form. The development takes the symbol type as a
parameter with decidable equality, and fixes nothing
else about it:

```
variable (Sym : Type) [DecidableEq Sym]
```

Choice taken: symbols are not natural numbers and not
identifiers of any kind. An encoding of symbols as
numbers is an implementation detail outside the model;
the old model's identifier lists are exactly what this
choice excludes. A subject supplies its own symbol
type (its own names, at its own grain), and the grain
of that type is the subject's minimum resolution.

### 2.2 Terms

A term is a symbolic expression: a finite tree built
from symbols. There is one grammar, fixed for all
scopes, all levels, and all qualifications:

```
inductive Term (Sym : Type) where
  | atom : Sym → Term Sym
  | form : Term Sym → List (Term Sym) → Term Sym
```

An atom term is a single symbol standing alone. A form
term is a head term applied to a finite list of
argument terms, in list order. List order in a form is
spelling: two forms whose argument lists differ only in
order are different terms until an equivalence in
section 6 joins them; the model does not silently
identify them.

The parts of a term, and the symbols of a term, are
functions of the grammar alone:

```
def parts : Term Sym → List (Term Sym)
  | .atom _ => []
  | .form head args => head :: args

def symbols : Term Sym → List Sym
  | .atom name => [name]
  | .form head args => symbols head ++ (args.map symbols).flatten
```

`symbols` is the occurrence list, with multiplicity.
The distinct symbols of a term are its occurrence list
read up to membership. Minimum resolution means exactly
this: every term is resolved down to its symbols, and
no analysis in the program resolves below a symbol.
The highest possible resolution is at least symbolic
resolution: a reading of observed behavior that stops
above the symbol is a coarser level (section 7), never
the foundation.

Terms are finite by construction of the inductive type.
Equality of terms as spelled (same tree, same symbols)
is decidable from decidable equality of symbols; the
development must provide that instance. Spelling
equality is not equivalence: equivalence is section 6.

## 3. Scope — the incremental widening rule

### 3.1 The three scopes

A scope is a decidable predicate on terms naming which
terms may be resolved while compute is bound at that
scope. Exactly three scopes are named, in widening
order:

```
def trivial : Term Sym → Bool
  | .atom _ => true
  | .form (.atom _) args =>
      args.all (fun arg => match arg with
        | .atom _ => true
        | _ => false)
  | _ => false

def first : Term Sym → Bool
  | .atom _ => true
  | .form (.atom _) args => args.all first
  | _ => false

def full : Term Sym → Bool
  | _ => true
```

The Lean names are `trivial`, `first`, and `full`, for
the trivial scope, the first order scope, and the full
scope. In words. A trivial term is an atom, or a form whose
head is an atom and whose every argument is an atom:
the first order trivial expressions. A first order term
is an atom, or a form whose head is an atom and whose
arguments are first order terms: compound arguments are
admitted, the head is still a symbol. A term outside
the first order scope — a form whose head is itself a
form, anywhere in its tree — is a higher order term.
The full scope admits every term.

The scopes are nested, and the rebuild must prove the
nesting as its first scope lemma: every trivial term is
first order, and every first order term is in the full
scope. A scope a subject needs between these is a
further decidable predicate on the same grammar; it is
added by appending its definition, never by changing
the grammar.

### 3.2 The rule

The scope rule is a rule of the model, not a parameter
of convenience:

1. Where compute is bound, resolution is restricted to
   the trivial scope. Where more compute is available,
   resolution widens to the first order scope, and then
   to the full scope. Widening is monotone: a term
   resolved at a narrower scope stays resolved, under
   the same name and in the same edge, at every wider
   scope.
2. What changes when scope widens: only the set of
   terms resolved and appended, and what is derived
   from them — the bounds taken, the edges formed, the
   colors painted. Nothing else changes.
3. What never changes when scope widens: the grammar of
   section 2, the symbol grain, the definition of
   equivalence, the singularity of the graph, the
   lattice of section 4, the append rules of section 8,
   the coloring rules of section 9, and the definition
   of redundancy in section 10.
4. A term outside the current scope is unresolved: it
   is absent from the graph, and its state is
   unmeasured, never absent in the sense of refuted, and
   never represented by a placeholder term, a dummy
   symbol, or a coarser stand-in inside the graph. A
   coarser reading of it may exist as its own term at
   its own level (section 7), as itself, not as a
   substitute.

## 4. The only lattice, and states

### 4.1 States

A state is a finite collection of terms, carried as a
list and read up to membership: two lists with the same
members are the same state for every purpose of this
model. This is the family's standing form, taken from
the bidirectional home at `b14fc92b` and the frontier
home at `cdeae4ad`, and it is the only state notion.

```
def State (Sym : Type) := List (Term Sym)
```

State equivalence and the information order are
membership statements:

- Two states are equivalent when every term of each is
  a member of the other.
- One state is below another when every term of the
  first is a member of the second: the second knows at
  least everything the first knows.

### 4.2 The lattice

The only lattice is the join semilattice of states up
to that equivalence, with join as list append:

- Join of two states is their append, read up to
  membership: the least state containing both.
- The bottom state is the empty list.
- Join is commutative, associative, and idempotent up
  to state equivalence, extends both parts, and is the
  least state doing so. The rebuild must prove these
  five laws in this vocabulary; they are the lattice
  laws every later bound rests on.

No other lattice is introduced anywhere in the program:
not per level, not per qualification, not per subject.
Bounds, levels, frontiers, and colorings that need an
order take this one. Choice taken: the ruling's word
lattice names this join semilattice, the family's one
lattice; a meet is not defined and not needed, and the
rebuild must not add one silently — if a later proof
needs a meet, that need is a spec change, owned by the
coordinator, not an implementer's liberty.

### 4.3 Finiteness

Finiteness is derived, never assumed. A qualification
names its software, its criteria, and the behavior
intended under them (frontier home, search spec,
section 5 of that document, cited not re-proved there
and cited here the same way). A resolved set is a list
by construction of the state type. Therefore every
bound taken in section 7 is a bound of a finite list,
and its finiteness is a conclusion of what a
qualification and a state are, stated nowhere as a
hypothesis.

## 5. The one hypergraph

### 5.1 Edges

An edge is a finite set of terms: the terms of one
equivalence class. An edge is not a pair, not a premise
list with a conclusion, and not a transition. It
carries its terms and its colors (section 9):

```
structure Edge (Sym : Type) where
  terms : List (Term Sym)
  colors : List (Color Sym)

structure Graph (Sym : Type) where
  edges : List (Edge Sym)
  levels : List (Level Sym)
  log : List (Entry Sym)
```

(`Level`, `Color`, and `Entry` are defined in sections
7, 9, and 8 respectively; the Lean development orders
the definitions so each is defined before use. The
three fields are the whole graph. There is no node
list and no separate edge list of pairs anywhere in
the model.)

### 5.2 Validity invariants

A graph is valid when all of the following hold. These
invariants are part of the definition of the model:
a value violating one is not a graph of this program,
and the rebuild must carry them as a validity predicate
proved of the empty graph and preserved by every
operation of section 8.

1. Every edge's term list is nonempty.
2. Every edge's term list has no repeated member, read
   by spelling equality: a term occurs once in its
   edge.
3. Distinct edges are term disjoint: no term, by
   spelling, is a member of two edges. (Two edges with
   the same term set would share every term, so this
   also forbids duplicate edges.)
4. Every edge's color list has no repeated member
   (section 9 gives color equality).
5. Every level recorded in the graph has all of its
   terms collected in the graph (section 7), and every
   term of a level satisfies that level's scope.
6. Exactness: the edges are exactly the equivalence
   classes generated by the log — every pair of terms
   in one edge is joined by a chain of equivalence
   entries in the log (section 8), and every pair so
   joined is in one edge. The log therefore determines
   the edges, and the edges are a derived reading of
   the log as much as the log is a record of the edges;
   neither may drift from the other, by this invariant.

A term is collected in a graph when it is a member of
some edge's term list. The collected terms of a valid
graph are partitioned by its edges: each collected term
is in exactly one edge.

### 5.3 The empty graph

The empty graph — no edges, no levels, an empty log —
is valid, and is the start of every construction. Every
graph of the program is reached from it by the
operations of section 8 alone.

## 6. Equivalence

Equivalence is a relation on collected terms, defined
by the graph and by nothing else:

```
def same (graph : Graph Sym) (left right : Term Sym) : Prop :=
  ∃ edge ∈ graph.edges, left ∈ edge.terms ∧ right ∈ edge.terms
```

Two terms are equivalent in a graph exactly when they
stand in one edge together. The rebuild must prove, for
every valid graph: equivalence is reflexive on collected
terms, symmetric, and transitive — transitivity is
exactly invariant 3 of section 5 read the other way,
since a term shared by two edges would break the
partition. A term equivalent to a member of an edge is
in that edge: edges are maximal, total classes, not
samples of classes. This is the total in total
equivalence graph: every collected term is in exactly
one class, and the class is the whole edge.

Equivalence is asserted only by an equivalence entry
appended to the log (section 8), and an equivalence
entry is admitted only on a witness: a proof, a
derivation in a derived view (section 12), or a
measurement at a named pin, recorded in the entry.
Equivalence is never asserted from spelling (distinct
spellings in one edge are the point of the model),
never from an identifier, and never from a hash.

## 7. Projection surface

This section is the surface the follow-on resolution
algorithm spec projects onto. It defines levels, the
bound, the view, and reconciliation, exactly, and it
specifies no algorithm: how a resolver chooses its
order, spends its compute, or schedules its work is
that later spec's business, in the relevant proof repo.
What is fixed here is what its inputs and outputs are,
as values of this model, and the properties every such
algorithm's output must satisfy to be an output of this
model at all. The follow-on lane cites this section; it
does not redefine any part of it.

### 7.1 Resolution levels

A level is a named, finite resolved set, with the scope
it was resolved under:

```
structure Level (Sym : Type) where
  name : Sym
  terms : List (Term Sym)
  scope : Term Sym → Bool
```

In words. The name is a symbol: levels are named inside
the model, at symbol grain, not by external labels. The
term list is the finite set resolved at that level,
duplicate free by spelling. The scope is one of the
scopes of section 3 (or a later appended predicate of
the same form), and every term of the level satisfies
it — invariant 5 of section 5.

A level is a value, not a graph. Two levels with
different names, different scopes, or different grains
of reading are two values that will both be appended
to the one graph (section 7.4). A coarser reading and a
finer reading of the same behavior are two levels whose
term lists differ: the finer level's terms include
parts (section 2) of the coarser level's terms, resolved
further toward the symbol. The link between a coarser
term and its finer parts is syntactic — the parts
function of the grammar — plus the presence of both in
the one graph. No mapping table, translation graph, or
pairing structure between levels exists in the model.

The refinement order on levels, in a graph: one level
refines another when every term of the coarser level is
either equivalent in the graph to a term of the finer
level, or has a chain of parts, each step collected in
the graph, ending in terms of the finer level. This
order is a derived reading of the one graph; it is not
a second lattice, and it orders levels, never graphs.

### 7.2 The finite resolved upper bound

The bound of a level in a graph is taken only through
the lattice of section 4, in exactly these steps:

1. Form the state of the level: its term list as a
   state.
2. Take the join, in the lattice, of the singleton
   states of its terms. By the join laws that join is
   the level's own state; the step is stated so that no
   other route to a bound exists — a bound is a lattice
   join of singletons, or it is not a bound of this
   model.
3. Saturate under the graph's equivalence: the bound is
   the state of all terms equivalent in the graph to a
   member of the level's state — that is, the union of
   the edges the level's terms stand in. Equality
   saturation here is the frontier home's standing
   notion: the least state containing the level's state
   and closed under the graph's equivalence.

The result is the finite resolved upper bound of that
level, at that resolution time. It is finite because
the level is a finite list and the graph has finitely
many edges (section 4.3). It is an upper bound in the
lattice order: the level's state is below it, and any
state below every edge state it unions is below it —
the rebuild must prove it is the least such saturated
state. Resolution time is the moment of the append that
records the level: the bound taken then is recorded in
that append's log entry as data — the level's term list
and the edge sets it met — and is never recomputed,
restated, or revised later. A later, larger graph has
later bounds, appended the same way; earlier bounds
stand as the record of what was resolved at their time.

Nothing is resolved beyond the bound at its time.
A claim about terms outside a level's bound is a claim
about unresolved terms, and its state is unmeasured
(section 3.2, rule 4).

### 7.3 The view

A projection, in this model, is a view: a derived
value, never a graph. The view of a graph at a level is
the list of the graph's edges that meet the level's
bound, each edge whole — all of its terms, all of its
colors:

The bound itself is a function of the graph and the
level, returning the bound state as a term list — the
union, in list form, of the edges the level's terms
stand in:

```
def bound (graph : Graph Sym) (level : Level Sym) :
    List (Term Sym) :=
  (graph.edges.filter (fun edge =>
    edge.terms.any (fun term => term ∈ level.terms)))
    |>.flatMap (fun edge => edge.terms)
```

```
def view (graph : Graph Sym) (level : Level Sym) :
    List (Edge Sym) :=
  graph.edges.filter (fun edge =>
    edge.terms.any (fun term => term ∈ bound graph level))
``` A view
is determined by the graph and the level alone. Under
growth of the graph (section 8), a view grows in the
exact sense of the growth rules: every edge of the old
view is a subset, in terms and in colors, of exactly
one edge of the new view. A view is materialized only
as an index or a reading; it is reproducible from the
graph, and it is never stored as a second graph, never
edited, and never fed back as evidence about its own
members — the standing source of truth rule, taken
from the frontier home: the hypergraph is the source
of truth, and every view is derived from it.

### 7.4 Reconciliation on the same graph

Mismatched resolution levels are reconciled on the
same graph, by append, in exactly this sense:

1. Each level is appended to the one graph by the
   operations of section 8: its terms are admitted, its
   equivalence entries are appended, its level record
   is appended. There is no step at which two levels
   exist as two graphs awaiting a merge.
2. A term collected under two levels — by spelling, or
   joined by an equivalence entry — stands in exactly
   one edge, by invariant 3. Reconciliation of shared
   terms is therefore not an operation: it is the
   partition invariant, holding at every moment.
3. A coarser term and its finer parts are both
   collected, as themselves. Neither is rewritten into
   the other. Their relation is read off by the
   refinement order of section 7.1 whenever a proof or
   a view needs it.
4. The reconciled state after appending two levels, in
   either order, satisfies: both levels are recorded,
   both bounds are recorded as taken at their append
   times, the growth relation of section 8 holds from
   the state before either append to the state after
   both, and the final edges are exactly the classes
   generated by the final log (invariant 6). Order of
   appends may change the log's order; it may not
   change the final partition, the final color sets, or
   any recorded bound — the rebuild must prove that
   order independence for the append operations, up to
   state equivalence of the edge list.

## 8. Append only growth, and the exclusion of drift

### 8.1 The log and its entries

The log is the append only record of resolved
information. An entry is one resolved fact, appended
once, never edited and never removed:

```
structure Entry (Sym : Type) where
  kind : Sym
  terms : List (Term Sym)
  level : Sym
  witness : Sym
```

The kind names what was resolved, as a symbol: the
admission of a term, an equivalence of two terms, the
recording of a level, the painting of a color (section
9) — the four kinds are named by four symbols fixed in
the development's first file, and a fifth kind is added
only by a spec change. The terms are the terms the fact
is about. The level is the name of the level at which
it was resolved (the empty name — a symbol the
development fixes for level free facts, such as a proof
conducted at the foundation scope — is stated in the
development, not improvised per entry). The witness
names the ground: a proof, a measurement at a pin, or a
derivation, by a symbol the program's records resolve
to that ground. The epoch of an entry is its position
in the log: the count of entries before it. Epochs are
therefore natural numbers, strictly growing, and free —
no epoch counter is stored or maintained apart from
the log itself.

### 8.2 The only operations

Every graph of the program is built from the empty
graph by these operations, and by no others. Each is a
total function on valid graphs, stated here by its
effect; the rebuild must define each, and prove of each
that it preserves validity (section 5.2) and satisfies
the growth relation (section 8.3).

1. Admit a term, at a level. If the term is already
   collected, the edges do not change. If not, a new
   edge is appended holding exactly that term and no
   colors. Either way, an admission entry is appended
   to the log.
2. Join two terms (assert their equivalence, on a
   witness). Both terms are admitted first, by operation
   1 in the same step if needed. If they already stand
   in one edge, the edges do not change. If they stand
   in two edges, those two edges are replaced by one
   edge whose term list is the two term lists joined
   (duplicate free, by the partition invariant) and
   whose color list is the union of the two color
   lists, up to membership. An equivalence entry is
   appended either way.
3. Record a level. The level's terms are admitted
   first, by operation 1 in the same step if needed;
   the level value is appended to the level list if a
   level of its name is not already recorded with the
   same terms and scope — if one is, the recording is a
   repeat witnessing (section 11) and only the log
   entry is appended. The bound of the level, taken as
   in section 7.2 at this moment, is recorded in the
   entry.
4. Paint a color, on the edge holding a named term
   (section 9). The term must be collected. The color
   is appended to that edge's color list if not already
   present. A painting entry is appended either way.

Replacement in operation 2 is the one place the edge
list changes shape, and it is growth, not revision:
the two edges' terms and colors are all carried into
the one edge, nothing is dropped, and the equivalence
that held inside each part still holds. Edges only
grow and merge. They never split, because no operation
splits one, and equivalence entries are never removed.

### 8.3 The growth relation, and drift

One graph grows to another when: the first graph's log
is a prefix of the second's; every level of the first
is recorded in the second with the same terms and
scope; every term collected in the first is collected
in the second; every pair equivalent in the first is
equivalent in the second; and every color on an edge of
the first is a color on the second's edge holding those
terms. The rebuild must prove the growth relation is
reflexive and transitive, and that each operation of
section 8.2 satisfies it from its input to its output.

Drift is any change in collected information that is
not growth: a term lost, an equivalence lost, an edge
split, a color lost, a level record altered, a bound
recomputed to a different value, a log entry edited or
dropped. Drift is excluded by construction, in the
plain sense that the model's only operations are the
four above, each proved to satisfy growth, and a graph
is by definition (section 5.3) a value reachable by
those operations from the empty graph. There is no
operation in the model whose output drifts from its
input, and no other route to a graph value. That is
the whole mechanism; the spec adds no drift detector,
no reconciliation pass, and no repair step, because
the construction leaves nothing to detect.

Persistence is in all respects of the collected
information: terms, equivalences, levels, bounds,
colors, and the log itself all persist under growth,
by the growth relation's clauses, each named above.

## 9. Colorings and qualifications

### 9.1 Colors

A color is one painted fact on an edge:

```
structure Color (Sym : Type) where
  who : Sym
  kind : Sym
  mark : Sym
  epoch : Nat
```

The painter is a symbol naming who or what paints: a
qualification, a proof, an intent, a measurement. The
kind is a symbol naming the coloring scheme — the
qualification scheme of section 9.2 is one kind; a
proof's scheme is another; kinds are added by appending
their definitions, never by overloading an existing
kind. The mark is the verdict, a symbol of the scheme's
own vocabulary. The epoch is the epoch (section 8.1)
at which the color was painted. Color equality is
equality of all four fields, so the same painter may
paint the same mark again at a later epoch as a new
fact, and may never repaint the past.

Choice taken: the color vocabulary is symbol valued,
not a fixed inductive type, because colorings across
proofs, across qualifications, and across intent are an
open family; a closed enum would force every new scheme
to masquerade as an old one. The one scheme whose marks
are fixed by this spec is the qualification scheme,
next.

### 9.2 Qualifications

A qualification is a named, finite thing: it names its
software, its criteria, and the behavior intended under
them. In this model a qualification is a painter whose
kind is the qualification kind, and whose marks are
exactly the frontier home's four, taken from its paint
at `cdeae4ad`:

- intended: the edge's terms are both observed and
  wanted under the qualification.
- stray: observed, not wanted.
- gap: wanted, not observed.
- unknown: no reading — neither observation nor intent
  speaks, or a reading is missing.

The two filters are never conflated (frontier home,
standing rule): the observed filter (what an
environment makes visible) and the qualified filter
(what is both intended and observed) are distinct
colorings, painted as distinct entries — observation
paints its own kind, intent paints its own kind, and
the qualification mark is derived from the two and
painted as its own entry, naming both in its witness.
No result may trade one filter for the other, and no
mark of intended is ever painted from observation
alone or from intent alone.

A qualification is applied to the graph in exactly the
two ways the ruling names:

1. Appended: the qualification resolves new terms, new
   equivalences, or a new level, by the operations of
   section 8.2, painted with its colors as it goes.
2. Colored in: the qualification paints colors on
   edges already collected — on the same edge, or the
   same set of edges, that other qualifications have
   painted. Painting never alters terms, equivalences,
   levels, or bounds.

Overlapping qualifications therefore coexist on one
edge as distinct color entries, differing in painter,
epoch, or mark. There is no single color of an edge,
no priority among painters, and no overwriting:
composition of qualifications on an edge is union of
its color list, up to membership — commutative,
associative, and idempotent, as a join in the lattice
spirit of section 4, over color lists. The rebuild
must prove those three laws for color union on an
edge, and that painting by one qualification never
removes, alters, or shadows a color of another.

### 9.3 Composition across proofs

A proof in this program is a construction over the one
graph whose outputs are exactly: equivalence entries
it appends on its own witness, colors it paints under
its own painter name, and levels it records. A proof
has no private graph, no private equivalence, and no
private coloring. Composition of proofs is therefore
precise by construction: the composed state is the
graph grown by both proofs' appends, in either order,
with the order independence of section 7.4 clause 4
covering the pair, and every conclusion of each proof
— stated, as all conclusions must be, as a fact about
equivalence, bounds, colors, or excess in the graph it
was proved in — carried forward by the growth relation
to every later graph. A conclusion that cannot be so
carried is not a conclusion of this program's proofs;
it is a statement about a view, and must be labeled
with its view (section 7.3) wherever it is stated.

## 10. Redundancy, restated on this model

Redundancy is a property of equivalence classes, at
symbolic resolution:

- A term is redundant in a graph when its edge holds
  at least one other term, distinct from it by
  spelling. The two terms are equivalent, both are
  collected, and each stands for the other: the compute
  the second expression represents is already
  represented by the first, at the minimum resolution,
  in the same graph.
- The excess of a graph is the count of collected terms
  minus the count of edges: the sum, over edges, of
  the edge's size minus one. Excess is a natural
  number, defined from the graph alone, with no list
  order in it: the term lists are read as sets, up to
  membership, and the rebuild must prove excess is
  unchanged by any re-listing of an edge's terms or of
  the edge list.

```
def excess (graph : Graph Sym) : Nat :=
  (graph.edges.map (fun edge => edge.terms.length)).sum
    - graph.edges.length
```

- A graph is witnessed redundant when its excess is at
  least one. The rebuild must prove the witness form:
  excess is at least one exactly when some edge holds
  two distinct terms — an explicit pair of distinct
  equivalent expressions is the witness, and every
  witness is such a pair.

Choice taken, and marked because the old model decided
the other way: re-collecting the same term, by
spelling, is not redundancy. A repeat admission appends
provenance (a log entry, a repeat witnessing in the
registry of section 11) and changes no edge. Redundancy
requires two distinct expressions in one class.
Duplication of files, of records, or of occurrences
may be evidence that leads a measurement to an
equivalence witness; it is not itself redundancy in
this model, and no count of duplicates is an excess.

## 11. Registry and epochs — the coloring obligations

These are the coloring obligations of the original
brief, restated on this model. They concern a registry
that accompanies the one graph; the registry is not a
second graph and holds no terms of its own.

### 11.1 Configurations

A configuration is a finite witnessed state of the
graph at a bound: the view (section 7.3) of the graph
at a recorded level, taken up to equivalence of views —
two views are the same configuration when they have
the same edges up to membership, edge by edge the same
terms up to membership and the same colors up to
membership. A configuration is therefore at symbolic
resolution by construction: its edges hold terms, its
terms resolve to symbols.

### 11.2 The registry

The registry is an append only list of entries, one
per unique witnessed configuration. An entry holds:
the configuration, its provenance (the list of
witnesses — graphs pins, levels, and epochs — at which
that configuration was witnessed), and its colors
under section 11.3, as a list of epoch and score pairs.

Uniqueness is by content, up to the configuration
equivalence above. Choice taken: identity of a
configuration is that equivalence, not a digest; a
hash or digest is an implementation index, reproducible
from the content, and is never the identity in the
model. Appending a witnessing of a configuration
already in the registry appends the new provenance to
that entry and nothing else — no second entry, and no
change to its recorded colors. Appending a new
configuration appends a new entry. No entry is edited
in any other way, and none is removed. The rebuild
must prove: the registry after any appends has exactly
one entry per configuration equivalence class ever
appended, and each entry's provenance is exactly the
list of its witnessings, in append order.

### 11.3 Deterministic coloring, and reweighting by epochs

A coloring scheme for the registry is a weights
record: a finite list of pairs of a measure name and a
natural weight, over a fixed measure list. The
measures are functions of configuration content alone,
fixed by this spec to these five, each a natural
number read off the view: the term count, the edge
count, the excess (section 10, of the view's edges read
as a graph fragment — terms in the view minus edges in
the view), the colored edge count (edges holding at
least one color), and the distinct symbol count (the
union of the symbols of the view's terms, up to
membership). A scheme's score of a configuration is
the sum, over the measure list, of weight times
measure. The color of a configuration under a scheme
is that score.

Determinism is by construction and must be proved as
such: the score is a function of the configuration's
content and the scheme, so two witnessings of one
configuration under one scheme have the same color,
and the registry's recorded color is that value.

An epoch of the registry is one appended weights
record. Epochs form an append only list, numbered from
zero in append order; epoch zero is the founding
scheme, recorded with the registry's founding. A
reweighting is exactly the append of a new epoch: it
edits no prior epoch, recolors no entry under any
prior epoch, and removes nothing. An entry's colors
grow by append: when a configuration is witnessed
under a new epoch, the pair of that epoch and its
score under it is appended to the entry's color list;
pairs under earlier epochs stand. The current color of
an entry is its latest epoch pair, and current is a
reading, not a stored field that could drift from the
list.

A weighting is never an upper bound (frontier home,
standing rule, restated for this registry): no scheme,
epoch, or score may exclude a configuration from the
registry, prune a term from a view, or tighten a bound
of section 7. A change that alters which configurations
exist is not a reweighting; it is a change of
qualification, governed by section 9. A scheme is
adopted over its predecessor only on a stated metric,
measured on a named instance set, with the adoption
recorded as an epoch entry naming the metric, the set,
and both schemes: campaign discipline, recorded here
as a rule of the registry, not as a theorem.

## 12. Derived views — what is not an edge

Everything else the family speaks of is constructed
from the one graph as a derived view, in the frontier
home's sense: reproducible from the graph, labeled as
derived wherever it is produced, and never a second
source of truth. In particular:

- A dependency graph: a projection of derived steps
  (below) — it scopes what might be affected and never
  turns a joint premise into independent evidence.
- An incidence view: any listing of terms against
  edges is the membership reading of section 5, derived
  by inspection of the edge lists. There is no
  incidence list in the model and no count over one.
- Recorded steps and derivability, in the persistence
  home's sense at `eb01cf2e` and the bidirectional
  home's sense at `b14fc92b`: a step — a premise list
  and a conclusion — is a derived object whose terms
  are members of edges of the one graph, recorded as a
  color or as a level's content under the scheme that
  owns it, never as an edge of the graph. Derivability
  is the closure reading over such steps, and its
  standing facts are restated over the graph: monotone
  in the collected terms and in the recorded steps, and
  the elimination fact — adjoining a term already
  derivable changes the derivable reading not at all.
  The rebuild states these in its derived view layer
  and proves them there; it does not import the homes'
  premise-and-conclusion graphs as graphs.
- The frontier of a qualification: the nondominated
  set of the qualified view, under the frontier home's
  contract axes, its two filters kept distinct per
  section 9.2, and its bounds taken per section 7.2.
  The frontier is a view of a view and is labeled so.

## 13. Claims to re-prove, and controls

Each claim below is proposed semantics: an exact
statement in the language of sections 2 to 11, which
the rebuild must prove from those definitions, under
the family gate, before any of it is called verified.
Names in this section are plain words; the development
gives each claim a single word name of its own.

- Claim one, monotonicity under expansion. Under the
  growth relation: every pair equivalent stays
  equivalent (by definition of growth, proved of the
  operations), witnessed redundancy persists (excess at
  least one stays at least one), and excess never
  decreases. The last clause is the theorem: admit
  changes excess by zero (a new singleton edge adds one
  term and one edge; a repeat admission adds neither);
  join changes excess by exactly one when it merges
  two edges, and by zero when its terms already stand
  together; paint and record change it by zero. Excess
  of a grown graph is therefore the sum of the join
  deltas along its log — proved by induction on the
  log.
- Claim two, compounding. For two appends made to a
  common graph, in either order: the excess of the
  state after both is at least the excess after each
  one alone; it is exactly the excess of the common
  graph plus the count of effective joins in the two
  appends together, where an effective join is a join
  operation that merges two edges at its moment; and a
  join that is effective only in the combined appends —
  its two terms arriving one from each append — is
  counted exactly once. Compounding on this model is
  accumulation of effective joins, no more and no less:
  there is no additive claim over shared content,
  because shared content is collected once (section
  10, choice taken), and the rebuild must not state
  one.
- Claim three, appearance. If two appends to a common
  graph each leave excess at the common graph's excess,
  and an equivalence is then appended joining a term of
  the first append to a distinct term of the second,
  the resulting excess is at least one above the common
  graph's. And the control direction: with no cross
  join — no appended equivalence, and no shared term,
  joining content of the two appends — the combined
  excess is exactly the sum of the two appends' deltas
  over the common graph, each computed alone.
- Claim four, coloring. Color union on an edge is
  commutative, associative, and idempotent up to
  membership; painting preserves every existing color;
  a qualification mark of intended is present only
  where both an observation entry and an intent entry
  for that qualification are present (the two filter
  rule, as a theorem about the derived mark, with the
  painting discipline of section 9.2 as its premise
  stated in the development).
- Claim five, bounds. The bound of a level (section
  7.2) is a state of the one lattice; it is the least
  saturated state above the level's state; it is
  finite; under growth, the bound state of a fixed
  level, recomputed as a reading, only grows — while
  the recorded bound in the log never changes (both
  halves stated and proved; they are about different
  objects, the reading and the record, and the
  development must keep the two apart by name).
- Claim six, reconciliation. Appending two levels to a
  graph, in either order, yields graphs whose edge
  partitions and color sets agree up to state
  equivalence, whose recorded bounds are the bounds as
  taken at their append times, and which both satisfy
  growth from the starting graph (section 7.4).
- Claim seven, scope. Widening scope changes no
  existing edge except by growth: if a graph is built
  under a narrower scope and resolution then continues
  under a wider one, the growth relation holds across
  the widening, every term resolved under the narrower
  scope is collected with the same spelling, and any
  edge it stands in afterward is a growth of its edge
  before.
- Claim eight, registry. The uniqueness, provenance,
  determinism, and epoch clauses of section 11, each as
  stated there.

Standing controls the rebuild must carry, each a
proved statement over concrete data in its tree:

- Control zero: a valid graph with excess zero and at
  least one edge exists (all edges singleton). No
  universal redundancy claim is stated anywhere.
- Control split: there is no operation sequence from a
  graph whose excess is at least one to a graph growing
  from it with smaller excess — stated as: growth from
  a witnessed redundant graph is witnessed redundant
  (claim one), and the control exhibits the concrete
  instance.
- Control free: two appends with no cross join and no
  shared term do not produce appearance (claim three,
  control direction, on a concrete instance).
- Control order: two spellings differing only in
  argument order stand in distinct edges in a concrete
  graph until an equivalence entry joins them — the
  model does not silently identify them (section 2.2).
- Control filter: on a concrete graph, an edge painted
  observed only carries no intended mark, and an edge
  painted wanted only carries none either (section
  9.2).

Premise labels the rebuild inherits, stated now so
they are never discovered later: witness honesty (an
equivalence entry's witness is what it names — a proof
checked by the gate, a measurement at its pin; the
development proves everything from the entries and
cannot prove an entry honest); and reading fidelity
(a subject's symbol type and term readings are the
subject's own — the model proves facts about the terms
as read, not about the behavior they were read from).
Both bind where the model is applied, not what its
theorems say.

## 14. Choices taken, collected

1. Symbols are an abstract parameter type with decidable
   equality, never numbers or identifiers (section 2.1).
2. The ruling's lattice is the family's join semilattice
   of states up to membership; no meet is defined
   (section 4.2).
3. The stored form of the graph is its edges, levels,
   and log, with exactness (invariant 6) binding edges
   to the log; equivalence is co-membership in an edge
   (sections 5 and 6).
4. The link between resolution levels is the syntactic
   parts function plus co-presence in the one graph; no
   mapping structure between levels exists (section
   7.1).
5. A bound is recorded as data at its append time and
   never recomputed; the growing recomputed reading is
   a separate, differently named object (sections 7.2
   and 13, claim five).
6. Color vocabulary is symbol valued and open; only the
   qualification scheme's four marks are fixed (section
   9.1).
7. Steps and derivability are derived views, never
   edges (section 12).
8. Redundancy requires two distinct spellings in one
   edge; repeat collection of one spelling is provenance,
   not redundancy (section 10).
9. Configuration identity is content equivalence, not a
   digest (section 11.2).
10. Compounding is stated as accumulation of effective
    joins, not as additivity over parts; no additive
    form is claimed (section 13, claim two).

Not decided here, with owners: the name and home of
the new repo (coordinator; the disposition beside this
spec recommends a new family repo and gives reasons);
the four kind symbols and the level free name symbol
of section 8.1 (the rebuild's first file, fixed there
and then frozen); the resolution algorithm itself —
its order, its compute spending, its handling of
arbitrary compute availability over all changes that
can provably be resolved (the follow-on lane, specified
separately in the relevant proof repo, projecting onto
section 7 of this spec and onto no other surface).
