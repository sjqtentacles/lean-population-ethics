// Arrhenius's sixth impossibility theorem: a machine-checked counterexample.
// Build: typst compile paper/sixth-theorem.typ

#let author = "Allen Sarkisyan"
#let affiliation = ""  // optional: affiliation or contact line
#let repo = link("https://github.com/sjqtentacles/lean-population-ethics")

#set document(title: "Arrhenius's Sixth Impossibility Theorem Is False as Stated", author: author)
#set page(paper: "a4", margin: (x: 2.6cm, y: 2.6cm), numbering: "1")
#set text(font: "Libertinus Serif", size: 10.5pt, lang: "en")
#set par(justify: true, leading: 0.62em, spacing: 0.9em)
#set heading(numbering: "1.")
#show heading: it => block(above: 1.4em, below: 0.8em, text(size: 11pt, weight: "bold", it))
#set enum(indent: 0.6em)
#set list(indent: 0.6em)
#show link: set text(fill: rgb("#1a4d8f"))

#let pp(n, x) = $#n bracket.l.stroked #x bracket.r.stroked$
#let geq = $succ.curly.eq$
#let gt = $succ.curly$
#let cond(name, body) = block(inset: (left: 1.2em, right: 1.2em), above: 0.8em, below: 0.8em)[
  *#name.* #body
]

#align(center)[
  #text(size: 15pt, weight: "bold")[Arrhenius's Sixth Impossibility Theorem \ Is False as Stated]
  #v(0.5em)
  #text(size: 11pt)[A machine-checked counterexample]
  #v(0.9em)
  #author
  #if affiliation != "" [ \ #text(size: 9.5pt)[#affiliation] ]
  #v(0.3em)
  #text(size: 9.5pt)[25 November 2026]
]

#v(0.8em)
#block(inset: (x: 1.8em))[
  #set text(size: 9.8pt)
  *Abstract.* Arrhenius's sixth impossibility theorem states that no population
  axiology satisfies Egalitarian Dominance, General Non-Extreme Priority,
  Non-Elitism, Weak Non-Sadism and Weak Quality Addition. The published proof is
  known to contain a mistake, and it has been said that the theorem requires a
  stronger form of Weak Quality Addition. No counterexample to the theorem as
  stated has been given for a discrete welfare scale. We give one. There is a
  reflexive, transitive and complete axiology, on a discrete welfare scale, that satisfies all five conditions
  in their published exact formulations. The same axiology satisfies the hypotheses
  of Lemma 1.3 of the published proof and violates its conclusion. Both results are
  formalised in the Lean 4 proof assistant.
]

= Introduction

Gustaf Arrhenius has argued in a series of papers that plausible adequacy
conditions on a theory of the value of populations are jointly unsatisfiable. The
theorem he regards as the strongest, the sixth in the numbering of his book
manuscript, reads #cite(<arrhenius2011>, supplement: [§1.4]):

#cond("The Impossibility Theorem")[
  There is no population axiology which satisfies the Egalitarian Dominance, the
  General Non-Extreme Priority, the Non-Elitism, the Weak Non-Sadism, and the Weak
  Quality Addition Condition.
]

Two things are known about it. First, it depends on the assumption that any two
welfare levels are separated by finitely many small steps; axiologies that deny
this, such as lexical totalism, satisfy all five conditions
@thomas2018 @carlson2022 @thornley2021. Second, the published proof is incorrect.
Thomas's reconstruction finds a mistake and reaches a weaker conclusion than the
one required @thomas2016, and he remarks that, as far as he knows, the premisses
must be slightly strengthened @thomas2018. Thornley, citing Thomas, states the
theorem with the first two quantifiers of Weak Quality Addition exchanged and says
that the theorem requires this stronger condition
#cite(<thornley2021>, supplement: [n. 7]).

These remarks show that the published proof needs the stronger condition. They do
not show that the theorem is false as stated, and the counterexamples cited above
deny small steps. To our knowledge no counterexample on a discrete welfare scale
has been published. @sec-axiology gives one, and @sec-proof locates
the step of the published proof that it falsifies. The counterexample is not
proposed as a plausible axiology; it shows only that the theorem needs a stronger
premise.

= Framework and conditions <sec-conditions>

We follow #cite(<arrhenius2011>, form: "prose", supplement: [§1.2]). Welfare
levels are indexed by the integers, with $0$ neutral, so Discreteness holds. A
population is identified with the finite multiset of its members' welfare levels.
We write $pp(n, x)$ for $n$ lives at level $x$, $X + Y$ for the union of disjoint
populations, $X geq Y$ for "$X$ is at least as good as $Y$", and $X gt Y$ for
$X geq Y$ and not $Y geq X$. A population is _within_ $[a, b]$ if all its members
have welfare between $a$ and $b$. A _welfare range_ $R(a, b)$ consists of the
levels from $a$ to $b$ and contains at least three levels.

The five conditions, in their exact formulations
#cite(<arrhenius2011>, supplement: [§1.3]), are as follows. Weak Quality Addition
has the same form in the earlier publication of the theorem @arrhenius2009.

#cond("Egalitarian Dominance")[
  For any level $x$, any $n > 0$ and any population $B$ of size $n$ whose members
  all have welfare below $x$: $pp(n, x) gt B$.
]
#cond("General Non-Extreme Priority")[
  For any level $z$ there are a level $u$, a range $R(1, y)$ with $u > y$, and
  $n > 0$ such that, for every $x >= u$, every $B$ of size $n$ within $[1, y]$ and
  every population $E$: $pp(n, x) + pp(1, z) + E geq B + pp(1, z + 1) + E$.
]
#cond("Non-Elitism")[
  For any levels $x, y$ with $x - 1 > y$ there is $n > 0$ such that, for every
  population $D$ within $[y, x]$:
  $pp((n + 1), x - 1) + D geq pp(1, x) + pp(n, y) + D$.
]
#cond("Weak Non-Sadism")[
  There are a level $x < 0$ and $n > 0$ such that, for every $y > 0$, every $k$ and
  every population $C$: $pp(k, y) + C geq pp(n, x) + C$.
]
#cond("Weak Quality Addition")[
  For any population $X$ there are a level $x < 0$, ranges $R(u, v)$ and $R(1, y)$
  with $u > y$, and $n, m > 0$ such that, for every $z >= u$ and every population
  $B$ within $[1, y]$: $pp(n, z) + X geq B + pp(m, x) + X$.
]

In Weak Quality Addition the level $x$ and the number $m$ are chosen after $X$ and
may depend on it. The strengthening suggested by the observations of Thomas and
Thornley chooses them first:

#cond("Strong Quality Addition")[
  There are a level $x < 0$ and $m > 0$ such that for any population $X$ there are
  ranges $R(u, v)$ and $R(1, y)$ with $u > y$ and $n > 0$ such that, for every
  $z >= u$ and every population $B$ within $[1, y]$:
  $pp(n, z) + X geq B + pp(m, x) + X$.
]

= The axiology <sec-axiology>

Call a life _excellent_ if its welfare is at least $4$. For a population $X$ let
$E(X)$ be the number of its excellent lives, $S(X)$ the sum of $-w$ over its lives
with negative welfare $w$ (its _suffering_), and $T(X)$ its total welfare. Say that
$X$ is _compensated_ if $S(X) <= E(X)$, and define

$ X geq Y quad "iff" quad & X "is compensated and" Y "is not, or" \
  & X "and" Y "are alike in this respect and" T(X) >= T(Y). $

This orders populations lexically by the pair (compensated or not, total welfare),
so it is reflexive, transitive and complete. Let $d(w) = -w$ for $w < 0$,
$d(w) = 0$ for $0 <= w <= 3$ and $d(w) = -1$ for $w >= 4$, so that $X$ is
compensated exactly when $D(X) = sum_(w in X) d(w) <= 0$. The function $d$ is
non-increasing and falls by at most $1$ between consecutive levels. We use the
following repeatedly.

#cond("Criterion")[
  If $T(X) >= T(Y)$, and $X$ is compensated whenever $Y$ is, then $X geq Y$.
]

#cond("Proposition 1")[
  The ordering $geq$ satisfies Egalitarian Dominance, General Non-Extreme Priority,
  Non-Elitism, Weak Non-Sadism and Weak Quality Addition.
]

_Proof._ _Egalitarian Dominance._ Let $A = pp(n, x)$, so $T(A) > T(B)$. If
$x >= 0$ then $S(A) = 0$ and $A$ is compensated. If $x < 0$ then every member of
$B$ is negative and $B$ is not compensated. Either way $A$ is compensated if $B$
is, so $A geq B$ by the Criterion, and $B geq A$ fails because $T(B) < T(A)$.

_General Non-Extreme Priority._ Take $u = 4$, $y = 3$, $n = 1$, and let $b$ be the
member of $B$. Passing from $B + pp(1, z + 1) + E$ to $pp(1, x) + pp(1, z) + E$
changes $D$ by $d(x) - d(b) + d(z) - d(z + 1) = -1 + d(z) - d(z + 1) <= 0$ and $T$
by $x - b - 1 >= 0$.

_Non-Elitism._ Take $n = 1$. The total changes by $x - 2 - y >= 0$. If $y >= 0$,
no life on either side is negative and both sides are compensated. If $y < 0$,
then $2 d(x - 1) <= d(x) + d(y)$, by cases on whether $x <= 0$, $0 < x < 4$,
$x = 4$ or $x > 4$, so $D$ does not increase.

_Weak Non-Sadism._ Take $x = -1$, $n = 1$. Then
$D(pp(k, y) + C) <= D(C) < D(pp(1, -1) + C)$ and
$T(pp(k, y) + C) >= T(C) > T(pp(1, -1) + C)$.

_Weak Quality Addition._ Given $X$, take $x = -1$, $u = 4$, $v = 6$, $y = 3$,
$n = S(X) + 1$ and $m = E(X) + 1$. For $z >= 4$, the population $pp(n, z) + X$ has
suffering $S(X)$ and $E(X) + n$ excellent lives, so it is compensated. For $B$
within $[1, 3]$, the population $B + pp(m, -1) + X$ has suffering
$S(X) + m > E(X)$ and $E(X)$ excellent lives, so it is not. #h(1fr) $square$

The number $m = E(X) + 1$ grows with the number of excellent lives in $X$. No
single choice works for every $X$:

#cond("Proposition 2")[
  The ordering $geq$ violates Strong Quality Addition.
]

_Proof._ Fix $x < 0$ and $m > 0$, and let $X = pp((-m x), 4)$. For any
$u > y >= 3$ and $n > 0$, both $pp(n, u) + X$ and $pp(N, 3) + pp(m, x) + X$ are
compensated, and the second has the greater total once $3N > n u - m x$.
#h(1fr) $square$

= Where the published proof fails <sec-proof>

The published proof derives two auxiliary conditions, β and δ, from Non-Elitism and
General Non-Extreme Priority. Its Lemma 1.3 states that Weak Quality Addition and
Condition δ imply Restricted Quality Addition, and its Lemma 1.4 derives a
contradiction from Restricted Quality Addition, β, δ, Egalitarian Dominance and
Weak Non-Sadism.

#cond("Condition δ")[
  For any $z < 0$ and $m > 0$ there are a level $u$, a range $R(1, y)$ with
  $u > y$, and $n > 0$ such that, for every $x >= u$, every $B$ of size $n$ within
  $[1, y]$ and every population $E$:
  $pp(n, x) + pp(m, z) + E geq B + pp(m, 3) + E$.
]
#cond("Restricted Quality Addition")[
  For any population $X$ there are a level $x$, a range $R(1, y)$ with $x > y$, and
  sizes $n, m$ such that, for every $z >= x$ and every $B$ within $[1, y]$ of size
  at least $m$: $pp(n, z) + X geq B + X$.
]

#cond("Proposition 3")[
  The ordering $geq$ satisfies Weak Quality Addition and Condition δ and violates
  Restricted Quality Addition. Hence Lemma 1.3 is false.
]

_Proof._ For Condition δ take $u = 4$, $y = 3$ and $n = m(3 - z)$. The $n$
excellent lives outnumber the suffering $-m z$ of the lives at $z$, and the total
changes by at least $n - m(3 - z) = 0$. Restricted Quality Addition fails at
$X = emptyset$: populations of lives at positive levels are all compensated, so
$pp(n, x) geq pp(N, 1)$ requires $n x >= N$, which fails for large $N$.
#h(1fr) $square$

The step that fails is line (12) of the proof of Lemma 1.3. The proof fixes $X$,
takes a negative level $z$ and sizes $p$, $m$ that satisfy Weak Quality Addition
for $X$, takes $n$ from Condition δ for $z$ and $m$, and asserts that
$A_1 + A_2 + X geq A_1 + B_2 + C + X$ follows from Weak Quality Addition. Here
$A_1$ and $A_2$ consist of $n$ and $p$ lives at a high level, $C$ of $m$ lives at
$z$, and $B_2$ of any number of lives in a low positive range. This comparison has
background $A_1 + X$, not $X$, and the witnesses for $A_1 + X$ may differ from
those for $X$.

In our ordering they do differ, because the lives in $A_1$ are excellent. Take
$X = emptyset$. The witnesses in the proof of Proposition 1 are $z = -1$ and
$p = m = 1$, and those in the proof of Proposition 3 are $n = 4$ at level $4$. With
$B_2 = pp(2, 3)$, line (12) asserts
$pp(5, 4) geq pp(4, 4) + pp(2, 3) + pp(1, -1)$. Both populations are compensated,
and their totals are $20$ and $21$.

Strong Quality Addition fixes $z$ and $m$ before the background, which removes
this dependence. We have not checked whether the rest of the published proof then
goes through, nor verified the strengthened versions of the theorem in
#cite(<thomas2016>, form: "prose") and #cite(<thornley2021>, form: "prose"), which
are stated with fixed thresholds for very high and very low welfare. By
Proposition 2 our ordering is not a counterexample to a theorem with the stronger
premise. The two premises differ in substance: Weak Quality Addition lets the
amount of added suffering grow with the background population, and Strong Quality
Addition demands one amount that works against every background.

= Formalisation <sec-lean>

Propositions 1 to 3 and the instance of line (12) are formalised in Lean 4 with
Mathlib @lean4 @mathlib, in `PopEthics/SixthTheorem.lean` of the accompanying
repository (#repo), as the theorems `sixth_theorem_fails_as_stated`,
`lex_not_strongQualityAddition`, `lemma_1_3_fails` and `line_12_fails`. The file
also proves that total utilitarianism violates Weak Quality Addition as formalised,
so the formal condition is not vacuous. The proofs use only Lean's three standard
axioms.

Lean establishes that the formal statements are proved, not that they say what the
published conditions say. The formal conditions are a few lines each and are
meant to be compared with
#cite(<arrhenius2011>, form: "prose", supplement: [pp. 8–9]). Where the published
wording leaves a choice we took the reading that is harder to satisfy: populations
within a range may mix levels, background populations may be empty, Weak
Non-Sadism requires $n > 0$, and in Weak Quality Addition the high-welfare
population may lie at any level $z >= u$. There is one exception. Egalitarian
Dominance is restricted to non-empty populations, since the published wording at
$n = 0$ would require the empty population to be better than itself. Arrhenius
allows welfare levels to be partially ordered; we treat the totally ordered case,
which his framework includes. Independently of Lean, the script
`search/check_sixth_theorem.py` codes the conditions from the published wording
and tests them exhaustively on small populations; apart from that empty case it
finds no violation.

#v(0.6em)
#text(size: 9.5pt)[
  *Statement on the use of AI.* The counterexample, the Lean formalisation and the
  first draft of this note were produced with an AI system (Claude, by Anthropic)
  working under the author's direction. The author takes responsibility for the
  contents.

  © 2026 Allen Sarkisyan. This note is licensed under CC BY 4.0.
]

#bibliography("refs.yml", title: "References", style: "apa")
