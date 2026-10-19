#import "template.typ": *

#let concat = math.class("normal", sym.bar.v.double)

#set text(font: "Libertinus Sans")
#show strong: it => {
  show emph: e => context text(stroke: 0.025em + text.fill, e)
  it
}

#show: themed_document.with(
  title: "ZK-SNARKs for Dummies",
  author: "Ben Mayer",
  title_align: center,
  sidenotes: true,
  toc: true,
  margins: "compact"
)

This document is an attempt to explain how modern _hash-based multilinear_ ZK-SNARKs work from the ground up, for someone familiar only with basic discrete math.#s[Systems built on _univariate_ polynomials like STARKs and Plonky2 are pretty different under the hood, and will not be covered here.] We'll gradually build up a set of tools, each with just enough motivation to see why we'd want it, and by the end we'll piece them all together into a working proof system. The particular system we'll construct is optimized for understanding rather than performance, but the core ideas should still carry over to fancier schemes that swap out some of the tools for faster/smaller alternatives.#s[E.g. WHIR for commitments, Lasso for lookups, CFW26 for zero-knowledge, etc.]

_If you don't know what a ZK-SNARK is, quickly #link("https://snarkage.substack.com/p/snarks-and-their-broad-use-cases")[read this] first, I won't do much explaining of what they are and why they're useful here._


= Finite fields <fields>

Everything in this document happens in a _finite field_. Informally, a field is a set of numbers where we can add, subtract, multiply and divide (by anything except zero), and all the usual rules of arithmetic hold, e.g. $a(b + c) = a b + a c$.

The fields we'll use are almost all large _prime fields_,#s[Except for _extension fields_, which we'll cover in @extensionfields.] which are basically just the integers modulo some massive prime $p$:

#definition[Prime field][
  For a prime $p$, the field $FF_p$ is the integers ${0, 1, ..., p - 1}$, with addition, subtraction and multiplication all done modulo $p$.

  For example, in $FF_17$: $thick 9 + 10 = 2$, $quad 3 dot 6 = 1$, $quad 2 - 5 = 14$.

  #note[Division works by multiplying by an inverse, e.g. in $FF_17$ since $3 dot 6 = 1$, $6$ is the inverse of $3$ and thus $1\/3 = 6$ and $5\/3 = 5 dot 6 = 13$, etc. Negatives work by wrapping around, e.g. $-1 = 16$ and $-5 = 12$ in $FF_17$.]
]

*Why finite?* Because it means every value fits in a fixed number of bits while arithmetic is still exact. With e.g. rationals our numbers can explode in size over the rounds of our proof, and with floats we get rounding errors and a bunch of other nastiness.#s[Floats technically aren't a field at all, as floating point addition isn't associative.]

*Why a prime?* The integers mod $n$ are only a field when $n$ is prime. Otherwise we end up with non-zero numbers without inverses, which breaks division. Many of our _soundness_ arguments#s[_Soundness_ being the guarantee that, with high probability, a cheating prover can't get a false claim accepted.] rely on the _Schwartz-Zippel lemma_ (more on this soon!), which only applies over fields. There are more exotic finite fields too, but integers mod $p$ are simple and generally performant on commodity CPUs and GPUs.

*Why large?* As we'll see, almost every way a cheating prover can get lucky happens with probability proportional to $1\/abs(FF)$, where $abs(FF)$ is the number of elements in the field (e.g. $abs(FF_p) = p$). Thus we want $abs(FF)$ to be really big, typically at least $2^64$.

The one issue with doing everything in a finite field is that we have to be careful to make sure our inputs and computed values don't wrap around $p$, but we won't worry about that here.

= Tables & Extensions

#definition[Table][

We'll define a table to be a list of $2^ell$ _cells_, all of which are values from the same finite field $FF$. Tables are indexed by $ell$ bits, $x_1,...,x_ell$, where $x_1$ is the low bit, so a table $g$ is a function $g : {0,1}^ell -> FF$.#s[If you're unfamiliar with some of this notation: ${0,1}^ell$ is the set of all lists of $ell$ bits, i.e. ${0,1} times dots.c times {0,1}$ with $ell$ copies, so it has $2^ell$ elements, one per cell. For example: ${0,1}^2 = {(0,0), (1,0), (0,1), (1,1)}$. 

Likewise, $FF^ell$ is the set of all lists of $ell$ field elements. The arrow in $g : A -> B$ just means $g$ takes an input from $A$ and returns a value in $B$.

Fun fact: ${0,1}^ell$ is often called the _boolean hypercube_, since its points are the corners of an $ell$-dimensional cube.
]

Consider the table $c = [1, 5, 3, 9]$, where $ell = 2$. We can read it as a function $c : {0,1}^2 -> FF$ of its input bits (remembering that $x_1$ is the low bit), i.e.:


$ c\(undershell(0, x_1), undershell(0, x_2)\) = 1 quad c(1, 0) = 5 quad c(0, 1) = 3 quad c(1, 1) = 9 $

#note[A table is only defined for 0/1 inputs, i.e. $x_1, ..., x_ell in {0, 1}$, not for arbitrary field elements.]]

Consider the table $a = [1, 5]$, i.e. $a : {0,1} -> FF$. Observe that we can construct a polynomial $tilde(a) : FF -> FF$ such that $tilde(a)(x_1) = a(x_1)$ for $x_1 in {0, 1}$, by simply linearly interpolating between the two values, i.e.:

$ tilde(a)(x_1) = 1 + 4 x_1 $

Let $b = [3, 9]$. Again, we can construct $tilde(b) : FF -> FF$ via linear interpolation of its cells:

$ tilde(b)(x_1) = 3 + 6 x_1 $

Now return to the table $c = [1, 5, 3, 9]$. We can construct $tilde(c) : FF^2 -> FF$ such that $tilde(c)(x_1, x_2) = c(x_1, x_2)$ for $x_1, x_2 in {0, 1}$ as an interpolation between $tilde(a)$ and $tilde(b)$ in $x_2$.

$ tilde(c)(x_1, x_2) &= (1 - x_2) dot tilde(a)(x_1) + x_2 dot tilde(b)(x_1) \
&= (1 - x_2) dot (1 + 4 x_1) + x_2 (3 + 6 x_1) \
&= 1 + 2 x_2 + 4 x_1 + 2 x_2 x_1
$

$tilde(c)$ is a _multilinear_ polynomial, as it has degree at most $1$ in each variable $x_1,...,x_ell$. We can generalize this to arbitrary size tables.

#definition[Multilinear extension of a table][
  For a table $g : {0,1}^ell -> FF$ of any $ell$, we can construct $tilde(g) : FF^ell -> FF$, a polynomial with degree at most one in each variable _(multilinear)_, which equals the table's cell at every 0/1 point.

  $ forall x_1,...,x_ell in {0,1} quad g(x_1, ..., x_ell) = tilde(g)(x_1,..., x_ell) $
]

#theorem[Multilinear extensions are unique][
  If two multilinear polynomials in $ell$ variables agree on every 0/1 input, *they are the same polynomial*.

#proof[See #link("http://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.html")[Thaler, _Proofs, Arguments, and Zero-Knowledge_], Ch. 3.
]
]<mlunique>

#corollary[Different tables always have different extensions][
  If $g, g' : {0,1}^ell -> FF$ are tables with $g != g'$, then $tilde(g) != tilde(g')$.#s[*Proof:* They differ at some 0/1 point, and each extension agrees with its own table there, so the extensions must be different. #QED]
]<diffmultilin>

Multilinear extensions of tables are extremely useful, because *they turn tables into polynomials*, and we can do a lot of cool things with polynomials.

== Identity testing

Say we want to check whether two tables $a, a' : {0,1}^ell -> FF$ are equal.

Turns out, simply drawing a random "challenge" $r in FF^ell$ and evaluating whether $tilde(a)(r) = tilde(a')(r)$ is enough to say with high confidence whether they are equal. If $a = a'$, this will pass 100% of the time. If they are different, it will pass with probability at most $ell\/abs(FF)$.

#theorem[If $a != a'$ then $limits(Pr)_(r in FF^ell) [tilde(a)(r) = tilde(a')(r)] <= ell\/abs(FF)$][
#proof[
  By @diffmultilin, if $a != a'$, $tilde(a) != tilde(a')$, thus $tilde(a) - tilde(a')$ is a non-zero multilinear polynomial. The test passes iff that difference evaluates to $0$ at $r$.

  By the #link("https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma")[_Schwartz-Zippel lemma_], a non-zero polynomial in $ell$ variables of total degree#s[The total degree of a polynomial is the largest sum of exponents in one term. For example, $x_1 x_2$ has total degree 2.] at most $d$ is zero at a uniformly random point $r in FF^ell$ with probability at most $d\/abs(FF)$.

  $tilde(a) - tilde(a')$ is multilinear, so it has total degree at most $ell$.#s[Its largest possible term is $x_1 x_2 x_3 dot dot dot x_ell$.] Thus, the test passes with probability at most $ell\/abs(FF)$.]
]<identitytest>


This is great news because, as discussed in @fields, the field we sample $r$ from is *very large*, typically at least $2^64$. Even for a table with more than a trillion entries (e.g. $ell = 40 => 2^40$ cells), the chance of $tilde(a)(r) = tilde(a')(r)$ holding for random $r$ when $a != a'$ is at most $40 \/ 2^64 approx 2.2 times 10^(-18)$.

=== Extension fields <extensionfields>

Sometimes, even if our field is quite large (e.g. $approx 2^64$), $ell\/abs(FF)$ is too weak of a bound to be secure, for example if this check is one step amongst many and the errors are additive. However, *using a larger field for a table is not free*. A larger field can require using multiple machine words to store each cell, which can drastically decrease efficiency. Thus, we often store tables with cells in a prime field $FF_p$ such that values from that field fit in a single machine word, and then *draw challenges* from a larger _extension field_#s[A larger field that contains $FF_p$. See #link("https://en.wikipedia.org/wiki/Finite_field#Non-prime_fields")[_Finite field_] on Wikipedia for how these are built in general.] $FF$. The Schwartz-Zippel lemma applies unchanged, because a table with cells in $FF_p$ is also a table with cells in $FF$.

#note[Despite the similar name, extension fields have nothing to do with a table's multilinear _extension_. They're completely unrelated concepts, don't mix them up!]

For example, a popular base field is the _Goldilocks field_, $FF_p$ with $p = 2^64 - 2^32 + 1$, whose elements fit in a single 64-bit word. Its _quadratic extension_ $FF_(p^2)$ consists of elements $a + b i$ with $a, b in FF_p$, where $i$ is a new symbol satisfying $i^2 = 7$.#s[This works because $7$ has no square root in $FF_p$, much like how the complex numbers extend the reals with an $i$ satisfying $i^2 = -1$, which has no real square root.] Arithmetic works just like with complex numbers, except $i^2$ becomes $7$, e.g. $(a + b i)(c + d i) = (a c + 7 b d) + (a d + b c) i$. $FF_p$ sits inside $FF_(p^2)$ as the elements with $b = 0$.

This squares the field size to $p^2 approx 2^128$, which matters most for bounds with a big numerator. In @lookups we'll see a soundness bound of $2^ell\/abs(FF)$, which for $ell = 40$ over the Goldilocks field is only $2^(-24) approx "1 in 16 million"$, well within reach of a cheating prover who can retry many times.#s[Which is possible once the protocol is made non-interactive. See @fiatshamir.] Over the extension $FF_(p^2)$, it's $2^(-88)$.

The cost is that extension elements take two words, and multiplying two of them takes three or four base field multiplications. But *only values derived from challenges* (folded tables, round polynomials, claimed evaluations) *live in the extension*. The big tables we commit to stay in $FF_p$, and multiplying one of their cells by an extension challenge takes just two base multiplications, since $c(a + b i) = c a + (c b) i$.

== Folding

We said we could compare tables by evaluating their extensions at a random $r$, but how should we actually compute $tilde(a)(r)$ given some $a$? We could work out all $2^ell$ coefficients of $tilde(a)$, then plug $r$ into every term, but there's a faster way: _folding_.

For example, folding $c = [1, 5, 3, 9]$ by $r_1 = 2$ replaces each adjacent pair of cells (those differing only in $x_1$) with a linear interpolation between them at $2$:

$ c' = [(1 - 2) dot 1 + 2 dot 5, med (1 - 2) dot 3 + 2 dot 9] = [9, 15] $

$c' : {0,1} -> FF$ is an ordinary table with $2$ cells, indexed by the single bit $x_2$. Its cells are values of $tilde(c)$ with $x_1$ fixed to $2$:

$ c'(0) = 9 = tilde(c)(2, 0) quad c'(1) = 15 = tilde(c)(2, 1) $

Folding $c'$ by $r_2 = 3$ leaves a table with a single cell:

$ c'' = [(1 - 3) dot 9 + 3 dot 15] = [27] $

and indeed $tilde(c)(2, 3) = 1 + 2 dot 3 + 4 dot 2 + 2 dot 3 dot 2 = 27$.

#definition[Folding][
  _Folding_ a table $g : {0,1}^ell -> FF$ by some $r in FF$ produces a table $g' : {0,1}^(ell - 1) -> FF$ with $2^(ell - 1)$ cells:

  $ g'(x_2, ..., x_ell) = (1 - r) dot g(0, x_2, ..., x_ell) + r dot g(1, x_2, ..., x_ell) $

  Cell by cell, each adjacent pair $(u, v)$ becomes $u + r(v - u)$.
]

#theorem[Folding fixes a variable of the extension][
  If $g'$ is $g$ folded by $r$, then $tilde(g')(x_2, ..., x_ell) = tilde(g)(r, x_2, ..., x_ell)$ for all $x_2, ..., x_ell in FF$.#s[*Proof:* Both sides are multilinear in $x_2, ..., x_ell$ and agree on 0/1 points, and thus they're equal by @mlunique. #QED]
]<foldfix>

Applying this repeatedly, folding $g$ by $r_1$, then $r_2$, and so on through $r_ell$ leaves a single cell equal to $tilde(g)(r_1, ..., r_ell)$. Each fold halves the table, so this takes fewer than $2^ell$ multiplications in total.#s[If the cells are in $FF_p$ and the challenges are drawn from an extension field $FF$, the cells become elements of $FF$ after the first fold.]

Folding gives us both a way to efficiently evaluate a table's multilinear extension at a specific point and a way to turn a claim about a large table into a claim about a table half its size, which will come in handy later.

== Extensions as weighted sums

As we just saw, folding $g$ by $r_1$, then $r_2$, and so on through $r_ell$ leaves a single cell equal to $tilde(g)(r)$. Each fold only ever combines cells by scaling them by $1 - r_i$ or $r_i$ and adding them up, so that final cell (and thus $tilde(g)(r)$ as well) is just a weighted sum of $g$'s original cells! Each cell's weight is the product of the factors it picked up, one per fold,#s[$1 - r_i$ if its $i$-th bit is $0$ and $r_i$ if it is $1$] and these weights form a table of their own that we'll call the $"eq"$ table:

#definition[The eq table][
  For a point $r = (r_1, ..., r_ell) in FF^ell$, the table $"eq"_r : {0,1}^ell -> FF$ has $2^ell$ cells:

  $ "eq"_r (x_1, ..., x_ell) = product_(i = 1)^ell (r_i x_i + (1 - r_i)(1 - x_i)) $
]<eqtable>

Putting this together:

#theorem[$tilde(g)(r)$ is a weighted sum of $g$][
For any table $g : {0,1}^ell -> FF$ and any $r in FF^ell$, the value $tilde(g)(r)$ is equal to the sum of $g$'s cells, each weighted by the matching cell of $"eq"_r$, i.e.:
  $ tilde(g)(r) = sum_(x_1, ..., x_ell in {0,1}) g(x_1, ..., x_ell) dot "eq"_r (x_1, ..., x_ell) $
]<evalweightedsum>

#figure(
  image("figures/eq_tree.svg", width: 100%),
  caption: [Folding $c = [1, 5, 3, 9]$ by $r = (2, 3)$, and how $"eq"_r$ relates.],
)<fig-eq-tree>

This property, that *evaluating a table's multilinear extension can be expressed as a weighted sum over the underlying table*, will be useful later.

= Commitments <commitments>

Our end goal is a ZK-SNARK. We'll get to the _ZK_ (zero-knowledge) part later, so for now let's focus on the _SNARK_, short for _Succinct Non-Interactive Argument of Knowledge_: a proof system that lets one person (the _prover_) prove to another person (the _verifier_) that a statement is true, with a proof that is small and fast to check, even if the statement is about a very large computation.#s[We'll cover the non-interactive part in @fiatshamir, and ignore it for now.]

When constructing SNARKs, we often end up wanting a system that lets a prover _commit_ to a table, such that *once committed, the prover cannot change any of its cells*, and a verifier can later query/_open_ parts of it and trust that the answers are faithful to the same table the prover committed to. This property is often called _binding_: once the prover has committed to some table $g$, it's stuck with it, and can't open the commitment to values from any other table.

This is useful because we often want the verifier to make some kind of random challenge and test something about a table with it. But that only works if the prover can't change its table on the fly after seeing the challenge. Committing to the table first ensures that.

We ideally want our commitments to be _succinct_, meaning the *commitment and each opening proof are much smaller than the table* and checking an opening is much cheaper than reading the whole table.

#link("https://en.wikipedia.org/wiki/Merkle_tree")[Merkle trees] are one
such succinct commitment scheme. The prover just sends a single hash (the root hash of the tree) to the verifier, then can later _open_ the value of a specific cell by providing its value along with some sibling hashes, which the verifier can easily use to check the claimed cell value is faithful. Each opening costs only a logarithmic number of hashes, so they work great if we only need to access a small number of specific cells.

For our use cases, we'll want a commitment scheme that lets us efficiently open a table's _multilinear extension_ at a specific point, rather than specific cells. Merkle trees on their own can't help us: the evaluation of a multilinear extension is a weighted sum of the whole table, so with a Merkle tree we'd have to open every single cell, which is not efficient/practical. _Polynomial commitment schemes_ solve exactly this. We'll discuss how to actually build them later. For now, we'll treat them as a black box with two steps:

+ *Commit.* The prover sends a short _commitment_ to a table $g$, e.g. a single hash.#s[When we say the prover _commits_ to a table, we mean it sends a commitment.]
+ *Open.* Later, if the prover wishes to show $tilde(g)(r) = v$, it can send $v$ along with a short proof that $tilde(g)(r) = v$, which the verifier checks against the commitment.

Commitments/openings are succinct but not free by any means, so the fewer tables we need to commit to and the fewer openings we have to perform, the better.

= Sum-check

Say we, the _prover_, have some table $g$ and we want to convince some _verifier_ that $sum g = H$. That is, if $g$ has $2^ell$ cells and $H in FF$:

$ sum_(x_1,...,x_ell in {0,1}) g(x_1, ..., x_ell) = H $<sumcheckclaim>

The _sum-check protocol_#s[Lund, Fortnow, Karloff and Nisan (1992)] is an interactive protocol that lets the verifier check the claim using $ell$ rounds of short back-and-forth messages and a single evaluation of $tilde(g)$ at a random point,#s[For example, if the prover has committed to $g$, by opening the commitment at that point.] without ever reading the whole table.

The protocol works in rounds, and each round shrinks the claim from a table to that table folded in half. The key tool is a polynomial the prover sends each round, which we'll call the _round polynomial_. For the current table $g$, it is simply the sum of the cells of $g$ folded by $t$, as a function of $t$:

$ s(t) = sum_(x_2, ..., x_ell in {0,1}) tilde(g)(t, x_2, ..., x_ell) $

Two things make this polynomial useful. First, folding by $0$ or $1$ just picks out half of the table, so together they cover every cell:

$ s(0) + s(1) &= sum_(x_2, ..., x_ell in {0,1}) tilde(g)(0, x_2, ..., x_ell) + sum_(x_2, ..., x_ell in {0,1}) tilde(g)(1, x_2, ..., x_ell) \
&= sum_(x_1, ..., x_ell in {0,1}) tilde(g)(x_1, ..., x_ell) $

which is our original claim @sumcheckclaim. Second, $s$ is just a line: each term $tilde(g)(t, x_2, ..., x_ell)$ has degree at most $1$ in $t$, since $tilde(g)$ is multilinear, and a sum of lines is a line. So the prover can send it as just two numbers.

The prover and verifier start with the claim "$g$ sums to $H$." Each round turns a claim about a table into a claim about that table folded in half. In round $i$:

+ The prover sends the round polynomial $s_i$ of the current table.#s[Since $s_i$ is a line, this is just two field elements, e.g. its two coefficients.]
+ The verifier checks that $s_i (0) + s_i (1)$ equals the current claimed sum, and rejects if not.
+ The verifier picks a random $r_i in FF$ and sends it to the prover.
+ The new claim is that the current table folded by $r_i$ sums to $s_i (r_i)$. The prover folds its table by $r_i$.

After $ell$ rounds, the table has been folded down to a single cell, which should equal $tilde(g)(r_1, ..., r_ell)$. The final claim is that this one cell equals $s_ell (r_ell)$, and the verifier checks it with its single evaluation of $tilde(g)$.


$ H &= sum_(x_1, ..., x_ell in {0,1}) tilde(g)(x_1, x_2, ..., x_ell) &&= s_1(0) + s_1(1) \
s_1(r_1) &= sum_(x_2, ..., x_ell in {0,1}) tilde(g)(r_1, x_2, ..., x_ell) &&= s_2(0) + s_2(1) \
s_2(r_2) &= sum_(x_3, ..., x_ell in {0,1}) tilde(g)(r_1, r_2, x_3, ..., x_ell) &&= s_3(0) + s_3(1) \
&dots.v \
s_(ell-1)(r_(ell-1)) &= sum_(x_ell in {0,1}) tilde(g)(r_1, ..., r_(ell-1), x_ell) &&= s_ell (0) + s_ell (1) \
s_ell (r_ell) &= tilde(g)(r_1, r_2, ..., r_ell) $

*If a prover wants to claim an incorrect sum, how likely is it the verifier fails to catch them?* As it turns out, just as unlikely as passing the identity test from earlier, at most $ell\/abs(FF)$.

#theorem[If $"claim" != sum g$, $Pr["sum-check passes"] <= ell\/abs(FF)$.][


  #proof[
    Imagine the prover is lying about the sum. In round 1, it has to send a round polynomial whose values at $0$ and $1$ add up to its claimed sum, or the verifier's check fails immediately. The true round polynomial adds up to the true sum, so the prover is forced to send a different one.#s[True = what an honest prover would send for $g$ folded by the challenges so far.]

    Both are lines, and two different lines cross at one point or not at all. So at some random $r_1$ from the verifier, the prover's line and the true line almost certainly disagree there. Thus the new claim $s'_1(r_1)$ is _still a lie_, just about a table half the size.

    With high probability, this will keep happening round after round. The prover can't make the lie go away, and just keeps passing it down. After $ell$ rounds, the lie is about a single cell, $tilde(g)(r_1, ..., r_ell)$, which the verifier can check directly.

    The only way for the prover to succeed here is if some $r_i$ lands exactly where its line crosses the true one. That happens with probability at most $1\/abs(FF)$ each round, so across all $ell$ rounds the chance a lying prover gets by is $<=ell\/abs(FF)$.#s[This is via the union bound.]
  ]
]<sumchecksoundness>

== Sum-check over elementwise products <elementwiseproducts>

In practice, the table we want to make a sum claim about is often#s[We'll discuss more soon, but e.g. summing a table against a mask, evaluating a multilinear extension at a point, and multiplying matrices all take this form.] an elementwise product of other tables. For two tables $f$ and $g$ of the same size, the claim looks like:

$ sum_(x_1, ..., x_ell in {0,1}) f(x_1, ..., x_ell) dot g(x_1, ..., x_ell) = H $

You might assume we could just multiply the tables cell by cell into a single table $h$ and run sum-check on that. But the final check would need $tilde(h)$ at a point, and since $h$ isn't committed, there's no easy way to prove its value.#s[Couldn't the verifier compute it as $tilde(f) dot tilde(g)$, you ask? No, that can have degree $2$ in each variable, so it isn't $tilde(h)$, which is multilinear by definition.]<naivedontwork>

So instead, we fold _both_ $f$ and $g$ by the same value each round, making the round polynomial:

$ s(t) = sum_(x_2, ..., x_ell in {0,1}) tilde(f)(t, x_2, ..., x_ell) dot tilde(g)(t, x_2, ..., x_ell) $

The one real difference from the original sum-check protocol is that $s$ is no longer a line. Each term is a product of two lines in $t$, so it has degree at most $2$, and so does their sum. A quadratic is determined by three points, so each round the prover sends three values, e.g. $s_i (0)$, $s_i (1)$ and $s_i (2)$, instead of two.

The protocol is otherwise unchanged: the verifier checks $s_i (0) + s_i (1)$ against the current claim, picks a random $r_i$, and the new claim is $s_i (r_i)$.#s[To compute $s_i (r_i)$, the verifier recovers $s_i$ from its three values, e.g. by Lagrange interpolation.] At the end, the verifier just needs $tilde(f)(r_1, ..., r_ell)$ and $tilde(g)(r_1, ..., r_ell)$,#s[Which it can get by e.g. opening their commitments.] and checks that their product equals $s_ell (r_ell)$.

Nothing here is special to two tables. For a product of $d$ tables, each round polynomial has degree at most $d$ and the prover sends $d + 1$ values per round.

*The bound on soundness is the same as before, just multiplied by $d$, so $d ell\/abs(FF)$.* The argument is nearly identical to @sumchecksoundness. The only change is that two different polynomials of degree at most $d$ agree on at most $d$ points, rather than one.#s[Their difference is a non-zero polynomial of degree at most $d$, which has at most $d$ roots.] So each round, a random $r_i$ lets the lie escape with probability at most $d\/abs(FF)$, and across $ell$ rounds, at most $d ell\/abs(FF)$.

== Sum-check over elementwise polynomials

A product is just one way to combine tables cell by cell. For example, given tables $f$ and $g$, we might want to prove a claim like this:

$ sum_(x in {0,1}^ell) (f(x) dot g(x) + f(x)) = H $

Each term of this sum is a polynomial in $f(x)$ and $g(x)$: it only involves additions, subtractions and multiplications of the two tables' values at the same cell, and constants. In general, we can take any polynomial $P$ in $k$ variables and any $k$ tables $f_1, ..., f_k$ of the same size, and prove a claim about:

$ sum_(x in {0,1}^ell) P(f_1 (x), ..., f_k (x)) = H $

The protocol is mostly unchanged from before, with the exception of the degree of the round polynomial. Each folded cell is a line in $t$, so if $P$ has total degree $d$, each term of $s$ has degree at most $d$, and so does $s$.#s[Recall that the total degree is the largest sum of exponents in one term. For example, $P(a, b) = a^2 b + b$ has total degree $3$, from the term $a^2 b$.] The prover sends $d + 1$ values per round, and at the end, the verifier needs $tilde(f)_1 (r), ..., tilde(f)_k (r)$, applies $P$ to them, and checks the result against $s_ell (r_ell)$.

Soundness bounds are the same as sum-check over elementwise products of tables, $d ell\/abs(FF)$, where $d$ is the total degree of $P$. The proof again mirrors @sumchecksoundness.

== Proving elementwise polynomial relations <elementwisepoly>

So far, we've used sum-check to prove, well, the sums of tables.#s[Or of any polynomial combining several tables cell by cell, like $sum_x (f(x) dot g(x) + f(x))$.] But a sum loses information, since many different tables have the same sum. Often we want to prove something stronger, that every cell of one table is the result of applying some operation to the matching cells of other tables. For example, say the prover holds tables $f$ and $h$, and claims that a third table $g$ is their elementwise product:


$ g(x) = f(x) dot h(x) quad "for every" x in {0,1}^ell $<cellbycell>

We'll use our identity test from earlier, where we take a random point $r in FF^ell$ and check that $tilde(g)(r)$ equals $tilde((f dot h))(r)$. *The trouble is, how do we compute $tilde((f dot h))(r)$?* As mentioned in @elementwiseproducts, the naive guess does not work: $tilde((f dot h))(r) != tilde(f)(r) dot tilde(h)(r)$.@naivedontwork

So what do we do? Recall from @evalweightedsum that we can rewrite any extension as a weighted sum over the table:

$ tilde((f dot h))(r) = sum_(x in {0,1}^ell) f(x) dot h(x) dot "eq"_r (x) $

Now a claim about $tilde((f dot h))(r)$ can be rewritten as a claim about the sum of a product of three tables, and *we can use the sum-check protocol to prove such a claim*!

Thus, to prove @cellbycell, we start from a claim $tilde(g)(r) = v$ at a random point $r in FF^ell$. If $g$ is the final output of the computation, the verifier picks $r$ and can compute $v$ itself (assuming $g$ is some public table), otherwise, this claim was left behind by proving a later operation that used $g$. Then, we run $ell$ rounds of sum-check to reduce it down to a claim about the product of $tilde(f)$, $tilde(h)$ and $tilde("eq")_r$ at some random $r' in FF^ell$.

$ g(x) = f(x) dot h(x) thick "for every" x in {0,1}^ell \

arrow.b.double^"identity test" \
 tilde(g)(r) = tilde((f dot h))(r) thick "for random" r in FF^ell \
 arrow.b.double^(#text[@evalweightedsum]) \
 tilde(g)(r) = sum_(x in {0,1}^ell) f(x) dot h(x) dot "eq"_r (x) thick  "for random" r in FF^ell \
 arrow.b.double^"sum-check"\
  tilde(f)(r') dot tilde(h)(r') dot tilde("eq")_r (r') = s_ell (r'_ell) thick " for random" r' in FF^ell

$

At this point, the verifier can compute $tilde("eq")_r (r')$ itself, since its product formula takes only $O(ell)$ work.#s[The product formula is multilinear in $x$ and matches the table at every 0/1 point, so by @mlunique it _is_ $tilde("eq")_r$, and we can plug $r'$ straight into it.] The prover then makes claims for the value of $tilde(f)(r')$ and $tilde(h)(r')$, and the verifier checks that the final equation holds given them.

What we've built is a _reduction_: if the claim about $tilde(g)(r)$ is false, then with high probability at least one of the new claims about $tilde(f)(r')$ or $tilde(h)(r')$ is false too.

*This is a really big deal!* We started with a claim about the output $g$ at a random point, and ended with claims about the inputs $f$ and $h$ at a random point. Those claims can get checked in one of two ways:
+ _If the table is committed or public_, the prover can just open the commitment for it at $r'$, or the verifier can compute it directly.#s[See @commitments if you need a refresher on the mechanism here.]
+ Otherwise, _the table is the output of some earlier operation_, and we can repeat this process for that operation, reducing the claim to new ones about _its inputs_.#s[Assuming the operation is _polynomial_. Non-polynomial operations like ReLU can't be reduced to their inputs in this way. We'll explain how to deal with them in @nonpoly.]
So we can apply this _as many times as we want_, working backwards until every claim lands on a committed or public table. This means the verifier can check an entire chain of operations *without ever seeing the intermediate tables*, and the prover only needs to commit and open the ones that can't be reduced further.

#wideblock[#figure(
  image("figures/claim_chain.svg", width: 100%),
  caption: [Proving $y = (x dot W_1) dot W_2$ with sum-check. Each sum-check turns a claim about one table into claims about its inputs, until every claim becomes about a committed/public table. This is often called a _#link("https://dl.acm.org/doi/10.1145/2699436")[GKR]-style_ protocol.],
) <fig-claim-chain>]

With this technique, a cheating prover gets through with probability at most $ell\/abs(FF)$ from the identity test, plus $3 ell\/abs(FF)$ from the sum-check, since its round polynomials have degree at most $3$. By the union bound, this is at most $4 ell\/abs(FF)$ overall.

To be clear, nothing here is special to products. To prove $g(x) = P(f_1 (x), ..., f_k (x))$ for any polynomial $P$ of total degree $d$, we just sum-check $sum_x P(f_1 (x), ..., f_k (x)) dot "eq"_r (x)$ instead, which spits out $k$ claims, one for each $tilde(f)_i $. The round polynomials then have degree at most $d + 1$, so the bound becomes $(d + 2) ell\/abs(FF)$.

== Proving matmuls <matmul>

The elementwise relations we learned to prove so far with sum-check only combine values across tables at the _same_ cell, but *matrix multiplication is different*. With a matmul, each cell of the output depends on a whole row of one input and a whole column of the other, so we can't prove it using the technique from @elementwisepoly out of the box.

#definition[Matrices as tables][

An $m times k$ matrix $A$ is just a table with $m k$ cells.#s[Assume $m$, $k$ and $n$ are powers of two. If they aren't, we can always just pad them with zeros.] Its index bits split into two groups: $log m$ bits for the row, and $log k$ bits for the column.

We'll write $A(i, j)$ for the cell in row $i$ and column $j$, where $i$ and $j$ are each a group of bits, and $tilde(A)(i, j)$ for its multilinear extension.
]


Say the prover holds an $m times k$ matrix $A$ and a $k times n$ matrix $B$, and claims that $C = A B$:

$ C(i, j) = sum_(y in {0,1}^(log k)) A(i, y) dot B(y, j) quad "for all" i, j $<matmulclaim>

*How do we prove this?* We'll obviously start with an identity test. As we proved earlier, to check $C = A B$ it's enough to check their multilinear extensions agree at a random point $r = (r_"row", r_"col")$, i.e.:

$ tilde(C)(r) = tilde(A B)(r) $<matrixclaim>

But how do we compute $tilde(A B)(r)$? This time, unlike the elementwise case in @elementwiseproducts, *the naive guess actually works:*#s[In the elementwise case, $tilde(f)$ and $tilde(h)$ both have the same variables in their terms, so their product has degree $2$ in each. In this case though, the row variables appear only in $tilde(A)$ and the column variables only in $tilde(B)$, and $y$ just gets summed away, so the RHS of @matmulidentity is still multilinear.]

$ tilde(A B)(r_"row", r_"col") = sum_(y in {0,1}^(log k)) tilde(A)(r_"row", y) dot tilde(B)(y, r_"col") $<matmulidentity>

#note[$tilde(A)(r_"row", y)$, as a function of $y in {0,1}^(log k)$, is the table we get by folding the row bits of $A$ by $r_"row"$. Likewise, $tilde(B)(y, r_"col")$ is the table we get by folding the column bits of $B$ by $r_"col"$.#s[Folding works on any group of bits, not just the lowest. We just pair up cells that differ only in the bit being folded.] Both folded tables have $k$ cells, indexed by the same bits.]

Thus claim @matrixclaim becomes: $ tilde(C)(r) = sum_(y in {0,1}^(log k)) tilde(A)(r_"row", y) dot tilde(B)(y, r_"col") $

which is provable via sum-check over the product of the two folded tables, and after its $log k$ rounds, reduces down to claims about the inputs $A$ and $B$ each at a single point.#s[As in the elementwise relation case, the value of $tilde(C)(r)$ is itself just a claim, either left behind by a later operation or checked directly at the end of the chain.]

$
C = A B \
  arrow.b.double^"identity test" \
  tilde(C)(r_"row", r_"col") = tilde(A B)(r_"row", r_"col") \
  arrow.b.double^(#ref(<matmulidentity>)) \
  tilde(C)(r_"row", r_"col") = sum_(y in {0,1}^(log k)) tilde(A)(r_"row", y) dot tilde(B)(y, r_"col") \
  arrow.b.double^"sum-check" \
  tilde(A)(r_"row", r') dot tilde(B)(r', r_"col") = s_(log k) (r'_(log k)) $


Again, just like with elementwise relations, we started with a claim about the output $C$ at a random point, and ended with claims about the inputs $A$ and $B$ at a random point. So if e.g. $A$ was itself computed by an earlier matrix product, we can use the claim about $tilde(A)$ as the starting point for proving that product, and so on.

A cheating prover gets through only if it gets lucky on the identity test, with probability at most $(log m + log n)\/abs(FF)$, or on the sum-check, with probability at most $2 log k\/abs(FF)$.#s[Since $ell= log m + log n$ for the identity test and the sum-check runs for $log k$ rounds with round polynomials of degree $<=2$.] By the union bound, the chance of either happening is at most $(log m + log n + 2 log k)\/abs(FF)$.

*This is also fairly efficient for the prover!* Besides actually doing the matmul, the only real extra work the prover must do is folding $A$ and $B$, which takes about $m k + k n$ field multiplications#s[And about twice as many additions.], plus a sum-check over tables of size $k$.

= Lookups <lookups>

Say we have a table $f$ with $2^ell$ cells, and a fixed public table $T$ with $N$ cells. By fixed public table, we mean $T$ is fixed before the proof starts and doesn't depend on the computation.#s[For example, with $T = [2, 3, 5, 7]$, @lookupclaim says every cell of $f$ is a prime less than 10. Typically $f$ is far bigger than $T$, so most entries of $T$ are used many times, and some not at all.] Can we convince a verifier who does not hold $f$ that every value of $f$ is in $T$? i.e.:

$ forall x in {0,1}^ell quad  exists y in {0,1}^(log N) quad st quad  f(x) = T(y) $<lookupclaim>

Proving this is non-obvious. We don't have any techniques so far that let us prove things about sets in this way. The trick is to turn @lookupclaim into a statement we do know how to prove.#s[There are several ways to do this; lookup schemes are a very active area of research! We'll use #link("https://eprint.iacr.org/2022/1530")[_LogUp_], a scheme from 2022, but there are many other designs, e.g. #link("https://eprint.iacr.org/2020/315")[_Plookup_] and #link("https://eprint.iacr.org/2023/1216")[_Lasso_].] One such method is called _LogUp_, which *turns it into a statement about sums*, which fits nicely with the sum-check tooling we've built up.

For each entry $y$ of $T$, let $m(y)$ count how many cells of $f$ equal $T(y)$.#s[If $T$ contains a value more than once, it doesn't matter which of them we use for counting, only the total matters.] Then if every cell of $f$ appears in $T$, the following holds for any $X$:


$ sum_(x in {0,1}^ell) 1 / (X - f(x)) = sum_(y in {0,1}^(log N)) m(y) / (X - T(y)) $<logup>


Why does this work? Well, the left-hand side has one term per cell of $f$, and if we group cells of the same value together, a value $a$ that appears $c$ times in $f$ contributes $c\/(X - a)$, which is exactly the term the right-hand side has for $a$. If some value $a$ in $f$ is missing from $T$, the left-hand side has a $1\/(X - a)$ term and the right-hand side doesn't, *so no choice of $m$ makes them equal*.#s[Thus if any $m$ works, we're good.]

To prove this equality to the verifier, we can first commit to $m$, then have the verifier provide us with some random $beta in FF$ for an identity test:

$ sum_(x in {0,1}^ell) 1 / (beta - f(x)) = sum_y m(y) / (beta - T(y)) $<logupbeta>

This is great, but @logupbeta still isn't something we can sum-check directly, since its terms are fractions rather than polynomials in the cells. So the prover computes the fractions itself, as two new tables:

$ u(x) = 1 / (beta - f(x)) quad quad v(y) = m(y) / (beta - T(y)) $

and proves they're correct using an identity test + sum-check with elementwise relations that _are_ polynomial,#s[The right-hand side of @ucond is $1$ because the table of all ones has the constant $1$ as its multilinear extension.] i.e.:

$ sum_x "eq"_r (x) dot u(x) dot (beta - f(x)) = 1 $<ucond>
$ sum_y "eq"_s (y) dot v(y) dot (beta - T(y)) = tilde(m)(s) $<vcond>

Unlike the intermediate tables of a computation, claims about $m$, $u$ and $v$ can't be carried backwards to earlier tables, since they're whatever the prover says they are. So the prover must commit to them, and claims about them are checked via openings on their commitments. With those tables established, @logupbeta becomes as simple as:

$ sum_x u(x) = sum_y v(y) $<sumuv>

Whew okay, that was a lot of steps. *To summarize:*

+ The prover commits to $m$.
+ The verifier sends a random $beta in FF$.
+ The prover commits to $u$ and $v$.
+ The prover proves @sumuv, by claiming a value for both sums and running sum-check on each.
+ The prover proves $u(x) dot (beta - f(x)) = 1$ for every $x$, via an identity test at a random $r in FF^ell$, followed by sum-check on @ucond.
+ The prover proves $v(y) dot (beta - T(y)) = m(y)$ for every $y$ the same way, with an identity test at a random $s in FF^(log N)$ and sum-check on @vcond.


#wideblock[#figure(
  image("figures/logup.svg", width: 100%),
  caption: [_LogUp_ on $f = [3, 5, 3, 7]$ and $T = [2, 3, 5, 7]$.],
) <fig-logup>]

A cheating prover gets through only if it gets a lucky $beta$, which has probability at most $(2^ell + N)\/abs(FF)$,#s[Multiplying out the denominators in @logup gives a non-zero polynomial of degree at most $2^ell + N$, and $beta$ would have to land on one of its roots. _If $beta$ lands directly on some $f(x)$, then $beta - f(x) = 0$ has no inverse, so no $u(x)$ can satisfy $u(x)(beta - f(x)) = 1$ anyway._] or if it gets lucky on one of the identity tests or sum-checks, which adds at most $5(ell + log N)\/abs(FF)$, and is marginal in comparison.#s[The $f$ side adds $ell + 3 ell + ell = 5 ell$, from the identity test, its sum-check over a product of three tables, and the sum-check on $u$. The $T$ side is the same with $log N$ in place of $ell$.] Note that because of the $2^ell$ in the numerator, this is a much weaker bound than we've seen before, so we'll almost certainly have to draw $beta$ from an extension field as described in @extensionfields.


*Isn't building and committing two new tables expensive?* Somewhat, and it's the main cost of LogUp. $u$ has as many cells as $f$, so the prover pays for $2^ell$ field inversions#s[This can be done efficiently in bulk, see #link("https://www.johndcook.com/blog/2026/01/14/montgomerys-trick/")[_Montgomery’s trick_].] plus a commitment to a table of that size. And since $beta$ is drawn from an extension field, the cells of $u$ are extension field elements, which makes that commitment more expensive still. $v$ is usually much cheaper, at most $N$ inversions and $N$ cells, and $N$ is typically far smaller than $2^ell$. A refinement to LogUp from 2023 called #link("https://eprint.iacr.org/2023/1284")[_LogUp-GKR_] removes the need to commit to $u$ and $v$ entirely.

== Proving elementwise non-polynomial relations <nonpoly>

Now say we want to prove that some table $h$ of size $2^ell$ is just a version of some table $g$ that's had some non-polynomial operation $phi$, e.g. a ReLU, applied elementwise:

$ h(x) = phi(g(x)) "for all" x in {0, 1}^ell $<tuplesclaim>

Assume the cells of $g$ only take values in some small set $D$, for example all 16-bit integers. #sidenote(counter:none)[#image("figures/relu_pairs.svg")] We can make a table that matches inputs/outputs of $phi$, and look up _pairs_ in this table to prove @tuplesclaim.

Let $T$ have $N = abs(D)$ rows and two columns, every possible input $T_"in" (y) in D$ alongside $T_"out" (y) := phi(T_"in" (y))$. Our claim is thus that every pair $(g(x), h(x))$ is a row of $T$. Each input appears in exactly one row, so this forces $h(x) = phi(g(x))$.

We don't have any machinery to prove this kind of paired lookup, *so we'll need to reduce this to a standard single-value lookup* like in @lookupclaim. We can do this like so: have the verifier send a random $gamma in FF$, and use it to squash each pair into a single value, forming two final tables:

$ f(x) = g(x) + gamma dot h(x) quad quad t(y) = T_"in" (y) + gamma dot T_"out" (y) $

Unlike $u$ and $v$ in LogUp, *these two tables are never committed or sent*. The prover computes $f$ cell by cell, which costs only $2^ell$ multiplications (cheap next to the lookup's inversions), and as we'll see below, every claim about $f$ or $t$ reduces directly to claims about $g$, $h$ and the public table $T$.

We then prove every cell of $f$ appears in $t$. A pair that isn't a row of $T$ only survives squashing if $gamma$ is unlucky. For each row $y$, the pair squashes onto that row's value only if $(g(x) - T_"in" (y)) + gamma (h(x) - T_"out" (y)) = 0$. The LHS is a non-zero polynomial of degree at most $1$ in $gamma$, and thus a random $gamma$ makes it zero with probability at most $1\/abs(FF)$.#s[This is via Schwartz-Zippel again, as in @identitytest.] By the union bound over all $N$ rows, a bad pair survives with probability at most $N\/abs(FF)$.#s[If $N$ is big, e.g. $2^16$ if $T$ covers all 16-bit integers, this bound is fairly weak, so we likely need to draw $gamma$ from an extension field for security.]

#wideblock[#figure(
  image("figures/tuple_lookup_no_claims.svg", width: 100%),
  caption: [Proving $h = "ReLU"(g)$ for $g = [-1, 2, 0, 3]$ with $D=[-2, -1, 0, 1, 2, 3].$],
) <fig-tuple-lookup>]

Like for any lookup, this ends with a claim about $tilde(f)$ at some random point $r'$, and one about $tilde(t)$ at another point $s'$. The claim about $tilde(t)$ is easy to check, as $T$ is public and the verifier can compute it itself. For $tilde(f)$, since $f = g + gamma h$ is linear in $g$ and $h$, the naive guess works this time: $tilde(f)(r') = tilde(g)(r') + gamma tilde(h)(r')$. Thus the prover sends $tilde(g)(r')$ and $tilde(h)(r')$, and the verifier checks they combine to the claim. That leaves two claims to check.

The claim about $tilde(g)(r')$ can be carried backwards as usual, if $g$ is the result of some earlier operation. For $tilde(h)(r')$, carrying it backwards would mean using $h = phi(g)$ to turn it into a claim about $g$, which is exactly what we can't do, since $phi$ isn't a polynomial. So instead, *the prover must commit to $h$* before the verifier sends $gamma$, and the claim about $tilde(h)(r')$ is checked by opening it.#s[If $h$ were committed after $gamma$, the prover could pick incorrect values for $h$ that still squash onto valid rows of $t$.]

Overall, a cheating prover gets through with probability at most $N\/abs(FF)$ from squashing, plus the lookup's own bound, for $(2^ell + 2N + 5(ell + log N))\/abs(FF)$ in total.#s[#note[This doesn't count the openings of the committed tables, which depend on the commitment scheme!]] Generally the $2^ell$ term dominates, so looking up pairs costs barely more than looking up single values.

= Merging claims <mergingclaims>

Often we end up with several claims about the _same_ table. For example, if a table $f$ is the input to two different operations, proving each one leaves behind its own claim about $tilde(f)$ at a different point. If $f$ is a committed table, we'd need to do an opening for each claim, and if it's an intermediate table, we'd have to carry each claim back through whatever operations produced $f$ separately. Both of these are expensive, particularly openings, so we'd like to squash them all into one claim if possible.

Say we have claims $tilde(f)(r_c) = v_c$ for several points $r_c$. By @evalweightedsum, each one is just a weighted sum of $f$'s cells, $sum_x "eq"_(r_c) (x) dot f(x) = v_c$. So, just like squashing pairs in @nonpoly, the verifier draws a random weight $kappa_c$ for each claim $c$, and instead of checking every claim separately, we check a single weighted sum of them, which rearranges into one sum over $f$:

$ & sum_x "eq"_(r_c) (x) dot f(x) = v_c quad "for every claim" c \
<==>^"w.h.p." quad & sum_c kappa_c dot (sum_x "eq"_(r_c) (x) dot f(x) - v_c) = 0 \
<==> quad & sum_x underbrace(sum_c kappa_c dot "eq"_(r_c) (x), W(x)) dot f(x) = sum_c kappa_c dot v_c $<mergedclaim>

If every claim holds, the weighted sum is obviously zero. The "w.h.p." is about the other direction: if any claim $c$ is false, then $sum_x "eq"_(r_c) (x) dot f(x) - v_c != 0$, so the second line's left-hand side is a non-zero polynomial of degree $1$ in the $kappa_c$'s, and by Schwartz-Zippel#s[Go back to @identitytest if you need a refresher!], it's zero with probability at most $1\/abs(FF)$.#s[#note[It's important that the $kappa_c$'s are only drawn once every claim is fixed, otherwise a cheating prover could choose its lies so that they cancel out in the weighted sum.]]

The last line is a sum over the elementwise product of two tables, $W$ and $f$, so we can prove it with sum-check (@elementwiseproducts). At the end, the verifier needs $tilde(W)(r')$ and $tilde(f)(r')$ at a single random point $r'$. It can compute $tilde(W)(r') = sum_c kappa_c dot tilde("eq")_(r_c) (r')$ itself, and the one claim left about $tilde(f)(r')$ gets checked like any other: by opening $f$ if it's committed, or by carrying it back to whatever produced $f$. *So no matter how many claims we make about a table, we only ever have to check one!*

#note[Nothing here needs the weights to be $"eq"$ tables. Any pile of claims of the form $sum_x W_c (x) dot f(x) = v_c$, each a public-weighted sum of the same table, merges into one in exactly the same way.#s[This will be helpful later (@mergingpad), when making our proofs zero-knowledge leaves us with a big pile of exactly these kinds of claims.]]

*This does come with a slight soundness cost, though.* A cheating prover now also gets through if it gets lucky with the $kappa_c$'s, with probability at most $1\/abs(FF)$, or on the sum-check, with probability at most $2 ell\/abs(FF)$, so at most $(2 ell + 1)\/abs(FF)$ extra overall.

= Polynomial commitments <pcs>

Since @commitments, we've been waving our hands about how we'll actually implement commitments and openings for our tables. Let's open the black box and discuss how to implement a _polynomial commitment scheme_ (PCS), specifically _Ligero-PC_.#s[There are a ton of polynomial commitment schemes, just like lookup schemes, such as _KZG_ and _Brakedown-PC_. Some, like KZG, are built on elliptic curve pairings (instead of hashes), which give much smaller proofs but need a #link("https://vitalik.ca/general/2022/03/14/trustedsetup.html")[_trusted setup_] and aren't quantum-resistant. Ligero-PC gets its name from the #link("https://eprint.iacr.org/2022/1608")[_Ligero_] paper, where the idea first appeared.]

We'll need to introduce two tools/tricks before describing the scheme: a way to compute $tilde(g)(r)$ from a single weighted sum of a table $g$'s rows, and _Reed-Solomon codes_.

== Evaluating extensions from a weighted sum of rows

Say we have a table $g$ with $2^ell$ cells. No matter its "true" structure (whether it represents a matrix or a flat table or a tensor, etc), *we can lay it out as a matrix $G$ with $W$ columns and $R$ rows, such that $W R = 2^ell$.* We'll let the low bits of a cell's index pick its column, and the high bits pick its row, so each row is a run of consecutive cells.#s[To keep the low bits first like in our table notation, we'll write $G(x_"col", x_"row")$ with the column index before the row index.] For example, $c = [1, 5, 3, 9]$ would become:

$ C = mat(1, 5; 3, 9) $

If we want to evaluate $tilde(g)$ at some point $r$, we can equivalently think about this as evaluating $tilde(G)$ at the point split by column/row into $r_"col"$ and $r_"row"$, i.e.:

$ tilde(g)(r) = tilde(G)(r_"col", r_"row") $

Recall @evalweightedsum, which states we can write $tilde(g)(r)$ as a weighted sum of $g$'s cells:

$ tilde(g)(r) = sum_(x_1, ..., x_ell in {0,1}) g(x_1, ..., x_ell) dot "eq"_r (x_1, ..., x_ell) \

st \

 "eq"_r (x_1, ..., x_ell) = product_(i = 1)^ell (r_i x_i + (1 - r_i)(1 - x_i)) $

Generalizing this to matrices, we notice $"eq"_r$ can be split into a product of column and row parts:

$ "eq"_r (x_"col", x_"row") = "eq"_(r_"col")(x_"col") dot "eq"_(r_"row")(x_"row") $

Thus by plugging this into @evalweightedsum for $G$, and pulling out the column part of the inner sum we can write:

$ tilde(G)(r) &= sum_(x_"col" in {0,1}^(log W) \ x_"row" in {0, 1}^(log R)) G(x_"col", x_"row") dot overbrace("eq"_(r_"col")(x_"col") dot "eq"_(r_"row")(x_"row"), "eq"_r (x_"col", x_"row")) \
&=  sum_(x_"col") "eq"_(r_"col")(x_"col") quad dot underbrace(sum_(x_"row") G(x_"col", x_"row") dot "eq"_(r_"row")(x_"row"), G_r_"row" (x_"col"))
$<udef>

The inner sum doesn't depend on $r_"col"$, so let's give it a name: $G_r_"row"$. It's a table of $W$ cells, one per column, so we can think of it as a single row. Each of its cells is a weighted sum down the matching column of $G$, so as a whole, *$G_r_"row"$ is a weighted sum of all the rows of $G$*, with weights $"eq"_(r_"row")$.#s[Notice that this is just $G$ with its row bits folded by $r_"row"$!]

The outer sum is thus a weighted sum of $G_r_"row"$ with weights $"eq"_(r_"col")$, which by @evalweightedsum is its extension at $r_"col"$:

$ tilde(g)(r) = tilde(G)(r_"col", r_"row") = tilde(G_r_"row")(r_"col") $

Why did we just do all that? *Well, now, if a prover just sends $G_r_"row"$, the verifier can finish evaluating $tilde(g)$ itself* by folding $G_r_"row"$, which is cheap since $G_r_"row"$ only has $W prop sqrt(2^ell)$ cells, rather than $g$'s full $2^ell$ cells. For example, take $c$ from earlier and $r = (2, 3)$, so $r_"col" = 2$ and $r_"row" = 3$. The row weights are $"eq"_3 = [1 - 3, 3] = [-2, 3]$, so:

$ C_3 = -2 dot [1, 5] + 3 dot [3, 9] = [7, 17] $

and folding $C_3$ by $2$ gives $(1 - 2) dot 7 + 2 dot 17 = 27$, which matches $tilde(c)(2, 3) = 27$ from before.

The problem is, of course, *that nothing stops the prover from sending a fake $G_r_"row"$* which folds to whatever it wants, e.g. if it wants to claim $tilde(c)(2, 3) = 28$, it can just send $C'_3 = [6, 17]$, which folds to $28$. The verifier needs some way to check $G_r_"row"$ is really the correct weighted sum of the committed rows.


One naive idea would be to commit a Merkle tree of $G$'s columns, and then have the verifier randomly check some entries of $G_r_"row"$ by opening the matching columns $x_"col"$ of $G$ and ensuring $G_r_"row" (x_"col") = sum_(x_"row" )  G(x_"col", x_"row") dot "eq"_(r_"row")(x_"row") $. The problem is that a cheating prover only needs to fake _one_ entry of $G_r_"row"$ to change what it folds to (e.g. $C'_3$ differs from $C_3$ only in its first cell), so each random column only catches the lie with probability $1\/W$.

*If only there was a way to spread any lie in $G_r_"row"$ across most of the columns...* oh, that's exactly what _error-correcting codes_ do! We'll use Reed-Solomon, though other linear codes can work too.

== Reed-Solomon codes <reedsolomon>

#definition[Reed-Solomon code#s[Or _RS_ codes for short.]][
  Fix a positive "rate" $rho < 1$ such that $W\/rho$ is an integer, e.g. $rho = 1\/8$.

  To _encode_ a row#s[We say "row" since that's how we'll use RS codes in our commitment scheme, encoding each row of a matrix, but to be clear they work on any list of values.] $m$ of $W$ values, treat them as the coefficients of a polynomial (i.e. $P_m (X) = m_0 + m_1 X + dots + m_(W-1) X^(W-1)$)#s[*Careful:* this is a different way to read a row as a polynomial than the multilinear extension! There, $[1, 5]$ were the values at $0$ and $1$, while here they're coefficients.] and evaluate it at $M = W\/rho$ fixed, distinct points $z_0, ..., z_(M-1)$.

  The list of those $M$ values of $P_m$ is called the row's _codeword_, $"Enc"(m)$, such that its $c$-th cell is $"Enc"(m)(c) = P_m (z_c)$.

  #divider

  For example, consider the row $[1, 5]$. With $rho = 1/2$  and the points $z_c = c$, i.e. $0, 1, 2, 3$, $P_[1,5](X) = 1 + 5 X$ so $"Enc"([1, 5])= [1, 6, 11, 16]$.
]

Reed-Solomon codes are useful for us because they're *massively redundant*. Changing just one value of a row changes most of the codeword:

#theorem[Different rows have very different RS codewords][
  If $m != m'$, then $"Enc"(m)$ and $"Enc"(m')$ differ in $>= M(1-rho)$ of their $M$ cells.

  #proof[The difference of their polynomials $P_m - P_(m')$ has degree less than $W$, and thus it has at most $W-1$ roots/zeros. Thus the two codewords agree on at most $W-1$ points, and thus differ in at least $M(1-rho)$ cells.]
]<rsdistance>


#figure(image("figures/pcs_rs_distance.svg", width: 100%),
  caption: [RS codewords of different rows agree at less than $W$ points, so a random position almost always tells them apart.]) <fig-pcs-rs-distance>
With rate $rho=1/2$, two different rows' codewords differ in more than half their positions, meaning checking *a single random codeword cell has at least a 50% chance of telling them apart*.

The other property of Reed-Solomon codes that will come in handy is that their encoding is *linear*:

#theorem[RS encoding is linear][

  For any rows $m_1, ..., m_n$ of $W$ values and any $a_1, ..., a_n in FF$:

  $ sum_(i = 1)^n a_i dot "Enc"(m_i) = "Enc"lr((sum_(i = 1)^n a_i dot m_i)) $

  #proof[The $k$-th coefficient of $P_(sum_i a_i dot m_i)$ is $sum_i a_i dot (m_i)_k$, so $P_(sum_i a_i dot m_i) = sum_i a_i dot P_(m_i)$. Thus the two sides agree at every evaluation point.]
]<rslinear>

In other words, *encoding a weighted sum of rows gives the same result as taking that weighted sum of their codewords*. This is exactly what we need: if the prover commits to the codewords of $G$'s rows and later sends us a weighted sum of those rows (e.g. $G_r_"row"$), the verifier can encode it themselves and check it against the committed codewords!

== Ligero-PC

We're now finally ready to discuss the complete implementation of our polynomial commitment scheme, _Ligero-PC_.

=== Commitments

To _commit_ to some table $g$, the prover does the following:

1. Lay out $g$ as an $R times W$ matrix $G$.#s[#note[$R$ and $W$ are important parameters to tune for proof size and speed. During an opening, the prover will send $G_r_"row"$ (which has $W$ values) and $t$ opened columns ($t dot R$ values, where $t$ is the number of columns the verifier checks, see @openings), so the proof size is $approx W + t R$. Given $W R = 2^ell$, $W + t R$ is minimized when $W approx t R$, i.e. $W approx sqrt(t dot 2^ell)$, so $G$ should be a lot wider than it is tall. The verifier's work scales similarly, since it encodes $G_r_"row"$ and sums each opened column.]]
2. Encode every row with RS, giving an $R times M$ matrix of codewords $E$.
3. Build a Merkle tree whose leaves are (hashes of) the _columns_ of $E$, and send the root to the verifier.

#figure(
  image("figures/pcs_commit_steps.svg", width: 100%),
  caption: [Committing to a table $g$ with Ligero-PC. The root of the Merkle tree is sent to the verifier.],
) <fig-pcs-commit-steps>

=== Openings <openings>

To prove $tilde(g)(r) = v$ for any $r in FF^ell$, the prover/verifier do the following:

1. The prover sends $G_r_"row"$, as defined in @udef, to the verifier.
2. *(Value check)* The verifier checks that $tilde(G_r_"row")(r_"col")=v$ by folding.
3. The verifier computes $"Enc"(G_r_"row")$ itself, and then picks $t$ random column indexes to request from the prover.
4. The prover opens those columns of $E$, each with its Merkle path.#s[See #link("https://en.wikipedia.org/wiki/Merkle_tree")[Wikipedia] if you need a refresher on how Merkle trees work.]
5. *(Column check)* For each opened column $c$, the verifier checks that:
   $   sum_(x_"row" )   "eq"_(r_"row")(x_"row") dot E(c, x_"row") = "Enc"(G_r_"row")(c)  $

If all column checks pass, the opening is successful.


#wideblock[#figure(
  image("figures/pcs_open_steps.svg", width: 100%),
  caption: [Interactively proving $tilde(g)(r) = v$ via a Ligero-PC opening.],
) <fig-pcs-open-steps>]



*Why the column check works might not be obvious at first glance*, so let's break it down. Let $G_(x_"row")$ be row $x_"row"$ of $G$. Each row of $E$ is just the codeword of the matching row of $G$, i.e. $E(c, x_"row") = "Enc"(G_(x_"row"))(c)$. Thus for every column $c$:

$ sum_(x_"row") "eq"_(r_"row")(x_"row") dot E(c, x_"row")
  = "Enc"lr((sum_(x_"row") "eq"_(r_"row")(x_"row") dot G_(x_"row")), size: #2em)(c)
  = "Enc"(G_r_"row")(c) $

The first equality is just linearity (@rslinear), which says a weighted sum of codewords is the codeword of the same weighted sum of rows. The second is the definition of $G_r_"row"$ from @udef. Thus, if the prover is honest, the check will pass.

*How likely is it that a cheating prover gets a false opening accepted?* _Assume for now that every row of $E$ is a valid RS codeword._ To pass the value check with a false $v$, the prover must send some fake $G'_r_"row" != G_r_"row"$. By @rsdistance, $"Enc"(G'_r_"row")$ differs from $"Enc"(G_r_"row")$ in more than a $(1 - rho)$ fraction of columns, and each of those columns fails the column check. Thus, given our assumption about $E$:

#theorem[If $v != tilde(g)(r)$, and every row of $E$ is a valid\ RS codeword, $Pr["opening passes"] < rho^t$
][
    #note[We'll see that we can't quite guarantee every row of $E$ is a codeword, only that it's close to one, but this bound barely changes. More on this below.]

  #proof[Each of the $t$ columns, drawn independently, passes with probability less than $rho$, and all $t$ must pass.]
]<openingsoundnessevalid>

Unlike \~all our other bounds, this one *doesn't improve as the field gets bigger*. The only parameters that matter are $t$ and $rho$. Opening more columns ($arrow.t t$) costs proof size, since each one comes with $R$ values and another Merkle path. A smaller RS rate ($arrow.b rho$) means fewer columns for the same security, but longer codewords, so more work for the prover when encoding and a bigger Merkle tree to build.

*But what if the rows of $E$ aren't RS codewords?*#s[It's okay if $E$ is made up of codewords from a random $G$-shaped matrix, not necessarily the "true" $G$, it just needs to be composed of RS codewords period.] We made this assumption above, but if it's not true, a cheating prover could just hash whatever matrix it wants for $E$, making our soundness argument above useless. Luckily we can prove that, _with high probability_, the column check will catch any $E$ that's far from being made of RS codewords, which turns out to be all we need.#s[As long as $r$ is *drawn randomly after the prover committed to the table*. If not, the prover could build $E$'s errors to cancel out under exactly the weights $"eq"_(r_"row")$.

The fix is to squash in a _proximity test_: a second weighted sum of the rows, with weights the prover couldn't predict.

+ The verifier picks a random weight $alpha_(x_"row")$ for every row, and the prover sends $s$, the value that $G_alpha = sum_(x_"row") alpha_(x_"row") dot G_(x_"row")$ folds to by $r_"col"$.

+ Then the verifier picks a random $zeta$, and the prover sends $G_r_"row" + zeta dot G_alpha$ in place of $G_r_"row"$. The verifier then checks this folds to $v + zeta s$, the same trick as the mask row in @maskedopenings.

The original Ligero-PC sends $G_alpha$ as a separate row instead, but squashing lets us save bandwidth.
]

Why only _far_? If only a few cells of $E$ are corrupted, the opened columns will usually miss them. But that's fine, since *a few corrupted cells can make a check fail, but can't get a false claim accepted.* What matters is that $E$ is _$delta$-close_, meaning it matches some matrix $E^*$ whose rows are all valid RS codewords, in all but at most $delta M$ columns. As long as $delta < (1 - rho)\/2$, a $delta$-close $E$ has only one such $E^*$,#s[Each would match $E$ outside its own $delta M$ bad columns, so the two would differ in at most $2 delta M < (1 - rho) M$ columns. But by @rsdistance, two different codewords differ in more than that.] which corresponds to the RS encoding of $G$.

So the only way for a malicious prover to cheat is to hash a $delta$-far $E$.#s[$delta$-far just means "not $delta$-close".] How likely is such an $E$ to pass a column check? Not likely: by #link("https://eprint.iacr.org/2023/630")[Diamond and Posen (2023)], summing the rows of a $delta$-far $E$ with weights $"eq"_(r_"row")$, for a random $r_"row"$, gives something $delta$-far from every RS codeword with probability at least about $1 - log_2 R dot M\/abs(FF)$. And when the sum is $delta$-far, each opened column in the column check catches it with probability more than $delta$. So taking all of this into account, the true soundness of openings is:

#theorem[Soundness of openings][
  $"If" v != tilde(g)(r)$, $Pr["opening passes"] <= (log_2 R dot M)/abs(FF) + (1 - delta)^t + (rho + delta)^t $

  #proof[
    A cheating prover can only get lucky in three ways:

    - $E$ is $delta$-far, but summing its rows with the weights $"eq"_(r_"row")$ happens to give something close to an RS codeword anyway. As explained above, this happens with probability about $log_2 R dot M\/abs(FF)$.
    - $E$ is $delta$-far and its weighted sum isn't close to any RS codeword, so each opened column catches it with probability more than $delta$, but all $t$ columns miss anyway. This happens with probability less than $(1 - delta)^t$.
    - $E$ is $delta$-close, so to pass the value check the prover must send a fake $G'_r_"row"$. A column misses it only if it's one of the fewer than $rho M$ columns where the fake and true codewords agree, or one of the at most $delta M$ corrupted columns, so all $t$ columns miss with probability at most $(rho + delta)^t$.

The chance of any of these occurring is $<=$ their sum, via the union bound.
  ]
]<openingsoundnessproximity>

#note[The first two terms of @openingsoundnessproximity only depend on whether $E$ is close to RS codewords, which doesn't change between openings. So if a table will be opened many times, its first opening can use lots of columns to show it's $delta$-close for a tiny $delta$, and later openings then need far fewer, since only $(rho + delta)^t approx rho^t$ is left.#s[For example, say $rho = 1\/4$ and we want $2^(-128)$ soundness. A one-off opening needs about $190$ columns. Showing $E$ is very close, say $0.05$-close, takes about $1750$ columns, but after that, each opening only needs about $74$.]]

= Zero-knowledge

ZK-SNARK stands for _Zero-Knowledge_ Succinct Non-Interactive Argument of Knowledge. So far, we've built a lot of tools that achieve the _succinct_ and _argument of knowledge_ parts, but not discussed _zero-knowledge_ or _non-interactivity_. Luckily, all of our existing tools can be modified/augmented fairly easily to be both ZK (keep reading!) and non-interactive (see @fiatshamir). First, let's discuss why our tools as is are not considered _zero-knowledge_.

For a protocol to be zero-knowledge, the verifier should learn nothing beyond the fact that the claim is true from a proof. *Our tools so far are all pretty leaky.* Almost every message the prover sends to the verifier gives the verifier an equation that can be aggregated together with others to solve for the underlying committed tables.#s[Some concrete examples:
- *Sum-check.* For $c = [1, 5, 3, 9]$, the first round polynomial has $s_1 (0) = 1 + 3 = 4$, so the verifier learns that $c(0, 0) + c(0, 1) = 4$.
- *Openings.* $G_r_"row"$ is a weighted sum of $G$'s rows, so opening $c$ at $r_"row" = 3$ reveals $-2 dot [1, 5] + 3 dot [3, 9] = [7, 17]$. Open it again at $r_"row" = 2$ and the verifier gets $-1 dot [1, 5] + 2 dot [3, 9] = [5, 13]$, and with two equations in two unknown rows, it can solve for the whole table!
- *Opened columns.* Each one reveals a codeword entry of every row, which is yet another equation per row.]<leakexamples> *How do we make it such that a verifier can't learn anything about our committed tables, even from many proofs?*


What if, before sending a value computed from a secret, we just added some fresh random value (a _mask_) to it? In theory, this works surprisingly well:

#theorem[Masking with a uniform value hides it][
  If some _mask_ $z in FF$ is drawn uniformly at random, independently of $v$, then $v + z$ is uniformly random, no matter what $v$ is.

  #proof[For any $y in FF$, exactly one $z$ gives $v + z = y$, namely $z = y - v$. So every $y$ has probability exactly $1\/abs(FF)$, whatever $v$ is.]
]<onetimepad>

This is the same idea as a _one-time pad_ in cryptography, and it comes with the same two big caveats:

+ *A mask can only be used once.* If the verifier sees $v + z$ and $v' + z$, it can subtract them to get $v - v'$, and the mask cancels out entirely.
+ *A mask must never leak.* If any other message reveals $z$, or even just something computed from it, the verifier can use it to undo the mask and recover $v$. So we have to look at _everything the verifier sees_ together, not just each message on its own.

If we're careful to obey these rules, we can make our proof zero-knowledge by applying masks to any leaky messages (_masking_ them).#s[#note[Technically masking gives only what's called _honest-verifier_ zero-knowledge, which only holds for a verifier that generates its challenges randomly like it's supposed to. But this is fine, once the protocol is made _non-interactive_ (see @fiatshamir), the challenges come from a hash, so the verifier can't deviate anyway.]] The tricky part is doing this without breaking soundness, since the verifier still needs to _check_ what the prover sends.

Our tools leak in two different ways, which we'll fix separately:

+ *Through the values the prover sends*, like sum-check's round polynomials. The challenge here is that the verifier has to check these values without ever seeing them (@pads).
+ *Through the commitments themselves.* Each opening reveals columns of $E$ straight from the commitment, which the verifier checks against the Merkle root. These can't be masked after the fact, so the masking has to be built into the commitment (@zkcommitments).

We'll start with the values.

== Hiding values with committed pads <pads>

All of our tools involve the prover sending the verifier values computed from secrets: sum-check's round polynomials, the helper values in lookups, etc.

We'll need to mask these too if we want to achieve full zero-knowledge, but we can't just throw random masks on everything because the verifier needs these values to do arithmetic checks on, e.g. in sum-check the verifier must check $s_1(0) + s_1(1) =H$. If a prover sends $s_1 (0) + z$ instead of $s_1 (0)$, the verifier can't run this check anymore, a cheating prover could claim _any_ number and say "that's the true value plus my mask, trust me bro."

So how can the verifier check something it can't see? Well, it already does this with commitments: it never sees a committed table, but the prover can still convince it of facts about it. *So what if the prover committed to its masks too?*#s[This is the core idea of #link("https://eprint.iacr.org/2026/683")[_VEIL_] (Dalal, Hemo, Rabinovich and Rothblum, 2026), which most of this section follows.] Let's see how that might work.

At the start of each proof, we'll have the prover generate a long list of fresh random masks $h_1, h_2, dots$ and commit to them as one table $P$. We'll call these committed masks _pads_.#s[As in _one-time pad_.] Then, whenever the prover would normally send some secret value $y_j$ to the verifier, it sends $overline(y_j) = y_j + h_j$ instead. As long as each pad is used only once, by @onetimepad, every $overline(y_j)$ is uniformly random and tells the verifier nothing on its own.

*But how do we still allow the verifier to do checks on these values, when it doesn't know the pads?* In short, we'll turn every check into a claim about committed values, which the prover can prove later (@padclaims).


#wideblock[#figure(
  image("figures/pad_value.svg", width: 100%),
  caption: [The prover sends a secret value plus a committed pad. The verifier can't check it directly, so it writes down a claim about the pads instead.],
) <fig-pad-value>]

=== Linear checks <linearclaims>

Take for example the check from the first round of sum-check:

$ s_1(0) + s_1(1) = H $

If the prover sends $overline(s_1(0)) = s_1 (0) + h_a$ and $overline(s_1(1)) = s_1 (1) + h_b$, the verifier's desired check becomes:

$ overline(s_1(0)) + overline(s_1(1)) = H + h_a + h_b \
iff \
h_a + h_b = overline(s_1(0)) + overline(s_1(1))  - H
$

This equivalent form has only pads on the left and values the verifier knows on the right, so *it's now just a claim about a weighted sum of a committed table!* That's very close to what our openings from @pcs already let us check.#s[Recall: evaluating a multilinear extension $tilde(g)$ at some point $r$ is equivalent to evaluating a weighted sum of the table with weights $"eq"_r$. See @evalweightedsum.] The one wrinkle is that a standard opening proves a sum of the table weighted by $"eq"_r$, while this is a sum weighted by something else (here, just picking out two cells). Luckily, as we'll see in @padclaims, it's fairly straightforward to prove this nonetheless.

*We can do this for every linear check the verifier normally makes, turning checks into claims about the committed pads, which we'll save to verify later*.#s[Using the method described in @padclaims.] Note that this means the verifier no longer does its checks live as it gets messages from the prover, and instead just writes them all down and waits to check them at the very end.

Generalizing this, as long as a check is linear in the secret values $y_j$, substituting $y_j = overline(y_j) - h_j$ for every secret value turns it into a claim $c$ of the form:

$ sum_x L_c (x) dot P(x) = b_c $<linform>

where $L_c$ is some public weight table (zero on every pad the claim doesn't touch), and $b_c$ is a public number. We'll see how to prove these claims soon in @padclaims.

*What about the claims passed between sum-checks?* Recall from @elementwisepoly that a sum-check proving $g = f dot h$ ends with a claim about $tilde(f)(r')$, which becomes the starting claim of the next sum-check, the one proving how $f$ was computed. With pads, the prover just sends $tilde(f)(r')$ padded, so the next sum-check's first check, $s_1 (0) + s_1 (1) = tilde(f)(r')$, has hidden values on both sides. But it's still linear, so it turns into a pad claim like any other. *So claims get passed all the way back up the chain without ever being revealed.*

=== Non-linear checks <nonlinearclaims>

Not all checks are linear, sometimes a check multiplies secret values together. For example, at the end of a sum-check over an elementwise product of tables (@elementwiseproducts), the verifier needs to check that $c = a dot b$, where $a$, $b$ and $c$ are all secret. Naively substituting $a = overline(a) - h_i$, $b = overline(b) - h_j$, etc would result in a claim involving a product of two pads, which isn't of the form @linform.

It's important we have some way to do these checks. Luckily, there's a neat trick we can do to effectively turn them linear, and thus we can verify them using the same machinery we'll verify all our linear claims with. It's a bit complex, buckle up.

Let's get formal. Say the verifier needs to check the following claim, where $c, a_1, ..., a_k$ are secret values (each already sent padded as $overline(c), overline(a_1), ..., overline(a_k)$), and $Q$ is some public polynomial where every term has the same total degree $d$, a.k.a. $Q$ is _homogeneous_:#s[For example, $a b$ is homogeneous of degree $2$, but $a^2 b + b$ isn't. If $Q$ isn't homogeneous, we can always make it so by introducing a public constant $a_0 = 1$ and multiplying each term by enough copies of $a_0$ to bring it up to degree $d$, e.g. $a^2 b + b$ becomes $a^2 b + a_0^2 b$.]

$ c = Q(a_1, ..., a_k) $

*How do we prove this without revealing the $a_i$'s?* If the verifier knew the $a_i$'s, it'd be easy, $Q(a_1,...,a_k)$ would just be a public number and "$c = "that number"$" would be a linear claim. Our first instinct might be to use the padded values $overline(a_i) = a_i + h_i$ so the verifier can compute $Q(overline(a_1), ..., overline(a_k))$ itself. Expanding it gives $Q(a_1, ..., a_k)$ plus a bunch of terms where the $a_i$'s and $h_i$'s are multiplied together. Call the sum of those terms $x$. The verifier can't compute $x$ itself, since it involves secrets, so the prover sends it padded, and the check becomes:


$ c + x = Q(overline(a_1), ..., overline(a_k)) $

This is linear in the secrets $c$ and $x$, but nothing ensures the $x$ the prover sends is correct, so a prover lying about $c$ could just send whatever $x$ makes up the difference. And we can't fix this by checking $x$ directly, since $x$ is a non-linear combination of the $a_i$'s and $h_i$'s, which puts us right back where we started. What we need is a way to *prevent a cheating prover from using $x$ to cancel a lie in $c$, without needing to actually check $x$ itself*.

The trick is to have the verifier send a random challenge $gamma$ that scales $c$, but only _after_ the prover has sent $x$. That way, the difference $x$ would need to make up depends on $gamma$, so a cheating prover can't know which $x$ would cancel out a lie.#s[This trick comes from #link("https://eprint.iacr.org/2021/076")[_QuickSilver_] (Yang et al., 2021).] The prover scales each $a_i$ by $gamma$ and masks it with a fresh pad $h'_i$, sending $overline(gamma a_i) = gamma dot a_i + h'_i$. Since $Q$ is homogeneous, expanding $Q(overline(gamma a_1), dots, overline(gamma a_k))$ gives a polynomial in $gamma$ whose top coefficient is exactly $Q(a_1, dots, a_k)$. For example, with $Q(a, b) = a b$:


$ (gamma a + h'_1)(gamma b + h'_2) = gamma^2 dot a b + gamma dot (a h'_2 + h'_1 b) + h'_1 h'_2 $

Here the top coefficient is $a b = Q(a, b)$, and the other two, $a h'_2 + h'_1 b$ and $h'_1 h'_2$, contain pads. Generalizing this, for any homogeneous $Q$ of degree $d$, the top coefficient is always $Q(a_1, dots, a_k)$, and the other $d$ coefficients, which we'll call $x_0, dots, x_(d-1)$, all involve pads:

$ Q(overline(gamma a_1),dots,overline(gamma a_k)) = &gamma^d dot Q(a_1, dots, a_k) \
&+ thick gamma^(d-1) dot x_(d-1) + dots + gamma dot x_1 + x_0
$

$x_0, dots, x_(d-1)$ don't depend on $gamma$, so the prover can compute them in advance and send them, padded, before the verifier picks $gamma$. They play the same role as $x$ in the naive idea, but now, since they're sent before $gamma$ is chosen and only appear on lower powers of $gamma$, they can't be used to cancel out a lie in $c$.

Swapping in the prover's claim $c$ for $Q(a_1, dots, a_k)$, the verifier's check becomes:

$ gamma^d dot c + gamma^(d-1) dot x_(d-1) + dots + gamma dot x_1 + x_0 = Q(overline(gamma a_1),dots,overline(gamma a_k)) $<linhomopolyclaim>

The left-hand side is linear in the secret values $c, x_0, dots, x_(d-1)$, since the verifier knows $gamma$. The right-hand side is a public number, since the verifier knows every $overline(gamma a_i)$. So this is now a linear check, which the verifier can turn into a claim about the pads like any other!

*To summarize*, to prove $c = Q(a_1, ..., a_k)$, the prover/verifier do the following:

1. The prover computes $x_0, dots, x_(d-1)$ and sends $overline(x_0), dots, overline(x_(d-1))$.
2. The verifier sends a random $gamma in FF$.
3. The prover sends each $overline(gamma a_i) = gamma dot a_i + h'_i$.
4. The verifier saves the linear claim @linhomopolyclaim, plus one linear claim $gamma dot a_i + h'_i = overline(gamma a_i)$ for each $i$, to make sure the prover sent the $overline(gamma a_i)$'s honestly.#s[Each $a_i$ was already sent padded as $overline(a_i) = a_i + h_i$, so substituting gives the pad claim $h'_i - gamma h_i = overline(gamma a_i) - gamma overline(a_i)$.]


*Why is this sound?* If $c != Q(a_1,dots,a_k)$, the two sides of @linhomopolyclaim are _different_ polynomials of degree $d$ in $gamma$, whatever $x_j$'s the prover sent, and so they agree with probability at most $d\/abs(FF)$ by Schwartz-Zippel. Note this is a new way for a cheating prover to get lucky that the non-ZK version didn't have. Going zero-knowledge costs us a little soundness!

*Why is it zero-knowledge?* All sent values derived from secret values are masked by fresh pads, and so via @onetimepad, they are uniformly random and the verifier learns nothing.


== Proving claims about pads <padclaims>

By the end of a proof, the verifier is sitting on a big pile of claims about the pads, each of the @linform form:

$ sum_x L(x) dot P(x) = b  $

Let's now discuss how we'll actually prove these. Looking at the form of these claims, we can quickly tell we'll want to use sum-check somehow to prove this, as it's just an elementwise product of two tables, $L$ and $P$. But we can't just use sum-check as is, the back-and-forth messages that sum-check requires would leak information about the pads, and we can't mask those or we'll just keep recursively generating more and more pad claims.

*Instead of masking the sum-check's messages, we'll mask the pads themselves, all at once.* A masked table looks like pure noise (@onetimepad), so we can prove things about it without masking any of the messages involved. So back at the very start of the proof, alongside $P$ we'll also have the prover commit to a table $Z_P$ of uniformly random masks, the same size as $P$, which it never uses anywhere else.

Thus, to prove some claim $ sum_x L(x) dot P(x) = b$, we just run the following protocol:

1. The prover sends $b_Z = sum_x L(x) dot Z_P (x)$
2. The verifier sends a random $chi in FF$
3. The prover proves the following with standard, non-ZK sum-check:
   $ sum_x L(x) dot underbrace(chi dot P(x) + Z_P (x), Y(x)) = chi dot b + b_Z $<padclaimfinal>
4. The sum-check ends needing $tilde(L)(r')$, which the verifier computes itself, and $tilde(Y)(r')$, which the prover proves by opening $Y$ at $r'$. It never opens $P$ on its own, since $tilde(P)(r')$ would leak information about the pads.#s[$Y$ isn't committed itself, but if $P$ and $Z_P$ are committed with the same column positions, then by linearity (@rslinear), each column of $Y$'s encoding is just $chi$ times $P$'s column plus $Z_P$'s. So the verifier can combine the opened columns itself and run an ordinary opening.]

*Why is this sound?* Let's rearrange @padclaimfinal like so:

$ chi dot (sum_x L(x) dot P(x) - b) + ( sum_x L(x) dot Z_P (x) - b_Z ) = 0 $

Notice that if the prover is lying, and thus $ sum_x L(x) dot P(x) != b$, the left-hand side is a non-zero polynomial of degree $1$, so by Schwartz-Zippel, it's zero with probability $<= 1\/abs(FF)$.

*Why is this zero-knowledge?* Everything the verifier sees in step 3 is computed from $chi dot P + Z_P$, and since $Z_P$ is uniformly random and never used anywhere else, those values are uniformly random too (@onetimepad), and the verifier learns nothing about $P$.#s[And $b_Z$ doesn't help either: given $Y$, it's just $sum_x L(x) dot Y(x) - chi dot b$, which the verifier could compute itself.]

=== Merging pad claims <mergingpad>

Proving every pad claim this way would be very expensive, though. Each claim would need its own sum-check and opening, and worse, its own mask table $Z_P$, since a mask can only be used once. *Luckily, we can merge them all into one*, exactly like in @mergingclaims: each pad claim is a public-weighted sum of the same table $P$, so the verifier draws a random weight $kappa_c$ for each claim $c$, and they squash into the single claim:

$ sum_x underbrace(sum_c kappa_c dot L_c (x), L^star (x)) dot P(x) = underbrace(sum_c kappa_c dot b_c, b^star) $<oneequation>

which, with high probability, only holds if every claim does. It's of the same form as before, so the prover proves it with the protocol above, *once*, with a single $Z_P$.



Each of the challenges we've added along the way ($gamma$, $chi$ and the $kappa_c$'s, plus $beta$ in @zkcommitments) gives a cheating prover one more small chance to get lucky, at most $d\/abs(FF)$ each. So zero-knowledge isn't quite free, but over a big enough field the cost is negligible.


*So all the verifier ever learns is that every claim about the pads holds.* That means we can make any of our tools zero-knowledge by masking every value it sends with pads, and leaving behind only claims about the pads instead of checks.

#wideblock[#figure(
  image("figures/zk_chain.svg", width: 100%),
caption: [The proof from @fig-claim-chain, made fully zero-knowledge. Intermediate claims stay hidden, committed tables only get ZK openings (@maskedopenings), and everything leaves behind claims about the pads, which get proven together at the end.],
) <fig-zk-chain>]

== ZK commitments <zkcommitments>


Ligero-PC openings leak in two ways we haven't dealt with yet: through the $t$ *columns of $E$* the prover reveals for the column check, and through *the row $G_r_"row"$* it sends.

We can't make the column reveal ZK with pads. The verifier hashes them to check them against the Merkle root, so it needs exactly the data that was committed. And unlike the verifier's other checks, a Merkle check isn't algebra: the hash of a padded column has nothing to do with the hash of the real one, so there's no way to turn it into a claim about pads. So to hide the columns, we'll need to change what gets committed in the first place.

While we're at it, we'll also hide the row $G_r_"row"$ the prover sends this way. We _could_ pad it, but that would take $W$ pads for every opening, whereas a mask hidden inside the commitment costs just one extra row.

Let's start with the columns.

=== Masking the RS codewords of $E$

Each opened column contains a codeword entry of _every_ row, so it leaks a little about each one. One naive idea to make this ZK would be to add random noise to $E$ directly (i.e. mask it), but then its rows wouldn't be valid RS codewords anymore, and thus the column check would fail. *Instead, we'll need to add the randomness _before_ RS encoding.*

Specifically, before encoding, the prover extends each row $m$ of $G$ with a random _tail_ $u = [u_0, ..., u_(tau - 1)]$ of $tau$ extra coefficients, so instead of $P_m$ it encodes $P_(m concat u)$:

$   P_(m concat u) (X)  = underbrace(P_m (X), "the row") + underbrace(X^W dot P_u (X), "random tail") $

where $m concat u = [m_0, ..., m_(W - 1), u_0, ..., u_(tau - 1)]$ is the _concatenation_ of $m$ and $u$. So every row of $E$ is still a valid RS codeword, just of a row with $W + tau$ values instead of $W$. Linearity still holds, so the *column check still works*, and *the value check just ignores the tail*, folding only the first $W$ entries of the row the prover sends.

#figure(
  image("figures/zk_commit.svg", width: 100%),
  caption: [Committing to a table $g$, laid out as a matrix $G$, with a mask row $Z$ and random tails $u$.],
) <fig-zk-commit>

*Is this zero-knowledge?* Yup! Each codeword entry is now the row's value plus the tail's value at that point, so the tail acts as a mask (@onetimepad). The catch is that these masks all come from the same $tau$ random coefficients, so they aren't independent.#s[E.g. with $tau = 1$, the tail at $x$ is $x^W dot u_0$. That's a fine mask alone, but at any second point it's a fixed multiple of the first, so two opened entries can cancel it.] Being handwavy here, we can think of each random coefficient as having enough randomness to mask one entry. Formally, this is because a random polynomial with $tau$ coefficients is #link("https://en.wikipedia.org/wiki/K-independent_hashing")[_$tau$-wise independent_]. This means as long as at most $tau$ distinct columns are ever opened, they reveal nothing about the row.#s[Except at $X = 0$, so the evaluation points must avoid $0$.] This is another reason why we generally want to merge all claims about a table into one (@mergingclaims), so only one set of $t$ columns is ever revealed, keeping us well under $tau$.

The cost is that rows now have $W + tau$ values, so with rate $rho$ the codewords grow from $W\/rho$ to $(W + tau)\/rho$ entries, which means *more data for the prover to encode, hash and store.*

#note[Each Merkle leaf should also be hashed with some random bytes (a _salt_), otherwise the verifier could guess and check columns against the tree.]

=== Masking rows sent during openings, i.e. $G_r_"row"$ <maskedopenings>

Tails hide the opened columns, but the verifier still sees the row $G_r_"row"$ itself. As we saw, padding it would take $W$ pads per opening, so instead we'll hide it with a single mask row, committed alongside the data.

Before committing, we'll have the prover append an extra row#s[Technically a few rows, not one, because a single base field row isn't random enough to hide values from an extension field (@extensionfields). See #link("https://eprint.iacr.org/2024/1037")[Haböck and Al Kindi (2024)] for more.] $Z$ of uniformly random masks to $G$, which gets a tail, and is encoded and committed like every other row.#s[Even though $Z$ is already random, it needs a tail. $G_r_"row"$'s tail is a weighted sum of the data rows' tails, so sending it unmasked would expose a combination of the very randomness hiding the opened columns. $Z$'s tail hides it.] Now, to open $tilde(g)(r) = v$:

  1. The prover sends $overline(v) = v + h_1$ and $overline(z) = z + h_2$, where $z = tilde(Z)(r_"col")$.#s[As usual, $h_1, h_2$ are fresh pads.]
  2. The verifier sends a random $beta in FF$.
  3. The prover sends $G^"masked"_r_"row" = G_r_"row" + beta dot Z$ instead of $G_r_"row"$.#s[Tails included, so $W + tau$ entries. As above, the value check folds only the first $W$ and the column check encodes all of them.]
  4. *(Value check)* The verifier folds $G^"masked"_r_"row"$ by $r_"col"$, and the result should be $v + beta z$.#s[Folding is just a weighted sum of the cells (@evalweightedsum), so folding $G_r_"row" + beta dot Z$ gives whatever $G_r_"row"$ folds to (a.k.a. $v$), plus $beta$ times what $Z$ folds to (a.k.a. $z$).] It can't check this directly, but substituting $v = overline(v) - h_1$ and $z = overline(z) - h_2$ turns it into a linear claim about the pads (@linearclaims), which it records.
  5. *(Column check)* As before, but treating $Z$ as one more row with weight $beta$, i.e.:
    $sum_(x_"row") ("eq"_(r_"row")(x_"row") dot E(c, x_"row")) + beta dot E(c, Z) = "Enc"(G^"masked"_r_"row")(c) $

    
#wideblock[#figure(
  image("figures/zk_open_steps.svg", width: 100%),
  caption: [Interactively proving $tilde(g)(r) = v$ via a Ligero-PC opening with $G_r_"row"$ masked.],
) <fig-zk-open-steps>]

*Why do we need $beta$?* Without it, the value check would just be "$G^"masked"_r_"row"$ folds to $v + z$", and nothing checks $z$ against the committed $Z$, so a cheating prover could claim whatever $v$ it wants and pick a $z$ to make up the difference. Adding the random challenge $beta$ fixes this, since the verifier only sends it _after_ the prover has locked in $v$ and $z$ (by sending them padded), so the prover can't choose a $z$ that perfectly cancels a fake $v$. The column check then forces $G^"masked"_r_"row"$ to fold to $v_"true" + beta dot z_"true"$, so a fake $v$ only passes if $beta$ happens to make the two lies cancel exactly, which happens with probability at most $1\/abs(FF)$.#s[This is via the Schwartz-Zippel lemma again, as in @identitytest.]


*Is this zero-knowledge?* Yes! By @onetimepad, $G^"masked"_r_"row"$ is just $G_r_"row"$ plus a uniformly random row, so it's uniformly random too.#s[Okay, technically not _completely_ random, as it must fold to $v + beta z$. But the verifier never learns $v + beta z$, and even if it did, $z$ is random and hides $v$.] And $v$ itself stays hidden by its pad, so unlike in a plain opening, the verifier never even learns the value it opened.#s[In practice, $v$ often isn't sent at all: it only appears inside a claim together with pads, and the mask row's part ($z$) is sent without any padding. The opening and the proof of the pad claims then happen in one step, with one challenge blinding both the data rows and the pads.]

= Fiat-Shamir <fiatshamir>

So far, every tool we've introduced requires the verifier to be in communication with the prover to complete the proof. In some circumstances this kind of _interactive proof_ is fine, but to satisfy the "N" in ZK-SNARK, we want our proofs to be _non-interactive_. With _non-interactive_ proofs, anyone in the world can verify them after the fact, and they can more easily be generated under tight latency constraints as we don't need to wait for messages from the verifier.

*So, do we have to throw out all our tools and try to think of some new non-interactive ones?* Luckily, no, thanks to a simple trick called the _Fiat-Shamir transformation_#s[From Fiat and Shamir (1986).] which turns any interactive proof into a non-interactive one.

The idea is really simple: at any point where we'd normally wait for the verifier to send a random challenge, *just hash everything the verifier would have seen so far and use that as the challenge*. Anyone can later recompute the exact same hashes themselves, even if they weren't there at generation time.

#wideblock[#figure(
  image("figures/fiat_shamir.svg", width: 100%),
  caption: [Fiat-Shamir replaces each random challenge with a hash of everything sent so far.],
) <fig-fiat-shamir>]

*Why does this work?* Each challenge is a hash of the prover's earlier messages, so changing any of those messages changes the challenge too. And since a good hash function is unpredictable, the prover can't know what challenge it'll get until it has already settled on its messages, just like in the interactive version.#s[This is why it's critical that we hash _everything_ a challenge is meant to test. If some value the prover can choose isn't hashed, the challenge doesn't depend on it, so the prover can compute the challenge first and then pick that value to pass whatever check the challenge feeds into. Getting this wrong has broken real proof systems, see #link("https://eprint.iacr.org/2023/691")[Dao et al. (2023)].] 

*There's just one big issue: _grinding_.* Against a live verifier, a cheating prover only gets one shot per challenge. But against a hash, it can just keep tweaking its message over and over offline until a challenge happens to land somewhere lucky. Specifically, if each attempt succeeds with probability $epsilon$, then $q$ attempts succeed with probability up to about $q dot epsilon$.#s[This assumes the hash behaves like a truly random function, a.k.a. the #link("https://en.wikipedia.org/wiki/Random_oracle")[_random oracle model_].]

For a degree-$2$ round polynomial over the Goldilocks field, $epsilon approx 2^(-63)$, so an attacker who can afford $2^60$ hashes (the Bitcoin network does $approx 2^70$/s) can succeed at cheating with probability  $approx 1\/8$, yikes! This is one of the main reasons *why we draw challenges from an extension field* (@extensionfields), as e.g. over $FF_(p^2)$ the chance of success even after $2^60$ attempts is only $approx 2^(-67)$.



= Putting it all together

That's all the tools we need! It might seem limiting to have to express everything in terms of tables and matrices, but they're actually enough to prove arbitrary computation. This is because any program can be rewritten as an _arithmetic circuit_, a DAG of addition and multiplication gates, and circuits are easy to prove with our tools: each layer's wire values become a table and each gate becomes an elementwise polynomial relation (@elementwisepoly).#s[Circuits are usually expressed as an #link("https://www.rareskills.io/post/rank-1-constraint-system")[_Rank-1 Constraint System (R1CS)_], which is just three matrix products and one elementwise product, provable via the tools from @matmul and @elementwisepoly.] Some operations make for awkward (and thus expensive) circuits though, like comparisons or bit manipulation, and for those we reach for lookups instead (@nonpoly).

To recap how the pieces fit together into one proof:

+ The prover *commits* to every table that can't be justified any other way (the inputs, lookup helpers like $m$, $u$ and $v$, outputs of non-polynomial operations) and its pads (@pads), using Ligero-PC (@pcs) with tails and mask rows so the commitments don't leak data about the tables (@zkcommitments).
+ Starting from a claim about the output at a random point, it works backwards through the computation. For every elementwise relation or matrix product, a *sum-check* turns claims about the operation's output into claims about its inputs (@elementwisepoly), while *lookups* take care of operations that aren't polynomials (@nonpoly).
+ Every value the prover reveals along the way is masked with *pads* to randomize them and keep the proof zero-knowledge. Every check on those values the verifier would normally make is turned into a claim about the pads instead (@pads).
+ Claims that pile up on the same committed table get *merged* (@mergingclaims), so each table only gets opened once.
+ At the very end, all the claims about the pads get merged into one megaclaim and proven in one go (@padclaims).
+ And every random challenge is just a hash of everything sent so far (@fiatshamir), so the whole thing is a single proof file that anyone can check later.

The result is _succinct_, since the verifier only ever checks a few short sum-checks and a handful of opened columns, _sound_, since a cheating prover only gets through if it gets very lucky with one of the random challenges, _zero-knowledge_ and _non-interactive_. LFG, we made a ZK-SNARK!


= Commitments at scale <commitmentsatscale>

The tools above really are all we need to build a ZK-SNARK. However, for tables that are really big (\~terabytes), and/or get opened across many proofs, our commitments need a few extra tricks to be practical for real world deployments.

== Recursive openings <recursiveopenings>

Recall that for a Ligero-PC opening on a table $g$, the prover must send both the row $G_r_"row"$ ($W$ field elements) and $t$ opened columns ($R$ field elements each) to the verifier. Since $W dot R$ is fixed at $2^ell$ by construction, the sizes of the row and the columns trade off against each other. For large tables (e.g. $2^40$ cells), no matter how we balance $W$ and $R$, we'll be sending _hundreds of megabytes_ to the verifier for each opening!#s[For example, with $t = 256$ the best balance is a row of $2^24$ cells. Its cells are extension field elements (@extensionfields), so that's about $256$ MB for the row alone.]

But notice that the row and the columns aren't checked in the same way. For columns, the verifier must hash them against the commitment's Merkle root, so it truly needs the columns' full contents. *But the row is only checked via arithmetic, and we have a lot of tools to reduce arithmetic checks down into statements that are cheaper to verify... so maybe we can avoid sending the row?*

Observe that the two checks we do on $G_r_"row"$ are both checks on a weighted sum of its cells, with public weights:

+ *The value check:* Folding $G_r_"row"$ by $r_"col"$ is a weighted sum with weights $"eq"_(r_"col")$.
+ *The column check:* $"Enc"(G_r_"row")(c)$ is $P_(G_r_"row")(z_c)$, the row's polynomial evaluated at column $c$'s point (see @reedsolomon for a refresher), which looks like:
  $ P_(G_r_"row")(z_c) = (G_r_"row")_0 dot 1 + (G_r_"row")_1 dot z_c + dots + (G_r_"row")_(W-1) dot z_c^(W-1) $
  This is a weighted sum of the row's cells, where cell $j$ has weight $z_c^j$.

Right now, the verifier computes these sums itself, from the row it was sent. But we can check a weighted sum of a _committed_ table without ever seeing it, since a sum-check reduces it to a single opening (see the end of @mergingclaims). *So what if the prover committed to $G_r_"row"$ as a new table, $eta$, instead of sending it?* The verifier could then check those weighted sums against the commitment, without ever having to be sent the full row. 

Concretely, to prove $tilde(g)(r) = v$:

+ The prover commits to $eta$, which is just $G_r_"row"$ laid out as a matrix.
+ The verifier then picks $t$ columns of $E$, and the prover opens them as usual.
+ The value check and the $t$ column checks become claims about $eta$, which are merged into one (@mergingclaims) and sum-checked, leaving a claim about $tilde(eta)$ at a random point.#s[#note[To finish the sum-check, the verifier also needs to evaluate the merged weights' extension at the random point itself (@mergingclaims). That's cheap, since both kinds of weights have extensions with a product formula. For $"eq"_(r_"col")$ it's the one in @eqtable, and for the column checks' weights $z_c^j$ it's:

$ product_(i = 1)^(log W) ((1 - r'_i) + r'_i dot z_c^(2^(i - 1))) $]]
+ That claim is resolved with an opening of $eta$.

But step 4 is an opening too, which means sending a row again. The difference is that $eta$ is far smaller than $g$, so a row from it is much shorter. If it's still not small enough, *we can repeat this trick as many times as we need*, committing to $eta$'s row instead of sending it, opening that, etc etc.

#wideblock[#figure(
  image("figures/recursive_open.svg", width: 100%),
   caption: [A recursive opening of $g$, with three levels of recursion.],
) <fig-recursive-open>]

This is a bigger deal than it might seem! Since the original table's row is never sent, its size barely matters, so *we can lay out $G$ very wide and short, which makes the columns tiny too*. The same goes for $eta$ and every table after it! Together, this lets us shrink the whole opening down to a few short columns from each commitment, a sum-check for each new table, and one small row at the very end. For a $2^40$-cell table, that's around a megabyte with recursive openings, versus hundreds of megabytes without.

*Does this cost us any soundness?* Yes, but just a little. Each level of recursion gives a cheating prover the same chances to get lucky as a normal opening (@openings), plus a merge and a sum-check. So a recursive opening with $L$ levels is about $L+1$ times as likely to be fooled as a non-recursive one.#s[Specifically, if level $k$'s commitment (with $g$'s at $k = 0$) has $R_k$ rows, $2^(ell_k)$ cells, codewords of length $M_k$ and $t_k$ opened columns, a false claim passes with probability at most:

  $ sum_(k = 0)^L ((1 - delta)^(t_k) + (rho + delta)^(t_k))  \ + sum_(k = 0)^L (log_2 R_k dot M_k) / abs(FF) + sum_(k = 1)^L (2 ell_k + 1) / abs(FF) $

  Here the first two sums are each commitment's own opening error (@openingsoundnessproximity), and the last sum is the merge ($1\/abs(FF)$) and the sum-check ($2 ell_k\/abs(FF)$) at each level $k$.] We can just open a few more columns per level to make up for this.

*What about zero-knowledge?* In a zero-knowledge opening (@maskedopenings), the row the prover sends is the masked one, $G^"masked"_r_"row"$, which is uniformly random (@onetimepad). With recursion, that masked row is what gets committed as $eta$. So everything the later levels reveal is computed from random noise and public challenges, and tells the verifier nothing about $g$. *So only the first level needs to be zero-knowledge,* and every level after can be a plain non-ZK opening.

== Refreshing commitments <manyopenings>

Some tables are ephemeral, committed only for one proof and then never used again. Others might get committed once and then used over and over across many proofs. *The zero-knowledge commitments we've constructed can't hide a table forever though*, since the random tails we added in @zkcommitments only hide the table while at most $tau$ distinct columns have been opened, and every opening reveals some new random columns. Once a commitment hits that limit, it's no longer safe to open, and we need to make a new one to "refresh" it.#s[Recursive openings (as described above in @recursiveopenings) make long tails cheap, so $tau$ can be huge, and once a table's first opening has shown it's close to RS codewords, later openings only need a few columns each. But on a long enough time scale, we'll hit the limit _eventually_.]

*But how can a verifier trust that our new commitment holds the same underlying table?* With a _link_ proof! Say the old commitment is of $g$ and the new one is of $g'$, with fresh tails. To prove $g = g'$, the verifier picks a random point $r$, opens both commitments at it (@openings), and checks that the two opened rows fold to the same value.#s[This is just the identity test (@identitytest) on $g$ and $g'$. Only the first $W$ cells of each row get folded, since their tails are different on purpose. In practice these are ZK openings (@maskedopenings), so the comparison becomes a claim about the pads (@padclaims).] 

#note[The old commitment is already known to be close to RS codewords, so just a few of its columns are enough. The new one hasn't been opened before, so the verifier opens lots of its columns to show it's close to RS codewords too.]

To trust a new commitment, the verifier has to check every link between it and the original. So rather than linking each new commitment to the one before it, which makes the path longer with each additional commitment, the *prover links all new commitments straight to the first one* (the _root_ commitment), which gets one big opening up front to show it's close to RS codewords, and serves as the table's single, permanent source of truth.

#figure(
  image("figures/refresh_star.svg", width: 100%),
  caption: [A root commitment and its refreshes.],
) <fig-refresh>

#note[Each link spends a few of the root's columns, so a root can only be linked to so many commitments. If that's not enough, we can link new commitments to other commitments below the root, forming a _tree of commitments_. Every extra layer multiplies how many commitments we can have, but only adds one more link for the verifier to check. In practice, one layer is usually plenty.]