\section{Thinning Algorithms}

Consider again our generic problem speficication: |max_unlhd . foldR f e|.
For many problems, the monotonicity condition \eqref{eq:monotonicity} is a lot to demand --- it is not always the case that |f| satisfies \eqref{eq:monotonicity} with respect to |unlhd|.
It is more common that |f| satisfies \eqref{eq:monotonicity} with respect to some other ordering, say, |preceq|, a stronger variation of |unlhd|.
The catch, however, is that |preceq| is not total.
The Greedy Theorem still holds, but refines the specification to a monadic program that does not return results for most if not all inputs.
For such situations we need another theorem.

Let us look at an example.

\subsection{Example: 0-1 Knapsack}
\label{sec:ex:0-1-knapsack}

In the famous \emph{0-1 knapsack} problem, we are given a collection of items, each having a value and a weight --- for simplity we assume that both are natural numbers.
The aim is to choose a subset of these items such that the total value is maximised, while the total weight does not exceed a given weight limit |w|
(it is assumed that |w| is non-negative).
Let |Val|, |Wgt| respectively denote the types of values and weights.
The input can be abstractly represented as a list of pairs |List (Val, Wgt)|.
Also, define:
\begin{spec}
val  = sum . map fst {-"~~,"-}
wgt  = sum . map snd {-"~~."-}
\end{spec}
The function |subseq| non-deterministically computes a subsequence of the input list:
\begin{spec}
subseq :: List a -> P (List a)
subseq []      = return []
subseq (x:xs)  = subseq xs <|> ((x:) <$> subseq xs) {-"~~."-}
\end{spec}
For example, |subseq "abc"| returns
the empty string |""|, |"c"|, |"b"|, |"bc"|, |"a"|, |"ac"|, |"ab"|, and |"abc"|.
The function |subseq| can also be written as a |foldR|:
\begin{spec}
subseq = foldR subs (return []) {-"~~,"-}
  where subs x y = return y <|> return (x:y) {-"~~."-}
\end{spec}

Having the ingredients ready, the \emph{0-1 knapsack} problem can be specified by:
\begin{spec}
knapsack :: List (Val, Wgt) -> P (List (Val, Wgt))
knapsack = max_leqv . (filt ((w >) . wgt) <=< subseq) {-"~~."-}
\end{spec}
where |xs `leqv` ys = val xs <= val ys|.

%format subsw = "\Varid{subs}_{w}"
\paragraph*{Fusion.}~
To transform to the specification to our generic form, we try to fuse |filt ((w >) . wgt) <=< subseq| into one |foldR|.
Accroding to the |foldR| fusion rule \eqref{eq:foldRFusion}:
\begin{equation*}
  |foldR g (h e) `sse` h . foldR f e {-"~"-}<=={-"~"-} g x =<< h m `sse` h (f x =<< m) {-"~~,"-}|
\end{equation*}
if we manange to construct some function |subsw| that satisfies the fusion condition:
\begin{equation}
 |subsw x =<< (filt ((w>).wgt) =<< m) {-"~"-}`sse`{-"~"-} filt ((w>).wgt) =<< (subs x =<< m) {-"~~,"-}|
 \label{eq:filtSubseqFusionCond}
\end{equation}
we will have
\begin{spec}
  foldR subsw (return []) {-"~"-}`sse`{-"~"-} filt ((w >) . wgt) <=< subseq {-"~~."-}
\end{spec}
(For the second argument to |foldR|, |filt ((w >) . wgt) [] = return []| holds because |w| is non-negative.)
To construct |subsw|, one may start from the righthand side of \eqref{eq:filtSubseqFusionCond} and try to distribute |filt ((w>).wgt)| inside until it is applied to |m|.
One will eventually construct:
\begin{spec}
  subsw x ys = return ys <|> filt ((w>).wgt) (x:ys) {-"~~."-}
\end{spec}
The details are left to the reader as an exercise. The specification is now:
\begin{spec}
  knapsack = max_leqv . foldR subsw (return [])  {-"~~."-}
\end{spec}

\paragraph*{Failing Monotonicity.}~
It turns out, however, that |subsw| does not meet \eqref{eq:monotonicity} with respect to |geqv|.
To see that, let us construct a counter example.
For the convenience of our readers, we recite and instantiate \eqref{eq:monotonicity} here:
\begin{equation*}
\setlength{\jot}{-1pt}
\begin{aligned}
|do|~ & |(ys1, ys0) <- any|\\
      & |filt geqv (ys1, ys0)|\\
      & |zs0 <- subsw x ys0| \\
      & |return (ys1, zs0)|
\end{aligned}
~~|`sse`|~~
\begin{aligned}
|do|~& |(ys1, zs0) <- any|\\
     & |zs1 <- subsw x ys1|\\
     & |filt geqv (zs1, zs0)|\\
     & |return (ys1, zs0)| \mbox{~~.}
\end{aligned}
\tag{\ref{eq:monotonicity}'}
\end{equation*}
Let the weight limit |w| be |10|.
Consider the lefthand side.
Among all the possible values of |ys1| and |ys0|, we pick |ys1 = [(5,8)]| and |ys0 = [(4,6)]|,
for which we do have |ys1 `geqv` ys0|.
With |ys0| being a lesser solution, if (\ref{eq:monotonicity}') holds, we could use a greedy algorithm, dropping |ys0| and keeping only |ys1|.
Let |x = (3,3)|.
The two possible values of |zs0| are |[(4,6)]| and |[(3,3),(4,6)]|.
The inclusion demands that |(y1, z0)| be a result of the righthand side as well.
In particular, the righthand side must be able to yield |([5,8], [(3,3),(4,6)])| as a result.
However, with |ys1| fixed as |[(5,8)]| on the righthand side, the only possible value of |zs1| is |[(5,8)]| --- since |[(3,3),(5,8)]| exceeds the weight limit!
And we do not have |[(5,8)] `geqv` [(3,3),(4,6)]|.
Therefore (\ref{eq:monotonicity}') fails.

Notice that, comparing to traditional arguments using first-order logic, in the reasoning above we have expressions to execute with.
Notice also how the |return (ys1, zs0)| on the lefthand side forces the value of |ys1| and |zs0| on the righthand side.

The lesson we have just learned is that we cannot throw away a solution, such as |[(4,6)]|, simply because it is not the most valuable.
In fact, one may want to keep |[(4,6)]| for its being lighter, which implies potential for adding more items later.
Meanwhile, if a solution is neither more valuable, nor lighter, we may safely drop it without losing anything.
This observation inspires us to use the following ordering:
\begin{spec}
xs `leqvw` ys = val xs <= val ys && wgt xs >= wgt ys {-"~~,"-}
\end{spec}
One may prove that |subsw| is indeed monotonic on |geqvw|.
However, |leqvw| is not connected. For example, neither |[(10,9)] `leqvw` [(9,10)]| nor |[(10,9)] `geqvw` [(9,10)]| holds, and |max_leqvw| |{[(10,9)], [(9,10)]}| yields the empty set.
Therefore, while one may apply the Greedy Theorem to |max_leqvw . | |foldR subsw (return [])|, it does not give us a useful algorithm.

Instead, one may use a different strategy: let the |foldR| maintain, in some data structure, a collection of solutions that might be useful, while those that are definitely not going to contribute to the final solution can be disposed of.
For example, if at one point the algorithm computes a collection of solutions
|{[(5,8)],[(4,6)], [(4,8)]}|, the solutions |[(5,8)]| and |[(4,6)]| must be kept because we do not yet know which will contribute to the final solution.
Meanwhile, |[(4,8)]|, which is less valuable than |[(5,8)]| and heavier |[(4,6)]|, need not be kept.
This process of ``keeping useful solutions, while possibly dropping those useless ones'' is called \emph{thinning} in the terminology of \citet{BirddeMoor:97:Algebra}.

Note our wording: |[(4,6)]| need not be kept, but it does not mean that we \emph{have to} drop it.
An algorithm should have the flexibility of deciding how much thinning it needs to do.
Doing a full thinning keeps the set of solutions small, but could be time consuming,
and it may be beneficial to remove some but not all of the useless solutions.
Our specification of a thinning algorithm should allow such flexibility.

\subsection{Overview of Thinning}

We assume a data structure |T| used to store potentially useful partial solutions.
Conceptually, |T a| is just a set of |a|'s.
It could be implemented as a list, a tree, an array... the choice of implementation is problem-specific and often crucial to the efficiency of the algorithm.
We assume two operators:
\begin{spec}
mem      :: T a -> P a {-"~~,"-}
collect  :: P a -> T a {-"~~,"-}
\end{spec}
where |mem| non-deterministically yields an element in |T|, while |collect m| collects the results of |m| and stores them in the data structure |T|.
Both |T| and |P| represent sets. If we let |T = P|, we would have |mem = collect = id|, and some notations could be much simplified.
However, we prefer to treat |T| and |P| as different types, since they serve different purposes: |P| denotes non-determinism, while |T| denotes a \emph{finite} collection of potential solutions.

Given a preorder |preceq| on some type |b| that is not necessarily connected, and a table |xs :: T b|,
|thinT_preceq xs| computes a table that is possibly smaller, but still contains necessary elements that leads to an optimal solution.
There could be many such tables, therefore we let |thinT_preceq| have type |T b -> P (T b)|. It non-deterministically computes a table that meets the following criteria :
\begin{equation}
|ys `inn` thinT_preceq xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall x `inn` xs : (exists y `inn` ys : y `succeq` x)) {-"~~."-}|
\label{eq:thin-def-set}
\end{equation}
That is, |thin_preceq xs| contains all the table |ys| that is a sub-table of |xs|
(we overload the subset relation |(`sse`)| to tables), and for every element in |xs| there exists some element in |ys| that is at least as good.
The monadic function |thin_preceq| can be seen as a specification that contains all possible ways to thin a table,
of which the actual algorithm that maintains the table is a refinement.
The algorithm may aggressively remove all candidates that are not needed in each step.
It may also remove some but not all the redundant candidates, if that turns out to be more efficient.
In particular, |xs| itself is in |thin_preceq xs|, meaning that the algorithm may sometimes just keep the table unchanged.

Property \eqref{eq:thin-def-set} can be wrapped into the following universal property:
for all |f :: a -> P b| and |h :: a -> P (T b)|,
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
|h `sse` thinT_preceq . collect . f |\mbox{~~}|<==>|&\mbox{~~} |(mem <=< h) `sse` f &&|\\
&
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |t1 <- h x| \\
       & |y0 <- f x| \\
       & |return (t1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(t1, y0) <- any| \\
       & |y1 <- mem t1| \\
       & |filt succeq (y1, y0)|\\
       & |return (t1, y0)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:thin-univ-monadic}
\end{split}
\end{equation}
%if False
\begin{code}
propThinUniv :: forall a (b :: Type) . (a -> P (T b)) -> (a -> P b) -> a -> P (T b)
propThinUniv h f =
    h `sse` thin_Q . collect . f
 where pre0 = (mem <=< h) `sse` f
       pre1 = (do x <- any
                  t1 <- h x
                  y0 <- f x
                  return (t1, y0)) `sse`
               (do (t1, y0) <- any
                   y1 <- mem t1
                   filt_Q (y1, y0)
                   return (t1, y0))
\end{code}
%endif
The monadic inclusion in the big bracket encodes the existential quantification:
for all table |t1| returned by |h|, and for all |y0| returned by |f|,
there must exists an elememt |y1| in |t1| such that |y1 `succeq` y0|.
In |thinT_preceq. collect . f|, the results of |f| is collected into a table of type |T b| and passed to |thinT_preceq|.
Since |thinT_preceq| and |collect| often appear together, we will use the following abbreviation.
Given a preorder |(`preceq`)| on some type |b|, define
\begin{spec}
thin_preceq :: P b -> P (T b)
thin_preceq = thinT_preceq . collect {-"~~."-}
\end{spec}

Letting |h := thin_preceq| and |f := id| in \eqref{eq:thin-univ-monadic}, we get
\begin{equation}
    |mem <=< thin_preceq `sse` id|
\end{equation}
Letting |h := thin_preceq . f| in \eqref{eq:thin-univ-monadic}, we get the cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |x <- any| \\
        & |t1 <- thin_preceq (f x)| \\
        & |y0 <- f x| \\
        & |return (t1, y0)|
  \end{aligned}
  |`sse`|~~
  \begin{aligned}
  |do|~ & |(t1, y0) <- any| \\
        & |y1 <- mem t1| \\
        & |filt succeq (y1, y0)|\\
        & |return (t1, y0)|
  \end{aligned}
\end{equation}

|thin| introduction:
\begin{spec}
(max_unlhd . mem) <=< thin_preceq {-"\,"-}`sse`{-"\,"-} max_unlhd
\end{spec}


The thinning theorem is given by:
\begin{theorem}[Thinning Theorem]
\label{thm:thinning}
{\rm Let |preceq| be a binary relation on |b| that is reflexive and transitive,
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |succeq| for all |x|, we have
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
&|foldR (\x -> thin_preceq . (f x <=< mem)) (thin_preceq e) `sse`| \\
& \qquad  |thin_preceq . foldR f e  {-"~~."-}|
\end{split}
\label{eq:thinning}
\end{equation}
}
%if False
\begin{code}
thmThinning :: (a -> b -> P b) -> P b -> List a -> P (T b)
thmThinning f e =
  thin_Q . collect . foldR f e `spse`
    foldR (\x -> thin_Q. collect . (f x <=< mem))
       (thin_Q (collect e))
\end{code}
%endif
\end{theorem}

\subsection{Solving knapsack}

\begin{spec}
         max_leqv . (filt ((w >) . wgt) <=< subseq)
 `spse`    {- |foldR|-fusion -}
         max_leqv . foldR subsw (return [])
 `spse`    {- introducing |thin| -}
         ((max_leqv . mem) <=< thin_preceq) . foldR subsw (return [])
 ===       {- |(f <=< g) . h = f <=< (g . h)|-}
         (max_leqv . mem) <=< (thin_preceq . foldR subsw (return []))
 `spse`    {- thinning theorem -}
         max_leqv . foldR (\x -> thin_preceq . (subsw x <=< mem)) (thin_preceq (return []))
\end{spec}
