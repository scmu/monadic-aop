\section{Thinning Algorithms}

%if False
\begin{code}
module Thinning where

import Prelude hiding (max, any)
import GHC.Base (Alternative, (<|>))
import Control.Monad

import Common
import Prelim
import Greedy
\end{code}
%endif

Consider again our generic problem speficication: |max_unlhd . foldR f e|.
For many problems, wishing that |f| satisfies the monotonicity condition \eqref{eq:monotonicity}
with respect to |unlhd| is asking for a lot.
It is more common that |f| satisfies \eqref{eq:monotonicity} with respect to some other ordering, say, |preceq|, that is a stronger variation of |unlhd|.
The catch, however, is that |preceq| is not total.
The Greedy Theorem still holds, but refines the specification to a monadic program that does not return results for most if not all inputs.
For such situations we need another theorem.

Let us look at an example.

\subsection{Example: 0-1 Knapsack}
\label{sec:ex:0-1-knapsack}

In the famous \emph{0-1 knapsack} problem, we are given a collection of items, each having a value and a weight --- for simplicity we assume that both are natural numbers.
The aim is to choose a subset of these items such that the total value is maximised, while the total weight does not exceed a given weight limit |w|
(it is assumed that |w| is non-negative).
Let |Val|, |Wgt| respectively denote the types of values and weights.
An |Item|, abstractly, is a pair |(Val, Wgt)|, and the input is a list of |Item|s.
Define:
%if False
\begin{code}
type Val = Int
type Wgt = Int
\end{code}
%endif
\begin{code}
type Item = (Val, Wgt)
val  = sum . map fst {-"~~,"-}
wgt  = sum . map snd {-"~~."-}
\end{code}
The function |subseq| non-deterministically computes a subsequence of the input list:
\begin{code}
subseq :: List a -> P (List a)
subseq []      = return []
subseq (x:xs)  = subseq xs <|> ((x:) <$> subseq xs) {-"~~."-}
\end{code}
For example, |subseq "abc"| returns
the empty string |""|, |"c"|, |"b"|, |"bc"|, |"a"|, |"ac"|, |"ab"|, and |"abc"|.
The function |subseq| can also be written as a |foldR|:
%format subseq' = "\Varid{subseq}"
\begin{code}
subseq' = foldR subs (return []) {-"~~,"-}
  where subs x y = return y <|> return (x:y) {-"~~."-}
\end{code}
%if False
\begin{code}
subs x y = return y <|> return (x:y)
\end{code}
%endif

Having the ingredients ready, the \emph{0-1 knapsack} problem can be specified by:
\begin{code}
knapsack :: List Item -> P (List Item)
knapsack = max_leqv . (filt ((w >) . wgt) <=< subseq) {-"~~."-}
\end{code}
where |xs `leqv` ys = val xs <= val ys|.
%if False
\begin{code}
max_leqv :: P (List Item) -> P (List Item)
max_leqv = undefined

thin_leqvw :: P (List Item) -> P (T (List Item))
thin_leqvw = undefined

w :: Wgt
w = undefined
\end{code}
%endif

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
%if False
\begin{code}
filtSubseqFusionCond x m =
  subsw x =<< (filt ((w>).wgt) =<< m) `sse`
   filt ((w>).wgt) =<< (subs x =<< m)
\end{code}
%endif
we will have
\begin{spec}
  foldR subsw (return []) {-"~"-}`sse`{-"~"-} filt ((w >) . wgt) <=< subseq {-"~~."-}
\end{spec}
(For the second argument to |foldR|, |filt ((w >) . wgt) [] = return []| holds because |w| is non-negative.)
To construct |subsw|, one may start from the righthand side of \eqref{eq:filtSubseqFusionCond} and try to distribute |filt ((w>).wgt)| inside until it is applied to |m|.
One will eventually construct:
\begin{code}
subsw x ys = return ys <|> filt ((w>).wgt) (x:ys) {-"~~."-}
\end{code}
The details are left to the reader as an exercise. The specification is now:
%format knapsack' = "\Varid{knapsack}"
\begin{code}
knapsack' = max_leqv . foldR subsw (return [])  {-"~~."-}
\end{code}

\paragraph*{Failing Monotonicity.}~
It turns out, however, that |subsw| does not meet \eqref{eq:monotonicity} with respect to |geqv|.
To see that, let us construct a counterexample.
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
The inclusion demands that the same |(ys1, zs0)| be a result of the righthand side as well.
In particular, the righthand side must be able to yield |([(5,8)], [(3,3),(4,6)])| as a result.
Let us examine the righthand side, assuming that from |any| we draw |ys1 = [(5,8)]| and |zs0 = [(3,3),(4,6)]|.
With this value of |ys1|,
the only possible value of |zs1| is also |[(5,8)]| --- since |[(3,3),(5,8)]| exceeds the weight limit!
And we do not have |[(5,8)] `geqv` [(3,3),(4,6)]|.
Therefore the righthand side cannot return |([(5,8)], [(3,3),(4,6)])|, and thus (\ref{eq:monotonicity}') fails.

Notice that, comparing to traditional arguments using first-order logic, in the reasoning above we have expressions to execute with.
Notice also how the |return (ys1, zs0)| on the lefthand side forces the value of |(ys1, zs0) <- any| on the righthand side.

The lesson we have just learned is that we cannot throw away a solution, such as |[(4,6)]|, simply because it is not the most valuable.
Therefore a greedy algorithm would not work for this problem.
In fact, one may want to keep |[(4,6)]| for its being lighter, which implies potential for adding more items (in our example, |(3,3)|) later.

Meanwhile, if a solution is neither more valuable, nor lighter, we may safely drop it without losing anything.
If the two solution candidates were |[(5,8)]| and |[(4,8)]|, we can safely drop the latter, since any items one may add to |[(4,8)]| may also be added to |[(5,8)]| without exceeding the weight limit |w|.
This observation inspires us to use the following ordering:
\begin{spec}
xs `leqvw` ys = val xs <= val ys && wgt xs >= wgt ys {-"~~."-}
\end{spec}
One may prove that |subsw| is indeed monotonic on |geqvw|.
However, |leqvw| is not connected. For example, neither |[(10,9)] `leqvw` [(9,10)]| nor |[(10,9)] `geqvw` [(9,10)]| holds, and |max_leqvw| |{[(10,9)], [(9,10)]}| yields the empty set.
Therefore, while one may apply the Greedy Theorem to |max_leqvw . | |foldR subsw (return [])|, it does not give us a useful algorithm.

Instead, one may use a different strategy: let the |foldR| maintain, in some data structure, a collection of solutions that might be useful, while those that are definitely not going to contribute to the final solution can be disposed of.
For example, if at one point the algorithm computes a collection of solutions
|{[(5,8)],[(4,6)], [(4,8)]}|, the solutions |[(5,8)]| and |[(4,6)]| must be kept because we do not yet know which will contribute to the final solution.
Meanwhile, |[(4,8)]|, which is less valuable than |[(5,8)]| and heavier |[(4,6)]|, need not be kept.
This process of ``keeping useful solutions, while possibly dropping those useless ones'' is called \emph{thinning} in the terminology of \citet{BirddeMoor:97:Algebra}.

Note our wording: |[(4,8)]| need not be kept, but it does not mean that we \emph{have to} drop it.
An algorithm should have the flexibility of deciding how much thinning it needs to do.
Doing a full thinning keeps the set of solutions small, but the thinning itself could be time consuming,
and it may be beneficial to remove some but not all of the useless solutions.
A general specification of thinning algorithms should allow such flexibility.

\subsection{Thinning}

We assume a data structure |T| used to store potentially useful partial solutions.
Conceptually, |T a| is just a set of |a|'s.
It could be implemented as a list, a tree, an array... the choice of implementation is problem-specific and often crucial to the efficiency of the algorithm.
We assume two operators:
\begin{spec}
mem      :: T a -> P a {-"~~,"-}
collect  :: P a -> T a {-"~~,"-}
\end{spec}
%if False
\begin{code}
mem      :: T a -> P a {-"~~,"-}
mem = undefined
collect  :: P a -> T a {-"~~,"-}
collect = undefined
\end{code}
%endif
where |mem| non-deterministically yields an element in |T|, while |collect m| collects the results of |m| and stores them in the data structure |T|.
Both |T| and |P| represent sets. If we let |T = P|, we would have |mem = collect = id|, and some notations could be much simplified.
However, we prefer to treat |T| and |P| as different types, since they serve different purposes: |P| denotes non-determinism, while |T| denotes a \emph{finite} collection of potential solutions.

Given a preorder |preceq| on some type |b| that is not necessarily connected, and a table |xs :: T b|,
|thinT_preceq xs| computes a table that is possibly smaller, but still contains necessary elements that lead to an optimal solution.
There could be many such tables, therefore we let |thinT_preceq| have type |T b -> P (T b)|. It non-deterministically computes a table that meets the following criteria :
%if False
\begin{code}
thinT :: T b -> P (T b)
thinT = undefined
thin :: P b -> P (T b)
thin = thinT . collect
thinT_preceq = thinT
\end{code}
%endif
\begin{equation}
|ys `inn` thinT_preceq xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall x `inn` xs : (exists y `inn` ys : y `succeq` x)) {-"~~."-}|
\label{eq:thin-def-set}
\end{equation}
That is, |thin_preceq xs| contains all the table |ys| that is a sub-table of |xs|
(we overload the subset relation |(`sse`)| and membership relation |(`inn`)| to tables), and for every element in |xs| there exists some element in |ys| that is at least as good.
The monadic function |thinT_preceq| can be seen as a specification that contains all possible ways to thin a table,
of which the actual algorithm that maintains the table is a refinement.
The algorithm may aggressively remove all candidates that are not needed in each step.
It may also remove some but not all the redundant candidates, if that turns out to be more efficient.
In particular, we have |xs `inn` thin_preceq xs|, meaning that the algorithm may sometimes just keep the table unchanged.

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
propThinUniv :: (a -> P (T b)) -> (a -> P b) -> ((b, b) -> Bool) -> a -> P (T b)
propThinUniv h f succeq =
    h `sse` thinT . collect . f
 where pre0 = (mem <=< h) `sse` f
       pre1 = (do x <- any
                  t1 <- h x
                  y0 <- f x
                  return (t1, y0)) `sse`
               (do (t1, y0) <- any
                   y1 <- mem t1
                   filt succeq (y1, y0)
                   return (t1, y0))
\end{code}
%endif
Think of |f| as a function that non-deterministically generates some solution candidates, and |h| a function that non-deterministically builds a table of possibly useful solutions.
In |thinT_preceq. collect . f|, the results of |f| is collected into a table of type |T b| and passed to |thinT_preceq|.
The monadic inclusion in the big brackets encodes the combination of universal and existential quantification in \eqref{eq:thin-def-set}:
for all table |t1| returned by |h|, and for all |y0| returned by |f|,
there must exists an elememt |y1| in |t1| such that |y1 `succeq` y0|.

Since |thinT_preceq| and |collect| often appear together, we will use the following abbreviation:
given a preorder |(`preceq`)| on some type |b|, define
\begin{code}
thin_preceq :: P b -> P (T b)
thin_preceq = thinT_preceq . collect {-"~~."-}
\end{code}

Letting |h := thin_preceq| and |f := id| in \eqref{eq:thin-univ-monadic}, we get
%if False
\begin{code}
-- memThinId :: P c -> P c
memThinId =
\end{code}
%endif
\begin{code}
    mem <=< thin_preceq `sse` id {-"~~."-}
\end{code}
Letting |h := thin_preceq . f| in \eqref{eq:thin-univ-monadic}, we get the |thin|-cancelation law:
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
%if False
\begin{code}
propThinCancel :: (a -> P b) -> ((b, b) -> Bool) -> P (T b, b)
propThinCancel f succeq =
    (do x <- any
        t1 <- thin_preceq (f x)
        y0 <- f x
        return (t1, y0))
      `sse`   (do (t1, y0) <- any
                  y1 <- mem t1
                  filt succeq (y1, y0)
                  return (t1, y0))
\end{code}
%endif

The form of problem specifications we consider in this article ends with a |max_unlhd| for some ordering |unlhd|.
The following \emph{|thin| introduction law} says that
thinning the set of solutions with respect to |preceq| before taking maximum still yields legitimate results,
provided that |preceq| is a sub-ordering of |unlhd|:
%if False
\begin{code}
-- thinIntro :: P a -> P a
thinIntro = (max_unlhd . mem) <=< thin_preceq {-"\,"-}`sse`{-"\,"-} max_unlhd {-"~~."-}
\end{code}
%endif
\begin{equation}
  |(max_unlhd . mem) <=< thin_preceq {-"\,"-}`sse`{-"\,"-} max_unlhd|
    ~~~\Leftarrow~~~ |filt succeq `sse` filt unrhd| \mbox{~~,}
    \label{eq:thin-intro}
\end{equation}
where |filt succeq `sse` filt unrhd| is another way of saying that |(forall x y : x `succeq` y ==> x `unrhd` y)|.

With all the ingredients ready, we present the Thinning Theorem:
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
  thin . foldR f e `spse`
    foldR (\x -> thin . (f x <=< mem)) (thin e)
\end{code}
%endif
\end{theorem}
On the righthand side of |(`sse`)|, |foldR f e| computes all potential solutions before they are collected into a table and thinned by |thin|.
The theorem says that we may also, as seen in the lefthand side, distribute the thinning into each stage of the |foldR|, maintaining a smaller set of solutions, which may lead to an algorithm having a smaller time complexity.
With |x :: a|, the subexpression |thin . (f x <=< mem)| has type |T b -> P (T b)|.

\subsection{Solving knapsack}

Now we try to solve the 0-1 knapsack problem by thinning.
Starting from the fused specification, we introduce |thin|, and apply the Thinning Theorem:
%if False
\begin{code}
knapsackDer :: Wgt -> List Item -> P (List Item)
knapsackDer w =
\end{code}
%endif
\begin{code}
         max_leqv . (filt ((w >) . wgt) <=< subseq)
 `spse`    {- |foldR|-fusion -}
         max_leqv . foldR subsw (return [])
 `spse`    {- introducing |thin_leqvw| \eqref{eq:thin-intro} -}
         ((max_leqv . mem) <=< thin_leqvw) . foldR subsw (return []) {-"~~."-}
 ===       {- |(f <=< g) . h = f <=< (g . h)|-}
         (max_leqv . mem) <=< (thin_leqvw . foldR subsw (return []))
 `spse`    {- Thinning Theorem \eqref{eq:thinning} -}
         (max_leqv . mem) <=< foldR (\x -> thin_leqvw . (subsw x <=< mem)) (thin_leqvw (return [])) {-"~~."-}
\end{code}
In the second step we may introduce |thin_leqvw| because |xs `leqvw` ys ==> xs `leqv` ys|.

We now need to choose a representation of |T|.
We let |T| be a list of |List Item|, \emph{sorted by descending weights}.
%if False
\begin{code}
type T a = List a
\end{code}
%endif
Therefore we have:
\begin{spec}
collect (return xs)  = [xs] {-"~~,"-}
collect (t <|> u)    = mergeT (collect t) (collect u) {-"~~,"-}
\end{spec}
where |mergeT| merges two sorted lists of |List Item|:
\begin{code}
mergeT :: T (List Item) -> T (List Item) -> T (List Item)
mergeT []      u       = u
mergeT t       []      = t
mergeT (xs:t)  (ys:u)  | wgt xs >= wgt ys  = xs : mergeT t (ys:u)
                       | otherwise         = ys : mergeT (xs:t) u {-"~~."-}
\end{code}
With this representation, thinning can be performed by comparing values of adjacent solutions in the list, and drop those elements that are not more valuable, and yet not lighter:
\begin{code}
thinlist :: T (List Item) -> T (List Item)
thinlist []    = []
thinlist [xs]  = [xs]
thinlist (xs:ys:xss)  | val xs > val ys  = xs : thinlist (ys:xss)
                      | otherwise        = thinlist (ys:xss) {-"~~."-}
\end{code}
We have |return (thinlist t) `sse` thinT_leqvw t| for table |t :: T (List Item)|.

%format addw = "\Varid{add}_{w}"

Now we try to refine
\begin{spec}
 foldR (\x -> thin_leqvw . (subsw x <=< mem)) (thin_leqvw (return [])) {-"~~."-}
\end{spec}
%if False
\begin{code}
thinReturnDer =
         thin_leqvw (return [])
 ===     thinT (collect (return []))
 ===     thinT [[]]
 `spse`  return (thinlist [[]])
 ===     return [[]]
\end{code}
%endif
That |thin_leqvw (return []) `spse` return [[]]| is a routine calculation.
To refine |thin_leqvw . (subsw x <=< mem)|, we reason:
%if False
\begin{code}
tstepDer x t =
\end{code}
%endif
\begin{code}
         (thin . (subsw x <=< mem)) t
 ===       {- definition of |(<=<)| -}
         thin (subsw x =<< mem t)
 ===       {- definition of |subsw|, |(=<<)| distributes into |(<||>)|, monad laws -}
         thin (mem t <|> ((filt ((w>) . wgt) . (x:)) =<< mem t))
 ===       {- definition of |thin|, |collect| distributes into |(<||>)| -}
         thinT (mergeT (collect (mem t)) (collect ((filt ((w>) . wgt) . (x:)) =<< mem t)))
 ===       {-  |collect . mem = id| -}
         thinT (mergeT t (collect ((filt ((w>) . wgt) . (x:)) =<< mem t)))
 ===       {- construct |collect ((filt ((w>) . wgt) . (x:)) =<< mem t) = addw x t| -}
         thinT (mergeT t (addw x t))
 `spse`    {- |return (thinlist u) `sse` thinT_leqvw u| -}
         return (thinlist (mergeT t (addw x t))) {-"~~."-}
\end{code}

Consider the subexpression |collect ((filt ((w>) . wgt) . (x:)) =<< mem t)|.
\todo{Explain or derive this.}
\begin{code}
addw :: Item -> T (List Item) -> T (List Item)
addw x = map (x:) . dropWhile (((snd x + w) >) . wgt)
\end{code}
We have |collect ((filt ((w>) . wgt) . (x:)) =<< mem t = addw x t|.

Back to the derivation:
%if False
\begin{code}
knapsackDer2 :: Wgt -> List Item -> P (List Item)
knapsackDer2 w =
\end{code}
%endif
\begin{code}
         (max_leqv . mem) <=< foldR (\x -> thin_preceq . (subsw x <=< mem)) (thin_preceq (return []))
 `spse`     {- refinements above -}
         (max_leqv . mem) <=< foldR (\x t -> return (thinlist (mergeT t (addw x t)))) (return [[]])
 ===        {- by \eqref{eq:foldr-foldR} -}
         (max_leqv . mem) <=< (return . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]])
 ===        {- monad laws -}
         max_leqv . mem . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]]
 `spse`     {- |T| is a sorted list -}
         return . head . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]] {-"~~."-}
\end{code}

%format knapsack'' = "\Varid{knapsack}"
%if False
\begin{code}
knapsack'' :: List Item -> P (List Item)
\end{code}
%endif
\begin{code}
knapsack'' = return . head . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]] {-"~~."-}
\end{code}
