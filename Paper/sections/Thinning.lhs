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
\begin{spec}
mem      :: T a -> P a {-"~~,"-}
collect  :: P a -> T a {-"~~,"-}
\end{spec}

\subsection{Thinning}


The function |thin_preceq| now has type |T b -> P (T b)|.
Its universal property is:
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
|h `sse` thin_preceq . collect . f |\mbox{~~}|<==>|&\mbox{~~} |(mem <=< h) `sse` f &&|\\
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
propThinUniv x s =
    x `sse` thin_Q . collect . s
 where pre0 = (mem <=< x) `sse` s
       pre1 = (do a <- any
                  t0 <- x a
                  b1 <- s a
                  return (t0, b1)) `sse`
               (do (t0, b1) <- any
                   b0 <- mem t0
                   filt_Q (b0, b1)
                   return (t0, b1))
\end{code}
%endif
Letting |h := thin_preceq . collect| and |f := id| in \eqref{eq:thin-univ-monadic}, we get
\begin{equation}
    |mem <=< (thin_preceq . collect) `sse` id|
\end{equation}
Letting |h = thin_preceq . collect . f|, we have the cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |x <- any| \\
        & |t1 <- thin_preceq (collect (f x))| \\
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

\subsection{The Thinning Theorem}

The thinning theorem is given by:
\begin{theorem}[Thinning Theorem]
\label{thm:thinning}
{\rm Let |preceq| be a binary relation on |b| that is reflexive and transitive,
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |succeq| for all |x|, we have
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
&|foldR (\x -> thin_preceq . collect . (f x <=< mem)) (thin_preceq (collect e)) `sse`| \\
& \qquad  |thin_preceq . collect . foldR f e  {-"~~."-}|
\end{split}
\label{eq:thinning}
\end{equation}
}
%if False
xtxttx\begin{code}
thmThinning :: (a -> b -> P b) -> P b -> List a -> P (T b)
thmThinning f e =
  thin_Q . collect . foldR f e `spse`
    foldR (\x -> thin_Q. collect . (f x <=< mem))
       (thin_Q (collect e))
\end{code}
%endif
\end{theorem}

\subsection{Proof of the Thinning Theorem}

\begin{proof}
By the fixed-point property of |foldR| \eqref{eq:foldRPrefixPt}, to prove \eqref{eq:thinning} it is sufficient to show that:
\begin{spec}
     (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs `sse`
       (thin_preceq . collect . foldR f e) (x : xs)
<=>      {- definition of |foldR| -}
     (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs `sse`
       thin_preceq (collect (f x =<< foldR f e xs))
<=>     {- abstracting away |xs| -}
     (thin_preceq . collect . (f x <=< mem)) <=< (thin_preceq . collect . foldR f e) `sse`
       thin_preceq . collect . (f x <=< foldR f e) {-"~~."-}
\end{spec}
%if False
\begin{code}
propFixPoint0 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint0 f e x xs =
  (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs
  `sse` (thin_Q . collect . foldR f e) (x : xs)

propFixPoint1 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint1 f e x xs =
  (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs
  `sse` (thin_Q . collect . foldR f e) (x : xs)
  `sse` thin_Q (collect (f x =<< foldR f e xs))

propFixPoint2 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint2 f e x  =
  (thin_Q . collect . (f x <=< mem)) <=< (thin_Q . collect . foldR f e)
  `sse` thin_Q . collect . (f x <=< foldR f e)
\end{code}
%endif
According to the universal property of |thin_preceq|, for the above to hold we need to show that
\begin{spec}
  mem <=< (thin_preceq . collect . (f x <=< mem)) <=< (thin_preceq . collect . foldR f e) `sse` f x <=< foldR f e {-"~~,"-}
\end{spec}
and that
%if False
\begin{code}
pfThinThm2 :: (a -> b -> P b) -> P b -> a -> P (T b, b)
pfThinThm2 f e x =
\end{code}
%endif
\begin{code}
     do  xs <- any
         t1 <- (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs
         y0 <- f x =<< foldR f e xs
         return (t1, y0)
===  do  xs <- any
         u1 <- (thin_preceq . collect) (foldR f e xs)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         b0 <- foldR f e xs
         y0 <- f x b0
         return (t1, y0)
`sse`  {- |thin| cancelation -}
     do  (u1, b0) <- any
         b1 <- mem u1
         filt preceq (b1, b0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         y0 <- f x b0
         return (t1, y0)
`sse`  {- monotonicity -}
     do  (u1, y0) <- any
         b1 <- mem u1
         y1 <- f x b1
         filt preceq (y1, y0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         return (t1, y0)
===    {- monad laws -}
     do  (u1, y0) <- any
         y1 <- (f x <=< mem) u1
         filt preceq (y1, y0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         return (t1, y0)
`sse`  {- |thin| cancelation -}
     do  (y0, t1, y1) <- any
         y2 <- mem t1
         filt preceq (y2, y1)
         filt preceq (y1, y0)
         return (t1, y0)
`sse`  {- transitivity of |preceq| -}
     do  (y0, t1) <- any
         y2 <- mem t1
         filt preceq (y2, y0)
         return (t1, y0) {-"~~."-}
\end{code}
Note that the second "monotonicity" step is not quite the same as the
monotonicity assumption --- |b1| is not drawn from |any|, but a result of
|mem u1|. This is fine because
|do {b1 <- mem u1 ...} | can be rewritten as
|do {b1' <- mem u1; b1 <- any; filt (=) b1 b1' ... }|.
\end{proof}
