
\section{Proof of the Thinning Theorem}

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
