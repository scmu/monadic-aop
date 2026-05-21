\section{Monadic counterparts of other relational operators}
\label{sec:rel-op}

Like relations, union and intersection of monadic arrows can be defined as:
\begin{spec}
(`union`) :: (a -> P b) -> (a -> P b) -> a -> P b
(f `union` g) x = f x <|> g x {-"~~,"-}
(`intersect`) :: (a -> P b) -> (a -> P b) -> a -> P b
(f `intersect` g) x = f x `intersect` g x {-"~~."-}
\end{spec}
The |(`intersect`)| in the righthand side of the last line refers to intersection of sets.
They respectively satisfy the universal properties:
\begin{align*}
|f `union` g {-"\,"-}`sse`{-"\,"-} h|    &  |{-"~"-}<=>{-"~"-} f `sse` h {-"\,"-}&&{-"\,"-} g `sse` h {-"~~,"-}|\\
|h `sse` f  {-"\,"-}&&{-"\,"-} h `sse` g| & |{-"~"-}<=>{-"~"-} h {-"\,"-}`sse`{-"\,"-} f `intersect` g   {-"~~."-}|
\end{align*}

The converse operator is defined by:
\begin{spec}
conv _ :: (a -> P b) -> (b -> P a)
(conv f) y = { x | y `inn` f x } {-"~~."-}
\end{spec}
It can be proved that converse idempotent (|conv ((conv f)) = f|) and order preserving
(|f `sse` g <=> conv f `sse` conv g|).

Left and right factors are defined by:
\begin{spec}
(`lfac`) :: (b -> P c) -> (a -> P c) -> (a -> P b)
(f `lfac` h) x = { y | (forall z : z `inn` f y ==> z `inn` h x) } {-"~~,"-}
(/) :: (a -> P c) -> (a -> P b) -> (b -> P c)
(h / g) y = { z | (forall x : y `inn` g x ==> z `inn` h x) } {-"~~."-}
\end{spec}
They satisfy the universal properties:
\begin{align*}
|g {-"\,"-}`sse`{-"\,"-} f `lfac` h| & |{-"~"-}<=>{-"~"-} f <=< g {-"\,"-}`sse`{-"\,"-} h{-"~~,"-}|\\
|f {-"\,"-}`sse`{-"\,"-} h / g| & |{-"~"-}<=>{-"~"-} f <=< g {-"\,"-}`sse`{-"\,"-} h{-"~~."-}|
\end{align*}
All the operators and properties above are defined and proved in our Agda model.
