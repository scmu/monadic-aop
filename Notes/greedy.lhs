\documentclass[dvipsnames, fleqn, 11pt]{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{natbib}

\usepackage{classicthesis}

\linespread{1.05} % a bit more for Palatino
\areaset[current]{420pt}{761pt} % 686 (factor 2.2) + 33 head + 42 head \the\footskip
\setlength{\marginparwidth}{7em}%
\setlength{\marginparsep}{2em}%

\usepackage{url}
\let\Bbbk\relax  % avoiding error "Bbbk' already defined."
\usepackage{tikz}
\usepackage{chngcntr} % for \counterwithout
\usepackage{caption}
\usepackage{subcaption}
\usepackage{scalerel}

%% lhs2Tex greedy.lhs | pdflatex --jobname=greedy

%if False
\begin{code}
(===) :: a -> a -> a
(===) = undefined

infixr 0 ===
\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt
%include common/Relation.fmt

%%\email{scm@iis.sinica.edu.tw}

\usepackage{common/doubleequals}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

%\def\commentbegin{\quad$\{$~}
%\def\commentend{$\}$}
\def\commentbegin{\quad\begingroup\color{SeaGreen}\{\ }
\def\commentend{\}\endgroup}

\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}

\definecolor{mediumpersianblue}{rgb}{0.0, 0.4, 0.65}
\everymath{\color{mediumpersianblue}}
\apptocmd{\[}{\color{mediumpersianblue}}{}{}
\AtBeginEnvironment{equation}{\color{mediumpersianblue}}
\AtBeginEnvironment{equation*}{\color{mediumpersianblue}}

\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}


\counterwithout{equation}{section}

\begin{document}

\title{Various Formulation of the Greedy Theorem and Their Proofs}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle


\section{Relation, Minimum, Fixed-Point}

%{
%format R = "\Varid{R}"
%format S = "\Varid{S}"
%format X = "\Varid{X}"

Recall the fixed-point properties of catamorphism:
\begin{spec}
 cata R `sse` X {-"~"-}<=={-"~"-} R . F X . conv alpha `sse` X  {-"~~,"-}
 X `sse` cata R {-"~"-}<=={-"~"-} X `sse` R . F X . conv alpha  {-"~~."-}
\end{spec}
The relation |min| is defined by
\begin{spec}
  min_R = mem `cap` R{-"\!"-}/{-"\!"-}ni {-"~~,"-}
\end{spec}
with the universal property
\begin{spec}
  X `sse` min_R . Lam S {-"~\,"-}<=>{-"~\,"-} X `sse` S {-"\,"-}&& {-"\,"-} X . conv S `sse` R {-"~~."-}
\end{spec}
In particular, letting |X = min_R . Lam S| we have |min_R . Lam S . conv S `sse` R|.

The greedy theorem is given by
\begin{spec}
  min_R . Lam (cata S) {-"\,"-}`spse` {-"\,"-} cata (min_R . Lam S) {-"~"-}<=={-"~"-} F R . conv S `sse` conv S . R {-"~~."-}
\end{spec}
\begin{proof}
A shorter route is to start with the universal property of |min|,
leading to
\begin{spec}
 cata (min . Lam S) `sse` cata S {-"~"-}&& {-"~"-} cata (min . Lam S) . conv (cata S) `sse` R {-"~~,"-}
\end{spec}
where the second clause can be proved by hylomorphism theorem.
This is the proof given in AoP.
However, for this note we try to avoid hylomorphism (due to extra issues we have to deal with in Agda). Thus we stick with catamorphisms and use its fixed-point property:
\begin{spec}
     cata (min_R . Lam S) `sse` min_R . Lam (cata S)
<==    {- fixed-point property of cata -}
     min_R . Lam S . F (min_R . Lam (cata S)) . conv alpha `sse` min_R . Lam (cata S)
<=>    {- universal property of |min| -}
     min_R . Lam S . F (min_R . Lam (cata S)) . conv alpha `sse` cata S &&
     min_R . Lam S . F (min_R . Lam (cata S)) . conv alpha . conv (cata S) `sse` R {-"~~."-}
\end{spec}
The first clause holds immediately because |min_R . Lam S `sse` mem . Lam S = S| and the same with |cata S|. Regarding the second:
\begin{spec}
       min_R . Lam S . F (min_R . Lam (cata S)) . conv alpha . conv (cata S)
=       {- catamorphism -}
       min_R . Lam S . F (min_R . Lam (cata S)) . F (conv (cata S)) . conv S
`sse`   {- |min_R . Lam (cata S) . conv (cata S) `sse` R| -}
       min_R . Lam S . F R . conv S
`sse`   {- |F R . conv S `sse` conv S . R| -}
       min_R . Lam S . conv S . R
`sse`   {- |min_R . Lam S . conv S `sse` R| -}
       R . R
`sse`   {- |R| transitive -}
       R {-"~~."-}
\end{spec}
\end{proof}
%}

\section{Relation, Minimum, Fusion}

%{
%format R = "\Varid{R}"
%format S = "\Varid{S}"
%format T = "\Varid{T}"
%format X = "\Varid{X}"

Recall the cata-fusion theorem:
\begin{spec}
cata T `sse` S . cata R {-"~"-}<=={-"~"-} T . F S `sse` S . R  {-"~~,"-}
S . cata R `sse` cata T {-"~"-}<=={-"~"-} S . R `sse` T . F S  {-"~~."-}
\end{spec}
To use the fusion theorem, recall:
\begin{spec}
Lam (cata S) = cata (Lam (S . F mem)) {-"~~."-}
\end{spec}
Now we prove the theorem:
\begin{proof}
To prove that
\begin{spec}
cata (min_R . Lam S) `sse` min_R . Lam (cata S) = min_R . cata (Lam (S . F mem)) {-"~~,"-}
\end{spec}
the fusion condition is:
\begin{spec}
  min_R . Lam S . F min_R `sse` min_R . Lam (S . F mem) {-"~~,"-}
\end{spec}
which by universal property of |min| is equivalent to
\begin{spec}
  min_R . Lam S . F min_R `sse` S . F mem  &&
  min_R . Lam S . F min_R . conv (S . F mem) `sse` R {-"~~."-}
\end{spec}
The first clause holds because |min_R `sse` mem|.
For the second clause:
\begin{spec}
       min_R . Lam S . F min_R . F ni . conv S
`sse`   {- |min_R . ni `sse` R / ni . ni `sse` R| -}
       min_R . Lam S . F R . conv S
`sse`   {- |F R . conv S `sse` conv S . R| -}
       min_R . Lam S . conv S . R
`sse`   {- |min_R . Lam S . conv S `sse` R| -}
       R . R
`sse`   {- |R| transitive -}
       R {-"~~."-}
\end{spec}
\end{proof}
%}

\section{Relation, Shrink}

%{
%format R = "\Varid{R}"
%format S = "\Varid{S}"
%format X = "\Varid{X}"
The shrink operator is defined by:
\begin{spec}
 S `shrink` R = S `cap` R{-"\!"-}/{-"\!"-}conv S {-"~~,"-}
\end{spec}
with the universal property:
\begin{spec}
  X `sse` S `shrink` R {-"~\,"-}<=>{-"~\,"-} X `sse` S {-"\,"-}&& {-"\,"-} X . conv S `sse` R {-"~~."-}
\end{spec}

The greedy theorem can be formulated using shrink:
\begin{spec}
  cata S `shrink` R {-"\,"-}`spse` {-"\,"-} cata (S `shrink` R) {-"~"-}<=={-"~"-} F R . conv S `sse` conv S . R {-"~~."-}
\end{spec}
\begin{proof}
Similarly, we avoid using hylomorphism and start with the fixed-point property of catamorphism:
\begin{spec}
     cata (S `shrink` R) `sse` cata S `shrink` R
<==    {- fixed-point property of cata -}
     S `shrink` R . F (cata S `shrink` R) . conv alpha `sse` cata S `shrink` R
<=>    {- universal property of shrink -}
     S `shrink` R . F (cata S `shrink` R) . conv alpha `sse` cata S &&
     S `shrink` R . F (cata S `shrink` R) . conv alpha . conv (cata S) `sse` R {-"~~."-}
\end{spec}
The first clause holds immediately because |S `shrink` R `sse` S| and |cata S `shrink` R `sse` cata S|. Regarding the second:
\begin{spec}
       S `shrink` R . F (cata S `shrink` R) . conv alpha . conv (cata S)
=       {- catamorphism -}
       S `shrink` R . F (cata S `shrink` R) . F (conv (cata S)) . conv S
`sse`   {- |cata S `shrink` R . conv (cata S) {-"~"-}`sse`{-"~"-} R / conv (cata S)  . conv (cata S) {-"~"-}`sse`{-"~"-} R| -}
       S `shrink` R . F R . conv S
`sse`   {- |F R . conv S `sse` conv S . R| -}
       S `shrink` R . conv S . R
`sse`   {- |S `shrink` R . conv S {-"~"-}`sse`{-"~"-} R / conv S  . conv S {-"~"-}`sse`{-"~"-} R| -}
       R . R
`sse`   {- |R| transitive -}
       R {-"~~."-}
\end{spec}
\end{proof}
%}

\section{Monad, Minimum, Lists}

%{
%format X = "\Varid{X}"

For the monadic version, we try formulating the problem for monadic |foldr|:
\begin{spec}
foldr :: (a -> b -> m b) -> m b -> List a -> m b
foldr f e []      = e
foldr f e (x:xs)  = f x =<< foldr f e xs {-"~~."-}
\end{spec}
And now |min_R| has type |P b -> P b|, with universal property that for |f :: a -> P b|:
\begin{spec}
 X `sse` min_R . f {-"~"-}<=>{-"~"-} X `sse` f {-"\,"-}&&{-"\,"-} X <=< conv f `sse` R {-"~~."-}
\end{spec}

The greedy theorem is givem by:
\begin{spec}
min_R . foldr f e `spse` foldr (\x -> min_R . f x) (min_R e)
   <== R <=< conv (f x) `sse` conv (f x) <=< R {-"~~."-}
\end{spec}
\begin{proof}
By the fixed-point property of |foldr|, we need to show that
\begin{spec}
     min_R (foldr f e (x:xs)) `spse` (min_R . f x) =<< min_R (foldr f e xs)
<=>   {- definition of |foldr| -}
     min_R (f x =<< foldr f e xs) `spse` (min_R . f x) =<< min_R (foldr f e xs)
<=>   {- abstracting away |xs| -}
     min_R . (f x <=< foldr f e) `spse`  (min_R . f x) <=< (min_R . foldr f e) {-"~~."-}
\end{spec}
By the universal property of |min|, we need:
\begin{spec}
  (min_R . f x) <=< (min_R . foldr f e) `sse` f x <=< foldr f e  &&
  (min_R . f x) <=< (min_R . foldr f e) <=< conv (f x <=< foldr f e) `sse` R {-"~~."-}
\end{spec}
The first clause holds because |min_R . g `sse` g| for all |g|.
Regarding the second clause:
\begin{spec}
    (min_R . f x) <=< (min_R . foldr f e) <=< conv (foldr f e) <=< conv (f x)
`sse`   {- |(min_R . g) <=< conv g `sse` R| -}
    (min_R . f x) <=< R <=< conv (f x)
`sse`   {- |R <=< conv (f x) `sse` conv (f x) <=< R| -}
    (min_R . f x) <=< conv (f x) <=< R
`sse`   {- |(min_R . g) <=< conv g `sse` R| -}
    R <=< R
`sse`   {- |R| transitive -}
    R {-"~~."-}
\end{spec}
\end{proof}

\section{Monad, Minimum, Lists, Fusion}

The fusion theorem for monadic |foldr| is
\begin{spec}
  h . foldr f e `spse` foldr g (h e) {-"\,"-}<=={-"\,"-} h (f x =<< m) `spse` g x =<< h m {-"~~"-}
\end{spec}
The fusion condition can also be written |h . (f x =<<) `spse` g x <=< h|.

Try proving the theorem using |foldr|-fusion.
The fusion condition is:
\begin{spec}
  min_R . (f x =<<) `spse` (min_R . f x) <=< min_R {-"~~."-}
\end{spec}
By universal property of |min|, this is equivalent to
\begin{spec}
  (min_R . f x) <=< min_R `sse` (f x =<<) &&
  (min_R . f x) <=< min_R <=< conv (f x =<<) `sse` R {-"~~."-}
\end{spec}
The first clause holds because |min_R `sse` id|. For the second clause,
note that |(g =<<) = (g <=< id)|. Therefore,
\begin{spec}
      (min_R . f x) <=< min_R <=< conv (f x =<<)
=       {- |(g =<<) = (g <=< id)| -}
      (min_R . f x) <=< min_R <=< conv (f x <=< id)
=       {- converse -}
      (min_R . f x) <=< (min_R . id) <=< conv id <=< conv (f x)
`sse`   {- |(min_R . g) <=< conv g `sse` R| -}
      (min_R . f x) <=< R <=< conv (f x)
`sse`   {- |R <=< conv (f x) `sse` conv (f x) <=< R| -}
      (min_R . f x) <=< conv (f x) <=< R
`sse`   {- |(min_R . g) <=< conv g `sse` R| -}
      R <=< R
`sse`   {- |R| transitive -}
      R {-"~~."-}
\end{spec}
%}

\section{Monad, List, Uncurried}

%{
%format X = "\Varid{X}"
%format R = "\Varid{R}"
%format b0
%format b1
%format b2
%format y0
%format y1

To avoid the use of converses, we switch to an ``uncurried'' variation of relations. That is, |A -> B -> Set| now becomes |A :* B -> Set|.

The set |any :: P a| contains all elements having type |a|. Computationally, it creates an arbitrary element of an apporpriate type.
The command |filt :: (a -> Bool) -> a -> P a| is defined by
\begin{spec}
filt p x  | p x        = return x
          | otherwise  = fail {-"~~."-}
\end{spec}
The new universal property of |min| is given by:
% \begin{spec}
% X `sse` min_R . f {-"\,"-}<=> {-"\,"-}  X `sse` f &&
%                                         (  do  a   <- any
%                                                b0  <- X a
%                                                b1  <- f a
%                                                return (b0, b1) {-"\,"-} `sse`
%                                                  do  (b0, b1) <- any
%                                                      filt R (b0, b1) {-"\,"-}) {-"~~."-}
% \end{spec}
\begin{equation*}
|X `sse` min_R . f|\mbox{~~}|<==>|\mbox{~~} |X `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |a <- any| \\
       & |b0 <- X a| \\
       & |b1 <- f a| \\
       & |return (b0, b1)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(b0, b1) <- any| \\
       & |filt R (b0, b1)|
 \end{aligned}
 \right)\mbox{~~.}
\end{equation*}
The second clause is the uncurried translation of |X <=< conv f `sse` R|.
Let |X| be |min_R . f|, we have the following useful |min|-cancelation rule:
% \begin{spec}
% do  a <- any
%     b0 <- min_R (f a)
%     b1 <- f a
%     return (b0, b1) `sse`
%    do  (b0, b1) <- any
%        filt R (b0, b1) {-"~~."-}
% \end{spec}
\begin{equation*}
  \setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |a <- any| \\
        & |b0 <- min_R (f a)| \\
        & |b1 <- f a| \\
        & |return (b0, b1)|
  \end{aligned}
  ~~|`sse`|~~
  \begin{aligned}
  |do|~ & |(b0, b1) <- any| \\
        & |filt R (b0, b1)| \mbox{~~.}
  \end{aligned}
\end{equation*}

The greedy theorem is written as that we have
\begin{spec}
min_R . foldr f e `spse` foldr (\x -> min_R . f x) (min_R e) {-"~~,"-}
\end{spec}
provided that
% \begin{spec}
%    <==  do  (y0, y1) <- any
%             b1 <- f x y1
%             filt R (y0, y1)
%             return (y0, b1)  {-"~~"-}`sse`
%           do  (b1, y0) <- any
%               b2 <- f x y0
%               filt R (b2, b1)
%               return (y0, b1){-"~~."-}
% \end{spec}
\begin{equation*}
  \setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |(y0, y1) <- any| \\
        & |b1 <- f x y1)| \\
        & |filt R (y0,y1)| \\
        & |return (y0, b1)|
  \end{aligned}
  ~~|`sse`|~~
  \begin{aligned}
  |do|~ & |(b1, y0) <- any| \\
        & |b2 <- f x y0|\\
        & |filt R (b2, b1)|\\
        & |return (y0,b1)| \mbox{~~.}
  \end{aligned}
\end{equation*}

Note how the monotonicity condition |R <=< conv (f x) `sse` conv (f x) <=< R| is translated to the uncurried expression above.

\begin{proof}
Recall from the previous section that, by the fixed-point property, we ought to prove
\begin{spec}
     min_R . (f x <=< foldr f e) `spse`  (min_R . f x) <=< (min_R . foldr f e) {-"~~."-}
\end{spec}
Now we use the universal property. We focus on the second clause.
We use |do|-notation to implicitly invoke the monad laws, and commutative laws, behind-the-scene.
\begin{spec}
       do  xs <- any
           b0 <- (min_R . f x) =<< min_R (foldr f e xs)
           b1 <- f x =<< foldr f e xs
           return (b0, b1)
=      do  xs <- any
           y0 <- min_R (foldr f e xs)
           b0 <- min_R (f x y0)
           y1 <- foldr f e xs
           b1 <- f x y1
           return (b0, b1)
`sse`   {- |min|-cancelation -}
       do  (y0, y1) <- any
           filt R (y0, y1)
           b0 <- min_R (f x y0)
           b1 <- f x y1
           return (b0, b1)
`sse`   {- monotonicity -}
       do  (b1, y0) <- any
           b2 <- f x y0
           filt R (b2, b1)
           b0 <- min_R (f x y0)
           return (b0, b1)
`sse`   {- |min|-cancelation -}
       do  (b0, b1, b2) <- any
           filt R (b0, b2)
           filt R (b2, b1)
           return (b0, b1)
`sse`   {- |R| transitive -}
       do  (b0, b1) <- any
           filt R (b0, b1) {-"~~."-}
\end{spec}
\end{proof}

We have chosen to use the fixed-point property for the proof, to demonstrate more steps. We could have also used the fusion-theorem instead.
Recall the fusion condition:
\begin{spec}
  min_R . (f x =<<) `spse` (min_R . f x) <=< min_R {-"~~."-}
\end{spec}
By the universal property of |min|, we ought to prove:
% \begin{spec}
% do  ys <- any
%     b0 <- (min_R . f x) =<< min_R ys
%     b1 <- f x =<< ys
%     return (b0, b1) `sse`
%    do  (b0, b1) <- any
%        filt R (b0, b1) {-"~~."-}
% \end{spec}
\begin{equation*}
  \setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |ys <- any| \\
        & |b0 <- (min_R . f x) =<< min_R ys| \\
        & |b1 <- f x =<< ys|\\
        & |return (b0, b1)|
  \end{aligned}
  ~~|`sse`|~~
  \begin{aligned}
  |do|~ & |(b0, b1) <- any| \\
        & |filt R (b0, b1)| \mbox{~~.}
  \end{aligned}
\end{equation*}

The first step can be carried out by |min|-cancelation with |f := id|. The rest is the same.
%}

\section{Monad, List, Uncurried, Point-Free}

%{
%format X = "\Varid{X}"
%format R = "\Varid{R}"
%format b0
%format b1
%format b2
%format y0
%format y1

The monadic version above, due to its use of |(>>=)| or |do|, unnecessarily assumes an order of execution in the |do| block.
This can be avoided by a point-free variation. Define:
\begin{spec}
split :: (a -> m b) -> (a -> m c) -> a -> m (b :* c)
split f g x = do y <- f x; z <- g x; return (y,z) {-"~~,"-}

(`prod`) :: (a -> m b) -> (c -> m d) -> (a :* c) -> m (b :* d)
f `prod` g = split (f . fst) (g . snd)  {-"~~,"-}

assocr :: ((a :* b) :* c) -> (a :* (b :* c))
assocr ((x,y),z) = (x,(y,z)) {-"~~."-}
\end{spec}
The universal property of |min| is more concisely given by:
\begin{spec}
X `sse` min_R . f {-"\,"-}<=> {-"\,"-}  X `sse` f && split X f =<< any `sse` filt R =<< any {-"~~,"-}
\end{spec}
where we let |R :: (a :* a) -> Bool| be uncurried.
It gives us a nice cancelation rule:
\begin{spec}
split (min_R . f) f =<< any `sse` filt R =<< any {-"~~."-}
\end{spec}

Meanwhile, monotonicity is less pretty, written as:
\begin{spec}
 (id `prod` f x)=<< filt R =<< any `sse`
   (id `prod` (snd <$> filt R)) =<< (assocr <$> (split id (f x) `prod` id) =<< any) {-"~~,"-}
\end{spec}
while this is transitivity of |R| written point-free:
\begin{spec}
(id `prod` (snd <$> filt R)) =<< (assocr <$> (filt R `prod` id) =<< any)
  `sse` filt R =<< any {-"~~."-}
\end{spec}
Note that the |any| in the first line generates a tuple containing three things |((x,y),z)|, while we keep only |(x,z)| in the output.

The highlight of the proof is given below:
\begin{proof}
Recall that, by the fixed-point property, we ought to prove
\begin{spec}
     min_R . (f x <=< foldr f e) `spse`  (min_R . f x) <=< (min_R . foldr f e) {-"~~."-}
\end{spec}
We focus on the second clause of the universal property:
\begin{spec}
  split ((min_R . f x) <=< (min_R . foldr f e)) (f x <=< foldr f e) =<< any
=       {- product -}
  ((min . f x) `prod` f x) =<< split (min_R . foldr f e) (foldr f e) =<< any
`sse`   {- |min|-cancelation -}
  ((min . f x) `prod` f x) =<< filt R =<< any
`sse`   {- monotonicity -}
  ((min . f x) `prod` (snd <$> filt R)) =<< (assocr <$> (split id (f x) `prod` id) =<< any)
=       {- naturality of |assocr| -}
  (id `prod` (snd <$> filt R)) =<< (assocr <$> (((min . f x) `prod` id) `prod` id) =<< (split id (f x) `prod` id) =<< any)
=       {- product -}
  (id `prod` (snd <$> filt R)) =<< (assocr <$> (split (min . f x) (f x) `prod` id) =<< any)
=       {- |min|-cancelation -}
  (id `prod` (snd <$> filt R)) =<< (assocr <$> (filt R `prod` id) =<< any)
`sse`   {- |R| transitive -}
   filt R =<< any {-"~~."-}
\end{spec}
\end{proof}
%}
\end{document}
