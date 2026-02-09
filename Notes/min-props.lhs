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

%% lhs2Tex min-props.lhs | pdflatex --jobname=min-props

%if False
\begin{code}
{-# OPTIONS_GHC -Wno-missing-methods #-}
import Prelude hiding (max, min, any)
import GHC.Base (Alternative)
import Data.Kind (Type)
import Control.Applicative
import Control.Monad

(===) :: a -> a -> a
(===) = undefined

infixr 0 ===

-- type P a = [a]
data P a

instance Functor P where
instance Applicative P where
instance Monad P where
instance Alternative P where
instance MonadPlus P where
instance MonadFail P where

type List a = [a]

max :: P a -> P a
max = undefined

min :: P a -> P a
min = undefined

maxlist :: List a -> a
maxlist = undefined

any :: P a
any = undefined

infixr 0 `spse`
spse :: a -> a -> a
spse = undefined

infixr 0 `sse`
sse :: a -> a -> a
sse = undefined

wrap x = [x]

leqs :: List Int -> List Int -> Bool
leqs xs ys = sum xs <= sum ys

geqs :: List Int -> List Int -> Bool
geqs xs ys = sum xs >= sum ys

filt :: (a -> b -> Bool) -> (a, b) -> P (a,b)
filt = undefined

\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt
%include common/Relation.fmt

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
\title{Some Crucial Properties of Minimum}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle

%format y0
%format y1

Recall the universal property of |min|:
\begin{equation}
  |Y `sse` min X {-"~"-}<=>{-"~"-} Y `sse` X && (forall y `mem` Y, x `mem` X : y <= x))| \mbox{~~.}
  \label{eq:min-universal-set}
\end{equation}
Instantiating |Y| to |{y}|, we get:
\begin{equation}
  |y `mem` min X {-"~"-}<=>{-"~"-} y `mem` X && (forall x `mem` X : y <= x))| \mbox{~~.}
  \label{eq:min-membership}
\end{equation}

There is also a function-composition version of the universal property:
\begin{equation}
  |h `sse` min . f {-"~"-}<=>{-"~"-} h `sse` f && (forall x : (forall y0 `mem` h x, y1 `mem` f x : y0 <= y1))| \mbox{~~,}
  \label{eq:min-universal-fol}
\end{equation}
and it monadic version:
\begin{equation}
|h `sse` min . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y0 <- h x| \\
       & |y1 <- f x| \\
       & |return (y0, y1)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y0, y1) <- any| \\
       & |filt (<=) (y0, y1)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:min-universal-monad}
\end{equation}


Recall also that |(=<<)| for the set monad is defined by:
\begin{equation}
  |y `mem` f =<< m  {-"~"-}<=>{-"~"-} (exists x `mem` m : y `mem` f x)| \mbox{~~.}
  \label{eq:bind-defn}
\end{equation}

\section{Distributivity}

The aim is to prove that we prove that for all |f| and |m|:
%if False
\begin{code}
propDist3 f g m =
  min (f =<< m) === min ((min . f) =<< m) {-"~~."-}
\end{code}
%endif
\begin{equation}
|min (f =<< m) === min ((min . f) =<< m)| \mbox{~~.}
\label{eq:min-bind-distr}
\end{equation}
Note that by letting |m := g x| for some |g| and |x|, we get
%if False
\begin{code}
propDist2 f g x =
\end{code}
%endif
\begin{code}
  min (f =<< g x) === min ((min . f) =<< g x) {-"~~,"-}
\end{code}
equivalently, forall |f| and |g|,
%if False
\begin{code}
propDist f g =
\end{code}
%endif
\begin{code}
  min . (f <=< g) === min . ((min . f) <=< g) {-"~~."-}
\end{code}

\begin{proof}
The |spse| direction of \eqref{eq:min-bind-distr} is easy, since |min `sse` id|.
We look at the |sse| direction:
\begin{equation*}
|min (f =<< m) `sse` min ((min . f) =<< m)| \mbox{~~.}
\end{equation*}
According to the universal property \eqref{eq:min-universal-set}, to establish that we need
\begin{align}
&  |min (f =<< m) `sse` (min . f) =<< m|~~\wedge
  \label{eq:mem-bind-distr-a1} \\
&  |(forall y `mem` min (f =<< m), x `mem` ((min . f) =<< m) :  y <= x)|
  \label{eq:mem-bind-distr-a2}
\end{align}

To prove \eqref{eq:mem-bind-distr-a1} we reason, for all |y|:
\begin{spec}
    y `mem` min (f =<< m)
 <=>    {- by \eqref{eq:min-membership}  -}
    y `mem` f =<< m  &&  (forall z `mem` f =<< m : y <= z)
 <=>    {- definition of |(=<<)| \eqref{eq:bind-defn} -}
   (exists x `mem` m : y `mem` f x) &&
   (forall z : (exists w `mem` m : z `mem` f w) ==> y <= z)
 <=>    {- quantifier manipulation -}
   (exists x `mem` m : y `mem` f x  &&
                (forall z : (exists w `mem` m : z `mem` f w) ==> y <= z))
 ==>    {- let |w = x| -}
   (exists x `mem` m : y `mem` f x   &&
                (forall z : z `mem` f x ==> y <= z))
 <=>    {- by \eqref{eq:min-membership}  -}
   (exists x `mem` m : y `mem` min (f x))
 <=>    {- by \eqref{eq:bind-defn} -}
    y `mem` (min . f) =<< m {-"~~."-}
\end{spec}

To prove \eqref{eq:mem-bind-distr-a2} we reason, for all |y| and |x|,
\begin{spec}
  y `mem` min (f =<< m)  &&  x `mem` ((min . f) =<< m)
 ==>   {- by \eqref{eq:min-membership} -}
  (forall z `mem` f =<< m : y <= z)  &&
  x `mem` (min . f) =<< m
 <=>   {- by \eqref{eq:min-membership} and \eqref{eq:bind-defn} -}
  (forall z : (exists w `mem` m : z `mem` f w) ==> y <= z)) &&
  (exists v `mem` m : x `mem` f v  &&  (forall u `mem` f v : x <= u))
 ==>   {- let |z, w := x, v| -}
   y <= x  && (exists v `mem` m : x `mem` f v  &&  (forall u `mem` f v : x <= u))
 ==>   {- conjunction -}
   y <= x {-"~~."-}
\end{spec}
\end{proof}

\section{Monotonicity}

We do not have |X `sse` Y ==> min X `sse` min Y| in general --
consider |X = {2}| and |Y = {1,2,3}|.
Consequently neither do we have |f `sse` g ==> min . f `sse` min . g|.
For the monotonicity condition to hold we need some side condition on |X| and |Y| (or |f| and |g|).
Yet I do not want that condition to be too strong.

Firstly, if |X| is empty, we certainly have |min X `sse` min Y|.
For non-empty |X|, intuitively, if we keep at least one minimum of |X| in |min X|, we shall have |min X `sse` min Y|.
To formalise that, the condition I am proposing is that
\begin{spec}
 min X `sse` min Y <==  X `sse` Y && (forall y `mem` Y : (exists x `mem` X : x <= y)) {-"~~."-}
\end{spec}
A compositional variation is:
\begin{spec}
 min . f `sse` min . g <==  f `sse` g && (forall z : (forall y `mem` g z : (exists x `mem` f z : x <= y))) {-"~~."-}
\end{spec}
A monadic encoding of it goes like:
\begin{equation}
|min . f `sse` min . g|\mbox{~~}|<==>|\mbox{~~} |f `sse` g &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |z <- any| \\
       & |y <- g z| \\
       & |return (y, z)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y, z) <- any| \\
       & |x <- f z| \\
       & |filt (<=) (x, y)|\\
       & |return (y,z)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:min-monotonic-monad}
\end{equation}
\begin{proof}
We assume the RHS of \eqref{eq:min-monotonic-monad} and try to prove its LHS, |min . f `sse` min . g|.
By the universal property \eqref{eq:min-universal-monad}, to have |min . f `sse` min . g| we need
|min . f `sse` g| and
\begin{equation*}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |z <- any| \\
       & |x <- min (f x)| \\
       & |y <- g x| \\
       & |return (x, y)|
 \end{aligned}
 ~~|`sse`|~~
 \begin{aligned}
 |do|~ & |(x, y) <- any| \\
       & |filt (<=) (x, y)|\mbox{~~.}
 \end{aligned}
\end{equation*}
The first conjunct is immediate:
|min . f `sse` f `sse` g|.
For the second conjunct, we assume the righthand side of \eqref{eq:min-monotonic-monad} and reason:
%if False
\begin{code}
minMonoPf :: Ord b => (a -> P b) -> (a -> P b) -> P (b, b)
minMonoPf f g =
\end{code}
%endif
\begin{code}
        do  z <- any
            x <- min (f z)
            y <- g z
            return (x, y)
 `sse`   {- RHS of \eqref{eq:min-monotonic-monad} -}
        do  (y,z) <- any
            w <- f z
            filt (<=) (w,y)
            x <- min (f z)
            return (x,y)
 `sse`   {- |min|-cancelation -}
        do  (x,y,w) <- any
            filt (<=) (w, y)
            filt (<=) (x, w)
            return (x,y)
 `sse`   {- |(<=)| transitive -}
        do  (x,y) <- any
            return (x,y) {-"~~."-}
\end{code}
\end{proof}
\end{document}
