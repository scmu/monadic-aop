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

%% lhs2Tex knapsack.lhs | pdflatex --jobname=knapsack

%if False
\begin{code}
{-# OPTIONS_GHC -Wno-missing-methods #-}
import Prelude hiding (max, any)
import GHC.Base (Alternative)
import Data.Kind (Type)
import Control.Applicative
import Control.Monad

(===) :: a -> a -> a
(===) = undefined

infixr 0 ===

-- type P a = [a]
newtype P a = P a

instance Functor P where
instance Applicative P where
instance Monad P where
instance Alternative P where
instance MonadPlus P where
instance MonadFail P where

type List a = [a]

filt :: (a -> Bool) -> a -> P a
filt = undefined

max :: P (List Item) -> P (List Item)
max = undefined

max_v :: P (List Item) -> P (List Item)
max_v = max

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

type T a = List a

-- instance Functor T where

thinT_preceq :: T a -> P (T a)
thinT_preceq = undefined

thinT :: T a -> P (T a)
thinT = thinT_preceq

thin_preceq :: P a -> P (T a)
thin_preceq = undefined

thin :: P a -> P (T a)
thin = thin_preceq

collect :: P a -> T a
collect = undefined

mem :: T a -> P a
mem = undefined

filt_Q :: (a, a) -> P (a, a)
filt_Q = undefined

(<|.>) :: (a -> P b) -> (a -> P b) -> (a -> P b)
(f <|.> g) x = f x <|> g x

-- mergeT :: T a -> T a -> T a
-- mergeT = undefined

joinT :: T (T a) -> T a
joinT = undefined

foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []      = e
foldR f e (x:xs)  = f x =<< foldR f e xs {-"~~."-}
\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt
%include common/Relation.fmt

%%\email{scm@iis.sinica.edu.tw}

%format `leqv` = "\mathrel{\leq_{v}}"
%format leqv   = "(\leq_{v})"
%format `geqv` = "\mathrel{\geq_{v}}"
%format geqv   = "(\geq_{v})"
%format max_v = "\Varid{max}_{\leq_{v}}"
%format thin_preceq = "\Varid{thin}_{\preceq}"
%format <|.> = "\mathrel{\lbrack\hat{\!}\rbrack}"

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

\title{Knapsack in a Monadic Setting}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle

\section{Definitions}

Refer to other documents for definitions of |foldR|.

The function |subseq| non-deterministically computes a sub-sequence of the given list.
It can be defined inductively:
\begin{code}
subseq :: List a -> P (List a)
subseq []      = return []
subseq (x:xs)  = subseq xs <|> ((x:) <$> subseq xs) {-"~~,"-}
\end{code}
but we will use a |foldR|-based definition here:
\begin{spec}
subseq = foldR subs (return []) {-"~~,"-}
  where subs x ys = return ys <|> return (x:ys) {-"~~."-}
\end{spec}
%if False
\begin{code}
subs x ys = return ys <|> return (x:ys)
\end{code}
%endif

An item is specified by its value and weight:
\begin{code}
type Val = Int
type Wgt = Int
type Item = (Val, Wgt) {-"~~."-}

val :: List Item -> Val
val = sum . map fst {-"~~."-}

wgt :: List Item -> Wgt
wgt = sum . map snd {-"~~."-}
\end{code}
%if False
\begin{code}
w :: Wgt
w = undefined
\end{code}
%endif

Let |leqv| be defined by |xs `leqv` ys <=> val xs <= val ys|, thus
|max_v :: P (List Item) -> P (List Item)| choose those lists having the largest value.
The \emph{knapsack} problem can be defined by:
\begin{code}
knapsack :: List Item -> P (List Item)
knapsack = max_v . (filt ((w >) . wgt) <=< subseq) {-"~~."-}
\end{code}

\section{Fusion}

Recall the |foldR| fusion rule:
\begin{equation}
  |foldR g (h e) `sse` h . foldR f e {-"~"-}<=={-"~"-} g x =<< h m `sse` h (f x =<< m) {-"~~."-}|
\end{equation}

%format subsw = "\Varid{subs}_{w}"

The task is to fuse |filt ((w >) . wgt) <=< subseq| into |foldR subsw (return [])| for some |subsw|.
For the base case, we assume that |w| is non-negative, therefore |filt ((w >) . wgt) [] = return []| holds.
The function |subsw| should satisfy the fusion condition:
\begin{spec}
 subsw x =<< (filt ((w>).wgt) =<< m) `sse` filt ((w>).wgt) =<< (subs x =<< m) {-"~~."-}
\end{spec}
To construct |subsw| we reason:
%if False
\begin{code}
filtSubsFusion :: Item -> P (List Item) -> P (List Item)
filtSubsFusion x m =
\end{code}
%endif
\begin{code}
      filt ((w>).wgt) =<< (subs x =<< m)
 ===     {- definition of |subs| -}
      filt ((w>).wgt) =<< ((\ys -> return ys <|> return (x:ys)) =<< m)
 ===     {- distributivity, definition of |(<$>)| -}
      filt ((w>).wgt) =<< (m <|> (x:) <$> m)
 ===     {- distributivity -}
      filt ((w>).wgt) =<< m <|> (filt ((w>).wgt) =<< (x:) <$> m)
 `spse`  {- since |(filt p =<<) `sse` id| -}
      filt ((w>).wgt) =<< m <|> (filt ((w>).wgt) =<< ((x:) <$>( filt ((w>).wgt) =<< m)))
 ===     {- definition of |(<$>)| and monad laws, to factor out |filt ((w>).wgt) =<< m| -}
      filt ((w>).wgt) =<< m <|> ((filt ((w>).wgt) . (x:)) =<< (filt ((w>).wgt) =<< m))
 ===     {-  distributivity,  definition of |(<$>)|-}
      (\ ys -> return ys <|> filt ((w>).wgt) (x:ys)) =<< (filt ((w>).wgt) =<< m) {-"~~."-}
\end{code}
Therefore we have
\begin{spec}
  foldR subsw (return []) {-"~"-}`spse`{-"~"-} filt ((w >) . wgt) <=< subseq  {-"~~,"-}
     where subsw x ys = return ys <|> filt ((w>).wgt) (x:ys) {-"~~."-}
\end{spec}
%if False
\begin{code}
subsw :: Item -> List Item -> P (List Item)
subsw x ys = return ys <|> filt ((w>) . wgt) (x:ys)
\end{code}
%endif

Curiously, in the step using |(filt p =<<) `sse` id| we need only one side of the inclusion,
therefore we have not yet demanded that |(w>).wgt| being suffix-closed.

%if False
\begin{code}
thin_intro :: P (List Item) -> P (List Item)
thin_intro =
          max_v
  `spse`  (max_v . mem) <=< thin_preceq
\end{code}

\begin{code}
proper f g h  =
       ((f <=< g) . h)
  ===  (f <=< (g . h))
\end{code}
%endif

\section{Introducing Thinning}

Main calculation:
%if False
\begin{code}
knapsackDer :: Wgt -> List Item -> P (List Item)
knapsackDer w =
\end{code}
%endif
\begin{code}
         max_v . (filt ((w >) . wgt) <=< subseq)
 `spse`    {- |foldR|-fusion -}
         max_v . foldR subsw (return [])
 `spse`    {- introducing |thin| -}
         ((max_v . mem) <=< thin_preceq) . foldR subsw (return []) {-"~~."-}
 ===       {- |(f <=< g) . h = f <=< (g . h)|-}
         (max_v . mem) <=< (thin_preceq . foldR subsw (return []))
 `spse`    {- thinning theorem -}
         (max_v . mem) <=< foldR (\x -> thin_preceq . (subsw x <=< mem)) (thin_preceq (return []))
 `spse`    {- refinement below -}
         (max_v . mem) <=< foldR (\x t -> return (thinlist (mergeT t (addw x t)))) (return [[]])
 ===       {- -}
         (max_v . mem) <=< (return . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]])
 ===       {- monad law -}
         max_v . mem . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]]
 ===       {- -}
         return . head . foldr (\x t -> thinlist (mergeT t (addw x t))) [[]] {-"~~."-}
\end{code}


We let |T| be list of items \emph{sorted by descending weights}.
\begin{spec}
     thin_preceq (return [])
===  thinT (collect (return []))
===  thinT [[]]
===  [[]] {-"~~."-}
\end{spec}

%if False
\begin{code}
tstepDer x t =
\end{code}
%endif
\begin{code}
         (thin . (subsw x <=< mem)) t
 ===     thin (subsw x =<< mem t)
 ===     thin (return =<< mem t <|> ((filt ((w>) . wgt) . (x:)) =<< mem t))
 ===     thin (mem t <|> ((filt ((w>) . wgt) . (x:)) =<< mem t))
 ===     thinT (mergeT (collect (mem t)) (collect ((filt ((w>) . wgt) . (x:)) =<< mem t)))
 ===     thinT (mergeT t (joinT (map (collect . filt ((w>) . wgt) . (x:)) t)))
 ===     thinT (mergeT t (addw x t))
 `spse`  return (thinlist (mergeT t (addw x t)))
\end{code}

\begin{code}
addw :: Item -> T (List Item) -> T (List Item)
addw x = map (x:) . dropWhile (((snd x + w) >) . wgt)

mergeT :: T (List Item) -> T (List Item) -> T (List Item)
mergeT [] u = u
mergeT t [] = t
mergeT (xs:t) (ys:u)  | wgt xs >= wgt ys = xs : mergeT t (ys:u)
                      | otherwise        = ys : mergeT (xs:t) u

thinlist :: T (List Item) -> T (List Item)
thinlist [] = []
thinlist [xs] = [xs]
thinlist (xs:ys:xss)  | val xs > val ys = xs : thinlist (ys:xss)
                      | otherwise       = thinlist (ys:xss)
\end{code}

%if False
\begin{code}
propJoinChoice :: (a -> P b) -> (a -> P b) -> P a -> P b
propJoinChoice f g xs =
  (f <|.> g) =<< xs === (f =<< xs) <|> (g =<< xs)

propCollectMem :: (a -> P b) -> T a -> T b
propCollectMem f t =
       collect (f =<< mem t)
  ===  collect (join (fmap f (mem t)))
  ===  joinT (map (collect . f) t)
\end{code}
%endif

\end{document}
