\documentclass[dvipsnames, fleqn]{jfp}
\usepackage{url}
\let\Bbbk\relax  % avoiding error "Bbbk' already defined."
\usepackage{tikz}
\usepackage{chngcntr} % for \counterwithout
\usepackage{caption}
\usepackage{subcaption}
\usepackage{scalerel}

%% lhs2TeX monadic-opt.lhs | pdflatex --jobname=monadic-opt

%if False
\begin{code}
import Prelude hiding (repeat)
(===) :: a -> a -> a
(===) = undefined

infixr 0 ===
\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include Formatting.fmt
%include Relation.fmt


%%\email{scm@iis.sinica.edu.tw}

\usepackage{doubleequals}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

\def\commentbegin{\quad$\{$~}
\def\commentend{$\}$}
\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}
\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}

\newcommand{\todo}[1]{{\color{brown}\lbrack{\bf to do}: #1 \rbrack}}

\counterwithout{equation}{section}

%format b0
%format b1
%format b1'
%format y0
%format y1
%format y2
%format z0
%format z1
%format z2
%format t0
%format t1
%format u0
%format u1
%format Set1


\begin{document}

\righttitle{A Monadic Notation for Calculating Optimisation Algorithms}
\lefttitle{S-C. Mu}

\title{A Monadic Notation for Calculating Optimisation Algorithms}
\begin{authgrp}
\author{Shin-Cheng Mu}
\affiliation{Institute of Information Science, Academia Sinica, Taipei, Taiwan}
\author{You-Zheng Yu}
\affiliation{National Taiwan University, Taipei, Taiwan}
\end{authgrp}

\date{}
\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{yyyy/xxxxx}
\jnlDoiYr{2025}

\begin{abstract}

\end{abstract}

\maketitle

\section{Introduction}
\label{sec:intro}

Program calculation is the technique of constructing a program from a specification in a stepwise manner, where each step is justified by established properties.
A canonical example of functional program derivation is the \emph{maximum segment sum} problem: given a list of numbers, compute the largest possible sum of a consecutive segment.
The problem can be specified by:
\begin{spec}
  mss :: List Int -> Int
  mss = maximum . map sum . segments {-"~~,"-}
\end{spec}
where |segments :: List a -> List (List a)| computes all consecutive segments of a given list. The sums of each segment are computed by |map sum|, before |maximum :: List Int -> Int| returns the largest integer.
The one-liner specification above, if executed, is rather inefficient.
However, within several lines of reasoning, one may transform it to a program consisting of a |foldr| before a |maximum|, both run in time linear with respec to the length of the input:
\begin{spec}
   maximum . map sum . segments
=    {- |segments| can be defined as |map inits . tails| -}
   maximum . map sum . map inits . tails
=    {- ... other steps omitted ... -}
   maximum . foldr (\x y -> (x + y) `max` 0) 0 {-"~~."-}
\end{spec}
The specification |mss| is a total function --- for each input it computes exactly one maximum sum.
The final program and the specification are related by equality,
which means that the final program must return the \emph{one} exact result which |mss| would compute, given any input.

Pedagogical examples of program calculation for such optimisation problems tend to return the optimal value (in this case, the sum), rather than the solution that yields the optimal value (the list),
because this approach would not be feasible otherwise.
When there are multiple solutions that yield the optimal value,
the specification, being a function, has to pick a particular one, which the implementation has to return.
In the construction of a sorting algorithm, for example,
having to decide, in the specification phase, what list to return when there are items having the same key would severely limit the algorithm one can derive (e.g., limiting one to construct stable sorting), if not making the specification impossible at all (it is hard to predict how, say, quicksort arranges items having the same keys).
One therefore needs a different framework, where a specification describes a collection of solution that is allowed by the final program, which no longer equals, but is instead contained by the specification.

One of the possibilities is to use relations as specifications.
Foundations of this approach were laid by works including \cite{BackhousedeBruin:91:Relational}, \cite{Aarts:92:Relational}, \cite{BackhouseHoogendijk:92:Elements}, etc,
before \cite{BirddeMoor:97:Algebra}, taking a more abstract, categorical approach,
presented general theories for constructing various forms of greedy, thinning, and dynamic programming algorithms.
\cite{BirddeMoor:97:Algebra} presented a point-free calculus that is concise, elegant, and surprisingly expressive.
\todo{Why AoP is amazing}
Such conciseness and expressiveness also turned out to be a curse, however.
For those who not sharing the background, the calculus has a sharp learning curve, which limited its popularity to a small circle of enthusiasts.
\todo{Why AoP can't be popular.}

Efforts has been made to re-introduce variables back to the relational calculus, for example, \cite{deMoorGibbons:00:Pointwise}.
One cannot help feeling unease with some of its peculiarities, for example
\todo{What?}
Around two decades later, \cite{BirdRabe:19:How} presented a theoretical background of ``multifunctions'',
which was then used in
\cite{BirdGibbons:20:Algorithm}.
\todo{What is wrong with it?}

\todo{Why we recommend using monads.}

\paragraph*{In this article} we consider problems having the form:
\begin{spec}
  max . (filt p <=< foldR f e) {-"~~,"-}
\end{spec}
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kliseli composition and |(.)| is ordinary function composition.
Given an input of type |List A|, the collection of all solution candidates is generated by |foldR f e :: List A -> M B|, a monadic variation of fold on lists.
The function |filt :: (b -> Bool) -> b -> M b| keeps those solutions that satisfy predicate |p|, and |max :: M b -> M b| keeps only those having maximum value under some chosen ordering.
In all cases we consider, the filtering phase can be fused into |foldR|, therefore the actual form of the problem is |max . foldR f' e'|.
We then discuss conditions under which the specification can be refined to a fold-based greedy algorithm --- one where we greedily keep only the locally best solution in each step of the fold,
or a \emph{thinning} algorithm, where in each step of the fold we keep a set of solution candidates that still might be useful.

All these were covered in \cite{BirddeMoor:97:Algebra}.
Rather than solving new problems or discovering new algorithms, the purpose of this article is to propose new notations that make previous derivations more accessible, while still being accurate without being too cumbersome.
In traditional functional programming, one may reason about a functional program by induction on the input.
This article aims to show that reasoning about monadic programs is just like that: one only need to make use of monad laws and properties of effect operators.
\todo{Say more, and polish.}

\section{Preliminaries}

We introduce in this section the building blocks we need.

\subsection{Nondeterminism Monad}
\label{sec:non-det-monad}

A monad consists of a type constructor |M| and operators |return :: a -> M a| and |(>>=) :: M a -> (a -> M b) -> M b| that satisfy the \emph{monad laws}:
\begin{align*}
& \mbox{{\bf right identity}:} & |m >>= return| &= |m|  \mbox{~~,}\\
& \mbox{{\bf left identity}:}  & |return x >>= f| &= |f x| \mbox{~~,}\\
& \mbox{{\bf associativity}:}  &|(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
\end{align*}
The operator |(>>) :: M a -> M b -> M b|, defined by |m >> n = m >>= (\_ -> n)|, ignores the result of |m| before executing |n|.
A function |a -> b| can be lifted to monad |M| by |fmap|:
\begin{spec}
fmap :: (a -> b) -> M a -> M b
fmap f m = m >>= (return . f) {-"~~."-}
\end{spec}
We also write |fmap f m| infix as |f <$> m|, where the operator |(<$>)| is left-associative like function application.
It follows from the monad laws that
|id <$> m = m| and |(f . g) <$> m = f <$> (g <$> m)|, that is, |M| is a functor with |(<$>)| as its functorial map.

In this paper we will also make extensive use of the reverse bind and the Kliseli composition:
\begin{spec}
(=<<) :: (a -> M b) -> M a -> M b
f =<< m = m >>= f {-"~~,"-}

(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)
(f <=< g) x = f =<< g x {-"~~."-}
\end{spec}
Kliseli composition |(<=<)| is associative, |(=<<)| is right-associative, and both bind looser than function composition |(.)|.
We will add parentheses where there might be confusion.

Alternatively, a monad can be defined by three operators: |return :: a -> M a|, |join :: M (M a) -> M a|, and its functorial map |(<$>) :: (a -> b) -> M a -> M b|. The two styles of definitions are equivalent, as |(>>=)| can be defined in terms of |join| and |(<$>)|, and vice versa:
\begin{spec}
join :: M (M a) -> M a
join m = m >>= id {-"~~,"-}

(>>=) :: M a -> (a -> M b) -> M b
m >>= f = join (f <$> m) {-"~~."-}
\end{spec}

Non-determinism is the only effect we are concerned with in this article: |M a| denotes a non-deterministic computation that may yield zero, one, or more values of type |a|.
We let |mplus :: M a -> M a -> M a| denote non-deterministic choice and |mzero :: M a| failure. Together they form a monoid (that is, |mplus| is associative with |mzero| as its identity element).
We demand that |(>>=)| distributes into |mplus| from both sides:
\begin{align*}
  |m >>= (\x -> f x `mplus` g x)| &= |(m >>= f) `mplus` (m >>= g)| \mbox{~~,}\\
  |(m `mplus` n) >>= f| &= |(m >>= f) `mplus` (n >>= f)| \mbox{~~.}
\end{align*}
and that |mzero| is a zero of |(>>=)|:
\begin{align*}
  |mzero >>= f| &= |mzero| \mbox{~~,}\\
  |f >> mzero|  &= |mzero| \mbox{~~.}
\end{align*}
Furthermore, |mplus| is commutative (|m `mplus` n = n `mplus` m|) and idempotent (|m `mplus` m = m|).

The containment relation of non-determinism monad is defined by:
\begin{spec}
m `sse` n = (m `mplus` n = n) {-"~~."-}
\end{spec}
When |m `sse` n|, we say that |m| refines |n|.
Every value |m| might yield is a value allowed by |n|.
We also lift the relation to functions: |f `sse` g = (forall x : f x `sse` g x)|.

A structure that supports all the operations above is the set monad: for all type |a|,
|m :: P a| is a set whose elements are of type |a|,
|mzero| is the empty set, |mplus| is set union for two sets, |join| is union for a set of sets, |(`sse`)| is set inclusion, |return| forms a singleton set, and |m >>= f| is given by |join {f x || x <- m }|.
For the rest of the paper we take |M = P|.

The set |any :: P a| contains all elements having type |a|.
Computationally, it creates an arbitrary element of its type.
The command |filt : (a -> Bool) -> a -> P a| is defined by
\begin{spec}
filt p x  | p x        = return x
          | otherwise  = mzero {-"~~."-}
\end{spec}
It returns its input |x| if it satisfies |p|, and fails otherwise.%
\footnote{Conventionally there is a function |guard :: Bool -> M ()| that returns |()| when the input is true, and |filt p x| is defined by |do { guard (p x); return x }|. In this paper we try to introduce less construct and use only |filt|.}


\paragraph*{Example: Prefixes and Suffixes.}~
The function |prefix| non-deterministically computes a prefix of the given list:
\begin{code}
prefix :: List a -> P (List a)
prefix []      = return []
prefix (x:xs)  = return [] <|> (x:) <$> prefix xs {-"~~."-}
\end{code}
For example, |prefix [1,2,3]| yields four possibilities: |[]|, |[1]|, |[1,2]|, and |[1,2,3]|.
With idempotency of |(<||>)|, by a simple case analysis one can show that |return [] <||> prefix xs = prefix xs| for all |xs|.
Therefore we have |return [] `sse` prefix xs|.

%format prefixP = "\Varid{prefix}^{+}"
Meanwhile, |prefixP :: List a -> P (List a)| below computes the non-empty prefixes:
\begin{code}
prefixP []      = mzero
prefixP (x:xs)  = return [x] <|> (x:) <$> prefixP xs {-"~~."-}
\end{code}
We should have |prefixP `sse` prefix| --- proof of which will be discussed in the next section.

Conversely, the function |suffix| non-deterministically returns a suffix of the given list:
\begin{code}
suffix :: List a -> P (List a)
suffix []      = return []
suffix (x:xs)  = return (x:xs) <|> suffix xs {-"~~."-}
\end{code}
Evaluating |suffix [1,2,3]| yields |[1,2,3]|, |[2,3]|, |[3]|, and |[]|.
We get all segments of a list by |prefix <=< suffix|.

\subsection{An Agda Model of Set Monad}

To ensure that there is indeed a model of our set monad, we built one in Agda.
A first attempt was to represent a set |P| by its characteristic predicate:
\begin{spec}
P : Set -> Set1
P a = a -> Set {-"~~."-}
\end{spec}
Given |x : a|, |P x| is a type, or a proposition, stating the conditions under which |x| is in the set denoted by |P x|.
Monad operators |return| and |(>>=)| are defined by
\begin{spec}
return : {a : Set} -> a -> P a
return x  = \y ->  x <=> y {-"~~,"-}
(>>=) : {a b : Set} -> P a -> (a -> P b) -> P b
m >>= f   = \y -> Sum{-"\!"-}[x `mem` a] (m x * f x y) {-"~~,"-}
\end{spec}
where |(<=>)| is propositional equality, and |Sum| denotes dependent pair.
That is, |y| is a member of the set |return x| exactly when |x <=> y|,
and |y| is a member of |m >>= f| if there exists a witness |x|, presented in the dependent pair, that is a member of the set |m|, and |y| is a member of the set |f x|.

We would soon get stuck when we try to prove any of its properties.
To prove the right identity law |m >>= return = m|, for example, amounts to proving that
\begin{spec}
  (\y -> Sum{-"\!"-}[x `mem` a] (m x * x <=> y)) {-"~"-}<=>{-"~"-} m {-"~~."-}
\end{spec}
The righthand side |m| is a function which yields, for each member |y|, a proof that |y| is in |m|,
while the lefthand side is a function which produces, for each member |y|, a dependent pair consisting of a value |x : a| , a proof that |x| is in |m|, and a proof that |x <=> y|.
While logically we recognize that they are equivalent, in the type theory of Agda the two sides are different, albeit isomorphic, types.

\todo{Cubical Agda}

\subsection{Monadic Fold}

We define the monadic fold on lists as:
\begin{spec}
foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []      = e
foldR f e (x:xs)  = f x =<< foldR f e xs {-"~~."-}
\end{spec}
The function |prefix| defined in Section~\ref{sec:non-det-monad} can be defined in terms of |foldR|:
\begin{spec}
prefix    = foldR pre (return [])
pre x ys  = return [] <|> return (x : ys) {-"~~."-}
\end{spec}
%if False
\begin{code}
pre x ys = return [] <|> return (x : ys)
\end{code}
%endif
Due to the way we define our |foldR|, the definition above returns |[]| more frequently than that in Section~\ref{sec:non-det-monad}.
The equivalence of the two definitions of |prefix| depends on
commutativity and idempotency of |(<||>)|.
% Similarly, |prefixP| is a |foldR|:
% %format preP = "\Varid{pre}^{+}"
% \begin{spec}
% prefixP    = foldR preP mzero
% preP x ys  = return [x] <|> return (x : ys) {-"~~."-}
% \end{spec}

Given |h :: List a -> P b|, the \emph{fixed-point properties}, that is, sufficient conditions for |h| to contain or be contained by |foldR f e| are given by:
\begin{align}
|foldR f e `sse` h| & |{-"~"-}<=={-"~"-} e `sse` h [] {-"\,"-}&&{-"\,"-} f x =<< h xs `sse` h (x:xs)  {-"~~,"-}| \label{eq:foldRPrefixPt} \\
|h `sse` foldR f e| & |{-"~"-}<=={-"~"-} h [] `sse` e {-"\,"-}&&{-"\,"-} h (x:xs) `sse` f x =<< h xs  {-"~~."-}| \label{eq:foldRSuffixPt}
\end{align}
The properties above can be proved by routine induction on the input list.

For an example, consider showing that |prefixP `sse` prefix|.
One may go back to first principles and use an induction on the input list.
Alternatively, one may use the fixed-point property \eqref{eq:foldRPrefixPt}, exploiting the fact that |prefixP| is a |foldR|.
Through the latter route, one needs to show that |mzero `sse` return []|,
and that |preP x =<< prefix xs `sse` prefix (x:xs)|.
Proof of the latter proceeds by utilising monad laws and distributivity:
\begin{spec}
        preP x =<< prefix xs
 ===      {- definition of |preP| -}
        (\ys -> return [x] <|> return (x:ys)) =<< prefix xs
 ===      {- |(=<<)| distributes into |(<||>)| -}
        ((\ys -> return [x]) =<< prefix xs) <|> ((\ys -> return (x:ys)) =<< prefix xs)
 ===      {- monad laws, definition of |(<$>)| -}
        return [x] <|> (x:) <$> prefix xs
 ===      {- definition of |(<$>)|, distributivity -}
        (x:) <$> (return [] <|> prefix xs)
 ===      {- since |return [] `sse` prefix xs|, or |return [] <||> prefix xs = prefix xs| -}
        (x:) <$> prefix xs
 `sse`    {- since |m `sse` n <||> m| for all |m|, |n| -}
        return [] <|> (x:) <$> prefix xs
 ===      {- definition of |pre|, distributivity and monad laws -}
        pre x =<< prefix xs
 ===      {- definition of |prefix| -}
        prefix (x:xs) {-"~~."-}
\end{spec}
Yet another approach is to use \eqref{eq:foldRSuffixPt} and exploit the fact that
|prefix| is a |foldR|.
One would eventually get stuck and realise that we need to prove a stronger property:
\begin{spec}
   return [] <|> prefixP xs `sse` prefix xs {-"~~."-}
\end{spec}
This is a case where a stronger variation of a property is easier to prove!
The actual proof is left to the readers as an exercise.

% One would eventually get stuck and realise that we need to prove a stronger property:
% \begin{spec}
%   return [] <|> prefixP xs `sse` prefix xs {-"~~."-}
% \end{spec}
% This is a case where a stronger variation of a property is easier to prove!
% To prove the property above by \eqref{eq:foldRPrefixPt}, we need to show that
% |return [] <||> fail `sse` return []|, which is immediate, and that
% \begin{spec}
%  return [] <|> prefixP (x:xs) `sse` pre x =<< (return [] <|> prefixP xs) {-"~~."-}
% \end{spec}
% We try to simply the more complex righthand side to the lefthand side.
% The proof proceeds by utilising monad laws and distributivity:
% \begin{spec}
%       pre x =<< (return [] <|> prefixP xs)
%  ===    {- |(=<<)| distributes into |(<||>)| -}
%       (pre x =<< return []) <|> (pre x =<< prefixP xs)
%  ===    {- definition of |pre|, monad laws -}
%       return [] <|> return [x] <|> (pre x =<< prefixP xs)
%  ===    {- definition of |pre| -}
%       return [] <|> return [x] <|> ((\ ys -> return [] <|> return (x : y)) =<< prefixP xs)
%  ===    {- |(=<<)| distributes into |(<||>)|, monad laws, definition of |(<$>)| -}
%       return [] <|> return [x] <|> return [] <|> (x:) <$> prefixP xs
%  ===    {- idempotency of |(<||>)|, definition of |prefixP|  -}
%       return [] <|> prefixP (x:xs) {-"~~."-}
% \end{spec}
% We wanted an inclusion but end up proving an equality.
% We have actually proved that |return [] <||> prefixP xs = prefix xs|.

With the fixed-point properties, we can prove the following |foldR| fusion rule:
\begin{equation}
  |foldR g (h e) `sse` h . foldR f e {-"~"-}<=={-"~"-} g x =<< h m `sse` h (f x =<< m) {-"~~."-}|
  \label{eq:foldRFusion}
\end{equation}

%format f0
%format f1
%format e0
%format e1
With \eqref{eq:foldRPrefixPt} it is easy to show that |foldR| is monotonic:
\begin{equation}
|foldR f0 e0 `sse` foldR f1 e1 {-"~"-}<=={-"~"-} f0 `sse` f1 && e0 `sse` e1  {-"~~."-}|
\label{eq:foldR-monotonicity}
\end{equation}
Note that in |f0 `sse` f1|, set inclusion is lifted to denote |f0 x y `sse` f1 x y| for all |x| and |y|.

Finally, monadic |foldR| can be refined to pure |foldr| if both of its arguments are pure:
\begin{equation}
|return (foldr f e) = foldR (\x -> return . f x) (return e) {-"~~."-}|
\label{eq:foldr-foldR}
\end{equation}

\paragraph*{Scan and Its Properties.}~
Introducing a |scanr| is often a key step in speeding up algorithms related to lists.
For those who not familiar with it, |scanr :: (a -> b -> b) -> b -> List a -> List b|
is like |foldr|, but records the intermediate results of each step in a list.
For example, while |foldr (+) 0| computes the sum of a list, |scanr (+) 0| computes the running sum: |scanr (+) 0 [1,2,3] = [1+(2+(3+0)), 2+(3+0), 3+0, 0]| |= [6,5,3,0]|.
An important property of |scanr| is the following \emph{scan lemma}:
\begin{spec}
  scanr f e = map (foldr f e) . tails {-"~~,"-}
\end{spec}
where |tails :: List a -> List (List a)| returns all the suffixes of the input list.
That is, |scanr| computes |foldr| for every suffix of the input.

For this article, we define a monadic variation of |scanr|:
\begin{code}
scanR :: (a -> b -> P b) -> P b -> List a -> P (List b)
scanR f e []        = wrap <$> e
scanR f e (x : xs)  = do  ys <- scanR f e xs
                          z <- f x (head ys)
                          return (z : ys) {-"~~,"-}
\end{code}
where |wrap x = [x]|.
With |f| and |e| being non-deterministic, |scanR f e| returns a set of all possible lists.
\todo{example.}

The function |scanR| can be defined in terms of a |foldR|:
\begin{spec}
scanR f e = foldR f' (wrap <$> e)
  where f' x ys = do {z <- f x (head ys); return (z:ys)} {-"~~."-}
\end{spec}
Therefore, from \eqref{eq:foldr-foldR} one can induce that |scanR| with a
deterministic step function is itself deterministic:
\begin{align}
  |scanR (\x -> return . f x) (return e)| ~&=~ |return . scanr f e| \mbox{~~.}
    \label{eq:scanr-scanR}
\end{align}

The main property of |scanR| that we need for this article is a monadic variation of \emph{scan lemma}.
Let the function |member| non-deterministically returns an element of the given list:
\begin{code}
member :: List a -> P a
member []        = mzero
member (x : xs)  = return x <|> member xs {-"~~."-}
\end{code}
Our scan lemma for |scanR| goes:
%if False
\begin{code}
propScanLemmaStmt :: (a -> b -> P b) -> P b -> List a -> P b
propScanLemmaStmt f e =
   member <=< scanR f e === foldR f e <=< suffix
\end{code}
%endif
\begin{equation}
  |member <=< scanR f e === foldR f e <=< suffix | \mbox{~~.}
  \label{eq:ScanLemma}
\end{equation}
That is, every element in any list computed by |scanR| is a result of |foldR| applied to some suffix of the input, and vice versa.
\begin{proof}
Induction on the input. For the inductive case we reason:
%if False
\begin{code}
proofScanLemmaInd :: (a -> b -> P b) -> P b -> a -> List a -> P b
proofScanLemmaInd f e x xs =
\end{code}
%endif
\begin{code}
      foldR f e =<< suffix (x : xs)
 ===    {- definition of |suffix| -}
      foldR f e =<< (return (x:xs) <|> suffix xs)
 ===    {- |(=<<)| distributes into |(<||>)| -}
      (foldR f e =<< return (x:xs)) <|> (foldR f e =<< suffix xs)
 ===    {- induction -}
      foldR f e (x : xs) <|> (member =<< scanR f e xs)
 ===    {- definition of |foldR| -}
      (f x =<< foldR f e xs) <|> (member =<< scanR f e xs)
 ===    {- by \eqref{eq:HeadScan}: |head <$> scanR f e xs === foldR f e xs| -}
      (f x =<< (head <$> scanR f e xs)) <|> (member =<< scanR f e xs)
 ===    {- distributivity between |(=<<)| and |(<||>)|, switching to |do|-notation -}
      do  ys <- scanR f e xs
          f x (head ys) <|> member ys
 ===    {- monad laws -}
      do  ys <- scanR f e xs
          z <- f x (head ys)
          return z <|> member ys
 ===    {- definitions of |scanR| and |member| -}
      member =<< scanR f e (x : xs) {-"~~."-}
\end{code}
\end{proof}
In the last few steps of the proof we find it more comprehensible to use the |do|-notation.
In the proof we needed the property that the head of the list returned by |scanR| is always the result of |foldR| applied to the entire list, and vice versa:
%if False
\begin{code}
-- propHeadScanStmt :: (a -> b -> P b) -> P b -> List a -> P b
propHeadScanStmt f e xs =
   head <$> scanR f e xs === foldR f e xs
\end{code}
%endif
\begin{equation}
  |head <$> scanR f e xs === foldR f e xs| \mbox{~~.} \label{eq:HeadScan}
\end{equation}
% \begin{proof}
% Induction on |xs|. The case when |xs := []| is immediate.
% For |xs := x:xs| we reason:
%if False
\begin{code}
-- propHeadScanStmt :: (a -> b -> P b) -> P b -> List a -> P b
propHeadScanPfInd f e x xs =
\end{code}
\begin{code}
      head <$> scanR f e (x : xs)
 ===    {- definition of |scanR| -}
      head <$> do  ys <- scanR f e xs
                   z <- f x (head ys)
                   return (z : ys)
 ===    {- definition of |(<$>)|, monad laws -}
      do  ys <- scanR f e xs
          z <- f x (head ys)
          return z
 ===    {- monad law -}
      do  ys <- scanR f e xs
          f x (head ys)
 ===    {- |do|-notation -}
      f x =<< (head <$> scanR f e xs)
 ===    {- induction -}
      f x =<< foldR f e xs
 ===    {- definition of |foldR| -}
      foldR f e (x : xs) {-"~~."-}
\end{code}
%endif
%\end{proof}
Proof of \eqref{eq:HeadScan} is a routine induction, which we leave to the reader as an exercise.

\subsection{Maximum}

Consider a binary relation |unlhd| on some type |a|.
A value |y :: a| is a maximum of |xs :: P a| if |y| is in |xs|, and for every element |x `elem` xs| we have |y `unrhd` x|.
The definition itself does not assume much from |unlhd|.
In particular, since |unlhd| is not necessarily anti-symmetric, maximum elements might not be unique.
The function |max_unlhd :: P a -> P a| takes a set and returns a refined set that keeps all the maximum elements and nothing else.
In set-theoretical notation, |max_unlhd| can be defined by the following equivalence:
for all |xs| and |ys|,
\begin{equation}
|ys `sse` max_unlhd xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall y `mem` ys : (forall x `mem` xs : y `unrhd` x)) {-"~~."-}|
\label{eq:max-def-set}
\end{equation}
We omit the subscript |unlhd| when it is clear from the context or not relevant.
The |(==>)| direction of \eqref{eq:max-def-set}, letting |ys = max xs|, says that |max xs| is a subset of |xs|, and every member in |max xs| is no lesser than any member in |xs|. The |(<==)| direction of \eqref{eq:max-def-set} says that |max xs| is the largest such set --- any |ys| satisfying the righthand side is a subset of |max xs|.

In calculation, we often want to refine expressions of the form |max . f| where |f| generates a set. Therefore the following \emph{universal property} of |max| is more useful: for all |h| and |f| of type |a -> P b|,
\begin{equation}
|h `sse` max_unlhd . f {-"~"-}<==>{-"~"-} h `sse` f && (forall x : (forall y1 `mem` h x : (forall y0 `mem` f x : y1 `unrhd` y0))) {-"~~."-}|
\label{eq:max-univ-set}
\end{equation}
Properties \eqref{eq:max-def-set} and \eqref{eq:max-univ-set} are equivalent.
To prove \eqref{eq:max-def-set} from \eqref{eq:max-univ-set}, for instance, one let |h = const ys| and |f = const xs|.

The aim of our work, however, is to capture the ideas above in a monadic notation, such that programs can be manipulated and reasoned about in the monadic language.
It turns out that \eqref{eq:max-univ-set} can be rewritten monadically as below:
%\begin{spec}
%X `sse` min_R . f {-"\,"-}<=> {-"\,"-}  X `sse` f &&
%                                        (  do  a   <- any
%                                               b0  <- X a
%                                               b1  <- f a
%                                               return (b0, b1) {-"\,"-} `sse`
%                                                 do  (b0, b1) <- any
%                                                     filt R (b0, b1) {-"\,"-}) {-"~~."-}
%\end{spec}
\begin{equation}
|h `sse` max_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y1 <- h x| \\
       & |y0 <- f x| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:max-univ-monadic}
\end{equation}
In \eqref{eq:max-univ-monadic} and from now on we abuse the notation a bit,
using |filt unrhd| to denote |filt (\(y,z) -> y `unrhd` z)|.
The large pair of parentheses in \eqref{eq:max-univ-monadic} relates two monadic values. On the lefthand side we generate a pair of values |y1| and |y0|, which are respectively results of |h| and |f| for the same, arbitrarily generated input |x|. The inclusion says that |(y1, y0)| must be contained by the monad on the righthand side, which consists of all pairs |(y1, y0)| as long as |y1 `unrhd` y0|.

Letting |h = max| and |f = id| in \eqref{eq:max-univ-monadic}, we get |max `sse` id| on the righthand side.
Letting |h = max . f| in \eqref{eq:max-univ-monadic}, we get on the righthand side the |max|-cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y1 <- max (f x)| \\
       & |y0 <- f x| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)| \mbox{~~.}
 \end{aligned}
 \label{eq:max-cancelation}
\end{equation}

\noindent
{\bf Note}: by defining the ``split'' operator |split f g x = do { y <- f x; z <- g x; return (y,z) }|,
\eqref{eq:max-univ-monadic} can be written more concisely as below:
\begin{equation*}
|h `sse` max_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
|split h f =<< any {-"\,"-}`sse`{-"\,"-} filt unrhd =<< any| \mbox{~~.}
\end{equation*}
We may then manipulate expressions using properties of the |split| operator.
The |max|-cancelation law \eqref{eq:max-cancelation} is written neatly as
%|split (max_unlhd . f) f =<< any {-"\,"-}`sse`{-"\,"-} filt unrhd =<< any|.
\begin{equation*}
  |split (max_unlhd . f) f =<< any {-"\,"-}`sse`{-"\,"-} filt unrhd =<< any| \mbox{~~.}
\end{equation*}
Unfortunately, in numerous occasions in calculation we need the flexibility provided by |do|-notation, therefore the split notation is not as useful as we would like. {\bf End of Note.}

Recall that |max_unlhd| does not assume much from |unlhd|.
It is likely that there is no maximum in a set |xs| --- there is no element that is larger than every other element with respect to |unlhd|.
In that case |max_unlhd xs| reduces to the empty set |mzero|.
That is fine at the specification stage,
although we might not be able to refine this specification to a total function.
We will discuss about that soon.

% Maximum is defined as the dual of minimum:
% \begin{spec}
%   max_unlhd = min_unrhd {-"~~."-}
% \end{spec}

\paragraph*{Promotion into Kliseli Composition.}~
The function |max| promotes into |join|:
%if False
\begin{code}
-- propMinJoin :: forall {k} (a :: Type). P (P a) -> P a
propMaxJoin xss = max (join xss) === max (join (fmap max xss))
\end{code}
%endif
\begin{equation}
  |max . join === max . join  . fmap max| \mbox{~~.}
   \label{eq:MaxJoin}
\end{equation}
Consider an input |xss :: P (P a)|, a set of sets, as the input for both sides. On the lefthand side, |xss| is joined into a single set, from which we keep the minimums. It is equivalent to the righthand side, where we choose the minimums of each of the sets in |xss|, before keeping their minimums.
With \eqref{eq:MaxJoin} and the definition of |(>>=)| by |join| we can show how |max| promotes into |(=<<)| or |(<=<)|:
\begin{equation}
  |max . (f <=< g) === max . ((max . f) <=< g)| \mbox{~~,}
   \label{eq:MaxKComp}
\end{equation}
or |max (f =<< g x) === max ((max . f) =<< g x)| for all |x|.
%The proof goes:
%%if False
%\begin{code}
%-- propMaxJoin :: forall {k} (a :: Type). P (P a) -> P a
%propMaxBind f g xs =
%\end{code}
%%endif
%\begin{code}
%      max (f =<< g xs)
% ===    {- definition of |(=<<)| -}
%      max (join (fmap f (g xs)))
% ===    {- \eqref{eq:MaxJoin} -}
%      max (join (fmap (max . f) (g xs)))
% ===    {- definition of |(=<<)| -}
%      max ((max . f) =<< g xs) {-"~~."-}
%\end{code}

\paragraph*{Conversion from Lists.}~
In the last few steps of a program calculation we usually want to refine a monadic |max| to a function on lists.
If |unlhd| is total (that is, for all |x| and |y| of the right type, at least one of |x `unrhd` y| or |y `unrhd` x| holds), and if |xs| is non-empty, we have
\begin{equation}
 |return (maxlist xs) `sse` max_unlhd (member xs) | \label{eq:MaxMaxList}
\end{equation}
where |maxlist| is some implementation of maximum on non-empty lists, e.g.
\begin{spec}
  maxlist :: List a -> a
  maxlist [x] = x
  maxlist (x : y : xs) = x `bmax` maxlist (y : ys) {-"~~,"-}
   where x `bmax` y  =if x `unrhd` y then x else y {-"~~."-}
\end{spec}
That |unlhd| being total guarantees that maximum exists for non-empty |xs|.
The function |maxlist| may decide how to resolve a tie --- in the implementation above, for example, |maxlist| prefers elements that appears earlier in the list.

\paragraph*{In the Agda Model}
we implement |min| by:

\todo{more here.}

It is then proved in Agda that the above implementation satisfies \eqref{eq:max-univ-monadic}.

\section{The Greedy Theorem}

As stated in Section \ref{sec:intro}, this article focuses on problems of the form:
\begin{spec}
  max_unlhd . (filt p <=< foldR f e) {-"~~,"-}
\end{spec}
that is, problems whose solution candidates can be generated by a monadic fold.
In |foldR|, given the current element |x :: a| of the list, the function |f x :: b -> P b| takes a candidate of type |b| and extends it in all possible ways.
If certain conditions hold, however, we would not need all of them, but the locally best one.

Recall that we aim to compute the maximum solutions under ordering |unlhd|.
Therefore, when |y1 `unrhd` y0|, we call |y1| the preferred solution, and |y0| the (possibly) lesser one.
A function |f : b -> P b| is said to be \emph{Hoare-monotonic on |unrhd|} if
\begin{equation}
  |(forall y1, y0, z0 : y1 `unrhd` y0 && z0 `elem` f y0 ==> (exists z1 : z1 `elem` f y1 && z1 `unrhd` z0)) {-"~~."-}| \label{eq:monotonicity-logic}
\end{equation}
In words, let |y0| be a solution that is possibly lesser than |y1|,
\eqref{eq:monotonicity-logic} says that for any solution |z0| that |f| can produce from |y0|,
there must be at least one solution |f| may generate from |y1| that is no lesser than |z0|.
We may therefore safely drop |y0|.

To make use of Hoare-monotonicity in our proofs, \eqref{eq:monotonicity-logic} can be written as:
\begin{equation}
\setlength{\jot}{-1pt}
\begin{aligned}
|do|~ & |(y1, y0) <- any|\\
      & |filt unrhd (y1, y0)|\\
      & |z0 <- f y0| \\
      & |return (y1, z0)|
\end{aligned}
~~|`sse`|~~
\begin{aligned}
|do|~& |(y1, z0) <- any|\\
     & |z1 <- f y1|\\
     & |filt unrhd (z1, z0)|\\
     & |return (y1, z0)| \mbox{~~.}
\end{aligned}
\label{eq:monotonicity}
\end{equation}
On the lefthand side of \eqref{eq:monotonicity} we generate a pair of values |(y1, y0)| with the constraint that |y0| is possibly lesser.
Then we let |z0| be \emph{any} result we generate by |f| from the lesser solution |y0|, and return the pair |(y1, z0)|.
The inclusion means that nothing in the lefthand side is missing in the righthand side. The righthand side must be able to generate this particular pair |(y1, z0)|, that is, for this |(y1, z0)| the |filt| in the righthand side must succeed at least once.
Therefore, there must \emph{exist} some |z1| generated from |y1|, the preferred solution, such that |z1 `unrhd` z0|.

Notice that, while the pairs |(y1, z0)| in the righthand size are generated by |any|,
we care only about those |(y1, z0)| that are |return|ed by the lefthand side.
\footnote{To comprehend \eqref{eq:monotonicity}, for some readers it might help to see an example where it does \emph{not} hold. See Section~\ref{sec:ex:0-1-knapsack}.}

Again, by defining |(f *** g) x = do {y <- f x; z <- g x; return (y,z)}|,
\eqref{eq:monotonicity} can be written in point-free style as:
\begin{spec}
  (id *** f) =<< filt unrhd =<< any  {-"~"-}`sse`{-"~"-}  snd <$> split (filt unrhd =<< (f *** id)) id =<< any {-"~~."-}
\end{spec}
But the form of \eqref{eq:monotonicity} is more readily applicable to programs written in |do|-notation.

When \eqref{eq:monotonicity} holds for |f|, in |foldR f e| we can safely drop the lesser solution |y0|, knowing that for any solution it may generate, |y1| always yields something that is at least as good. In fact, in each step of |foldR| we need to keep only the currently most preferred solutions.
This is formalised by the following Greedy Theorem:
\begin{theorem}[Greedy Theorem]
\label{thm:greedy}
{\rm
Let |unlhd| be a binary relation on |b| that is reflexive and transitive.
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |unrhd| for all |x|, we have
\begin{equation}
|foldR (\x -> max_unlhd . f x) (max_unlhd e) {-"~"-}`sse`{-"~"-} max_unlhd . foldR f e {-"~~."-}|
\label{eq:greedy}
\end{equation}
} %rm
\end{theorem}

The specification on the righthand side can be refined to a |foldR| in which we apply |max| in every step. The algorithm still keeps a set of all maximums. It is in fact sufficient to keep only \emph{one} maximum solution, but the decision of which one to keep can be postponed when we further refine the lefthand side to a function.

\noindent {\bf Remark}: some explanations about our notion of monotonicity. Conventionally,
letting |unrhd| and |succeq| respectively be partial orders on types |A| and |B|,
a function |f :: A -> B| is said to be monotonic with respect to |unrhd| and |succeq| if |x `unrhd` y ==> f x `succeq` f y|.
If we let |succeq := {-"(\unrhd_{H})"-}|, where $(\unrhd_{H})$ is defined by:
\begin{equation*}
  |xs {-"\mathrel{\unrhd_{H}}"-} ys {-"~"-} = {-"~"-} (forall y `elem` ys : (exists x `elem` xs : x `unrhd` y))| \mbox{~~,}
\end{equation*}
we get \eqref{eq:monotonicity-logic}.
The ordering $(\unrhd_{H})$ happens to be the ordering used in \emph{Hoare powerdomain} \citep{Winskel:85:Powerdomains}, hence the name ``Hoare-monotonicity''.
Dually, in \emph{Smyth powerdomain} \citep{Smyth:78:Power} sets are ordered by |xs {-"\mathrel{\unrhd_{S}}"-} ys {-"~"-} = {-"~"-} (forall x `elem` xs : (exists y `elem` ys : x `unrhd` y))|.
We would be using this ordering if we prefer solutions that are smaller under |unlhd|.
{\bf End of Remark}.

\subsection{Proof of the Greedy Theorem}

To most users, what matters is how the Greedy Theorem can be put to use to solve actual problems.
But, having introduced something as awkward as \eqref{eq:monotonicity}, we would like to see how it helps to prove the theorem. It will turn out that \eqref{eq:monotonicity} fits quite well into the proof of Theorem \ref{thm:greedy}.

\begin{proof}
The aim is to prove \eqref{eq:greedy} given that the monotonicity condition holds.
There are various ways one can proceed.
We may apply both sides of \eqref{eq:greedy} to a list, and go with a usual inductive proof.
To go for the most concise proof one may use the |foldR| fusion theorem.
We will go for something in the middle: using the fixed-point property \eqref{eq:foldRPrefixPt}. This way we do not get the shortest proof, but we get to demonstrate more tricks that may be useful in reasoning about monadic programs.

By the fixed-point property \eqref{eq:foldRPrefixPt}, to establish \eqref{eq:greedy} we ought to prove that
\begin{spec}
  max e `sse` max (foldR f e []) &&
  (max . f x) =<< max (foldR f e xs) `sse` max (foldR f e (x : xs)) {-"~~."-}
\end{spec}
The first inclusion is immediate. The second expands to
\begin{spec}
  (max . f x) =<< max (foldR f e xs) `sse` max (f x =<< foldR f e xs) {-"~~."-}
\end{spec}
Abstracting |xs| away, we get
\begin{spec}
 (max . f x) <=< (max . foldR f e) `sse` max . (f x <=< foldR f e)    {-"~~,"-}
\end{spec}
which matches the form of the universal property \eqref{eq:max-univ-monadic} with |h := (max . f x) <=< (max . foldR f e)| and |f := f x <=< foldR f e|.
The first conjunct in the righthand side of \eqref{eq:max-univ-monadic}, that
|(max . f x) <=< (max . foldR f e) `sse` f x <=< foldR f e|
follows from that |max `sse` id|.
For the second conjunct, we need to prove that:
\begin{equation*}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |xs <- any| \\
       & |y1 <- (max . f x) =<< max (foldR f e xs)| \\
       & |y0 <- f x =<< foldR f e xs| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)|
 \end{aligned}\mbox{~~.}
\end{equation*}
It is usually easier to start from the smaller side (the lefthand side) and stepwise relaxing to to a larger monad (the righthand side).
That is, given the lefthand side we wish to show that |filt unrhd (y1, y0)|, or |y1 `unrhd` y0|, holds.
Since |y1| is generated by some |max|, the |max|-cancelation law \eqref{eq:max-cancelation} might help to guarantee that it is a preferred solution. However, we need to split |(max . f x) =<< max (foldR f e xs)| into parts to use the |max|-cancelation law.
Using associative of |(=<<)| and definition of |do|-notation, the lefthand side expands to:
\begin{spec}
do  xs <- any
    b1 <- max (foldR f e xs)
    y1 <- max (f x b1)
    b0 <- foldR f e xs
    y0 <- f x b0
    return (y1, y0) {-"~~."-}
\end{spec}
Now, having both |max (foldR f e xs)| and |foldR f e xs| allows us to use the |max|-cancelation law.
To apply the law, notice that lines generating |xs|, |b1|, and |b0| match that of the lefthand side of \eqref{eq:max-cancelation}, therefore we rewrite them accordingly to the righthand side:
\begin{spec}
       ...
`sse`   {- |max|-cancelation \eqref{eq:max-cancelation} -}
       do  (b1, b0) <- any
           filt unrhd (b1, b0)
           y1 <- max (f x b1)
           y0 <- f x b0
           return (y1, y0) {-"~~."-}
\end{spec}
Seeing |max (f x b1)|, we wish to use |max|-cancelation again,
but the penultimate line is a call to |f x b0| rather than |f x b1|.
The property that relates |f x b0| and |f x b1| is Hoare-monotonicity:
it assures that, instead of applying |f x| to |b0|, we lose nothing by
applying |f x| to the preferred solution |b1|.
To make use of monotonicity, notice that the lines generating |(b1, b0)| and |y0| and the |filt unrhd (b1, b0)| match the lefthand side of \eqref{eq:monotonicity}, therefore we rewrite them to the righthand side of \eqref{eq:monotonicity}:
\begin{spec}
       ...
`sse`   {- monotonicity -}
       do  (b1, y0) <- any
           z1 <- f x b1
           filt unrhd (z1, y0)
           y1 <- max (f x b1)
           return (y1, y0) {-"~~."-}
\end{spec}
Now we can use |max|-cancelation again to cancel |max (f x b1)| and |f x b1|:
\begin{spec}
       ...
`sse`   {- |max|-cancelation \eqref{eq:max-cancelation} -}
       do  (y1, y0, z1) <- any
           filt unrhd (y1, z1)
           filt unrhd (z1, y0)
           return (y1, y0)
`sse`   {- |unrhd| transitive -}
       do  (y1, y0) <- any
           filt unrhd (y1, y0) {-"~~."-}
\end{spec}
The last step uses transitivity of |unrhd|, and then we are done.
%
% \begin{spec}
%        do  xs <- any
%            y1 <- (max . f x) =<< max (foldR f e xs)
%            y0 <- f x =<< foldR f e xs
%            return (y1, y0)
% =        {- monad-laws, |do|-notation -}
%        do  xs <- any
%            b1 <- max (foldR f e xs)
%            y1 <- max (f x b1)
%            b0 <- foldR f e xs
%            y0 <- f x b0
%            return (y1, y0)
% `sse`   {- |max|-cancelation -}
%        do  (b1, b0) <- any
%            filt unrhd (b1, b0)
%            y1 <- max (f x b1)
%            y0 <- f x b0
%            return (y1, y0)
% `sse`   {- monotonicity -}
%        do  (b1, y0) <- any
%            z1 <- f x b1
%            filt unrhd (z1, y0)
%            y1 <- max (f x b1)
%            return (y1, y0)
% `sse`   {- |max|-cancelation -}
%        do  (y1, y0, z1) <- any
%            filt unrhd (y1, z1)
%            filt unrhd (z1, y0)
%            return (y1, y0)
% `sse`   {- |unrhd| transitive -}
%        do  (y1, y0) <- any
%            filt unrhd (y1, y0) {-"~~."-}
% \end{spec}
\end{proof}

What we have seen is a typical proof using the monadic notation.
Notice how it is syntax-driven.
Given is an expression, and we aim to prove that it is included in another.
We massage the expression such that some parts (lines) of it matches the lefthand sides of known laws such as |max|-cancelation \eqref{eq:max-cancelation} or monotonicity \eqref{eq:monotonicity}.
The matched lines are removed, while the righthand sides of the matched laws are added to our current expression.
We then simplify the expression and repeat the procedure again, until we reach the desired expression.
The |do|-notation is essential in that it allows us to implicitly invoke the monad laws and commutative laws behind-the-scene.

We have chosen to use the fixed-point property for the proof, to demonstrate more steps.
We could have also used the fusion-theorem instead.
The fusion condition is:
\begin{spec}
  max_unlhd . (f x =<<) `spse` (max_unlhd . f x) <=< max_unlhd {-"~~."-}
\end{spec}
By the universal property of |max|, we ought to prove:
\begin{equation*}
\setlength{\jot}{-1pt}
\begin{aligned}
|do|~& |ys <- any|\\
     & |z0 <- (max_unlhd . f x) =<< max_unlhd ys|\\
     & |z1 <- f x =<< ys|\\
     & |return (z0, z1)|
\end{aligned}
~|`sse`|~
\begin{aligned}
|do|~& |(z0, z1) <- any|\\
     & |filt rhd (z0, z1)|\mbox{~~.}
\end{aligned}
\end{equation*}
% \begin{spec}
% do  ys <- any
%     b0 <- (min_unlhd . f x) =<< min_unlhd ys
%     b1 <- f x =<< ys
%     return (b0, b1) `sse`
%    do  (b0, b1) <- any
%        filt rhd (b0, b1) {-"~~."-}
% \end{spec}
The first step can be carried out by |max|-cancelation with |f := id|. The rest is the same.

\subsection{Example: Segments Having Maximum Sum}

To see an application of the Greedy Theorem, we consider the classical maximum segment sum again,
but return the list instead of the sum.
The reason for reviewing an old problem is to see whether our usual pattern of problem solving:
factor segment problems into prefix-of-suffix problems, introducing a ``scan'', etc,
adapt smoothly into our new setting.

Let |geqs| be defined by |xs `geqs` ys = sum xs >= sum ys|, therefore
|max_leqs : P (List Int) -> P (List Int)| choose those lists having the largest sum.
The \emph{maximum segment sum} problem can be defined by:
\begin{code}
mss :: List Int -> P (List Int)
mss = max_leqs . (prefix <=< suffix) {-"~~."-}
\end{code}

\paragraph*{The Main Derivation.}~
The main derivation goes:
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
derMSSMain =
\end{code}
%endif
\begin{code}
         max . (prefix <=< suffix)
 ===         {- by \eqref{eq:MaxKComp} -}
         max . ((max . prefix) <=< suffix)
 `spse`      {- Greedy Theorem \eqref{eq:greedy}, letting |maxPre x = max . pre x| -}
         max . (foldR maxPre (return []) <=< suffix)
 ===         {- scan lemma \eqref{eq:ScanLemma} -}
         max . (member <=< scanR maxPre (return []))
 `spse`      {- |maxPre x `spse` return . zplus x|, by \eqref{eq:scanr-scanR} -}
         max . (member <=< (return . scanr zplus []))
 ===         {- monad law -}
         max . member . scanr zplus []
 `spse`      {- \eqref{eq:MaxMaxList} -}
         return . maxlist . scanr zplus [] {-"~~."-}
\end{code}
where |maxPre :: a -> List a -> P (List a)| and
|zplus :: a -> List a -> List a| are given by:
\begin{code}
maxPre x    = max . pre x {-"~~,"-}
zplus x ys  = if x + sum ys <= 0 then [] else (x:ys) {-"~~."-}
\end{code}
The function |maxPre x| is simply the composition of |max| and |pre x|, as demanded by the Greedy Theorem.
While |pre x ys| returns either |[]| or |x : ys|, |maxPre x| returns one among the two that has a larger sum.
The case when there is a tie (that is, when the sum of |x:ys| is |sum [] = 0|) is left for |zplus| to resolve.
Our |zplus| defined above prefers |[]| when there is a tie, but it could have made another choice by substituting |(<)| for |(<=)|.
The result would still meet the specification.

The final one-liner algorithm:
\begin{spec}
  maxlist . scanr zplus [] {-"~~,"-}
\end{spec}
is the famous linear-time algorithm for the maximum segment sum problem ---
if we assume that |sum ys| can be computed in constant time, which could be done by a datatype refinement storing the sum together with the list.

\paragraph*{The Monotonicity Condition.}~
The greedy theorem helped to establish that
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
derMSPRes =
\end{code}
%endif
\begin{code}
  max . prefix {-"~"-}`spse` {-"~"-} foldR maxPre (return []) {-"~~."-}
\end{code}
% Recall the greedy theorem:
% %format y0
% %format y1
% %format b0
% %format b1
% \begin{spec}
% min_R . foldr f e `spse` foldr (\x -> min_R . f x) (min_R e)
%    <==  do  (y0, y1) <- any
%             filt R (y0, y1)
%             b1 <- f x y1
%             return (y0, b1)  {-"~~"-}`sse`
%           do  (b1, y0) <- any
%               b0 <- f x y0
%               filt R (b0, b1)
%               return (y0, b1){-"~~."-}
% \end{spec}
%format ys0
%format ys1
%format zs0
%format zs1
To apply the theorem, one has to establish that |pre| is Hoare-monotonic,
that is, given |ys1 `geqs` ys0|, for any list |zs0| in |pre x ys0|, there
exists some list |zs1| in |pre x ys1| such that |zs1 `geqs` zs0|.

In most literatures on optimisation problems, establishing such monotonicity is usually done informally.
In the case of MSS, the readers would be given a verbal explanation consisting of a case analysis on what |pre x| might return as |zs0|, and for each case the reader is shown how a corresponding |zs1| can be constructed.

Such an informal explanation is often sufficient.
The monadic approach, however, provides a framework in which one can formally prove the monotonicity condition when it is desired. For the MSS problem, the proof goes:
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
proofMonoMSS x =
\end{code}
%endif
\begin{code}
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            zs0 <- pre x ys0
            return (ys1, zs0)
 ===       {- definition of |pre| -}
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            zs0 <- (return [] <|> return (x : ys0))
            return (ys1, zs0)
 ===       {- monad laws -}
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            return (ys1, []) <|> return (ys1, x : ys0)
 ===       {- |(>>=)| distributes into |(<||>)|, since |ys1 `geqs` []| -}
        do  (ys1, ys0) <- any
            (  do { return (ys1, []) } <|>
               do { filt geqs (ys1, ys0); return (ys1, x : ys0) } )
 ===       {- |geqs| monotonic w.r.t |(:)| -}
        do  (ys1, ys0) <- any
            (  do { filt geqs ([], []); return (ys1, []) } <|>
               do { filt geqs (x:ys1, x:ys0); return (ys1, x : ys0) } )
 `sse`  do  (ys1, ys0) <- any
            zs1 <- (return [] <|> return (x:ys1))
            (  do { filt geqs (zs1, []); return (ys1, []) } <|>
               do { filt geqs (zs1, x:ys0); return (ys1, x : ys0) } )
 `sse`  do  (ys1, zs0) <- any
            zs1 <- (return [] <|> return (x:ys1))
            filt geqs (zs1, zs0)
            return (ys1, zs0)  {-"~~."-}
\end{code}
Note that case analysis on |pre| is performed by expanding its definition and using distributivity of |(>>=)|, and that monad laws
\todo{review the proof above and explain a bit.}

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
However, |leqvw| is not connected. For example, neither |[(10,9)] `leqvw` [(9,10)]| nor |[(10,9)] `geqvw` [(9,10)]| holds, and |max_leqvw {[(10,9)], [(9,10)]}| yields the empty set.
Therefore, while one may apply the Greedy Theorem to |max_leqvw . foldR subsw (return [])|, it does not give us a useful algorithm.

Instead, one may use a different strategy: let the |foldR| maintain, in some data structure, a collection of solutions that might be useful, while those that are definitely not going to contribute to the final solution can be disposed of.
For example, if at one point the algorithm computes a collection of solutions
|{[(5,8)],[(4,6)], [(4,8)]}|, the solutions |[(5,8)]| and |[(4,6)]| must be kept because we do not yet know which will contribute to the final solution.
Meanwhile, |[(4,8)]|, which is less valuable than |[(5,8)]| and heavier |[(4,6)]|, need not be kept.
This process of ``keeping useful solutions, while possibly dropping those useless ones'' is called \emph{thinning} in the terminology of \cite{BirddeMoor:97:Algebra}.

Note our wording: |[(4,6)]| need not be kept, but it does not mean that we \emph{have to} drop it.
An algorithm should have the flexibility of deciding how much thinning it needs to do.
Doing a full thinning keeps the set of solutions small, but could be time consuming,
and it may be beneficial to remove some but not all of the useless solutions.
Our specification of a thinning algorithm should allow such flexibility.

\subsection{Overview of Thinning}



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



\section{Conclusions}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
