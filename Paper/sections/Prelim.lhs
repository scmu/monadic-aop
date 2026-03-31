\section{Preliminaries}
\label{sec:prelim}

%if False
\begin{code}
{-# OPTIONS_GHC -Wno-x-partial #-}
module Prelim where

import Prelude hiding (max, any)
import GHC.Base (Alternative, (<|>))
import Control.Monad

import Common
\end{code}
%endif


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

\paragraph*{Containment.}~
The containment relation of non-determinism monad is defined by:
\begin{spec}
m `sse` n = (m `mplus` n = n) {-"~~."-}
\end{spec}
When |m `sse` n|, we say that |m| refines |n|.
Every value |m| might yield is a value allowed by |n|.
We also lift the relation to functions: |f `sse` g = (forall x : f x `sse` g x)|.

The containment relation is reflexive and transitive.
Monadic bind |(=<<)| (and thus |(<=<)|) is monotonic with respect to containment,
\begin{align*}
  |m `sse` n| &~\Rightarrow~ |f =<< m `sse` f =<< n| \mbox{~~,}\\
  |f `sse` g| &~\Rightarrow~ |f =<< m `sse` g =<< m| \mbox{~~.}
\end{align*}
Meanwhile, function application (and composition) in general is \emph{not} monotonic with respect to containment, that is, having |m `sse` n| certainly does not guarantee that |h m `sse` h n| for arbitrary |h :: M a -> M b|, nor does |f `sse` g| guarantee |h . f `sse` h . g|.
Later in this article we will need monotonicity in more specific cases, where we will discuss conditions for such monotonicity to hold.%
\footnote{That |(.)| being not monotonic may look restrictive, but it is just a common phenomena that was often overlooked due to notational differences.
Consider \citet{BirddeMoor:97:Algebra}, for example, the equivalent of our |h . f| should be written as |h . {-"\Lambda\,"-} f| in their formulation, and the $\Lambda$ operator, which collects the results of a relation in a set, is \emph{not} monotonic.
The |(.)| operator of Bird and de Moor, denoting composition of relations, corresponds to our |(<=<)|, and is indeed monotonic with respect to |(`sse`)|.}

\paragraph*{Sets.}~ A structure that supports all the operations above is the set monad: for all type |a|,
|m :: P a| is a set whose elements are of type |a|,
|mzero| is the empty set, |mplus| is set union for two sets, |join| is union for a set of sets, |(`sse`)| is set inclusion, |return| forms a singleton set, and |m >>= f| is given by |join {f x || x <- m }|.
For the rest of the paper we take |M = P|.

The set |any :: P a| contains all elements having type |a|.
Computationally, it creates an arbitrary element of its type.
The command |filt :: (a -> Bool) -> a -> P a| is defined by
\begin{code}
filt p x  | p x        = return x
          | otherwise  = mzero {-"~~."-}
\end{code}
It returns its input |x| if it satisfies |p|, and fails otherwise.%
\footnote{The function |filt| is called |assert| in the standard Haskell library.
We think the latter name is misleading, and instead use |filt| in this paper.%
 % is a function |guard :: Bool -> M ()| that returns |()| when the input is true and |mzero| otherwise, and |assert p x| is defined by |do { guard (p x); return x }|. In this paper we try to introduce less construct and use only |filt|.
}

\paragraph*{Example: Prefixes and Suffixes.}~
The function |prefix| non-deterministically computes a prefix of the given list:
\begin{code}
prefix :: List a -> P (List a)
prefix []      = return []
prefix (x:xs)  = return [] <|> (x:) <$> prefix xs {-"~~."-}
\end{code}
For example, |prefix [1,2,3]| yields four possibilities: |[]|, |[1]|, |[1,2]|, and |[1,2,3]|.
With idempotency of |mplus|, by a simple case analysis one can show that |return [] <||> prefix xs = prefix xs| for all |xs|.
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
m >>= f   = \y -> Sum{-"\!"-}[x `inn` a] (m x * f x y) {-"~~,"-}
\end{spec}
where |(<=>)| is propositional equality, and |Sum| denotes dependent pair.
That is, |y| is a member of the set |return x| exactly when |x <=> y|,
and |y| is a member of |m >>= f| if there exists a witness |x|, presented in the dependent pair, that is a member of the set |m|, and |y| is a member of the set |f x|.

We would soon get stuck when we try to prove any of its properties.
To prove the right identity law |m >>= return = m|, for example, amounts to proving that
\begin{spec}
  (\y -> Sum{-"\!"-}[x `inn` a] (m x * x <=> y)) {-"~"-}<=>{-"~"-} m {-"~~."-}
\end{spec}
The righthand side |m| is a function which yields, for each member |y|, a proof that |y| is in |m|,
while the lefthand side is a function which produces, for each member |y|, a dependent pair consisting of a value |x : a| , a proof that |x| is in |m|, and a proof that |x <=> y|.
While logically we recognize that they are equivalent, in the type theory of Agda the two sides are different, albeit isomorphic, types.

\todo{Cubical Agda}

\subsection{Monadic Fold}

We define the monadic fold on lists as:
\begin{code}
foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []      = e
foldR f e (x:xs)  = f x =<< foldR f e xs {-"~~."-}
\end{code}
Recall |prefix| defined in Section~\ref{sec:non-det-monad}.
The following function |prefix'|, defined in terms of |foldR|,
also computes an arbitrary prefix of the input list:
\begin{code}
prefix' = foldR pre (return [])
  where pre x ys  = return [] <|> return (x : ys) {-"~~."-}
\end{code}
%if False
\begin{code}
pre x ys = return [] <|> return (x : ys)
\end{code}
%endif
Note that |prefix'| behaves subtly differently from |prefix|, in that the former returns  |[]| more frequently.
For example, while |prefix [1,2]| evaluates to:
\begin{spec}
    prefix [1,2]
 =    {- definition of |prefix| -}
    return [] <|> (1:) <$> (return [] <|> (2:) <$> return [])
 =    {- definition of |(<$>)| -}
    return [] <|> (return . (1:)) =<< (return [] <|> (return . (2:)) =<< return [])
 =    {- |(=<<)| distributes into |mplus| -}
    return [] <|> return [1] <|> return [1,2] {-"~~,"-}
\end{spec}
Evaluating |prefix' [1,2]|, we get:
\begin{spec}
    prefix' [1,2]
 =     {- definition of |prefix'| -}
    pre 1 =<< pre 2 =<< return []
 =     {- definition of |pre 2| -}
    pre 1 =<< (return [] <|> return [2])
 =     {- |(=<<)| distributes into |mplus| -}
    (pre 1 =<< return []) <|> (pre 1 =<< return [2])
 =     {- definition of |pre 1| -}
    return [] <|> return [1] <|> return [] <|> return [1,2] {-"~~,"-}
\end{spec}
The difference is due to that, in the case of |prefix'|, nondeterminism of |pre| happens inside |(=<<)|.
\todo{compare with Oege and Jeremy's early work.}
In the semantics of our set monad, due to commutativity and idempotency of |mplus|, the two results are seen as the same.
From now on we equate |prefix| and |prefix'|.

%format notPrefixP = "\Varid{notPrefix}^{+}"
%format preP = "\Varid{pre}^{+}"
Meanwhile, the following definition does \emph{not} equal |prefixP|:
\begin{code}
notPrefixP    = foldR preP mzero  {-"~~,"-}
  where preP x ys  = return [x] <|> return (x : ys) {-"~~,"-}
\end{code}
because |pre x =<< mzero| immediately reduces to |mzero|.

\paragraph*{Fixed-Point Properties and Fusion Laws.}~
Given |h :: List a -> P b|, the \emph{fixed-point properties}, that is, sufficient conditions for |h| to contain, be contained by, or equal to |foldR f e|, are given by:
\begin{align}
|foldR f e `sse` h| & |{-"~"-}<=={-"~"-} e `sse` h [] {-"\,"-}&&{-"\,"-} f x =<< h xs `sse` h (x:xs)  {-"~~,"-}| \label{eq:foldRPrefixPt} \\
|h `sse` foldR f e| & |{-"~"-}<=={-"~"-} h [] `sse` e {-"\,"-}&&{-"\,"-} h (x:xs) `sse` f x =<< h xs  {-"~~."-}| \label{eq:foldRSuffixPt} \\
|h = foldR f e| & |{-"~"-}<=>{-"~"-} h [] = e {-"\,"-}&&{-"\,"-} h (x:xs) = f x =<< h xs  {-"~~."-}| \label{eq:foldRFixPt}
\end{align}
The properties above can be proved by routine induction on the input list.

For an example we try to show that |prefixP `sse` prefix|.
One may go back to first principles and use an induction on the input list.
Alternatively, one may use property \eqref{eq:foldRSuffixPt}, exploiting the fact that |prefix| is a |foldR|.
It will soon turn out that it is easier to prove instead the following equivalence using \eqref{eq:foldRFixPt}:
\begin{spec}
   return [] <|> prefixP xs = prefix xs {-"~~,"-}
\end{spec}
from which |prefixP `sse` prefix|, that is, |prefixP <||> prefix = prefix|, follows.
This is a case where a stronger variation of a property is easier to prove since it is more informative.
The first antecedent of \eqref{eq:foldRFixPt} is immediate. For the second antecedent, we need to show that
|return [] <||> prefixP (x:xs) = pre x =<< (return [] <||> prefixP xs)|, which is established by utilising monad laws and distributivity:
%if False
\begin{code}
prefixPPrefixInd :: a -> List a -> P (List a)
prefixPPrefixInd x xs =
\end{code}
%endif
\begin{code}
     pre x =<< (return [] <|> prefixP xs)
 ===   {- |(=<<)| distributes into |mplus| -}
     (pre x =<< return []) <|> (pre x =<< prefixP xs)
 ===   {- definition of |pre| -}
     return [] <|> return [x] <|> return [] <|> (x:) <$> prefixP xs
 ===   {- commutativity and idempotency of |mplus| -}
     return [] <|> return [x] <|> (x:) <$> prefixP xs
 ===   {- definition of |prefixP| -}
     return [] <|> prefixP (x:xs) {-"~~."-}
\end{code}


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
%  ===    {- |(=<<)| distributes into |mplus| -}
%       (pre x =<< return []) <|> (pre x =<< prefixP xs)
%  ===    {- definition of |pre|, monad laws -}
%       return [] <|> return [x] <|> (pre x =<< prefixP xs)
%  ===    {- definition of |pre| -}
%       return [] <|> return [x] <|> ((\ ys -> return [] <|> return (x : y)) =<< prefixP xs)
%  ===    {- |(=<<)| distributes into |mplus|, monad laws, definition of |(<$>)| -}
%       return [] <|> return [x] <|> return [] <|> (x:) <$> prefixP xs
%  ===    {- idempotency of |mplus|, definition of |prefixP|  -}
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
%if False
\begin{code}
wrap :: a -> List a
wrap x = [x]
\end{code}
%endif
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
  |return . scanr f e|~&=~ |scanR (\x -> return . f x) (return e)|  \mbox{~~.}
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
 ===    {- |(=<<)| distributes into |mplus| -}
      (foldR f e =<< return (x:xs)) <|> (foldR f e =<< suffix xs)
 ===    {- induction -}
      foldR f e (x : xs) <|> (member =<< scanR f e xs)
 ===    {- definition of |foldR| -}
      (f x =<< foldR f e xs) <|> (member =<< scanR f e xs)
 ===    {- by \eqref{eq:HeadScan}: |head <$> scanR f e xs === foldR f e xs| -}
      (f x =<< (head <$> scanR f e xs)) <|> (member =<< scanR f e xs)
 ===    {- distributivity between |(=<<)| and |mplus|, switching to |do|-notation -}
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
propHeadScanStmt :: (a -> b -> P b) -> P b -> List a -> P b
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
propHeadScanPfInd :: (a -> b -> P b) -> P b -> a -> List a -> P b
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
In this section we explore its definition and properties.

\subsubsection{Universal Property}

In set-theoretical notation, |max_unlhd| can be defined by the following equivalence:
for all |xs| and |ys|,
\begin{equation}
|ys `sse` max_unlhd xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall y `inn` ys : (forall x `inn` xs : y `unrhd` x)) {-"~~."-}|
\label{eq:max-def-set}
\end{equation}
We omit the subscript |unlhd| when it is clear from the context or not relevant.
The |(==>)| direction of \eqref{eq:max-def-set}, letting |ys = max xs|, says that |max xs| is a subset of |xs|, and every member in |max xs| is no lesser than any member in |xs|. The |(<==)| direction of \eqref{eq:max-def-set} says that |max xs| is the largest such set --- any |ys| satisfying the righthand side is a subset of |max xs|.

In calculation, we often want to refine expressions of the form |max . f| where |f| generates a set. Therefore the following \emph{universal property} of |max| is more useful: for all |h| and |f| of type |a -> P b|,
\begin{equation}
|h `sse` max_unlhd . f {-"~"-}<==>{-"~"-} h `sse` f && (forall x : (forall y1 `inn` h x : (forall y0 `inn` f x : y1 `unrhd` y0))) {-"~~."-}|
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
%if False
\begin{code}
maxUnivMonadic ::
  (a -> P b) -> (a -> P b) -> ((b, b) -> Bool) ->
  (a -> P b, (a -> P b, P (b, b)))
maxUnivMonadic h f unrhd = (lhs, rhs)
  where lhs = h `sse` (max_unlhd . f)
        rhs = (conj1, conj2)
        conj1 = h `sse` f
        conj2 = (do x <- any
                    y1 <- h x
                    y0 <- f x
                    return (y1, y0)) `sse`
                 (do (y1, y0) <- any
                     filt unrhd (y1, y0))
\end{code}
%endif
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


\subsubsection{Conditional Monotonicity}
\label{sec:max-monotonic}

The function |max| is not monotonic with respect to |(`sse`)| ---
indeed, |{1,2} `sse` {1,2,3}|, while |max {1,2} = {2} {-"\not\subseteq"-} {3} = max {1,2,3}|.
Consequently, having |f `sse` g| does not give us |max . f `sse` max g|.%
\footnote{Again, the situation is the same in \citet{BirddeMoor:97:Algebra}: even though $\Varid{S} \subseteq \Varid{T}$, we do not have
$\Lambda \Varid{S} \subseteq \Lambda \Varid{T}$, therefore neither do we have $\Varid{max} \circo \Lambda \Varid{S} \subseteq \Varid{max} \circo \Lambda \Varid{T}$.
It has not been a major problem, probably due to that using Greedy Theorem to eliminate the outermost |max| is usually the first refinement step in their treatment of optimisation problems.}

Luckily, we only need monotonicity to hold in more specific cases.
Observing the counter example above, one might conjecture that |max s `sse` max t| if |s `sse` t| and |s| somehow keeps the maximum elements of |t|. Indeed, there are two such laws.
Provided that |unrhd| is transitive, we have:
\begin{spec}
max_unlhd xs `sse` max_unlhd ys  {-"~"-}<=={-"~"-} xs `sse` ys && (forall x `inn` xs, y `inn` ys : x `unrhd` y) {-"~~,"-}
max_unlhd xs `sse` max_unlhd ys  {-"~"-}<=={-"~"-} xs `sse` ys && (forall y `inn` ys : (exists x `inn` xs : x `unrhd` y)) {-"~~."-}
\end{spec}
The first one says that |max xs `sse` max ys| if all elements in |xs| are maximums.
The second laws is a bit relaxed, allowing |xs| to keep some non-maximum element, requiring only that every |y `inn` ys| is dominated by some element in |xs|.
Their function-compositional counterparts are written as:
\begin{spec}
max_unlhd . f `sse` max_unlhd . g  {-"~"-}<=={-"~"-} f `sse` g && (forall z, x `inn` f z, y `inn` g z : x `unrhd` y) {-"~~,"-}
max_unlhd . f `sse` max_unlhd . g  {-"~"-}<=={-"~"-} f `sse` g && (forall z, y `inn` g z : (exists x `inn` g z : x `unrhd` y)) {-"~~."-}
\end{spec}
These two laws cover all the cases in this article where we need |max| to be monotonic.
In particular, the first law automatically is satisfied if |g| has the form |max_unlhd . g'|, that is, |f| is already a refinement of some function that computes maximums.

The two laws translate to the monadic language as:
\begin{equation*}
|max_unlhd . f `sse` max_unlhd . g|\mbox{~~}|<==|\mbox{~~} |f `sse` g &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |z <- any| \\
       & |x <- f z| \\
       & |y <- g z| \\
       & |return (x, y)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(x, y) <- any| \\
       & |filt unrhd (x, y)|\\
 \end{aligned}
 \right)\mbox{~~,}
\end{equation*}
\begin{equation}
|max_unlhd . f `sse` max_unlhd . g|\mbox{~~}|<==|\mbox{~~} |f `sse` g &&|~
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
       & |filt unrhd (x, y)|\\
       & |return (y,z)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:max-monotonic-monadic}
\end{equation}
It might be instructive observing how the two laws are translated: universally quantified variables are introduced on the LHS of |(`sse`)|; existential quantification of |x| is represented by introducing it on the RHS of |(`sse`)|;
in \eqref{eq:max-monotonic-monadic} both sides return |(y,z)| to ensure that they are the same.

We present a proof of \eqref{eq:max-monotonic-monadic}, as our first example of proving properties about maximum in the monadic notation.
\begin{proof}
By the universal property \eqref{eq:max-univ-monadic}, to have |max . f `sse` max . g| we need
|max . f `sse` g| and
\begin{equation*}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |z <- any| \\
       & |x <- max (f x)| \\
       & |y <- g x| \\
       & |return (x, y)|
 \end{aligned}
 ~~|`sse`|~~
 \begin{aligned}
 |do|~ & |(x, y) <- any| \\
       & |filt unrhd (x, y)|\mbox{~~.}
 \end{aligned}
\end{equation*}
The first conjunct is immediate:
|max . f `sse` f `sse` g|.
For the second conjunct, we assume the righthand side of \eqref{eq:max-monotonic-monadic} and reason:
%if False
\begin{code}
minMonoPf :: Ord b => (a -> P b) -> (a -> P b) -> ((b,b) -> Bool) -> P (b, b)
minMonoPf f g unrhd =
\end{code}
%endif
\begin{code}
        do  z <- any
            x <- max (f z)
            y <- g z
            return (x, y)
 `sse`   {- matching |z <- any| and |y <- g z| in \eqref{eq:max-monotonic-monadic} and rewrite -}
        do  (y,z) <- any
            w <- f z
            filt unrhd (w,y)
            x <- max (f z)
            return (x,y)
 `sse`   {- |max|-cancelation -}
        do  (x,y,w) <- any
            filt unrhd (w, y)
            filt unrhd (x, w)
            return (x,y)
 `sse`   {- |unrhd| transitive -}
        do  (x,y) <- any
            return (x,y) {-"~~."-}
\end{code}
\end{proof}
Notice the first step of the calculation: |z <- any| and |y <- g z| match the LHS of |(`sse`)| in the big parentheses in \eqref{eq:max-monotonic-monadic}, allowing us to rewrite them to the RHS of |(`sse`)|.
It will be a technique we use a lot in such proofs: identifying the lines that matches the LHS of some |(`sse`)|, and rewrite them to the RHS.

\subsubsection{Promotion into Kliseli Composition}

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

\subsubsection{Conversion from Lists}

In the last few steps of a program calculation we usually want to refine a monadic |max| to a function on lists.
If |unlhd| is total (that is, for all |x| and |y| of the right type, at least one of |x `unrhd` y| or |y `unrhd` x| holds), and if |xs| is non-empty, we have
\begin{equation}
 |return (maxlist xs) `sse` max_unlhd (member xs) | \label{eq:MaxMaxList}
\end{equation}
where |maxlist| is some implementation of maximum on non-empty lists, e.g.
\begin{spec}
maxlist :: List a -> a
maxlist [x] = x
maxlist (x : y : xs) = x `bmax` maxlist (y : xs) {-"~~,"-}
   where x `bmax` y  =if x `unrhd` y then x else y {-"~~."-}
\end{spec}
%if False
\begin{code}
maxlist :: List a -> a
maxlist = undefined
\end{code}
%endif
That |unlhd| being total guarantees that maximum exists for non-empty |xs|.
The function |maxlist| may decide how to resolve a tie --- in the implementation above, for example, |maxlist| prefers elements that appears earlier in the list.

\subsubsection{In the Agda Model}

we implement |min| by:

\todo{more here.}

It is then proved in Agda that the above implementation satisfies \eqref{eq:max-univ-monadic}.
