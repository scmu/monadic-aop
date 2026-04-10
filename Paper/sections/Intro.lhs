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
However, within several lines of reasoning, one may transform it to a program consisting of a |foldr| before a |maximum|, both run in time linear with respect to the length of the input:
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

Pedagogical examples of program calculation for optimisation problems tend to return the optimal value (in this case, the sum), rather than the solution that yields the optimal value (the list),
because this approach would not be feasible otherwise.
When there are multiple solutions that yield the optimal value,
the specification, being a function, has to pick a particular one, which the implementation has to return.
In the construction of a sorting algorithm, for example,
having to decide, in the specification phase, what list to return when there are items having the same key would severely limit the algorithm one can derive (e.g., limiting one to construct stable sorting),
if not making the specification impossible at all (it is hard to predict how, say, quicksort arranges items having the same key).
One therefore needs a different framework, where a specification describes a collection of solution that is allowed by the final program, which no longer equals, but is instead contained by the specification.

One of the possibilities is to use relations as specifications.
Foundations of this approach were laid by works including \citet{BackhousedeBruin:91:Relational}, \citet{Aarts:92:Relational}, \citet{BackhouseHoogendijk:92:Elements}, etc,
before \citet{BirddeMoor:97:Algebra}, taking a more abstract, categorical approach,
presented general theories for constructing various forms of greedy, thinning, and dynamic programming algorithms.
\citet{BirddeMoor:97:Algebra} presented a point-free calculus that is concise, elegant, and surprisingly expressive.%
\footnote{Being ``point-free'' refers to a style where one tends not to mention arguments to a function/relation, but thinks in a higher level and construct programs by functional/relational composition, union, intersection, converses, etc. The opposite style where functions are often applied to named arguments is called ``pointwise''.}
Concepts such as monotonicity and maximum/minimum are concisely expressed in short expressions, consisting of  composition, union, intersection, and factor (a concept resembling division) of relations.
A short expression may encode rich interpretations, and algebraic properties of these operators are applied to prove properties of expressions.
Such conciseness and expressiveness also turned out to be a curse, however.
For those who not sharing the background, the calculus has a sharp learning curve, which limited its popularity to a small circle of enthusiasts.
Thinking point-free might be too abstract for some people;
as one might remember from high school algebra, reasoning about inequality (in this case, relational inclusion) is harder than reasoning about equality; and with the rich selection of relational operators, the number of properties one has to remember multiplies.

Efforts has been made to re-introduce variables back to the relational calculus, for example, \citet{deMoorGibbons:00:Pointwise}.
One cannot help feeling unease with some of its peculiarities.
For example, let |0{-"\!"-} `mplus`{-"\!"-} 1| denote a value that is non-deterministically |0| or |1|.
Non-determinism is resolved before functional application,
therefore |(\x -> x - x) (0 `mplus` 1)| is always |0|,
while |(0 `mplus` 1) - (0 `mplus` 1)| could be |-1|, |0|, and |1| ---
$\beta$-reduction does not hold!
In fact, $\beta$-reduction is applicable only to pure values.
Similarly, $\eta$-expansion also changes the non-deterministic behaviour of an expression.
Around two decades later, \citet{BirdRabe:19:How} presented a theoretical background of pointwise ``multifunctions'', which is subsequently used in \citet{BirdGibbons:20:Algorithm}.
While \citet{deMoorGibbons:00:Pointwise} interpreted their pointwise calculus by translating expressions to relations, \citet{BirdRabe:19:How} presented a set-theoretic semantics.
To the users, the two calculus are rather similar. While their foundations are solid, the aforementioned peculiarities makes it harder to reason about programs without making mistakes.

\paragraph*{This article} We propose a monadic notation for specifying optimisation problems and derive from them algorithms. We consider problems having the form:
\begin{spec}
  max . (filt p <=< foldR f e) {-"~~,"-}
\end{spec}
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kliseli composition and |(.)| is ordinary function composition.
Given an input of type |List A|, the collection of all solution candidates is generated by |foldR f e :: List A -> M B|, a monadic variation of fold on lists.
The function |filt :: (b -> Bool) -> b -> M b| keeps those solutions that satisfy predicate |p|, and |max :: M b -> M b| keeps only those having maximum value under some chosen ordering.
In all cases we consider, the filtering phase can be fused into |foldR|, therefore the actual form of the problem is |max . foldR f' e'|.
We then discuss conditions under which the specification can be refined to a fold-based greedy algorithm --- one where we greedily keep only the locally best solution in each step of the fold,
or a \emph{thinning} algorithm, where in each step of the fold we keep a set of solution candidates that still might be useful.

All these were covered in \citet{BirddeMoor:97:Algebra}.
Rather than solving new problems or discovering new algorithms, the purpose of this article is to propose new notations that make previous derivations more accessible, while still being accurate without being too cumbersome.
In traditional functional programming, one may reason about a functional program by induction on the input.
This article aims to show that reasoning about monadic programs is just like that: one only need to make use of monad laws and properties of effect operators.
\todo{Say more, and polish.}
