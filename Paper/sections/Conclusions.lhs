\section{Conclusions}

We presented a pointwise monadic notation for deriving deterministic programs from non-deterministic specifications.
The notation is expressive enough to encode concepts such as maximum, monotonicity, and the Greedy and Thinning Theorems of \citet{BirddeMoor:97:Algebra}.
We showed that this notation is capable of solving classical problems including maximum segment sum and 0-1 knapsack.
The monadic calculus is verified by Agda.

The monadic notation, being pointwise, is not as concise as the point-free calculus.
However, the notation enables one to use familiar proof techniques such as case analysis and structural induction, while still allows point-free techniques such as fold fusion and universal properties.
In fact, it allows us to formally prove properties that were usually dealt with informally.
With a clear distinction between a monad and the value it yields, the monadic notation avoid the ambiguity seen in previous proposed pointwise notations.
It also fits better into a functional programming curriculum.
In a course about reasoning and construction of functional programs, we may want to talk about solving optimisation problems, where it is likely that there are multiple possible solutions for one input.
Introducing relations or multi-functions seems to be an overkill for these ``corner cases''.
Meanwhile, monads are a general way to model effects, including non-determinism, which ought to be taught in any intermediate level functional programming course anyway.
Talking about these problems also demonstrates the importance of monad laws.

\paragraph{Related work.}
\citet{GibbonsHinze:11:Just} is a pioneering work showing that one does not have to give up equational reasoning with the presence of side effects.
On the contrary, monadic programs are very suitable for reasoning using monad laws and properties of effect operators.
Inspired, \citet{Mu:19:Equational} modelled Spark aggregation using non-determinism monad, in order to prove it properties.
\citet{MuChiang:20:Deriving} then explored how to derive programs from monadic specifications.
List sorting was specified using non-determinism monad, from which a pure quicksort on lists was derived.
The article went further to explore mixing of effects --- the quicksort algorithm on mutable arrays, defined using state monad, was also derived.

\citet{MuKoJansson:09:Algebra} encoded the relational instance of the calculus of \citet{BirddeMoor:97:Algebra} in Agda.
The intention was to use the interactive interface of Agda to carry out program derivations while having them formally checked.
As the scenario got more complicated, the details one has to provide in an Agda proof got more massive, thus in this article we no longer promote Agda as an ideal interface to derive program with.
Still, we use Agda to verify the correctness of our theory.
\cite{Affeldt:19:Hierarchy} presented an Coq/Rocq formalisation of monads and effects, the purpose being to formally model effects hierarchy and the properties of each effects.
Having built the formalisation, they verified a number of previous work on reasoning about monads and corrected many bugs.

 \citet{MuOliveira:12:Programming}

\cite{Pinho:22:Greedy}
