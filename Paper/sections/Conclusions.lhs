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
