%% lhs2TeX monadic-opt.lhs | pdflatex --jobname=monadic-opt

%let anonymous = False
%let draft = False

\documentclass[pearl,fleqn,review]{jfp-epi}

%include preamble.tex

\begin{document}

\author{Shin-Cheng Mu}
\orcid{0000-0002-4755-601X}
\affiliation{
\institution{Institute of Information Science, Academia Sinica}
\city{Taipei}
\country{Taiwan}
}
\author{You-Zheng Yu}
\affiliation{
\institution{National Taiwan University}
\city{Taipei}
\country{Taiwan}}

\title{A Monadic Notation for Calculating Optimisation Algorithms}

\begin{abstract}
In deriving algorithms for optimisation problems where optimal solutions are not unique, it is preferable to let the specification be non-deterministic and leave it to the derived algorithm to decide which one to return.
To formally talk about non-determinism, a point-free calculus based on relations was developed in the 90's,
which has been difficult to promote due to its complexity,
while subsequent pointwise approaches tend to be ad-hoc and imprecise.
We propose a notation for non-deterministic program derivation based on non-determinism monad,
show that it is expressive enough to model concepts including maximum, monotonicity, Greedy/Thinning Theorems,
and demonstrate how to carry out derivation in this notation.
One is allowed to use familiar proof techniques such as case analysis and structural induction, as well as fold fusion and universal properties.
Key properties of our calculus are verified in Agda.
\end{abstract}

\maketitle

%include sections/Intro.lhs
%include sections/Prelim.lhs
%include sections/Greedy.lhs
%include sections/Thinning.lhs
%include sections/Conclusions.lhs

\bibliographystyle{ACM-Reference-Format}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}

\appendix

%include sections/ThinningProof.lhs

\end{document}
