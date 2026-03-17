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

\end{abstract}

\maketitle

%include sections/Intro.lhs
%include sections/Prelim.lhs
%include sections/Greedy.lhs
%include sections/Thinning.lhs


\section{Conclusions}

\bibliographystyle{ACM-Reference-Format}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
