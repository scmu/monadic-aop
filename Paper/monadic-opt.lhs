%% lhs2TeX monadic-opt.lhs | pdflatex --jobname=monadic-opt

%let anonymous = False
%let draft = False

\documentclass[acmsmall,fleqn,screen,nonacm]{acmart}

%include preamble.tex

\begin{document}

\author{Shin-Cheng Mu}
\affiliation{
\institution{Institute of Information Science, Academia Sinica, Taipei, Taiwan}}
\author{You-Zheng Yu}
\affiliation{
\institution{National Taiwan University, Taipei, Taiwan}}

\title{A Monadic Notation for Calculating Optimisation Algorithms}

\begin{abstract}

\end{abstract}

\maketitle

\section{} % why doesn't this show up?

%include sections/Intro.lhs
%include sections/Prelim.lhs
%include sections/Greedy.lhs
%include sections/Thinning.lhs


\section{Conclusions}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
