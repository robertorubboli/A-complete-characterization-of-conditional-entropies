% Appendix fragment included from either tested entry point in this bundle.
% The main file already loads tikz, graphicx, booktabs, longtable, and array.

\section{Lean formalization and verification architecture}
\label{app:lean-formalization}

\subsection{Scope of the formalization}
\label{app:lean-scope}

The final Lean architecture covers the parameter classification and the
conditional-entropy law package used in Sections~4 and~5.  The parameter space
\texttt{Param} is endpoint-aware: it contains the orders \(0\) and \(1\), all
finite positive R\'enyi orders, and the top endpoint.  The development includes
the finite and endpoint R\'enyi formulas, differentiation of positive
real-power lines, signed-measure differentiation under the integral,
finite-support approximation and discretization, two-block and three-block
localization, the dedicated Shannon localization, all five necessity branches,
all four sufficiency branches, and the original semiring/channel lift.

At the source revision described by this appendix, all paper-facing terminal
declarations are present and the complete integrated release audit passes.  The
strict root build covers the complete declaration-bearing release dependency
tree, including the Shannon-to-classification chain and the original
semiring/channel branch.

The architecture is organized around two terminal declarations.  The classification
terminal \path{mainClassification} states necessary and sufficient parameter
conditions.  The law-package terminal
\path{allConditionalEntropyAxioms} assembles nonnegativity, embedding
invariance, tensor additivity, natural-log fair-bit normalization, and
monotonicity under the embedded conditional-majorization relation.  These are
separate conclusions: neither is used as an unproved premise of the other.

The singular moment at the Shannon order is represented by one-sided
extended-real moments together with a finiteness guard.  This avoids assigning
an ordinary signed integral where the positive and negative parts may both be
infinite.  The Lean development uses natural logarithms, so the independent
fair-bit normalization is \(\log 2\); normalization to one follows by positive
rescaling.

\subsection{Condensed two-branch architecture overview}
\label{app:lean-dependency-graph}

The repository provides three complementary diagrams rather than three
renderings of one graph. Figure~\ref{fig:lean-dependency-graph} is the
\emph{condensed two-branch architecture overview}. It summarizes the source
architecture more coarsely than the detailed module-group graph: individual
module names and manuscript statement numbers are intentionally suppressed.
An arrow \(A\to B\) uses the standard source-dependency direction and means
that declarations in \(B\) use declarations from \(A\).

The editable \emph{Lean implementation dependency graph}, including module
names inside every group, is \texttt{paper/dependency-graph.dot}; its SVG and
PNG files are renderings of that one DOT source. The Lean formalization supplement
contains the third view, a \emph{theorem-facing proof map} whose arrows instead
run from a conclusion to its proof ingredients. The declaration-level index is
\texttt{paper/DECLARATION\_INDEX.md}.

\begin{figure}[htbp]
  \centering
  \begin{tikzpicture}[
      x=1cm,y=1cm,
      dep/.style={-{Stealth[length=1.7mm]},draw=black!55,line width=.48pt},
      major/.style={draw=blue!65!black,fill=blue!7,rounded corners=2pt,
        align=center,font=\scriptsize,minimum height=8mm,text width=45mm},
      analytic/.style={draw=teal!70!black,fill=teal!7,rounded corners=2pt,
        align=center,font=\scriptsize,minimum height=8mm,text width=45mm},
      local/.style={draw=purple!75!black,fill=purple!7,rounded corners=2pt,
        align=center,font=\scriptsize,minimum height=8mm,text width=45mm},
      final/.style={draw=red!70!black,fill=red!6,rounded corners=2pt,
        align=center,font=\scriptsize,minimum height=8mm,text width=45mm}]

    \node[major] (foundation) at (-3.25,0)
      {Finite data, \texttt{Param}, measures, moments};
    \node[major] (semiring) at (3.25,0)
      {Finite semiring and quotient semiring};

    \node[analytic] (endpoint) at (-3.25,-1.35)
      {Endpoint R\'enyi calculus, signed integration, shape reduction};
    \node[major] (channels) at (3.25,-1.35)
      {Finite channels, channel algebra, semiring order};

    \node[local] (block) at (-3.25,-2.70)
      {Two-block and three-block localization};
    \node[major] (candidate) at (3.25,-2.70)
      {Normalization, tensor, and embedding packages};

    \node[local] (shannon) at (-3.25,-4.05)
      {Shannon escort, log-mass, expansion, and
       \texttt{shannonLocalization}};
    \node[analytic] (suff) at (3.25,-4.05)
      {Finite-support, general, tropical, and derivation sufficiency};

    \node[final] (necessity) at (-3.25,-5.40)
      {Temperate, tropical, and derivation necessity};
    \node[final] (allaxioms) at (3.25,-6.75)
      {\texttt{allConditionalEntropyAxioms}};

    \node[final] (bundle) at (-3.25,-6.75)
      {\texttt{necessityBundle}};
    \node[final] (classification) at (-3.25,-8.10)
      {\texttt{mainClassification}};

    \draw[dep] (foundation) -- (endpoint);
    \draw[dep] (foundation) -- (semiring);
    \draw[dep] (semiring) -- (channels);
    \draw[dep] (channels) -- (endpoint);
    \draw[dep] (endpoint) -- (block);
    \draw[dep] (block) -- (shannon);
    \draw[dep] (endpoint) to[bend right=10] (shannon);
    \draw[dep] (endpoint) -- (suff);
    \draw[dep] (channels) -- (candidate);
    \draw[dep] (endpoint) -- (candidate);
    \draw[dep] (block) -- (necessity);
    \draw[dep] (shannon) -- (necessity);
    \draw[dep] (endpoint.west) to[bend right=18] (necessity.west);
    \draw[dep] (necessity) -- (bundle);
    \draw[dep] (bundle) -- (classification);
    \draw[dep] (suff) -- (classification);
    \draw[dep] (candidate) -- (allaxioms);
    \draw[dep] (suff) -- (allaxioms);
    \draw[dep] (channels.east) to[out=0,in=0,looseness=1.35]
      node[right,font=\tiny,pos=.58]{\texttt{embeddingLift}}
      (allaxioms.east);
  \end{tikzpicture}
  \caption{Condensed two-branch architecture overview (appendix view).
  The left branch culminates in the necessary-and-sufficient parameter
  classification.  The right branch culminates in the five-part
  conditional-entropy law package and retains the original channel lift. An
  arrow points from prerequisite to dependent. Blue boxes group foundational
  and algebraic/channel components, teal boxes group analytic calculus and
  sufficiency, purple boxes group localization, and red boxes group necessity
  and terminal assemblies. Colors identify architectural roles, not
  verification status. For exact modules use the implementation graph; for
  numbered manuscript correspondence use the theorem-facing proof map.}
  \label{fig:lean-dependency-graph}
\end{figure}

The analytical branch passes through
\path{EndpointLineCalculus}, \path{EndpointParameterContinuity},
\path{SignedLineCalculus}, \path{UniformSignedDCT},
\path{BlockLocalizationInterfaces}, and
\path{ShannonLogMass}, \path{ShannonExpansion}, and
\path{ShannonLocalization}.  Its necessity leaves are
\path{PositiveNecessity}, \path{NegativeNecessity},
\path{PositiveTropicalNecessity},
\path{NegativeTropicalNecessity}, and
\path{DerivationNecessity}.  The algebraic branch passes through
\path{FiniteSemiringQuotient}, \path{FiniteChannelAlgebra},
\path{ConditionalSemiringOrder}, and the candidate law packages.

\subsection{Final declaration signatures}
\label{app:lean-final-signatures}

The necessity assembly has the following exact four-part conclusion.  Here
\texttt{DBulk}, \texttt{DMinus}, and the support condition are the
paper's parameter predicates, not additional proof assumptions.
{\small
\[
\begin{aligned}
&\texttt{necessityBundle (tau : ProbabilityMeasure Param) :}\\
&\quad
 \bigl(\forall t:\mathbb R,\ \forall\,\texttt{ht}:t\ne0,\\
&\qquad \texttt{CMMonotone}\\
&\qquad\quad \texttt{(HTemp t ht tau : PolyJointFunctional.\{u\})}\\
&\qquad \Longrightarrow \texttt{DBulk t tau}\bigr)\\
&\quad\land
 \bigl(\texttt{CMMonotone}\\
&\qquad\quad \texttt{(HMinus tau : PolyJointFunctional.\{u\})}\\
&\qquad \Longrightarrow \texttt{DMinus tau}\bigr)\\
&\quad\land
 \bigl(\texttt{CMMonotone}\\
&\qquad\quad \texttt{(HPlus tau : PolyJointFunctional.\{u\})}\\
&\qquad \Longrightarrow \texttt{tau = diracProb 0}\bigr)\\
&\quad\land
 \bigl(\texttt{CMMonotone}\\
&\qquad\quad \texttt{(HZero tau.toFiniteMeasure : PolyJointFunctional.\{u\})}\\
&\qquad \Longrightarrow \texttt{suppMeasure (probMeasure tau)}\\
&\qquad\quad \subseteq \texttt{Icc (0 : Param) 1}\bigr).
\end{aligned}
\]
}

The closed classification theorem is assumption-free apart from its displayed
data argument:
\[
  \texttt{mainClassification (tau : ProbabilityMeasure Param) : }
  \texttt{Classifies.\{u\} tau}.
\]
Unfolding \texttt{Classifies}, this is the conjunction of four equivalences:
finite nonzero temperature is equivalent to \texttt{DBulk}; the negative
tropical candidate is monotone exactly under \texttt{DMinus}; the positive
tropical candidate is monotone exactly for \texttt{diracProb 0}; and the
derivation candidate is monotone exactly when the parameter support is
contained in \([0,1]\).

The candidate-law terminal has the following exact four-family conclusion:
{\small
\[
\begin{aligned}
&\texttt{allConditionalEntropyAxioms :}\\
&\quad
 \bigl(\forall t:\mathbb R,\ \forall\tau:\texttt{ProbabilityMeasure Param},\\
&\qquad \forall\texttt{ h : DBulk t tau},\\
&\qquad \texttt{ConditionalEntropyAxioms}\\
&\qquad\quad \texttt{(HTemp t (DBulk.ne h) tau : PolyJointFunctional.\{u\})}\bigr)\\
&\quad\land
 \bigl(\forall\tau:\texttt{ProbabilityMeasure Param},\\
&\qquad \texttt{DMinus tau} \Longrightarrow \texttt{ConditionalEntropyAxioms}\\
&\qquad\quad \texttt{(HMinus tau : PolyJointFunctional.\{u\})}\bigr)\\
&\quad\land
 \texttt{ConditionalEntropyAxioms}\\
&\qquad \texttt{(HPlus (diracProb 0) : PolyJointFunctional.\{u\})}\\
&\quad\land
 \bigl(\forall\tau:\texttt{ProbabilityMeasure Param},\\
&\qquad \texttt{suppMeasure (probMeasure tau)}
      \subseteq\texttt{Icc (0 : Param) 1}\\
&\qquad \Longrightarrow \texttt{ConditionalEntropyAxioms}\\
&\qquad\quad \texttt{(HZero tau.toFiniteMeasure : PolyJointFunctional.\{u\})}\bigr).
\end{aligned}
\]
}
The proof of its monotonicity field calls \texttt{embeddingLift}; hence the
law-package theorem records the original semiring/channel construction rather
than replacing it with a project-specific assumption.

\subsection{Trust boundary and audit protocol}
\label{app:lean-audit}

The repository pins Lean~4.32.2 and mathlib~4.32.2.  Project source contains
no \texttt{sorry}, \texttt{admit}, project-defined
\texttt{axiom}, or project-defined \texttt{opaque} declaration.  The final
public declarations introduce no auxiliary project assumption: their premises
are precisely the mathematical admissibility or monotonicity conditions shown
in their signatures.

The verification script \texttt{scripts/check.ps1} performs four separate
checks:
\begin{enumerate}
  \item a source scan for forbidden proof placeholders and project
        declarations that bypass the kernel;
  \item a warning-as-error build of the
        \texttt{CompleteCharacterization} target;
  \item \texttt{\#print axioms} checks, via
        \texttt{scripts/AxiomAudit.lean}, for the endpoint, localization,
        necessity, sufficiency, channel-lift, and final declarations; and
  \item a correspondence audit requiring 152 source-ordered rows and exactly
        three columns.
\end{enumerate}
Mathlib's standard logical foundations may appear in
\texttt{\#print axioms}; the prohibition is on new project-specific
assumptions and unfinished proof terms.

\begin{center}
\fbox{\begin{minipage}{0.91\textwidth}
\textbf{Final verification status: passed.}
On 24 August 2026, the Lean source at commit
\texttt{8f3ee234cc528c5ff6d716e2fb0520aa97cdf6f4} passed the complete release audit with
Lean~4.32.2 and mathlib~4.32.2.  The warning-as-error root build checked 2,864
jobs; the forbidden-token scan passed; all 21 audited declarations depended
exactly on \texttt{propext}, \texttt{Classical.choice}, and
\texttt{Quot.sound}; and the correspondence checker confirmed 152
source-ordered rows with exactly three columns.  No project-defined axiom was
reported.
\end{minipage}}
\end{center}

\subsection{Statement-by-statement correspondence}
\label{app:lean-correspondence}

The following longtable gives the exact statement-by-statement ledger in
manuscript order.  Its columns are
\emph{Manuscript statement}, \emph{Lean declaration}, and \emph{Status}.
A split API is listed when one manuscript package is intentionally represented
by several smaller Lean declarations.  Every row is marked ``Formalized'' or
``Formalized (split API)'' and is covered by the strict root build.  The audit
box above records the release-wide verification result.

\input{paper/blueprint-statement-correspondence.inc}
