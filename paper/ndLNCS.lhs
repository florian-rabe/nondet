\documentclass{llncs}
\usepackage{amssymb}
\usepackage{stmaryrd}
%%\usepackage{ndetextras}
%%\usepackage{fleqnbird}


%include lhs2TeX.fmt
%include polycode.fmt
%include definitions.fmt

\def\commentbegin{\quad$\{$~}
\def\commentend{$\}$}

\pagestyle{plain} % remove for final version

\setcounter{tocdepth}{2} % for pdf bookmarks
\usepackage[bookmarks,bookmarksnumbered,bookmarksopen,colorlinks,citecolor=red]{hyperref}

\begin{document}
\bibliographystyle{plain}

\title{How to calculate with nondeterministic functions}
\titlerunning{How to calculate with nondeterministic functions}
\author{Richard Bird\inst{1} \and Florian Rabe\inst{2}}
\institute{Department of Computer Science, Oxford University\\
Wolfson Building, Parks Road, Oxford, OX1 3QD, UK
\and Laboratoire de Recherche en Informatique, University Paris Sud\\
Rue Noetzlin 91405 Orsay Cedex, France}

\date{}
\maketitle

\begin{abstract}
While simple equational reasoning is adequate for the calculation of many algorithms from 
their functional specifications, it is not up to the task of dealing with others,
particularly those specified as optimisation problems. One approach is to replace functions by 
relations, and equational reasoning by reasoning about relational inclusion. But such a wholesale 
approach means one has to adopt a new and sometimes subtle language to argue about the properties 
of relational expressions. A more modest proposal is to generalise our powers of specification by 
allowing certain nondeterministic, or multi-valued functions, and to reason about refinement instead. 
Such functions will not appear in any final code. Refinement calculi have been studied extensively 
over the years and our aim in this article is just to explore the issues in a simple setting and to 
justify the axioms of refinement using the semantics suggested by Morris and Bunkenburg.
\end{abstract}

\section{Introduction}

We set the scene by considering the following Haskell definition for an archetypal 
optimisation problem:
\begin{spec}
    mcc :: [Item] -> Candidate
    mcc = minWith cost . candidates
\end{spec}
The function |mcc| computes a candidate with minimum cost. The function |minWith| can be
defined by
\begin{spec}
    minWith :: Ord b => (a -> b) -> [a] -> a
    minWith f       =  foldr1 smaller
                       where smaller x y = if f x <= f y then x else y
\end{spec}
Applied to a finite, nonempty list of candidates, |minWith cost| returns the first candidate 
with minimum cost. The function |candidates| takes a finite list of items and returns a finite,
nonempty list of candidates. We will suppose that the construction uses |foldr|:    
\begin{spec}
    candidates :: [Item] -> [Candidate]
    candidates xs  =  foldr step [c0] xs
                      where step x cs  =  concatMap (additions x) cs
\end{spec}
The useful function |concatMap| is defined by |concatMap f = concat . map f|.
The value |c0| is some initial candidate and |additions x c| is a finite, nonempty list 
of extended candidates constructed from a new item |x| and an existing candidate |c|.
Think of the computation as a finite tree with |c0| as root and |additions x c|
as the children of the tree with label |c|. The list of final candidates
appears as the fringe of the tree.

A greedy algorithm for |mcc| arises as the result of successfully fusing the function
|minWith cost| with |candidates|. Operationally speaking, instead of 
building the complete list of candidates and then selecting a best one, we 
construct a single best candidate at each step. The usual formulation of the 
fusion rule for |foldr| states that
\begin{spec}
    f (foldr g e xs) = foldr h (f e) xs
\end{spec}
for all finite lists |xs| provided the fusion condition 
\begin{spec}
    f (g x y) = h x (f y)
\end{spec}
holds for all |x| and |y|. In fact the fusion condition is required to hold only for
all |y| of the form |y = foldr g e xs|; this version is called \emph{context-sensitive}
fusion.

The context-sensitive fusion condition for our problem reads:
\begin{spec}
    minWith cost . step x . candidates = add x . minWith cost . candidates
\end{spec}
for some function |add| and all finite lists. To see if it holds we can reason:
\begin{spec}
   ^^  minWith cost . step x . candidates
=        {- definition of |step| -}
       minWith cost . concatMap (additions x) . candidates
=        {- distributive law (see below) -}
       minWith cost . map (minWith cost . additions x) . candidates
=        {- define |add x = minWith cost . additions x| -}
       minWith cost . map (add x) . candidates
=        {- greedy condition (see below) -}
       add x . minWith cost . candidates
\end{spec}
The distributive law used in the second step is the fact that
\begin{spec}
    minWith f (concat xss) = minWith f (map (minWith f) xss)
\end{spec}
provided |xss| is a finite list of finite, nonempty lists. Equivalently,
\begin{spec}
    minWith f (concatMap g xs) = minWith f (map (minWith f . g) xs)
\end{spec}
provided |xs| is a finite list and |g| returns finite, nonempty lists. The proof 
of the distributivity law is straightforward using the given definition of |minWith|. 
Summarising this short calculation, we have shown that
\begin{spec}
    mcc    =  foldr add c0
              where  add x  =  minWith cost . additions x
\end{spec}
provided the following \emph{greedy condition} holds:
\begin{spec}
    minWith cost . map (add x) . candidates = add x . minWith cost . candidates
\end{spec}
That all seems simple enough. However, the fly in the ointment is that, in order to 
establish the greedy condition, we need to prove the very strong fact that
\begin{equation}
\label{strong}
|cost c1 <= cost c2  ^  <==>  ^  cost (add x c1) <= cost (add x c2)|
\end{equation}
for all candidates |c1| and |c2|. To see why, observe that if |c1| is the 
first candidate with minimum cost in a list of candidates, then |add x c1| has to be the first 
candidate with minimum cost in the list of extended candidates. This follows from our definition 
of |minWith| which selects the first element with minimum cost in a list of candidates. To ensure 
that the extension of a candidate |c2| earlier in the list has a larger cost we have to show that
\begin{equation}
\label{mono1}
|cost c2 > cost c1  ^  ==>  ^  cost (add x c2) > cost (add x c1)|
\end{equation}
for all |c1| and |c2|. To ensure that the extension of a candidate |c2| later in the list does
not have a smaller cost we have to show that 
\begin{equation}
\label{mono2}
|cost c1 <= cost c2  ^  ==>  ^  cost (add x c1) <= cost (add x c2)|
\end{equation}
for all |c1| and |c2|. The conjunction of (\ref{mono1}) and (\ref{mono2}) is (\ref{strong}).
The problem is that (\ref{strong}) is so strong that it rarely holds in practice. A similar 
condition is needed if, say, |minWith| returned the last element in a list with minimum cost, 
so the problem is not to do with the specific definition of |minWith|. What we really need 
is a form of reasoning that allows us to establish the necessary fusion condition from the 
simple monotonicity condition (\ref{mono2}) alone, and the plain fact of the matter is that 
equational reasoning with any definition of |minWith| is simply not adequate to provide it.

It follows that we have to abandon equational reasoning.  One approach is to replace our 
functional framework with a relational one, and to reason instead about the inclusion of one 
relation in another. Such an approach has been suggested in a number of places, including our 
own \cite{bird&demoor}. But, for the purposes of presenting a simple introduction to the 
subject of greedy algorithms in Haskell, this solution is way too drastic, more akin to 
a heart transplant than a tube of solvent for occasional use. The alternative, if it can be 
made to work smoothly, is to introduce nondeterministic functions, also called 
\emph{multi-valued} functions in mathematics, and to reason about refinement. 

The necessary
intuitions and syntax are introduced in Section~\ref{sec:syn}. Section~\ref{sec:calc} gives 
a formal calculus and Section~\ref{sec:sem} a denotational semantics for our language.
The soundness of the semantics establishes the consistency of the calculus.
We have formalised syntax, calculus, and semantics in the logical framework LF \cite{lf}; the formalisation is not given in this paper but is available online\footnote{\url{https://github.com/florian-rabe/nondet}}.

\section{Nondeterminism and refinement}\label{sec:syn}

Suppose we introduce |MinWith| as a nondeterministic function, specified only 
by the condition that if |x| is a possible value of |MinWith f xs|,
where |xs| is a finite nonempty list, then |x| is an element of |xs| and for all
elements |y| of |xs| we have |f x <= f y|.
Note the initial capital letter: |MinWith| is not part of Haskell. It is
not our intention to extend Haskell with nondeterministic functions; instead
nondeterminism is simply there to extend our powers of specification and cannot
appear in any final algorithm. 

%format E1
%format E2

Suppose we define |y <~ F x| to mean that |y| is one possible 
output of the nondeterministic function |F| applied to a value |x|. 
In words, |y| is a possible \emph{refinement} of the nondeterministic 
expression |F x|. For example, |1  <~ MinWith (const 0) [1,2]| and
|2  <~ MinWith (const 0) [1,2]|. More generally, if |E1| and |E2| are possibly 
nondeterministic expressions of the same type |T|, we will write |E1 <~ E2| to 
mean that for all values |v| of |T| we have
\begin{spec}
    v <~ E1  ^  ==>  ^  v <~ E2
\end{spec}
We define two nondeterministic expressions of the same type to be equal
if they both have the same set of refinements: |E1=E2| if
\begin{spec}
    v <~ E1  ^  <==>  ^  v <~ E2
\end{spec}
for all |v|. Equivalently, 
\begin{spec}
    E1 = E2  ^  <==>  ^  E1 <~ E2 && E2 <~ E1
\end{spec}
which just says that |<~| is anti-symmetric. Our task is to make
precise the exact rules allowed for reasoning about |<~| and to prove that
these rules do not lead to contradictions.

To illustrate some of the pitfalls that have to be avoided, we consider three examples.
First, here is the distributive law again in which |minWith| is replaced by |MinWith|:
\begin{spec}
    MinWith f (concat xss) = MinWith f (map (MinWith f) xss)
\end{spec}
If this equation is to hold for all finite, nonempty lists |xss| of finite, nonempty lists, 
and we do indeed want it to, then it has to mean there is no refinement of one side 
that is not also a refinement of the other side. It does \emph{not} mean that the 
equation should hold for all possible implementations of |MinWith|, and it cannot mean 
that because it is false. Suppose we define |minWith| to return the \emph{second} best 
candidate in a list of candidates, or the only best candidate if there is 
only one. In particular,
\begin{spec}
    minWith (const 0) (concat [[a],[b,c]])                   = b 
    minWith (const 0) (map (minWith (const 0)) [[a],[b,c]])  = c
\end{spec}
The results are different so the distributive law fails. What the distributive law has 
to mean is the conjunction of the following two assertions, in which |M| abbreviates 
|MinWith cost|:
\begin{spec}
x <~ M (concat xss)             ^  ==>  ^  (exists xs . xs <~ map M xss && x <~ M xs)
(xs <~ map M xss && x <~ M xs)  ^  ==>  ^  x <~ M (concat xss)
\end{spec}
It is easy enough to show that these two assertions do hold though we omit details.

For the second example, consider the function |double x = x + x| over the integers. Does
the equation
\begin{spec}
    double (M xs) = M xs + M xs
\end{spec}
hold, where |xs| is a finite nonempty list of integers and |M = MinWith (const 0)|? We have
\begin{spec}
  ^^  x <~ double (M [1,2])
<==>  exists y . y <~ M [1,2] && x = double y
<==>  x = 2 || x = 4
\end{spec}
while
\begin{spec}
  ^^  x <~ M [1,2] + M [1,2]
<==>  exists y,z . y <~ M [1,2] && z <~ M [1,2] && x = y + z
<==>  x = 2 || x = 3 || x == 4
\end{spec}
so the answer is no. We have only that |double (M xs) <~ M xs + M xs|.

For the third example, again let |M = MinWith (const 0)|. It is easy enough to show,
for all |f1|, |f2| and |x| that
\begin{spec}
    M [f1 x, f2 x] = M [f1,f2] x
\end{spec}
but it would be wrong to conclude by |eta| conversion that
\begin{spec}
    \x-> M[f1 x, f2 x] = M [f1,f2]
\end{spec}
We have 
\begin{spec}
    f <~ \x-> M[f1 x, f2 x] <==> forall x : f x = f1 x || f x = f2 x
\end{spec}
However, 
\begin{spec}
    f <~ M [f1,f2] <==> (forall x : f x = f1 x) || (forall x: f x = f2 x)
\end{spec}    
The results are different. The |eta| rule, namely |f = \x-> f x|,
does not hold if |f| is a nondeterministic function such as |M [f1,f2]|. 

What else do we want? Certainly, we want a refinement version of the fusion law
for |foldr|, namely that over finite lists we have
\begin{spec}
foldr g e' xs <~ H (foldr f e xs)
\end{spec}
for all finite lists |xs| provided that |e' <~ H e| and |g x (H y) <~ H (f x y)|.
The context-sensitive version of the second condition reads:
\begin{spec}
    g x (H (foldr f e xs)) <~ H (f x (foldr f e xs))
\end{spec}
Here is the proof of the fusion law. The base case is immediate and the 
induction step is as follows:
\begin{spec}
  ^^  foldr g e' (x:xs)
=       {- definition of |foldr| -}
      g x (foldr g e' xs)
<~      {- induction, and monotonicity of refinement (see below) -}
      g x (H (foldr f e xs))
<~      {- fusion condition, and monotonicity of refinement -}
      H (f x (foldr f e xs))
=       {- definition of |foldr| -}
      H (foldr f e (x:xs))
\end{spec}
The appeal to the monotonicity of refinement is assertion
\begin{spec}
E1 <~ E2  ^  ==>  ^  F E1 <~ F E2
\end{spec}
So this condition is also required to hold.

Let us see what else we might need by redoing the calculation of the greedy 
algorithm for |mcc|. This time we start with the specification
\begin{spec}
mcc <~ MinWith cost . candidates
\end{spec}
For the context-sensitive fusion condition we reason:
\begin{spec}
  ^^  MinWith cost . step x . candidates
=       {- definition of |step| -}
      MinWith cost . concatMap ( additions x) . candidates
=       {- distributive law -}
      MinWith cost . map (MinWith cost .  additions x) . candidates
~>      {- suppose |add x <~ MinWith cost .  additions x| -}
      MinWith cost . map (add x). candidates
~>      {- greedy condition (see below) -}
      add x . MinWith cost . candidates
\end{spec}
We write |E1 ~> E2| as an alternative to |E2 <~ E1|.
The second step makes use of the distributive law, and the third step
is an instance of the monotonicity of refinement.

Let us now revisit the greedy condition. This time we only have to show
\begin{spec}
    add x . MinWith cost . candidates <~ MinWith cost . map (add x) . candidates
\end{spec}
where |add x <~ MinWith cost .  additions x|.
Unlike the previous version, this claim follows from the monotonicity 
condition (\ref{mono2}). To spell out the details, let |cs = candidates xs|
and suppose |c1| is a candidate in |cs| with minimum cost. We have only
to show that 
\begin{spec}
    add x c1 <~ MinWith cost (map (add x) cs
\end{spec}
Equivalently, that
\begin{spec}
    cost (add x c1) <= cost (add x c2)
\end{spec}    
for all candidates |c2 `elem` cs|. But this follows from (\ref{mono2}) and 
the fact that |cost c1 <= cost c2|.

Summarising, we have shown that |mcc =foldr add  c0| provided (\ref{mono2}) holds
for a suitable refinement of |add|. Unlike the previous calculation, the new one
is sufficient to deal with most examples of greedy algorithms, at least when
candidate generation is expressed in terms of |foldr|.

We have concentrated on greedy algorithms and the function |MinWith|, but there is 
another nondeterministic function |ThinBy|, which is needed in the study of thinning 
algorithms. Not every optimisation problem can be solved by a greedy
algorithm, and between the extremes of maintaining just one candidate at each step and
maintaining all possible candidates, there is the option of keeping only a subset of
candidates in play. That is where |ThinBy| comes in. It is a function with type
\begin{spec}
    ThinBy :: (a -> a -> Bool) -> [a] -> [a]
\end{spec}
Thus |ThinBy (<<) xs| takes a comparison function |<<| and a list |xs| as arguments
and returns a subsequence |ys| of |xs| such that for all |x| in |xs| there is a |y|
in |ys| with |y << x|. The subsequence is not specified further, so |ThinBy| is
nondeterministic. We mention |ThinBy| to show that there is more than one nondeterministic
function of interest in the study of deriving algorithms from specifications.

The task now before us is to find a suitable axiomatisation for a theory of
refinement and to give a model to show the soundness and consistency of the axioms. 
Essentially, this axiomatisation is the one proposed in \cite{m&b,m&b2} but simplified by
leaving out some details inessential for our purposes.

\section{An axiomatic basis}\label{sec:calc}

%format E_n = "\Varid{E}_n"
%format E_i = "\Varid{E}_i"
%format ?   = "\mathbin{\sqcap}"
%format choose = "\sqcap /"


Rather than deal with specific nondeterministic functions such as |MinWith|
and |ThinBy|, we can phrase the required rules in terms of a binary choice 
operator |(?)|. Thus,
\begin{spec}
    E1 ? E2 = MinWith (const 0) [E1,E2]
\end{spec}
We also have
\begin{spec}
    MinWith f xs  = foldr1 (?) [x | x <- xs, and [f x <= f y | y <- xs]]
\end{spec}
so |MinWith| can be defined in terms of |(?)|. Below we write |choose| for |foldr1 (?)|.
Thus |choose| takes a finite, nonempty list of arguments and returns an arbitrary element
of the list.

To formulate the axioms we need a language of types and expressions, and we
choose the simply-typed lambda calculus. Types are given by the grammar
\begin{spec}
    T ::= B | T -> T
\end{spec}
|B| consists of the base types, such as |Int| and |Bool|. We could 
have included pair types explicitly, as is done in \cite{m&b}, but for present purposes 
it is simpler to omit them. Expressions are given by the grammar
\begin{spec}
     E ::= C | V |  choose [E1,E2,...,E_n] | E E | \V:T -> E
\end{spec}
where |n>0| and each of |E1, E2,...,E_n| are expressions of the same type. We omit the type of the bound variable in a $\lambda$-abstraction if it can be inferred, and we 
write |E1 ? E2| for |choose [E1,E2]|.
Included in the constants |C| are constant 
functions such as the addition function |+| on integers (written infix as usual) and integer literals |0,1,-1,...|. The typing rules are 
standard; in particular, |choose [E1,E2,...,E_n]|, has type |T| if all |E_i| do.

%%\begin{enumerate}
%%\item A constant, or a constant function applied only to pure expressions.
%%\item A variable.
%%\item A list of pure expressions.
%%\item An application of a lambda abstraction with a pure body to a pure
%%      expression. Equivalently, if the expression can be converted into
%%      a pure expression by |beta|-reduction (see below).
%%\item A lambda abstraction, whose body may or may not be pure.
%%\end{enumerate} 
%%For example, |2| is a pure expression and so is |(+) E1 E2| provided both |E1| and |E2| are. 
%%However, |id ? const 3| and |2 ? 2| are both impure, even though |2 ? 2| describes a single 
%%value. The lambda expression |\y -> 1?y| is pure but applying it to any expression gives an 
%%impure result. Finally, |(\x -> \y -> x?y)1| is pure, and equivalent by |beta|-reduction 
%%to the pure expression |\y ->1?y|.
%%FR start
\def\pure#1{\mathit{pure}(#1)}
Boolean formulas are formed using equality |E1 = E2| and refinement |E1 <~ E2| of expressions 
as well as universal and existential quantification and the propositional connectives in the 
usual way. Additionally, in order to state the axioms, we need a predicate $\pure{E}$ to 
distinguish a subclass of expressions, called \emph{pure} expressions. The intention is to 
define a semantics in which a pure expression denotes a single value, except for lambda 
abstractions with impure bodies, which denote a set of functions.
We add rules such that $\pure{E}$ holds if |E| is
\begin{itemize}
\item a constant |C| applied to any number of pure arguments (including |C| itself if 
there are no arguments),
\item a lambda abstraction (independent of whether its body is pure).
\end{itemize} 
Like any predicate symbol, purity is closed under equality, i.e., an expression is 
also pure if it is equal to a pure expression. For example, |2| and |E1 + E2| for pure |E1| 
and |E2| are pure because |2| and |+| are constants. Also |\y ->1?y| is pure because it is 
a lambda abstraction, and |(\x -> \y -> x?y)1| is pure because it is equal by |beta|-reduction
(see below) to the former. Furthermore, |2 ? 2| is pure because it is equal to |2| (using the 
axioms given below), but |(\y ->1?y)2| and |1 ? 2| are both impure.
In what follows we use 
lowercase letters for pure expressions and uppercase letters for possibly impure expressions. 
%%FR end

%format vee = "\mathbin{\,\vee\,}"

The reason for introducing pure expressions is in the statement of our 
first two axioms, the rules of |beta| and |eta| conversion. The |beta| rule is that if 
|e| is a pure expression, then
\begin{eqnarray}
\label{beta}
|(\x -> E)e| &=& |E(x:=e)|
\end{eqnarray}
where |E(x:=e)| denotes the expression |E| with all free occurrences of |x| replaced by |e|.
%% FR
Intuitively, the purity restriction to |beta|-reduction makes sense because the bound variable 
of the lambda abstraction only ranges over values and therefore may only be substituted with 
pure expressions.
%%In particular, since variables are pure we have |E = (\x -> E) x|.

The |eta| rule asserts that if |f| is a pure function, then
\begin{eqnarray}
\label{eta}
|f|          &=& |\x -> f x|
\end{eqnarray}
%%FR
The purity restriction to |eta|-expansion makes sense because lambda-abstractions are 
always pure and thus can never equal an impure function.

%%FR start
\def\rul#1#2{\frac{#1}{#2}}
\def\tb{\;\;\;\;}
\def\vd{\;\vdash\;}

Our notion of purity corresponds to the \emph{proper} expressions of \cite{m&b} except that 
we avoid the axiom that variables are pure. Our first draft used that axiom, but we were unable 
to formalise the calculus until we modified that aspect. The reason why the axiom is problematic 
is that it forces a distinction between meta-variables (which may be impure) and object variables
(which must be pure). That precludes using higher-order abstract syntax when representing and 
reasoning about the language, e.g., in a logical framework like \cite{lf}, and highly complicates 
the substitution properties of the language.
However, just like in \cite{m&b}, our binders will range only over values, which our calculus 
captures by adding a purity assumption for the bound variable whenever traversing into the body 
of a binder. For example, the $\xi$ rule for equality reasoning under a lambda becomes:
\[\rul{\pure{x}\vd E=F}{\vd \lambda x . E = \lambda x .F}\]
%%FR end

As we will see below, without the above purity restrictions we could derive a contradiction 
with the remaining four axioms, which are as follows:
\begin{eqnarray}
\label{refines}
   |E1 <~ E2|     &|<==>|& |forall x . x <~ E1 ==> x <~ E2|\\
\label{equality}
   |E1 = E2|      &|<==>|& |forall x . x <~ E1 <==> x <~ E2|\\
%%FR reformulate the choice rule to avoid the dependency on natural numbers and lists
\label{choice}
   |x <~  choose [E1,E2,...,E_n]| &|<==>|& |  x <~ E1 vee x <~ E2 vee ... vee x <~ E_n| \\
\label{apply}
   |x <~ F E|     &|<==>|& |exists f,e . f <~ F && e <~ E && x <~ f e|\\ 
\label{lambda}
   |f <~ \x -> E| &|<==>|& |forall x . f x <~ E|
\end{eqnarray} 
Recall that free lower case variables range over pure expressions only, i.e., the free 
variables |x| and |f| are assumed pure.

From (\ref{refines}) and (\ref{equality}) we obtain that |(<~)| is reflexive, transitive 
and anti-symmetric. From (\ref{choice}) we obtain that |(?)| is associative, commutative 
and idempotent. Axioms (\ref{choice}) and (\ref{apply}) are sufficient to establish
\begin{eqnarray}
\label{distrib}
    |F ( choose [E1,E2,...,E_n]) =  choose [F E1,F E2,...,F E_n]|
\end{eqnarray}
Here is the proof:
\begin{spec}
     ^^  x <~ F (choose [E1,E2,...,E_n])
<==>       {- (\ref{apply}) -}
         exists f,e . f <~ F && e <~  choose [E1,E2,...,E_n] && x <~ f e
<==>       {- (\ref{choice}) -}
         exists i,f,e . f <~ F && e <~ E_i && x <~ f e
<==>       {- (\ref{apply}) -}
         exists i . x <~ F E_i
<==>       {- (\ref{choice}) -}
         x <~  choose [F E1,F E2,...,F E_n]
\end{spec}
It follows from (\ref{distrib}) and (\ref{beta}) that
\begin{spec}
    (\x -> x+x) (1 ? 2) = (\x -> x+x) 1 ? (\x -> x+x) 2 = 2 ? 4
\end{spec}
If, however, (\ref{beta}) was allowed to hold for arbitrary expressions, then we
would have
\begin{spec}
    (\x -> x+x) (1 ? 2) = (1 ? 2) + (1 ? 2) = 2 ? 3 ? 4
\end{spec}
which is a contradiction.

%format F1
%format F2
%format G1
%format G2

We can also show, for example, that |\x -> x ? 3| and |id ? const 3| 
are different functions even though they are extensionally the same:
\begin{spec}
    (\x -> x ? 3) x = x ? 3 = (id ? const 3) x
\end{spec}
Consider the function |h = \f -> f 1 + f 2|. We have by |beta| reduction
that
\begin{spec}
    h (\x -> x ? 3) = (\x -> x ? 3) 1 + (\x -> x ? 3) 2 = (1 ? 3) + (2 ? 3) = 3 ? 4 ? 5 ? 6
\end{spec}
while, on account of (\ref{distrib}), we have
\begin{spec}
    h (id ? const 3) = h id ? h (const 3) =  (1 + 2) ? (3 + 3) = 3 ? 6
\end{spec}
Thus two nondeterministic functions can be extensionally equal without
being the same function. That explains the restriction of the |eta| rule to pure functions.
Finally, (\ref{apply}) gives us that
\begin{spec}
    G1 <~ G2   ==>   F . G1 <~ F . G2
    F1 <~ F2   ==>   F1 . G <~ F2 . G
\end{spec}
where |(.) = (\f -> \g -> \x -> f (g x))|.

%%FR start
To complete the presentation of the calculus, we need to give the rules for the logical 
operators used in the axioms. The rule for the propositional connectives are the standard ones
and are omitted. But the rules for the quantifies are subtle because we have to ensure the 
quantifiers range over pure expressions only. In single-conclusion natural deduction style, 
these are
\[\Large\begin{array}{ccc}
\rul{\pure{x} \vd F}{\vd \forall x : F} & \tb\tb &
\rul{\vd \forall x : F \tb \vd \pure{e}}{\vd F(x:=e)} \\[.2cm]
\rul{\vd F(x:=e) \tb \vd\pure{e}}{\vd \exists x : F} & \tb\tb &
\rul{\vd \exists x : F \tb \pure{x},\;F\vd G}{ \vd G}
\end{array}\]
Here $\pure{e}$ is the purity predicate, whose axioms are described above.
%%FR end
  
%format lb = "\llbracket\!"
%format rb = "\!\rrbracket"
%format ua = "\!\!\uparrow"
%format osb = "\{\!"
%format csb = "\!\}"
%format ZZ  = "\mathbb{Z}"
%format BB  = "\mathbb{B}"
%format PP  = "\mathbb{P}^*"
%format sse = "\mathbin{\subseteq}"
%format <.> = "\, | \,"

\section{A denotational semantics}\label{sec:sem}

%% FR I made more disruptive changes in this section than in the previous one; so changes are not marked anymore

\def\sem#1{\llbracket#1\rrbracket}
\def\seme#1#2{\llbracket#1\rrbracket_{#2}}
\def\semr#1{\seme{#1}{\rho}}
\def\sse{\subseteq}
\def\rc#1{#1^\leftarrow}
\def\PP#1{\mathbb{P^*}#1}
\def\ZZ{\mathbb{Z}}
\def\ov#1{\overline{#1}}

%format myexists = "\exists"
%format myforall = "\forall"

To establish the consistency of the axiomatisation we give a denotational semantics for
nondeterministic expressions. As the target language of our semantics, we use standard set 
theory, with the notations $A\to B$ and $\lambda x\in A.b$ for functions (with $\in A$ omitted 
if clear).

\paragraph{Overview}
The basic intuition of the interpretation function $\sem{-}$ is given in the following table where we write |PP A| for the set of non-empty subsets of |A|:

\begin{center}
\begin{tabular}{ll}
\hline
Syntax & Semantics \\
\hline
type $T$              & set $\sem{T}$ \\
context declaring $x:T$ & environment mapping $\rho: x\mapsto \sem{T}$\\
expression $E:T$      & non-empty subset $\sem{E}\in\PP\sem{T}$\\
refinement |E1 <~ E2| & subset $\semr{E_1}\sse\semr{E_2}$\\
function |f:S->T|     & set--valued function $\semr{f}:\sem{S}\to\PP\sem{T}$ \\
choice |E1 ? E2|      & union $\semr{E_1}\cup\semr{E_2}$\\
purity $\pure{E}$ for $E:T$  & $\semr{E}$ is generated by a single $v\in\sem{T}$\\
\hline
\end{tabular}
\end{center}

Thus, types denotes sets, and non-deterministic expressions denote sets of values.
Functions are set-valued, and choice is simply union.

Additionally, for each type $T$, we will define the operation
\[\sem{T}\ni v\mapsto\rc{v}\in\PP\sem{T},\]
which embeds the single (deterministic) values into the power set.
We call it \emph{refinement closure} because $\rc{v}$ is the set of all values that we 
want to allow as a refinement of $v$.
This allows defining the refinement ordering $\leq_T$ on $\sem{T}$ by $v\leq _T w$ iff 
$\rc{v}\sse \rc{w}$.
For every expression $E:T$, the set $\sem{E}$ will be downward closed with respect to $\leq_T$.
One could add an expression |bottom| as a value with no refinements other than itself, which
denotes the empty set. But doing so would mean that |bottom| would be a refinement of every 
expression, which we choose not to have. That explains the restriction to non-empty sets in 
our semantics. Note that $\leq_T$ is not the same as the usual approximation ordering on 
Haskell expressions of a given type with |bottom| as the least element.

%%An expression |E| of type |T|
%%is interpreted as an \emph{upclosed} subset of a semantic type |lb T rb|.
%%By definition, a subset |S| of a partial order |(P,<=)| is upclosed if
%%|S = S ua|, where the upclosure |S ua| of |S| is defined by
%%\begin{spec}
%%    S ua  =  osb p `elem` P  <.> exists s `elem` S : s <= p csb
%%\end{spec}

\paragraph{Choice and Refinement}
We define 
\[\semr{\sqcap/[E_1,...,E_n]} = \semr{E_1}\cup\ldots\cup\semr{E_n}\]
This captures our intuition that a choice refines to any of its arguments, i.e., 
it denotes all values denoted by any argument. This is tied to the intuition that the 
refinement property corresponds to the subset condition on denotations.
For example, |E1 <~ E1 ? E2| corresponds to $\semr{E_1}\sse\semr{E_1\sqcap E_2}$.

Pure expressions $e:T$ cannot be properly refined. Therefore, they are intuitively 
interpreted as singleton sets. Technically, we have $\semr{e}=\rc{v}$ for some $v\in\sem{T}$.

\paragraph{Variables}
As usual, expressions with free variables are interpreted relative to an environment $\rho$.
Analogously to variables ranging over pure expressions, the environment maps every variable $x:T$ to a value $v\in\sem{T}$ (but not to a subset of $\sem{T}$ as one might expect).
Consequently, the denotation of a variable is defined by applying the refinement closure
 \[\semr{x}=\rc{\rho(x)}\]

\paragraph{Base Types and Constants}
The interpretation of base types is straightforward, and we define
\begin{spec}
    lb Int rb   =  ZZ
    lb Bool rb  =  BB
\end{spec}
Moreover, we define $\rc{v}=\{v\}$ for $v\in \sem{B}$ for every base type $B$.
In particular, we have $v\leq_B w$ iff $v = w$. In other words, the refinement ordering
on base types is \emph{flat}.

We would like to interpret all constants |C| in this straightforward way as well, but that 
is not as easy. In general, we assume that for every user-declared constant $C:T$, a denotation 
$\ov{C}\in\sem{T}$ is provided. Then we define 
\[\semr{C}=\rc{\ov{C}}.\]
However, we cannot simply assume that $\ov{C}$ is the standard denotation that we would use 
to interpret a deterministic type theory.
For example, for |+:Int -> Int -> Int|, we cannot define $\ov{+}$ as the usual addition $+_\ZZ:\ZZ\to\ZZ\to\ZZ$ because we need a value $\ov{+}:\ZZ\to\PP(\ZZ\to\PP\ZZ)$.

For first-order constants, i.e., constants $C:B_1\to \ldots\to B_n\to B$ where $B$ and all $B_i$ are base types (e.g., the constant $+$), we can still lift the standard interpretation relatively easily:
If $f:\sem{B_1}\to\ldots\to\sem{B_n}\to\sem{B}$ is the intended interpretation for $C$, we define
\[\overline{C}:\sem{B_1}\to\PP(\sem{B_2}\to\ldots\to\PP(\sem{B_n}\to\PP\sem{B})\ldots)\]
by
\[\overline{C}=\lambda x_1.\{\lambda x_2.\ldots \{\lambda x_n.\{f \,x_1\,\ldots,\,x_n\}\}\ldots\}\]
Because all $B_i$ are base types, this yields we have $\semr{C}=\rc{\overline{C}}=\{\overline{C}\}$.
For $n=0$, this includes constants $C:B$, e.g., $\semr{1}=\{1\}$ and accordingly for all integer literals.

But we cannot systematically lift standard interpretations of higher-order constants $C$ accordingly.
Instead, we must provide $\ov{C}$ individually for each higher-order constant.
But for the purposes of program calculation, this is acceptable because we only have to do it once for the primitive constants of the language.
In \cite{m&b}, this subtlety is handled by restricting attention to first-order constants.
%% This restriction is hidden in the phrase "every operator symbol f of the base types" on page 20 of \cite{m&b}

%%For a constant function |c| 
%%of |n| arguments (including |n=0|) we define
%%\begin{eqnarray}
%%\label{confs}
%%|lb c  rbM rho = osb \x1 -> osb \x2 ... osb \x_n-> cM x1 x2 ... x_n csb ... csb csb|
%%\end{eqnarray}
%%Thus if |c| has type |A1 -> A2 -> ... -> A_n -> B|, then |lb c rbM rho| has type 
%%\begin{spec}
%%    PP (lb A1 rb -> PP (lb A2 rb -> ...  -> PP (lb A_n rb -> PP lb B rb) ...)) 
%%\end{spec}
%%For variables |x| we define
%%\begin{eqnarray}
%%\label{vars}
%%|lb x  rbM rho = osb rho (x) csb ua|
%%\end{eqnarray}
%%For example, if the environment |rho| binds |x| to the function |f0| of type
%%|lb B -> B rb| where |lb B rb = osb 0,1 csb|, then |lb x rbM rho| is the set of the nine functions
%%seen above.

\paragraph{Functions}
%%For function types we define
%%\begin{spec}
%%    lb A -> B rb  =  (lb A rb ->  PP (lb B rb),<=)
%%\end{spec}
%%where |PP (S)| is the type of \emph{nonempty} subsets of |S| and |(<=)| is
%%defined by
%%\begin{spec}
%%    f <= g =  forall v `elem` lb B rb . g(v) sse f(v)
%%\end{spec}
%%where |X sse Y| means that |X| is a \emph{nonempty} subset of |Y|.
We define the interpretation of function types as follows:
\[\sem{S\to T}=\sem{S}\to\PP\sem{T}\]
and for $f\in\sem{S\to T}$ we define
\[\rc{f}=\{g:\sem{S\to T}\,\mid\,g(v)\sse f(v)\mathrm{\,for\,all\,}v\in\sem{S}\}\]
Thus, the refinement ordering on functions acts point-wise: $g \leq_{S\to T} f$ iff $g(v)\sse f(v)$ for all $v\in\sem{S}$.

%format ob = "\{\!"
%format cb = "\!\}"
%format f0
%format f1
%format f2
%format f3
%format f4
%format f5
%format f6
%format f7
%format f8


For example, there are nine functions of type |lb Bool -> Bool rb| with |BB=osb 0,1 csb| whose tables are as follows:
\begin{spec}
      ^^  ^  f0      ^^  ^  f1      ^^ ^  f2     ^^   ^ f3       ^^  ^ f4       ^^  ^ f5     ^^  ^ f6     ^^  ^ f7     ^^  ^ f8 
    0 ^^  ob 0,1 cb  ^^  ob 0,1 cb  ^^ ob 0 cb    ^^  ob 1 cb    ^^  ob 0,1 cb  ^^  ob 0 cb  ^^  ob 0 cb  ^^  ob 1 cb  ^^  ob 1 cb
    1 ^^  ob 0,1 cb  ^^  ob 0 cb    ^^ ob 0,1 cb  ^^  ob 0,1 cb  ^^  ob 1 cb    ^^  ob 0 cb  ^^  ob 1 cb  ^^  ob 0 cb  ^^  ob 1 cb
\end{spec}
For example, $f_7=\ov{\neg}$ is the lifting of the usual negation function.
The ordering $\leq_{Bool\to Bool}$ has top element |f0| and the four bottom elements |f5|, |f6|, |f7| and |f8|.


%format bigcup = "\bigcup"
%format rbM   = "\rrbracket^M"
%format x_n = "\Varid{x}_n"
%format A1
%format A2
%format A_n = "\Varid{A}_n"
%format cM = "\Varid{c}^M"

%%We now define |lb E rbM rho|, the denotation of an expression |E| for
%%a given interpretation |M| of the basic constants and evaluated in an environment 
%%|rho|. Environments are mappings of variables to values.
%%For a constant function |c| 
%%of |n| arguments (including |n=0|) we define
%%\begin{eqnarray}
%%\label{confs}
%%|lb c  rbM rho = osb \x1 -> osb \x2 ... osb \x_n-> cM x1 x2 ... x_n csb ... csb csb|
%%\end{eqnarray}
%%Thus if |c| has type |A1 -> A2 -> ... -> A_n -> B|, then |lb c rbM rho| has type 
%%\begin{spec}
%%    PP (lb A1 rb -> PP (lb A2 rb -> ...  -> PP (lb A_n rb -> PP lb B rb) ...)) 
%%\end{spec}
%%For variables |x| we define
%%\begin{eqnarray}
%%\label{vars}
%%|lb x  rbM rho = osb rho (x) csb ua|
%%\end{eqnarray}
%%For example, if the environment |rho| binds |x| to the function |f0| of type
%%|lb B -> B rb| where |lb B rb = osb 0,1 csb|, then |lb x rbM rho| is the set of the nine functions
%%seen above.

Finally, the clauses for the denotation of $\lambda$ and application terms are
%%\begin{eqnarray}
%%\label{lam}                                            
%% |lb \x -> E  rb rho| &=& |osb \v -> lb E  rb(  rho(x := v)) csb ua|
%%\\
%%\label{app}
%% |lb F E  rb rho| &=& |bigcup osb f(v)  <.>   f `elem` lb F  rb rho &&
%%                                            v `elem` lb E  rb rho csb|
%%\end{eqnarray}
\begin{eqnarray}
\label{lam}                                            
 \semr{\lambda x:S.E} &=& \rc{(\lambda v\in\sem{S} . \seme{E}{\rho(x := v)})}
\\
\label{app}
 \semr{F\, E} &=& \bigcup \{f(e) \mid  f \in \semr{F},\, e \in \semr{E}\}
\end{eqnarray}
Here the notation $\rho(x := v)$ means the environment $\rho$ extended with the
binding of $v$ to $x$.
Because every expression in already interpreted as a set and function expressions must be interpreted as set-valued functions, a $\lambda$-abstraction can be interpreted essentially as the corresponding semantic function.
We only need to apply the refinement closure.
Equivalently, we could rewrite (\ref{lam}) using
%%\begin{spec}
%%    osb \v -> lb E rb (rho(x := v))csb ua  =  osb f  <.>  forall v : f(v) sse lb E rb (rho(x := v)) csb
%%\end{spec}
\[\rc{(\lambda v\in\sem{S} . \seme{E}{\rho(x := v)})}  =  \{f \mid  f(v) \sse \seme{E}{\rho(x := v)} \mathrm{\,for\,all\,}v\in\sem{S}\}\]
The clause for application captures our intuition of monotonicity of refinement: $F\,E$ is interpreted by applying all possible denotations $f$ of $F$ to all possible denotations $e$ of $E$; each such application returns a set, and we take the union of all these sets.

\paragraph{Formulas}
Because formulas are a special case of expressions, they are interpreted as non-empty subsets of $\sem{Bool}=\{0,1\}$.
We write $\top$ for the truth value $\{1\}$ denoting truth.
The truth value $\{0,1\}$ will never occur (unless the user willfully interprets a constant in a way that returns it).

The denotation of all Boolean constants and expressions is as usual.
The denotation of the quantifiers and the special predicates is defined by:
\begin{eqnarray}
\semr{E_1\leftarrow E_2}&=& \top \tb\mathrm{iff}\tb \semr{E_1}\sse\semr{E_2}\\
\semr{\pure{E}}        &=&  \top  \tb\mathrm{iff}\tb \semr{E}=\rc{v} \mathrm{\,for\,some\,} v\in\sem{S}\\
\semr{\forall_S x : F} &=&  \top  \tb\mathrm{iff}\tb \seme{F}{\rho(x:=v)} = \top \mathrm{\,for\,all\,} v\in\sem{S} \\
\semr{\exists_S x : F} &=&  \top  \tb\mathrm{iff}\tb \seme{F}{\rho(x:=v)} = \top \mathrm{\,for\,some\,} v\in\sem{S} 
\end{eqnarray}
Note that the quantified variables seamlessly range only over values.

%%\begin{eqnarray}
%%\label{refine}
%%\ensuremath{\Conid{E}_{1}\leftarrow\Conid{E}_{2}} &=& \ensuremath{\forall \rho \hsforall
%%\mathbin{:}\llbracket\!\;\Conid{E}_{1}\;\!\rrbracket\;\rho \;\mathbin{\subseteq}\;\llbracket\!\;\Conid{E}_{2}\;\!\rrbracket\;\rho }
%%\end{eqnarray}

\paragraph{Soundness and Consistency}
We can now state the soundness of our calculus as follows:

\begin{theorem}[Soundness]
If $F$ is provable, then $\semr{F}=\top$ for every environment $\rho$ for the free variables of $F$.
In particular, if |E1 <~ E2| is provable, then $\semr{E_1}\sse\semr{E_2}$ for all environments $\rho$.
\end{theorem}
\begin{proof}
As usual, the proof proceeds by induction on derivations.

In particular, we must justify the axioms (\ref{beta}) - (\ref{lambda}).
We concentrate on (\ref{beta}), which
requires us to show
\[\semr{(\lambda x:S.E)\, e} = \semr{E(x:=e)}\]
for all expressions |E|, all pure expressions |e| and all environments |rho|.  The proof divides into
two cases according to the two axioms for purity: either |e| is an application of a constant to pure arguments, in which case $\semr{e}$ is a singleton set, or $e$ is a lambda abstraction.
For the former we will need the fact that if |e| is single-valued, then
$\semr{E(x:=e)}  = \seme{E}{\rho(x:= !\semr{e})}$
where $!\{v\}=v$. This \emph{substitution lemma} can be proved by structural induction on |E|.
That means we can argue:
\def\by#1{\\=\{\text{#1}\}\\}
\def\byref#1{\by{\ref{#1}}}

\[\begin{array}{l}
\semr{(\lambda x:S.E)\,e}
\byref{app}
         \bigcup \{ f(v) \mid f\in \semr{\lambda x.E},\, v \in\semr{e}\}
\byref{lam}
         \bigcup \{ f(v) \mid f(w) \sse \seme{E}{\rho(x:=w)} \text{ for all } w\in\sem{S},\; v\in \semr{e}\}
\by{$\semr{e}\sse\sem{S}$ and in general $\bigcup \{X \mid X \sse Y \} = Y$}
         \bigcup \{ \seme{E}{\rho(x:=v)} \mid  v \in \semr{e}\}
\by{|e| is single-valued}
         \seme{E}{\rho(x:= !\semr{e})}
\by{substitution lemma}
         \semr{E(x:=e)}
\end{array}\]

For the second case, where |e| is a lambda abstraction |\y:T -> F|, we need the fact that
\[\semr{(\lambda x.E)\,(\lambda y.F)} = \seme{E}{\rho(x:= \lambda v.\seme{F}{\rho(y:= v)})}\]
This fact can be established as a corollary to the \emph{monotonicity lemma} which asserts $\seme{E}{\rho(x:=f)}\sse\seme{E}{\rho(x:=g)}$ whenever $f(v) \sse g(v)$ holds for all $v\in\sem{S}$.
for all expressions |E| and environments |rho|. The monotonicity lemma can be proved by structural induction on |E|.
The corollary above is now proved by reasoning
\[\begin{array}{l}
         \semr{(\lambda x.E)\,(\lambda y.F)}
\byref{app}
         \bigcup \{ h(f) \mid h \in \semr{\lambda x.E},\, f \in \semr{\lambda y.F} \}
\by{as in previous calculation}
         \bigcup \{ \seme{E}{\rho(x:=f)} \mid  f \in \semr{\lambda y. F}\}
\byref{lam}
         \bigcup \{ \seme{E}{\rho(x:=f)} \mid f(v)\sse\seme{F}{\rho(y:=v)} \text{ for all } v\in\sem{T}\}
\by{monotonicity lemma}
         \seme{E}{\rho(x:= \lambda v.\seme{F}{\rho(y:= v)})}
\end{array}\]
It remains to show that the latter is equal to $\semr{E(x:= \lambda y.F)}$.
Here we proceed by structural induction on |E|. We omit the details. The other axioms are proved by similar reasoning.
\end{proof}


%% FR these are two cases for the above structural induction
%%Here are two cases:
%%\begin{spec}
%%     ^^  lb x(x:= \y->F) rb rho
%%=          {- substitution -}
%%         lb \y->F rb rho
%%=          {- (\ref{lam}) -}
%%         osb \v-> lb F rb(rho(y:=v)) csb ua
%%=          {- substitution -}
%%         lb x rb(rho(x:= \v-> lb F rb(rho(y:=v))))
%%\end{spec}
%%and
%%\begin{spec}
%%    ^^   lb (\z->E)(x:= \y->F) rb rho
%%=          {- substitution, assuming |z| does not occur free in |F| -}
%%         lb \z->E(x:= \y->F) rb rho
%%=          {- (\ref{lam}) -}
%%         osb \v-> lb E(x:= \y->F rb (rho(z:=v)) csb ua
%%=          {- induction -}
%%         osb \v-> lb E rb(rho(z:=v)(x:= \w-> lb F rb(rho(z:=v)(y:=w)))) csb ua
%%=          {- since |z| does not occur free in |F| -}
%%         osb \v-> lb E rb(rho(z:=v)(x:= \w-> lb F rb(rho(y:=w)))) csb ua
%%=          {- environments: |rho(x:=a)(y:=b)=rho(y:=b)(x:=a)|  -}
%%         osb \v-> lb E rb(rho(x:= \w-> lb F rb)(rho(y:=w))(z:=v)) csb ua
%%=          {- (\ref{lam}) -}
%%         lb \z->E rb(rho(x:= \w-> lb F rb)(rho(y:=w)))     
%%\end{spec}


As a straightforward consequence of soundness, we have
\begin{theorem}[Consistency]
Our calculus is consistent, i.e., we cannot derive a contradiction.
\end{theorem}
\begin{proof}
If we could derive a contradiction, then soundness would yield a contradiction in set theory.
\end{proof}
Technically, our calculus is only consistent under the assumption that set theory is consistent.
We can strengthen that result by using a much weaker target language than set theory for our semantics.
Indeed, standard higher-order logic (using an appropriate definition of power set) is sufficient.

\section{Summary}

The need for nondeterministic functions arose while the first author was preparing a
text on an introduction to Algorithm Design using Haskell. The book, which is co-authored by
Jeremy Gibbons, will be published by Cambridge University Press next year. Two of the six
parts of the book are devoted to greedy algorithms and thinning algorithms. To make the
material as accessible as possible, we wanted to stay close to Haskell and that meant
we did not want to make the move from functions to relations, as proposed for instance in \cite{bird&demoor}.
Instead, we made use of just two nondeterministic functions, |MinWith| and |ThinBy| (or
three if you count |MaxWith|), and reasoned about refinement rather than equality when the
need arose. The legitimacy of the calculus, as propounded above, was omitted. The problems
associated with reasoning about nondeterminism were discussed at the Glasgow meeting of WG2.1 
in 2016, when the second author came on board. Our aim has been to write a short and hopefully
sufficient introduction to the subject of nondeterminism for functional programmers rather than logicians. In this enterprise we made much use of the very readable papers by Joe Morris and 
Alexander Bunkenberg. 

\begin{thebibliography}{99}


\bibitem[1]{bird&demoor}
Richard S. Bird and Oege de Moor. 
\newblock \emph{The Algebra of Programming}.
\newblock Prentice-Hall International Series in Computer Science, Hemel
Hempstead, UK (1997).

\bibitem[2]{lf}
R.~Harper, F.~Honsell, and G.~Plotkin.
\newblock {A framework for defining logics}.
\newblock {\em {Journal of the Association for Computing Machinery}},
  40(1):143--184, 1993.

\bibitem[3]{m&b}
Joseph M. Morris and Alexander Bunkenburg. 
\newblock Specificational functions.
\newblock \emph{ACM Transactions on Programming Languages and Systems},
21 (3) (1999) pp 677--701.

\bibitem[4]{m&b2}
Joseph M. Morris and Alexander Bunkenburg. 
\newblock Partiality and Nondeterminacy in Program Proofs
\newblock\emph{Formal Aspects of Computing} 10 (1998) pp 76--96.

\bibitem[5]{m&t}
Joseph M. Morris and Malcolm Tyrrell.
\newblock Dually nondeterministic functions.
\newblock\emph{ACM Transactions on Programming Languages and Systems},
30 (6), Article 34 (2008).

\end{thebibliography}





\end{document}
