$$
\newcommand{\llbracket}{[\\![}
\newcommand{\rrbracket}{]\\!]}
$$
$$\newcommand{\restr}[2]{{#1|}\_{#2}}
\newcommand{\pow}[1]{\mathcal{P}(#1)}
\newcommand{\arr}[2]{#1 \rightarrow #2}
\newcommand{\inj}[2]{#1 \hookrightarrow #2}
\newcommand{\func}[3]{#1 \colon \arr{#2}{#3}}
\newcommand{\parr}[2]{#1 \rightharpoonup #2}
\newcommand{\pfunc}[3]{#1 \colon \parr{#2}{#3}}
\newcommand{\Endo}[2]{\func{#1}{#2}{#2}}
\newcommand{\op}[1]{#1^{\mathrm{op}}}
\newcommand{\nat}[3]{#1 \colon #2 \Rightarrow #3}
\newcommand{\IntHom}[2]{\left[ #1, #2 \right]}
\newcommand{\prodArr}[1]{\langle #1 \rangle}
\newcommand{\coprodArr}[1]{\left[ #1 \right]}
\newcommand{\dom}{\operatorname{dom}}
\newcommand{\SVar}{\mathrm{SVar}}
\newcommand{\SEnv}{\mathrm{SEnv}}
\newcommand{\SCtx}{\mathrm{SCtx}}
\newcommand{\fpSem}[2]{\llbracket #1 \rrbracket_{#2}}
\newcommand{\arrObj}[3]{\begin{pmatrix}\mathop{\scriptstyle #1\downarrow}^{\phantom{#1}#2}_{\phantom{#1}#3}\end{pmatrix}}
\DeclareMathOperator{\const}{const}
\DeclareMathOperator{\id}{id}
\DeclareMathOperator{\Id}{Id}
\DeclareMathOperator{\colim}{colim}
\DeclareMathOperator{\supp}{supp}
\DeclareMathOperator{\dom}{dom}
$$

$\newcommand{\Cat}[1]{\mathbf{#1}}
\newcommand{\SetC}{\Cat{Set}}
\newcommand{\VecC}{\Cat{Vec}}
\newcommand{\CoalgC}[1]{\mathrm{CoAlg}(#1)}
\newcommand{\TopC}{\Cat{Top}}
\newcommand{\slice}[2]{#1/{\scriptstyle #2}}$

# Interpretation of Sized Types using Fibrations
## Size Environments are Fibred over Size Contexts
Let $\SVar$ be a set of size variable, denoted $i, j$, and $(S, \leq)$ a
well-ordered set, the elements of which we denote by $\alpha, \beta$.
A _size context_ $\Delta$ is a list of size variables $i_1, \dotsc, i_n$.
We order contexts by extension, that is, $\Delta \sqsubseteq \Delta'$ iff
$\Delta' = \Delta, i_1', \dotsc, i_k'$.
Using this ordering, we have a category $\SCtx$.

From contexts, we get \emph{size environments} as pairs of contexts $\Delta$
and partial maps $\sigma : \parr{\SVar}{S}$ with $\dom \sigma = \Delta$.
We order size environments lexicographically, that is,
$(\Delta, \sigma) \leq (\Delta', \sigma')$ iff $\Delta \sqsubseteq \Delta'$,
$\Delta = i_1, \dotsc, i_n$, and there is an $m$, s.t.
$\sigma(i_k) = \sigma'(i_k)$ for all $k < m$ and
$\sigma(i_m) \leq \sigma'(i_m)$.
The partial order gives again rise to a category of environments, denoted by
$\SEnv$.

By definition, $(\Delta, \sigma) \leq (\Delta', \sigma')$ implies
$\Delta \sqsubseteq \Delta'$ and so the map $c : \SEnv \to \SCtx$, given by
projecting on the context, is monontone, hence a functor.
Moreover, for all contexts $\Delta \sqsubseteq \Delta'$ and environments
$(\Delta', \sigma')$, we get an environment $(\Delta, \sigma)$, which is
lexicographically smaller than $(\Delta', \sigma')$, by restriction:
$\sigma = \restr{\sigma'}{\Delta}$.
Since all other environments $(\Delta, \tau)$ must be lexicograpically smaller
than $(\Delta, \sigma)$, we actually have that $\sigma$ is the
\emph{cartesian lifting} of $\Delta'$ along $\Delta \sqsubseteq \Delta'$.
Therefore, $c : \SEnv \to \SCtx$ is a fibration.

## Interpretation of Fixed Point Approximations
In this we section, we expose the structure necessary to interpret sized types,
that is, we approximate fixed points of functors and organise these
approximations by their approximation depth.

To this end, we will work in a category $\Cat{U}$, which is to thought of as
our type universe.
This category has to be total over $\SEnv$, that is, we require to be given
a fibration $\arrObj{p}{\Cat{U}}{\SEnv}$.
Moreover, since we want to interpret products, function types and dependent
types, $\Cat{U}$ should be fibrewise cartesian closed and have fibrewise left
and right adjoints $\Sigma_A \dashv \Delta_A \dashv \Pi_A$ to the diagonal
$\Delta_{A} : \Cat{U}_\sigma \to \slice{\Cat{U}\_\sigma}{A}$ for every
environment $\sigma$ and $A : \Cat{U}$.
These are the dependent sum and product, as usual.

An endofunctor on the fibration $\arrObj{p}{\Cat{U}}{\SEnv}$, i.e., a map of
fibrations, is an endofunctor $F$ on $\Cat{U}$ with $p \circ F = p$.
This means, that for every size environment $\sigma$ and type $A : \Cat{U}_A$
above $\sigma$, its image $F A$ must be over $\sigma$.
Since sizes shall represent fixed point approximations, this is exactly what
we want.
We will need the composed fibration $r = c \circ p : \Cat{U} \to \SCtx$,
mapping a type to its size context.

Approximations of the least and greatest fixed point of $F$ are given as
usual by constructing a diagram from smaller approximations and the taking
the colimit or limit, respectively.
To this end, let $\sigma : \SEnv$ a size environment for context $\Delta$,
$i \in \Delta$ and $\alpha = \sigma(i)$.
The semantics of $\mu^iF$ are given by the fibred colimit
$\fpSem{\mu^i F}{\sigma} = \colim D^\sigma_F$ for the following diagram

$$
\begin{align*}
  & D^\sigma_F : \arrObj{q}{S^{< \alpha}}{\SCtx} \to \arrObj{r}{\Cat{U}}{\SEnv} \\\\
  & D^\sigma_F (\beta) = F(\fpSem{\mu^i F}{\sigma[i \mapsto \beta]}) \\\\
  & D^\sigma_F (\beta \leq \beta') =
    f : \fpSem{\mu^i F}{\sigma[i \mapsto \beta]}
        \to \fpSem{\mu^i F}{\sigma[i \mapsto \beta']}
\end{align*}
$$
where

 - $q(\beta) = \Delta$ is the constant fibration and
 - $f$ is the given as the unique map from the colimit property, since the
  cocone over $D^{\sigma[i \mapsto \beta']}_F$ from
  $\fpSem{\mu^i F}{\sigma[i \mapsto \beta']}$ restricts to a cocone over
  $D^{\sigma[i \mapsto \beta]}_F$.

That $\fpSem{\mu^iF}{\sigma}$ is given as a fibred (over $r$) colimit,
guarantees that the size \emph{context} is not changed in the process.
This is where the fibration $\arrObj{c}{\SEnv}{\SCtx}$ becomes important.
We also note that this process is well-defined, since $S$ is well-ordered,
hence $S^{< \alpha}$ has a minimum, say $\alpha_0$.
Then the colimit of $D_F^{\sigma[i \mapsto \alpha_0]}$ is an initial object in
$\Cat{U}_\Delta$.

Analogously, we can approximate greatest fixed points as limits of a similar
diagram, as follows.
Let again $\sigma : \SEnv$ be a size environment for context $\Delta$,
$i \in \Delta$ and $\alpha = \sigma(i)$.
The semantics of the greatest fixed point is given by the fibred limit
$\fpSem{\mu^iF}{\sigma} = \lim \overline{D}^\sigma_F$ with
\begin{align*}
  & \overline{D}^\sigma_F : \arrObj{q}{\op{(S^{< \alpha})}}{\SCtx}
                           \to \arrObj{r}{\Cat{U}}{\SEnv} \\\\
  & \overline{D}^\sigma_F(\beta) = F(\fpSem{\nu^i F}{\sigma[i \mapsto \beta]}) \\\\
  & \overline{D}^\sigma_F(\beta \leq \beta') =
    f : \fpSem{\nu^i F}{\sigma[i \mapsto \beta']}
        \to \fpSem{\nu^i F}{\sigma[i \mapsto \beta]}
\end{align*}
where $q$ is again the constant fibration and $f$ is given by the limit
property as above.

From the (co)limit properties, we also get necessary constructors/destructors:
for all $\beta < \alpha$, we have
$$
\begin{align*}
  & \mathrm{in}\_\beta^{\alpha} : F\left(\mu^{\beta}\right) \to \mu^{\alpha} \\\\
  & \mathrm{out}_\beta^{\alpha} : \nu^{\alpha} \to F\left(\nu^{\beta}\right).
\end{align*}
$$
This is exactly the structure coming with sized types.

### todo
If we can interalise the quantification over $\beta$, we could actually get
$\mathrm{in}^{\alpha} :
  \left(\exists \beta < \alpha .F\left(\mu^{\beta}\right)\right)
  \to \mu^{\alpha}$
and
$\mathrm{out}^{\alpha} : \nu^{\alpha}
  \to \left(\forall \beta < \alpha .F\left(\nu^{\beta}\right)\right)$.
 <!--
% \begin{align*}
%   & \mathrm{in}^{\alpha} :
%     \left(\exists \beta < \alpha .F\left(\mu^{\beta}\right)\right)
%     \to \mu^{\alpha} \\
%   & \mathrm{out}^{\alpha}_{\beta} : \nu^{\alpha}
%     \to \left(\forall \beta < \alpha .F\left(\nu^{\beta}\right)\right).
% \end{align*}
-->
So far, this is not possible, since the usual definition of quantification
in such a fibred setting requires finite products in $\SEnv$.
In the current setup, $\sigma_1 \times \sigma_2$ is the least environment,
contained lexicographically in, both, $\sigma_1$ and $\sigma_2$.
Then quantification would be a rather weird concept in this setting.
I have to think about this.

## Example
Let $\Cat{U} = \SetC \times \SEnv$ and $p = \pi_2$.
This is rather trivially a fibration and probably our main example.
Since for every environment $\sigma$, we have $\Cat{U}_\sigma \cong \SetC$, it
is clear that $\Cat{U}$ is fibrewise cartesian closed and has depent sums and
products.

A functor $\Endo{F}{\Cat{U}}$ is a given by a family
$\\{\Endo{G_\sigma}{\SetC}\\}\_{\sigma : \SEnv}$ of functors.
Moreover, for contexts $\Delta$, the fibre over it with respect to $c \circ p$,
is just $\Cat{U}_\Delta \cong \SetC \times S^\Delta$, where $S^\Delta$ is the
collections of environments over the context $\Delta$.
The diagram $D^\sigma_F : S^{< \alpha} \to \Cat{U}_\Delta$ is then given by
\begin{equation*}
  D^\sigma_F(\beta) = (G_{\sigma'}(\mu^{\sigma'}F), \sigma'),
  \quad \sigma' = \sigma[i \mapsto \beta]
\end{equation*}
and its colimit is
\begin{equation*}
  \mu^{\sigma}F = \colim D^\sigma_F
  = (\colim \, (\pi_1 \circ D^{\sigma}_F), \sigma)
\end{equation*}
where the second colimit is taken in $\SetC$.

## Universes
In the notes, Andreas also mentions $\mathrm{Fun} \, A$, the collection of
endofunctors on $A$.
Since we do not have these internalised into the fibration $p$, the mentioned
monotonicity theorem does not play a role here.
I would rather require a hierarchy of such fibrations, where the functor
category $\IntHom{p}{p}$ lives one level up.

	
