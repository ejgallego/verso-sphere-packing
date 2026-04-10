import Verso
import VersoManual
import VersoBlueprint
import SpherePackingBlueprint.ToolchainWorkarounds
import SpherePackingBlueprint.Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option linter.style.longLine false


#doc (Manual) "Sphere Packings" =>


:::group "sphere_setup"
Definitions of sphere packings, density, and the optimization target.
:::

:::group "sphere_scaling"
Scaling invariance of finite density and asymptotic density.
:::

:::group "periodic_packings"
Periodic and lattice packings as a reduced optimization class.
:::

:::group "sphere_main_statement"
Reduction from Cohn-Elkies bounds to the final dimension-8 theorem.
:::

The sphere packing problem is a classic optimisation problem with widespread
applications that go well beyond mathematics. The task is to determine the
densest possible arrangement of spheres in a given space. It remains unsolved
in all but finitely many dimensions.

```tex
The Sphere Packing problem is a classic optimisation problem with widespread applications that go well beyond mathematics. The task is to determine the ``densest" possible arrangement of spheres in a given space. It remains unsolved in all but finitely many dimensions.
```

It was shown in {citet Via2017}[] that the optimal arrangement in $`\R^8` is
given by the $`E_8` lattice. The result depends strongly on the Cohn-Elkies
linear programming bound from {citet ElkiesCohn}[], which bounds the optimal
density of sphere packings in $`\R^d` in terms of a function $`\R^d \to \R`
satisfying certain conditions. The proof in {citet Via2017}[] uses modular
forms to construct a function that bounds the density of all sphere packings in
$`\R^8` above by the density of the $`E_8` lattice packing, and hence shows
that no packing in $`\R^8` can be denser than the $`E_8` lattice packing.

```tex
It was famously determined, in~\cite{Via2017}, that the optimal arrangement in $\mathbb{R}^8$ is given by the $E_8$ lattice. The result is strongly dependent on the Cohn-Elkies linear programming bound (Theorem 3.1 in~\cite{ElkiesCohn}), which, if a $\R^d \to \R$ function satisfying certain conditions exists, bounds the optimal density of sphere packings in $\R^d$ in terms of it. The proof in~\cite{Via2017} uses the theory of modular forms to construct a function that can be used to bound the density of all sphere packings in $\R^8$ above by the density of the $E_8$ lattice packing. This then allows us to conclude that no packing in $\R^8$ can be denser than the $E_8$ lattice packing.
```

This subsection gives an overview of the setup of the problem, both
informally and in Lean. Throughout this blueprint, $`\R^d` denotes the
Euclidean vector space equipped with distance $`\|\cdot\|` and Lebesgue
measure $`\mathrm{Vol}(\cdot)`. For any $`x \in \R^d` and
$`r \in \R_{>0}`, we denote by $`B_d(x,r)` the open ball in $`\R^d` with
center $`x` and radius $`r`. While we will give a more formal definition of
a sphere packing below, the underlying idea is that it is a union of balls of
equal radius centered at points that are far enough from each other that the
balls do not overlap.

```tex
This subsection gives an overview for the setup of the problem, both informally and in Lean. Throughout this blueprint, $\R^d$ will denote the Euclidean vector space equipped with distance $\|\cdot\|$ and Lebesgue measure $\mathrm{Vol}(\cdot)$. For any $x\in\R^d$ and $r\in\R_{>0}$, we denote by $B_d(x,r)$ the open ball in $\R^d$ with center $x$ and radius $r$. While we will give a more formal definition of a sphere packing below (and in Lean), the underlying idea is that it is a union of balls of equal radius centred at points that are far enough from each other that the balls do not overlap.
```

Arguably the most important definition in this subsection is that of packing
density, which measures which portion of $`d`-dimensional Euclidean space is
covered by a given sphere packing. Taking the supremum over all packings gives
the sphere packing constant, which is the quantity we are interested in
optimising.

```tex
Arguably the most important definition in this subsection is that of \emph{packing density}, which measures which portion of $d$-dimensional Euclidean space is covered by a given sphere packing. Taking the supremum over all packings gives what we refer to as the \emph{sphere packing constant}, which is the quantity we are interested in optimising.
```

:::definition "SpherePacking.balls" (lean := "SpherePacking.balls") (parent := "sphere_setup")
Given a set $`X \subset \R^d` and a real number $`r > 0` such that
$`\|x-y\| \ge r` for all distinct $`x,y \in X`, we define the sphere packing
$`\Pa(X)` with centers at $`X` to be the union of all open balls of radius
$`r` centered at points of $`X`:
$$`\Pa(X) := \bigcup_{x \in X} B_d(x,r)`
:::

```tex "SpherePacking.balls"
\begin{definition}\label{SpherePacking.balls}\lean{SpherePacking.balls}\leanok  % Do we want to replace the notation \mathcal{P} with \mathcal{P}_X or \mathcal{P}(X)?
  Given a set $X \subset \R^d$ and a real number $r > 0$ (known as the \emph{separation radius}) such that $\|x - y\| \geq r$ for all distinct $x, y \in X$, we define the \emph{sphere packing} $\Pa(X)$ with centres at $X$ to be the union of all open balls of radius $r$ centred at points in $X$:
  \[
    \Pa(X) := \bigcup_{x \in X} B_d(x, r)
  \]
\end{definition}
```

Note that a sphere packing is uniquely defined by a given set of centers,
provided that set admits a corresponding separation radius. During the
formalisation process, everything depending on sphere packings is therefore
defined in terms of `SpherePacking`, a `structure` bundling the identifying
information of a packing rather than the actual balls themselves. For this
blueprint, however, we will refrain from making that distinction.

```tex "SpherePacking"
\begin{remark}\label{SpherePacking}\lean{SpherePacking}\leanok
  Note that a sphere packing is uniquely defined from a given set of centres (which, in order to be a valid set of centres, must admit a corresponding separation radius). Therefore, as a conscious choice during the formalisation process, we will define everything that depends on sphere packings in terms of \verb|SpherePacking|, a \verb|structure| that bundles all the identifying information of a packing, but not the actual balls themselves. For the purposes of this blueprint, however, we will refrain from making this distinction.
\end{remark}
```

We now define a notion of density for bounded regions of space by considering
the density inside balls of finite radius.

```tex
We now define a notion of density for bounded regions of space by considering the density inside balls of finite radius.
```

:::definition "SpherePacking.finiteDensity" (lean := "SpherePacking.finiteDensity") (parent := "sphere_setup")
The finite density of a packing $`\Pa` is defined as
$$`\Delta_{\Pa}(R):=\frac{\mathrm{Vol}(\Pa\cap B_d(0,R))}{\mathrm{Vol}(B_d(0,R))},\quad R>0.`
{uses "SpherePacking"}[]{uses "SpherePacking.balls"}[]
:::

```tex "SpherePacking.finiteDensity"
\begin{definition}\label{SpherePacking.finiteDensity}\lean{SpherePacking.finiteDensity}\uses{SpherePacking, SpherePacking.balls}\leanok
  The \emph{finite density} of a packing $\mathcal{P}$ is defined as
  \[
    \Delta_{\mathcal{P}}(R):=\frac{\mathrm{Vol}(\mathcal{P}\cap B_d(0,R))}{\mathrm{Vol}(B_d(0,R))},\quad R>0.
  \]
\end{definition}
```

As intuitive as it seems to take the density of a packing to be the limit of
the finite densities as the radius of the ball goes to infinity, it is not
immediately clear that this limit exists. Therefore, we define the density of a
sphere packing as a limit superior instead.

```tex
As intuitive as it seems to take the density of a packing to be the limit of the finite densities as the radius of the ball goes to infinity, it is not immediately clear that this limit exists. Therefore, we define the density of a sphere packing as a limit superior instead.
```

:::definition "SpherePacking.density" (lean := "SpherePacking.density") (parent := "sphere_setup")
We define the density of a packing $`\Pa` as the limit superior
$$`\Delta_{\Pa}:=\limsup\limits_{R\to\infty}\Delta_{\Pa}(R).`
{uses "SpherePacking"}[]{uses "SpherePacking.finiteDensity"}[]
:::

```tex "SpherePacking.density"
\begin{definition}\label{SpherePacking.density}\lean{SpherePacking.density}\uses{SpherePacking, SpherePacking.finiteDensity}\leanok
  We define the \emph{density} of a packing $\mathcal{P}$ as the limit superior
  \[
    \Delta_{\mathcal{P}}:=\limsup\limits_{R\to\infty}\Delta_{\mathcal{P}}(R).
  \]
\end{definition}
```

We may now define the sphere packing constant, the quantity that the sphere
packing problem requires us to compute.

```tex
We may now define the sphere packing constant, the quantity that the sphere packing problem requires us to compute.
```

:::definition "SpherePackingConstant" (lean := "SpherePackingConstant") (parent := "sphere_setup")
The sphere packing constant is defined as the supremum of packing densities
over all possible packings:
$$`\Delta_d:=\sup\limits_{\substack{\mathcal{P}\subset\R^d\\ \scriptscriptstyle\mathrm{sphere}\;\mathrm{packing}}}\Delta_{\mathcal{P}}.`
{uses "SpherePacking.balls"}[]{uses "SpherePacking.density"}[]
:::

```tex "SpherePackingConstant"
\begin{definition}\label{SpherePackingConstant}\lean{SpherePackingConstant}\uses{SpherePacking.balls, SpherePacking.density}\leanok
  The \emph{sphere packing constant} is defined as supremum of packing densities over all possible packings:
  \[
    \Delta_d:=\sup\limits_{\substack{\mathcal{P}\subset\R^d\\ \scriptscriptstyle\mathrm{sphere}\;\mathrm{packing}}}\Delta_{\mathcal{P}}.
  \]
\end{definition}
```

Given that the problem concerns the arrangement of balls in space, it is
natural not to worry about the radius of the balls, so long as they are all
equal. However, the definition `SpherePacking.balls` involves a choice of
separation radius. In this subsection we describe how to change the separation
radius of a sphere packing by scaling the packing by a positive real number,
and prove that this does not affect its density. This will let us choose any
separation radius we like when defining the optimal sphere packing in $`\R^d`.

```tex
Given that the problem involves the \emph{arrangement} of balls in space, it is intuitive not to worry about the radius of the balls (so long as they are all equal to each other). However, Definition~\ref{SpherePacking.balls} involves a choice of separation radius. In principle, we would want two sphere packing configurations that differ only in separation radii to `encode the same information'. In this brief subsection, we will describe how to change the separation radius of a sphere packing by \emph{scaling} the packing by a positive real number and prove that this does not affect its density. This will give us the freedom to choose any separation radius we like when attempting to define the optimal sphere packing in $\R^d$.
```

:::definition "SpherePacking.scale" (lean := "SpherePacking.scale") (parent := "sphere_scaling")
Given a sphere packing $`\Pa(X)` with separation radius $`r`, we define the
scaled packing with respect to a real number $`c > 0` to be the packing
$`\Pa(cX)`, where $`cX = \setof{cx \in V}{x \in X}` has separation radius
$`cr`.
{uses "SpherePacking"}[]
:::

```tex "SpherePacking.scale"
\begin{definition}\label{SpherePacking.scale}\lean{SpherePacking.scale}\uses{SpherePacking}\leanok
  Given a sphere packing $\Pa(X)$ with separation radius $r$, we defined the \emph{scaled packing} with respect to a real number $c > 0$ to be the packing $\Pa(cX)$, where $cX = \setof{cx \in V}{x \in X}$ has separation radius $cr$.
\end{definition}
```

:::lemma_ "SpherePacking.scale_finiteDensity" (lean := "SpherePacking.scale_finiteDensity") (parent := "sphere_scaling")
Let $`\Pa(X)` be a sphere packing and $`c` a positive real number. Then, for
all $`R > 0`,
$$`\Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R).`
{uses "SpherePacking.finiteDensity"}[]{uses "SpherePacking.scale"}[]
:::

```tex "SpherePacking.scale_finiteDensity"
\begin{lemma}\label{SpherePacking.scale_finiteDensity}\lean{SpherePacking.scale_finiteDensity}\uses{SpherePacking.finiteDensity, SpherePacking.scale}\leanok
  Let $\Pa(X)$ be a sphere packing and $c$ a positive real number. Then, for all $R > 0$,
  \[
    \Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R).
  \]
\end{lemma}
```

:::proof "SpherePacking.scale_finiteDensity"
The proof follows by direct computation:
$$`\Delta_{\Pa(cX)}(cR) = \frac{\Vol{\Pa(cX) \cap B_d(0, cR)}}{\Vol{B_d(0, cR)}} = \frac{c^d \cdot \Vol{\Pa(X) \cap B_d(0, R)}}{c^d \cdot \Vol{B_d(0, R)}} = \Delta_{\Pa(X)}(R).`
The second equality follows from the fact that scaling a measurable set by a
factor of $`c` scales its volume by a factor of $`c^d`, together with
$`\Pa(cX) \cap B_d(0, cR) = c \cdot (\Pa(X) \cap B_d(0, R))`.
:::

```tex "SpherePacking.scale_finiteDensity" (slot := "proof")
\begin{proof}\leanok
  The proof follows by direct computation:
  \[
    \Delta_{\Pa(cX)}(cR) = \frac{\Vol{\Pa(cX) \cap B_d(0, cR)}}{\Vol{B_d(0, cR)}} = \frac{c^d \cdot \Vol{\Pa(X) \cap B_d(0, R)}}{c^d \cdot \Vol{B_d(0, R)}}
    % = \frac{\Vol{\Pa(X) \cap B_d(0, R)}}{\Vol{B_d(0, R)}}
    = \Delta_{\Pa(X)}(R)
  \]
  where the second equality follows from applying the fact that scaling a (measurable) set by a factor of $c$ scales its volume by a factor of $c^d$ to the fact that $\Pa(cX) \cap B_d(0, cR) = c \cdot (\Pa(X) \cap B_d(0, cR))$.
\end{proof}
```

:::lemma_ "SpherePacking.scale_density" (lean := "SpherePacking.scale_density") (parent := "sphere_scaling")
Let $`\Pa(X)` be a sphere packing and $`c` a positive real number. Then the
density of the scaled packing $`\Pa(cX)` is equal to the density of the
original packing $`\Pa(X)`.
{uses "SpherePacking.scale"}[]
:::

```tex "SpherePacking.scale_density"
\begin{lemma}\label{SpherePacking.scale_density}\lean{SpherePacking.scale_density}\uses{SpherePacking.scale}\leanok
  Let $\Pa(X)$ be a sphere packing and $c$ a positive real number. Then, the density of the scaled packing $\Pa(cX)$ is equal to the density of the original packing $\Pa(X)$.
\end{lemma}
```

:::proof "SpherePacking.scale_density"
One can show, using relatively unsophisticated real analysis, that
$$`\limsup_{R \to \infty} \Delta_{\Pa(cX)}(R) = \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR).`
Lemma {uses "SpherePacking.scale_finiteDensity"}[] tells us that
$`\Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R)` for every $`R > 0`. Therefore,
$$`\limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR) = \limsup_{cR \to \infty} \Delta_{\Pa(X)}(R) = \limsup_{R \to \infty} \Delta_{\Pa(X)}(R),`
where the second equality is the result of a similar change of variables.
:::

```tex "SpherePacking.scale_density" (slot := "proof")
\begin{proof}\uses{SpherePacking.scale_finiteDensity}\leanok
  One can show, using relatively unsophisticated real analysis, that
  \[
    \limsup_{R \to \infty} \Delta_{\Pa(cX)}(R) = \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR)
  \]
  Lemma~\ref{SpherePacking.scale_finiteDensity} tells us that $\Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R)$ for every $R > 0$. Therefore,
  \[
    \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR) = \limsup_{cR \to \infty} \Delta_{\Pa(X)}(R) = \limsup_{R \to \infty} \Delta_{\Pa(X)}(R)
  \]
  where the second equality is the result of a similar change of variables to the one done above.
\end{proof}
```

Therefore, as expected, we do not need to worry about the separation radius
when constructing sphere packings. This will be useful when we attempt to
construct the optimal sphere packing in $`\R^8`, and even more so when
attempting to formalise this construction, because the underlying structure of
the packing is given by the $`E_8` lattice, which has separation radius
$`\sqrt{2}`.

```tex
Therefore, as expected, we do not need to worry about the separation radius when constructing sphere packings. This will be useful when we attempt to construct the optimal sphere packing in $\R^8$---and even more so when attempting to \emph{formalise} this construction---because the underlying structure of the packing is given by a set known as the $E_8$ lattice, which has separation radius $\sqrt{2}$.
```

We can also use the lemma `SpherePacking.scale_density` to simplify the
computation of the sphere packing constant by taking the supremum not over all
sphere packings but only over those with separation radius $`1`.

```tex
We can also use Lemma~\ref{SpherePacking.scale_density} to simplify the computation of the sphere packing constant by taking the supremum not over \emph{all} sphere packings but only over those with density $1$.
```

:::lemma_ "SpherePacking.constant_eq_constant_normalized" (lean := "SpherePacking.constant_eq_constant_normalized") (parent := "sphere_scaling")
$$`\Delta_d = \sup\limits_{\substack{\Pa \subset \R^d \\ \text{sphere packing} \\ \text{sep.~rad.} = 1}} \Delta_{\Pa}`
{uses "SpherePackingConstant"}[]{uses "SpherePacking.density"}[]
:::

```tex "SpherePacking.constant_eq_constant_normalized"
\begin{lemma}\label{SpherePacking.constant_eq_constant_normalized}\lean{SpherePacking.constant_eq_constant_normalized}\uses{SpherePackingConstant, SpherePacking.density}\leanok
  \[
    \Delta_d = \sup\limits_{\substack{\Pa \subset \R^d \\ \text{sphere packing} \\ \text{sep.~rad.} = 1}} \Delta_{\Pa}
  \]
\end{lemma}
```

:::proof "SpherePacking.constant_eq_constant_normalized"
That the supremum over packings of unit density is at most the sphere packing
constant is obvious. For the reverse inequality, let $`\Pa(X)` be any sphere
packing with separation radius $`r`. By
{uses "SpherePacking.scale_density"}[], the density of $`\Pa(X)` is equal to
that of the scaled packing $`\Pa\!\left(\frac{X}{r}\right)`. Since the scaled
packing has separation radius $`1`, its density is at most the supremum over
all packings of unit density, and therefore the same is true of $`\Pa(X)`.
:::

```tex "SpherePacking.constant_eq_constant_normalized" (slot := "proof")
\begin{proof}\uses{SpherePacking.scale_density}\leanok
  That the supremum over packings of unit density is at most the sphere packing constant is obvious. For the reverse inequality, let $\Pa(X)$ be any sphere packing with separation radius $r$. We know, from Lemma~\ref{SpherePacking.scale_density}, that the density of $\Pa(X)$ is equal to that of the scaled packing $\Pa\!\left(\frac{X}{r}\right)$. Since the scaled packing has separation radius $1$, its density is naturally at most the supremum over all packings of unit density, meaning that the same is true of $\Pa(X)$.
\end{proof}
```

We begin by defining what a lattice is in Euclidean space.

```tex
We begin by defining what a lattice is in Euclidean space.
```

:::definition "IsZLattice" (parent := "periodic_packings")
We say that an additive subgroup $`\Lambda \le \R^d` is a lattice if it is
discrete and its $`\R`-span contains all the elements of $`\R^d`.
:::

```tex "IsZLattice"
\begin{definition}\label{IsZLattice}\lean{IsZLattice}\leanok
  We say that an additive subgroup $\Lambda \leq \R^d$ is a \emph{lattice} if it is discrete and its $\R$-span contains all the elements of $\R^d$.
\end{definition}
```

There is also a corresponding dual notion, which becomes relevant when we
start doing Fourier analysis on functions over lattices.

```tex
There is also a corresponding dual notion, which will become relevant when we start doing Fourier analysis on functions over lattices.
```

:::definition "def:dual-lattice" (lean := "LinearMap.BilinForm.dualSubmodule") (parent := "periodic_packings")
The dual lattice of a lattice $`\Lambda` is the set
$$`\Lambda^* := \setof{v \in \R^d}{\forall l \in \Lambda, \left\langle v,l \right\rangle \in \Z}.`
:::

```tex "def:dual-lattice"
\begin{definition}\label{def:dual-lattice}\lean{LinearMap.BilinForm.dualSubmodule}\leanok
  The \emph{dual lattice} of a lattice $\Lambda$ is the set
  \[ \Lambda^* := \setof{v \in \R^d}{\forall l \in \Lambda, \left\langle v,l \right\rangle \in \Z} \]
\end{definition}
```

We can now define periodic sphere packings.

```tex
We can now define periodic sphere packings.
```

:::definition "PeriodicSpherePacking" (parent := "periodic_packings")
We say that a sphere packing $`\Pa(X)` is $`\Lambda`-periodic if there exists
a lattice $`\Lambda \subset \R^d` such that for all $`x \in X` and
$`y \in \Lambda`, we have $`x+y \in X`.
{uses "SpherePacking"}[]{uses "IsZLattice"}[]
:::

```tex "PeriodicSpherePacking"
\begin{definition}\label{PeriodicSpherePacking}\lean{PeriodicSpherePacking}\uses{SpherePacking, IsZLattice}\leanok
  We say that a sphere packing $\Pa(X)$ is ($\Lambda$-)\emph{periodic} if there exists a lattice $\Lambda \subset \R^d$ such that for all $x \in X$ and $y \in \Lambda$, $x + y \in X$ (ie, $X$ is $\Lambda$-periodic).
\end{definition}
```

There is a natural definition of density for periodic sphere packings, namely
the local density of balls in a fundamental domain. However, a priori, the
density of a sphere packing need not coincide with this alternative
definition. In the periodic-density theorem below, we will prove that it does.

```tex
There is a natural definition of density for periodic sphere packings, namely the ``local'' density of balls in a fundamental domain. However, \textit{a priori} the density of sphere packing above need not to coincide with this alternative definition. In \cref{theorem:psp-density}, we will prove that this is the case.
```

Now that we have simplified the process of computing the packing densities of
specific packings, we can simplify the computation of the sphere packing
constant. It turns out that once again, periodicity is key.

```tex
Now that we have simplified the process of computing the packing densities of specific packings, we can simplify that of computing the sphere packing constant. It turns out that once again, periodicity is key.
```

:::definition "def:Periodic-sphere-packing-constant" (lean := "PeriodicSpherePackingConstant") (parent := "periodic_packings")
The periodic sphere packing constant is defined to be
$$`\Delta_{d}^{\text{periodic}} := \sup_{\substack{P \subset \R^d \\ \text{periodic packing}}} \Delta_P.`
{uses "SpherePacking.density"}[]{uses "PeriodicSpherePacking"}[]
:::

```tex "def:Periodic-sphere-packing-constant"
\begin{definition}\label{def:Periodic-sphere-packing-constant}\uses{SpherePacking.density, PeriodicSpherePacking}\lean{PeriodicSpherePackingConstant}\leanok
    The periodic sphere packing constant is defined to be
    $$ \Delta_{d}^{\text{periodic}} := \sup_{\substack{P \subset \R^d \\ \text{periodic packing}}} \Delta_P$$
\end{definition}
```

:::theorem "thm:periodic-packing-optimal" (lean := "periodic_constant_eq_constant") (parent := "periodic_packings")
For all $`d`, the periodic sphere packing constant in $`\R^d` is equal to
the sphere packing constant in $`\R^d`.
{uses "SpherePacking.density"}[]{uses "def:Periodic-sphere-packing-constant"}[]
:::

```tex "thm:periodic-packing-optimal"
\begin{theorem}\label{thm:periodic-packing-optimal}\uses{SpherePacking.density, def:Periodic-sphere-packing-constant}\lean{periodic_constant_eq_constant}\leanok
    For all $d$, the periodic sphere packing constant in $\R^d$ is equal to the sphere packing constant in $\R^d$.
\end{theorem}
```

:::proof "thm:periodic-packing-optimal"
State this in Lean (ready).
/- source paragraph break -/
Fill in proof here (see {citet ElkiesCohn}[], Appendix A).
:::

```tex "thm:periodic-packing-optimal" (slot := "proof")
\begin{proof}
  \todo{State this in Lean (ready).}
  \todo{Fill in proof here (see~\cite[Appendix A]{ElkiesCohn})}
\end{proof}
```

Thus, one can show a sphere packing to be optimal by showing its density to be
equal to the periodic sphere packing constant instead of the regular sphere
packing constant. Determining the periodic constant is easier than determining
the general constant, as we shall see when investigating the linear
programming bounds derived by Cohn and Elkies in {citet ElkiesCohn}[].

```tex
Thus, one can show a sphere packing to be optimal by showing its density to be equal to the \emph{periodic} sphere packing constant instead of the regular sphere packing constant. The determination of the periodic constant is easier than that of the general constant, as we shall see when investigating the Linear Programming bounds derived by Cohn and Elkies in~\cite{ElkiesCohn}.
```

With the terminologies above, we can state the main theorem of this project.

```tex
With the terminologies above, we can state the main theorem of this project.
```

:::theorem "theorem:CE_Main" (parent := "sphere_main_statement")
All periodic packings $`\mathcal{P} \subseteq \R^8` have density satisfying
$`\Delta_{\mathcal{P}} \leq \Delta_{E_8} = \frac{\pi^4}{384}`, the density of
the $`E_8` sphere packing.
{uses "E8-Lattice"}[]{uses "SpherePackingConstant"}[]{uses "SpherePacking.density"}[]{uses "E8Packing-density"}[]{uses "thm:g"}[]{uses "thm:Cohn-Elkies-general"}[]
:::

```tex "theorem:CE_Main"
\begin{theorem}\label{theorem:CE_Main}\uses{E8-Lattice,SpherePackingConstant,SpherePacking.density,E8Packing-density,thm:g,thm:Cohn-Elkies-general}
  All \emph{periodic} packing $\mathcal{P} \subseteq \R^8$ has density satisfying $\Delta_{\mathcal{P}} \leq \Delta_{E_8} = \frac{\pi^4}{384}$, the density of the $E_8$ sphere packing (see \cref{E8Packing}).
\end{theorem}
```

:::proof "theorem:CE_Main"
Directly follows from {uses "thm:Cohn-Elkies-general"}[] applied to the
function $`f(x)=g(x/\sqrt{2})` of {uses "thm:g"}[].
:::

```tex "theorem:CE_Main" (slot := "proof")
\begin{proof}
  Directly follows from \Cref{thm:Cohn-Elkies-general} applied to the function $f(x)=g(x/\sqrt{2})$ of \Cref{thm:g}.
  % TODO: Add a \ref to the actual proof at the end of this blueprint, I guess.
\end{proof}
```

:::corollary "corollary:upper-bound-E8" (parent := "sphere_main_statement")
All packings $`\mathcal{P} \subseteq \R^8` have density satisfying
$`\Delta_{\mathcal{P}} \leq \Delta_{E_8}`.
{uses "thm:periodic-packing-optimal"}[]{uses "theorem:CE_Main"}[]
:::

```tex "corollary:upper-bound-E8"
\begin{corollary}\label{corollary:upper-bound-E8}\uses{thm:periodic-packing-optimal, theorem:CE_Main}
  All packing $\mathcal{P} \subseteq \R^8$ has density satisfying $\Delta_{\mathcal{P}} \leq \Delta_{E_8}$.
\end{corollary}
```

:::proof "corollary:upper-bound-E8"
This is a direct consequence of Theorem
{uses "thm:periodic-packing-optimal"}[] and Theorem
{uses "theorem:CE_Main"}[].
:::

```tex "corollary:upper-bound-E8" (slot := "proof")
\begin{proof}
  This is a direct consequence of Theorem \cref{thm:periodic-packing-optimal} and \cref{theorem:CE_Main}.
\end{proof}
```

:::corollary "MainTheorem" (lean := "SpherePacking.MainTheorem") (parent := "sphere_main_statement")
$`\Delta_8 = \Delta_{E_8}`.
{uses "corollary:upper-bound-E8"}[]
:::

```tex "MainTheorem"
\begin{corollary}\label{MainTheorem}\uses{corollary:upper-bound-E8}\lean{SpherePacking.MainTheorem}
  $\Delta_8 = \Delta_{E_8}$.
\end{corollary}
```

:::proof "MainTheorem"
By definition, $`\Delta_{E_8} \leq \Delta_8`, while
{uses "corollary:upper-bound-E8"}[] shows that
$`\Delta_8 = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}`, and
the result follows.
:::

```tex "MainTheorem" (slot := "proof")
\begin{proof}
  By definition, $\Delta_{E_8} \leq \Delta_8$, while \cref{corollary:upper-bound-E8} shows $\Delta_8 = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}$, and the result follows.
\end{proof}
```
