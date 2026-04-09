import Verso
import VersoManual
import VersoBlueprint
import SpherePackingBlueprint.ToolchainWorkarounds
import SpherePackingBlueprint.Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option pp.rawOnError true
set_option linter.style.longLine false


#doc (Manual) "Cohn-Elkies Bounds" =>


:::group "ce_periodic"
Linear programming bound for periodic sphere packings.
:::

:::group "ce_general"
Passage from periodic to general packings.
:::

:::group "ce_optimal_function"
Existence of the optimal normalized auxiliary function in dimension eight.
:::

In 2003 Cohn and Elkies developed linear programming bounds that apply
directly to sphere packings; see {citet ElkiesCohn}[]. The goal of this
section is to formalize the Cohn-Elkies linear programming bound.

```tex
In 2003 Cohn and Elkies \cite{ElkiesCohn}  developed  linear programming bounds that apply directly to sphere packings. The goal of this section is to formalize the Cohn--Elkies linear programming bound.
```

The following theorem is the key result of {citet ElkiesCohn}[]. The original
theorem is stated for a class of functions more general than Schwartz
functions.

```tex
The following theorem is the key result of \cite{ElkiesCohn}. (Note that the original theorem is stated for a class of functions more general then Schwartz functions.)
```

:::theorem "thm:Cohn-Elkies-periodic" (lean := "LinearProgrammingBound'") (parent := "ce_periodic")
Let $`X\subset\mathbb{R}^d`$ be a discrete subset such that
$`\|x-y\|\geq 1`$ for any distinct $`x,y\in X`$. Suppose that $`X`$ is
$`\Lambda`$-periodic with respect to some lattice
$`\Lambda\subset\mathbb{R}^d`$. Let $`f:\R^d\to\R`$ be a Schwartz function
that is not identically zero and satisfies
$`f(x)\leq 0`$ for $`\|x\|\geq 1`$ and
$`\widehat{f}(x)\geq0`$ for all $`x\in\R^d`$.
Then the density of any $`\Lambda`$-periodic sphere packing is bounded above by
$$`\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
This uses {uses "def:Fourier-Transform"}[] and
{uses "SpherePacking.density"}[].
:::

```tex "thm:Cohn-Elkies-periodic"
\begin{theorem}[Cohn--Elkies {\cite{ElkiesCohn}}]\label{thm:Cohn-Elkies-periodic}\uses{def:Fourier-Transform, SpherePacking.density}\lean{LinearProgrammingBound'}\leanok

Let $X\subset\mathbb{R}^d$ be a discrete subset such that $\|x-y\|\geq 1$ for any distinct $x,y\in X$. Suppose that $X$ is $\Lambda$-periodic with respect to some lattice $\Lambda\subset\mathbb{R}^d$. Let $f:\R^d\to\R$ be a Schwartz function that is not identically zero and satisfies the following conditions:
\begin{equation}\label{eqn:Cohn-Elkies-condition-1}f(x)\leq 0\mbox{ for } \|x\|\geq 1\end{equation} and
\begin{equation}\label{eqn:Cohn-Elkies-condition-2}\widehat{f}(x)\geq0\mbox{ for all } x\in\R^d.\end{equation}
  Then the density of any $\Lambda$-periodic sphere packing is bounded above by $$\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).$$
\end{theorem}
```

:::proof "thm:Cohn-Elkies-periodic"
Here we reproduce the proof given in {citet ElkiesCohn}[] and use
{uses "thm:Poisson-summation-formula"}[].

The inequality
$$`\sharp (X/\Lambda)\cdot f(0)\geq \sum_{x\in X}\sum_{y\in X/\Lambda}f(x-y)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)`
follows from the condition $`f(x)\le 0`$ for $`\|x\|\ge 1`$ and the
assumption on the distances between points in $`X`$.

The equality
$$`\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}`
follows from the Poisson summation formula.

The right-hand side can be written as
$$`\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}=\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2.`
Note that $`\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2\geq0`$ for all
$`m\in\Lambda^*`$, and that the term corresponding to $`m=0`$ satisfies
$`\big|\sum_{x\in X/\Lambda}e^{2\pi i 0 x}\big|^2=\sharp (X/\Lambda)^2`$.

Now we use the condition $`\widehat{f}(x)\ge 0`$ and estimate
$$`\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m(x-y)}\big|^2
\geq \frac{\sharp (X/\Lambda)^2}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot \widehat{f}(0).`
Comparing the two inequalities, we arrive at
$$`\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\leq \frac{f(0)}{\widehat{f}(0)}.`
Now the density of the periodic packing $`\mathcal{P}_X`$ with balls of
radius $`1/2`$ is bounded by
$$`\Delta(\mathcal{P}_X)=\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot{\mathrm{vol}(B_d(0,1/2))}\leq
\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
This finishes the proof of the theorem for periodic packings.
:::

```tex "thm:Cohn-Elkies-periodic" (slot := "proof")
\begin{proof}\uses{thm:Poisson-summation-formula}\leanok
Here we reproduce the proof given in \cite{ElkiesCohn}.

The inequality
\begin{equation}
\sharp (X/\Lambda)\cdot f(0)\geq \sum_{x\in X}\sum_{y\in X/\Lambda}f(x-y)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)\end{equation}
follows from the condition \eqref{eqn:Cohn-Elkies-condition-1} of the theorem and the assumption on the distances between points in $X$.
The equality
$$\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}.$$
follows from the Poisson summation formula.
The right hand side of the above equation can be written as
$$\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}=\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2.$$
Note that $\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2\geq0$ for all $m\in\Lambda^*$. Moreover,  the term corresponding to $m=0$ satisfies $\big|\sum_{x\in X/\Lambda}e^{2\pi i 0 x}\big|^2=\sharp (X/\Lambda)^2$.
Now we use the condition \eqref{eqn:Cohn-Elkies-condition-2} and estimate
\begin{equation}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m(x-y)}\big|^2
\geq \frac{\sharp (X/\Lambda)^2}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot \widehat{f}(0).
\end{equation}
Comparing inequalities \eqref{eqn: sharp X 1} and \eqref{eqn: sharp X 2} we arrive at
$$\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\leq \frac{f(0)}{\widehat{f}(0)}.$$
Now we see that the density of the periodic packing $\mathcal{P}_X$ with balls of radius $1/2$ is bounded by
$$\Delta(\mathcal{P}_X)=\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot{\mathrm{vol}(B_d(0,1/2))}\leq
\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).$$
This finishes the proof of the theorem for periodic packings.
\end{proof}
```

:::theorem "thm:Cohn-Elkies-general" (lean := "LinearProgrammingBound") (parent := "ce_general")
Let $`f:\R^d\to\R`$ be a Schwartz function that is not identically zero and
satisfies the two Cohn-Elkies sign conditions above. Then the density of any
$`\Lambda`$-periodic sphere packing is bounded above by
$$`\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
:::

```tex "thm:Cohn-Elkies-general"
\begin{theorem}[Cohn--Elkies {\cite{ElkiesCohn}}]\label{thm:Cohn-Elkies-general}\lean{LinearProgrammingBound}\leanok
  Let $f:\R^d\to\R$ be a Schwartz function that is not identically zero and satisfies \eqref{eqn:Cohn-Elkies-condition-1} and \eqref{eqn:Cohn-Elkies-condition-2}. Then the density of any $\Lambda$-periodic sphere packing is bounded above by $$\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).$$
\end{theorem}
```

:::proof "thm:Cohn-Elkies-general"
The result follows immediately from Theorem
{uses "thm:periodic-packing-optimal"}[] and
{uses "thm:Cohn-Elkies-periodic"}[].
:::

```tex "thm:Cohn-Elkies-general" (slot := "proof")
\begin{proof}\uses{thm:Cohn-Elkies-periodic,thm:periodic-packing-optimal}\leanok
  The result follows immediately from Theorem~\ref{thm:periodic-packing-optimal} and \Cref{thm:Cohn-Elkies-periodic}.
\end{proof}
```

The main step in our proof of the main theorem is the explicit
construction of an optimal function. It will be convenient for us to scale this
function by $`\sqrt{2}`$.

```tex
The main step in our proof of \cref{MainTheorem} is the explicit construction of an optimal function. It will be convenient for us to scale this function by $\sqrt{2}$.
```

:::theorem "thm:g" (parent := "ce_optimal_function")
There exists a radial Schwartz function $`g:\R^8\to\R`$ which satisfies:
$$`g(x)\leq 0\mbox{ for } \|x\|\geq \sqrt{2}`
$$`\widehat{g}(x)\geq0\mbox{ for all } x\in\R^8`
$$`g(0)=\widehat{g}(0)=1.`
This uses {uses "thm:g1"}[].
:::

```tex "thm:g"
\begin{theorem}\label{thm:g}\uses{thm:g1}
There exists a radial Schwartz function $g:\R^8\to\R$ which satisfies:
\begin{align}
g(x)&\leq 0\mbox{ for } \|x\|\geq \sqrt{2} \label{eqn:g1}\\
\widehat{g}(x)&\geq0\mbox{ for all } x\in\R^8\label{eqn:g2}\\
g(0)&=\widehat{g}(0)=1.\label{eqn:g3}
\end{align}
\end{theorem}
```

The Cohn-Elkies theorem applied to the optimal function
$`f(x)=g(x/\sqrt{2})`$ immediately implies the main theorem.

```tex
Theorem \ref{thm:Cohn-Elkies-general} applied to the optimal function $f(x)=g(x/\sqrt{2})$ immediately implies \cref{MainTheorem}.
```
