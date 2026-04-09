import Verso
import VersoManual
import VersoBlueprint
import SpherePackingBlueprint.ToolchainWorkarounds

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option pp.rawOnError true
set_option linter.style.longLine false


#doc (Manual) "Density of Packings" =>


:::group "density_finite_bounds"
Bounds comparing finite density with local center counts.
:::

:::group "density_periodic_counts"
Volume-count asymptotics for lattice and periodic center sets.
:::

:::group "density_formula"
Closed formula for density of periodic sphere packings.
:::

The definition of density given in the sphere-packings section is
inconvenient to work with, especially when our packing is a structured one,
such as a periodic or lattice packing. This section fixes this problem.

```tex
The definition of density given in \cref{sec:sphere-packings} is inconvenient to work with, especially when our packing is a structured one, such as a periodic/lattice packing. This section fixes this problem.
```

Note that some of the proofs in this section have only been sketched. The
finer details are formalised in Lean.

```tex
Note that some of the proofs in this section have only been sketched. The finer details are formalised in Lean.
```

Observe that the finite density evaluated at some $`R > 0`$ measures the
density of sphere packings within a bounded open ball of radius $`R`$. As one
might expect, there is a relationship between the finite density and the
number of centers in the ball of radius $`R`$.

```tex
Observe that the finite density evaluated at some $R > 0$ measures the density of sphere packings within a bounded, open ball of radius $R$. As one might expect, there is a relationship between the finite density and the number of centers in the ball of radius $R$.
```

:::lemma_ "lemma:sp-finite-density-bound" (lean := "SpherePacking.finiteDensity_le,SpherePacking.finiteDensity_ge") (parent := "density_finite_bounds")
For any $`R > 0`$,
$$`\left|X \cap \mathcal{B}_d\left(R - \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
    \leq \Delta_{\mathcal{P}}(R)
    \leq \left|X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}.`
This is the basic estimate for {uses "SpherePacking.finiteDensity"}[].
:::

```tex "lemma:sp-finite-density-bound"
\begin{lemma}\label{lemma:sp-finite-density-bound}\lean{SpherePacking.finiteDensity_le,SpherePacking.finiteDensity_ge}\uses{SpherePacking.finiteDensity}\leanok
  For any $R > 0$,
  \[
    \left|X \cap \mathcal{B}_d\left(R - \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
    \leq \Delta_{\mathcal{P}}(R)
    \leq \left|X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}
  \]
\end{lemma}
```

:::proof "lemma:sp-finite-density-bound"
The high-level idea is to prove that
$`\mathcal{P} \cap \mathcal{B}_d(R) = \left(\bigcup_{x \in X} \mathcal{B}_d\left(x, \frac{r}{2}\right)\right) \subseteq \bigcup_{x \in X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)} \mathcal{B}_d\left(x, \frac{r}{2}\right),`$
and a similar inequality for the lower bound. The rest follows by rearranging
and using the fact that the balls are pairwise disjoint in
{uses "SpherePacking"}[].
:::

```tex "lemma:sp-finite-density-bound" (slot := "proof")
\begin{proof}\uses{SpherePacking}\leanok
  The high level idea is to prove that $\mathcal{P} \cap \mathcal{B}_d(R) = \left(\bigcup_{x \in X} \mathcal{B}_d\left(x, \frac{r}{2}\right)\right) \subseteq \bigcup_{x \in X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)} \mathcal{B}_d\left(x, \frac{r}{2}\right)$, and a similar inequality for the upper bound. The rest follows by rearranging and using the fact that the balls are pairwise disjoint.
\end{proof}
```

Suppose further that $`X`$ is a periodic packing with respect to the lattice
$`\Lambda \subseteq \R^d`$. Let $`\mathcal{D}`$ be a bounded fundamental region
of $`\Lambda`$, say the parallelopiped $`[0,1]^n\Lambda`$, and let $`L`$ be a
bound on the norm of vectors in $`\mathcal{D}`$, that is, a number satisfying
$`\forall x \in \mathcal{D}, \|x\| \leq L`$.

```tex
Suppose further that $X$ is a periodic packing w.r.t. the lattice $\Lambda \subseteq \R^d$. Let $\mathcal{D}$ be a (bounded) fundamental region of $\Lambda$, say the parallelopiped $[0, 1]^n\Lambda$, and let $L$ be the bound on the norm of vectors in $\mathcal{D}$, i.e. a number satisfying $\forall x \in \mathcal{D}, \|x\| \leq L$.
```

:::lemma_ "lemma:lattice-points-bound" (lean := "PeriodicSpherePacking.aux2_ge',PeriodicSpherePacking.aux2_le'") (parent := "density_periodic_counts")
For all $`R`$, we have the following inequality relating the number of lattice
points from $`\Lambda`$ in a ball with the volume of the ball and the
fundamental region $`\mathcal{D}`$:
$$`\frac{\mathrm{Vol}(\mathcal{B}_d(R - L))}{\mathrm{Vol}(\mathcal{D})}
    \leq \left|\Lambda \cap \mathcal{B}_d(R)\right|
    \leq \frac{\mathrm{Vol}(\mathcal{B}_d(R + L))}{\mathrm{Vol}(\mathcal{D})}.`
:::

```tex "lemma:lattice-points-bound"
\begin{lemma}\label{lemma:lattice-points-bound}\lean{PeriodicSpherePacking.aux2_ge',PeriodicSpherePacking.aux2_le'}\leanok
  For all $R$, we have the following inequality relating the number of lattice points from $\Lambda$ in a ball with the volume of the ball and the fundamental region $\mathcal{D}$:

  \[
    \frac{\mathrm{Vol}(\mathcal{B}_d(R - L))}{\mathrm{Vol}(\mathcal{D})}
    \leq \left|\Lambda \cap \mathcal{B}_d(R)\right|
    \leq \frac{\mathrm{Vol}(\mathcal{B}_d(R + L))}{\mathrm{Vol}(\mathcal{D})}
  \]
\end{lemma}
```

:::proof "lemma:lattice-points-bound"
For the first inequality, it suffices to prove that
$`\mathcal{B}_d(R - L) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D}),`$
since the cosets on the right are disjoint. For a vector
$`v \in \mathcal{B}_d(R - L)`$, we have $`\|v\| < R - L`$ by definition.
Since $`\mathcal{D}`$ is a fundamental domain, there exists a lattice point
$`x \in \Lambda`$ such that $`v \in x + \mathcal{D}`$. Rearranging gives
$`v - x \in \mathcal{D}`$, which means $`\|v - x\| \leq L`$. By the triangle
inequality, $`\|x\| < R`$, so $`x \in \mathcal{B}_d(R)`$.

For the second inequality, we prove that
$`\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R + L)`$.
Consider a vector $`x \in \Lambda \cap \mathcal{B}_d(R)`$ and a vector
$`y \in x + \mathcal{D}`$. Then $`\|x\| < R`$ and $`\|y - x\| \leq L`$, so
$`\|y\| < R + L`$, concluding the proof.
:::

```tex "lemma:lattice-points-bound" (slot := "proof")
\begin{proof}\leanok
For the first inequality, it suffices to prove that $\mathcal{B}_d(R - L) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D})$, since the cosets on the right are disjoint. For a vector $v \in \mathcal{B}_d(R - L)$, we have $\|v\| < R - L$ by definition. Since $\mathcal{D}$ is a fundamental domain, there exists a lattice point $x \in \Lambda$ such that $v \in x + \mathcal{D}$. Rearranging gives $v - x \in \mathcal{D}$, which means $\|v - x\| \leq L$. By the triangle inequality, $\|x\| < R$, i.e. $x \in \mathcal{B}_d(L)$, concluding the proof.

For the second inequality, we prove that $\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R + L)$. Consider a vector $x \in \Lambda \cap \mathcal{B}_d(R)$ and a vector $y \in x + \mathcal{D}$. From above, we know $\|x\| < R$ and $\|y - x\| \leq L$, so $\|y\| < R + L$, concluding the proof.
\end{proof}
```

To link the lemmas `lemma:sp-finite-density-bound` and
`lemma:lattice-points-bound`, we need a lemma relating
$`|\Lambda \cap \mathcal{B}|`$ with $`|X \cap \mathcal{B}|`$, which is what
the following lemma does.

```tex
To link \cref{lemma:sp-finite-density-bound} and \cref{lemma:lattice-points-bound}, we need a lemma relating $|\Lambda \cap \mathcal{B}|$ with $|X \cap \mathcal{B}|$, which is what the following lemma does:
```

:::lemma_ "lemma:periodic-points-bounds" (lean := "PeriodicSpherePacking.aux_ge,PeriodicSpherePacking.aux_le") (parent := "density_periodic_counts")
For all $`R`$, we have the following inequality relating the number of points
from $`X`$ periodic with respect to $`\Lambda`$ in a ball with the number of
points from $`\Lambda`$:
$$`\left|\Lambda \cap \mathcal{B}_d(R - L)\right|\left|X / \Lambda\right|
    \leq \left|X \cap \mathcal{B}_d(R)\right|
    \leq \left|\Lambda \cap \mathcal{B}_d(R + L)\right|\left|X / \Lambda\right|.`
:::

```tex "lemma:periodic-points-bounds"
\begin{lemma}\label{lemma:periodic-points-bounds}\lean{PeriodicSpherePacking.aux_ge,PeriodicSpherePacking.aux_le}\leanok
  For all $R$, we have the following inequality relating the number of points from $X$ (periodic w.r.t. $\Lambda$) in a ball with the number of points from $\Lambda$:
  \[
    \left|\Lambda \cap \mathcal{B}_d(R - L)\right|\left|X / \Lambda\right|
    \leq \left|X \cap \mathcal{B}_d(R)\right|
    \leq \left|\Lambda \cap \mathcal{B}_d(R + L)\right|\left|X / \Lambda\right|
  \]
\end{lemma}
```

:::proof "lemma:periodic-points-bounds"
For the first inequality, we notice that
$`\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R)`$,
because for $`x \in \Lambda \cap \mathcal{B}_d(R - L)`$ and
$`y \in x + \mathcal{D}`$, we have $`\|x\| < R - L`$ and
$`\|y - x\| \leq L`$, so $`\|y\| < R`$ by the triangle inequality.
Intersecting both sides with $`X`$ and simplifying, we get
$$`\left(\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D})\right) \cap X = \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} ((x + \mathcal{D}) \cap X) \subseteq \mathcal{B}_d(R) \cap X.`
Taking cardinalities and noting that
$`|(x + \mathcal{D}) \cap X| = |X / \Lambda|`$ for all $`x`$, we obtain
$`|\Lambda \cap \mathcal{B}_d(R - L)||X / \Lambda| \leq |X \cap \mathcal{B}_d(R)|`$.

The proof of the second inequality is similar. We again observe that
$`\mathcal{B}_d(R) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R + L)} (x + \mathcal{D}),`$
which follows from the tiling property of a fundamental domain. Intersecting
both sides with $`X`$ and taking cardinalities concludes the proof.

There are several technicalities when formalising in Lean, such as having to
prove that $`|\Lambda \cap \mathcal{B}_d(R)|`$ is countable and finite. Those
are handled in `aux3`.
:::

```tex "lemma:periodic-points-bounds" (slot := "proof")
\begin{proof}\leanok
  For the first inequality, we notice that $\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R)$, because for $x \in \Lambda \cap \mathcal{B}_d(R - L)$ and $y \in x + \mathcal{D}$, we have $\|x\| < R - L$ and $\|y - x\| \leq L$, so $\|y\| < R$ by triangle inequality. Intersecting both sides with $X$ and simplifying, we have

  \[
    \left(\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D})\right) \cap X = \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} ((x + \mathcal{D}) \cap X) \subseteq \mathcal{B}_d(R) \cap X
  \]

  Consider the (finite) cardinality on both sides and noting that $|(x + \mathcal{D}) \cap X| = |X / \Lambda|$ for all $x$, we see that $|\Lambda \cap \mathcal{B}_d(R - L)||X / \Lambda| \leq |X \cap \mathcal{B}_d(R)|$, as desired.

  The proof of the second inequality is similar. We again observe that $\mathcal{B}_d(R) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R + L)} (x + \mathcal{D})$, which follows from the tiling property of fundamental domain (i.e. every point can be translated by a $\Lambda$ lattice point into $\mathcal{D}$). Intersecting both sides with $X$ and considering cardinality of both sides concludes the proof.

  There are several technicalities when formalising in Lean, such as having to prove $|\Lambda \cap \mathcal{B}_d(R)|$ is countable and finite. Those are handled at \texttt{aux3}.
\end{proof}
```

When we combine the inequalities above, we need one additional computational
lemma.

```tex
When we combine the inequalities above, we need one additional computational lemma.
```

:::lemma_ "lemma:volume-ball-ratio-limit" (lean := "volume_ball_ratio_tendsto_nhds_one''") (parent := "density_periodic_counts")
For any constant $`C > 0`$, we have
$$`\lim_{R \to \infty} \frac{\mathrm{Vol}(\mathcal{B}_d(R))}{\mathrm{Vol}(\mathcal{B}_d(R + C))} = 1.`
:::

```tex "lemma:volume-ball-ratio-limit"
\begin{lemma}\label{lemma:volume-ball-ratio-limit}\lean{volume_ball_ratio_tendsto_nhds_one''}\leanok
  For any constant $C > 0$, we have

  \[
    \lim_{R \to \infty} \frac{\mathrm{Vol}(\mathcal{B}_d(R))}{\mathrm{Vol}(\mathcal{B}_d(R + C))} = 1
  \]
\end{lemma}
```

:::proof "lemma:volume-ball-ratio-limit"
Write out the formula for the volume of a ball and simplify. More
specifically, we have
$`\mathrm{Vol}(\mathcal{B}_d(R)) = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)`$,
so
$`\mathrm{Vol}(\mathcal{B}_d(R)) / \mathrm{Vol}(\mathcal{B}_d(R + C)) = R^d / (R + C)^d = \left(1 - \frac{1}{R + C}\right)^d`$,
which tends to $`1`$.
:::

```tex "lemma:volume-ball-ratio-limit" (slot := "proof")
\begin{proof}\leanok
  Write out the formula for volume of a ball and simplify. More specifically, we have $\mathrm{Vol}(\mathcal{B}_d(R)) = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)$, so $\mathrm{Vol}(\mathcal{B}_d(R)) / \mathrm{Vol}(\mathcal{B}_d(R + C)) = R^d / (R + C)^d = \left(1 - \frac{1}{R + C}\right)^d = 1$.
\end{proof}
```

Finally, we can relate the density of a periodic sphere packing to the natural
definition of density given by any of its fundamental domains.

```tex
Finally, we can relate the density of a periodic sphere packing to the natural definition of density given by any of its fundamental domain:
```

:::theorem "theorem:psp-density" (lean := "PeriodicSpherePacking.density_eq") (parent := "density_formula")
For a periodic sphere packing $`\mathcal{P} = \mathcal{P}(X)`$ with centers
$`X`$ periodic with respect to the lattice $`\Lambda`$ and separation $`r`$,
$$`\Delta_{\mathcal{P}} = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}.`
This identifies {uses "SpherePacking.density"}[] for periodic packings.
:::

```tex "theorem:psp-density"
\begin{theorem}\label{theorem:psp-density}\uses{SpherePacking.density}\lean{PeriodicSpherePacking.density_eq}\leanok
  For a periodic sphere packing $\mathcal{P} = \mathcal{P}(X)$ with centers $X$ periodic to the lattice $\Lambda$ and separation $r$,

  \[
    \Delta_{\mathcal{P}} = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}
  \]
\end{theorem}
```

:::proof "theorem:psp-density"
Fix any fundamental domain $`\mathcal{D}`$ induced by a basis of the lattice
$`\Lambda`$. Combining {uses "lemma:sp-finite-density-bound"}[],
{uses "lemma:lattice-points-bound"}[], and
{uses "lemma:periodic-points-bounds"}[], we get the following inequality for
the finite density:
$$`|X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R - r / 2 - 2L)}}{\Vol{\mathcal{B}_d(R)}}
    \leq \Delta_{\mathcal{P}}(R)
    \leq |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R + r / 2 + 2L)}}{\Vol{\mathcal{B}_d(R)}}.`
Taking limits on both sides as $`R \to \infty`$ and applying the sandwich
theorem together with {uses "lemma:volume-ball-ratio-limit"}[], we obtain
$$`\Delta_{\mathcal{P}} = \limsup_{R \to \infty} \Delta_{\mathcal{P}}(R) = \lim_{R \to \infty} \Delta_{\mathcal{P}}(R) = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}.`
:::

```tex "theorem:psp-density" (slot := "proof")
\begin{proof}\uses{lemma:sp-finite-density-bound,lemma:lattice-points-bound,lemma:periodic-points-bounds,lemma:volume-ball-ratio-limit}\leanok
  Fix any fundamental domain $\mathcal{D}$ (induced by any basis) of the lattice $\Lambda$. Combining \cref{lemma:sp-finite-density-bound}, \cref{lemma:lattice-points-bound} and \cref{lemma:periodic-points-bounds}, we get the following inequality for the \textit{finite} density:

  \[
    |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R - r / 2 - 2L)}}{\Vol{\mathcal{B}_d(R)}}
    \leq \Delta_{\mathcal{P}}(R)
    \leq |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R + r / 2 + 2L)}}{\Vol{\mathcal{B}_d(R)}}
  \]

  Taking limit on both sides as $R \to \infty$ and apply the Sandwich theorem and \cref{lemma:volume-ball-ratio-limit}, we get

  \[
    \Delta_{\mathcal{P}} = \limsup_{R \to \infty} \Delta_{\mathcal{P}}(R) = \lim_{R \to \infty} \Delta_{\mathcal{P}}(R) = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}
  \]
\end{proof}
```
