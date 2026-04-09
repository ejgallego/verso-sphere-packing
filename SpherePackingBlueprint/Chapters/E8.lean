import Verso
import VersoManual
import VersoBlueprint
import SpherePackingBlueprint.ToolchainWorkarounds

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option pp.rawOnError true


#doc (Manual) "The E8 Lattice" =>


:::group "e8_definitions"
Equivalent models of the E8 lattice.
:::

:::group "e8_properties"
Basic structural and arithmetic properties of E8.
:::

:::group "e8_density"
Definition and density computation of the E8 sphere packing.
:::

There are several equivalent definitions of the $`E_8`$ lattice. Below, we
formalise two of them and prove that they are equivalent.

```tex
\subsection{Definitions of $E_8$ lattice}

There are several equivalent definitions of the $E_8$ lattice. Below, we formalise two of them, and prove they are equivalent.
```

:::definition "E8-Set" (lean := "Submodule.E8") (parent := "e8_definitions")
We define the $`E_8`$ lattice as a subset of $`\R^8`$ by
$$`\Lambda_8=\{(x_i)\in\Z^8\cup(\Z+\textstyle\frac12\displaystyle )^8|\;\sum_{i=1}^8x_i\equiv 0\;(\mathrm{mod\;2})\}.`
:::

```tex "E8-Set"
\begin{definition}{($E_8$-lattice, Definition 1)}\label{E8-Set}\lean{Submodule.E8}\leanok
  We define the \emph{$E_8$-lattice} (as a subset of $\R^8$) to be
$$\Lambda_8=\{(x_i)\in\Z^8\cup(\Z+\textstyle\frac12\displaystyle )^8|\;\sum_{i=1}^8x_i\equiv 0\;(\mathrm{mod\;2})\}.$$
\end{definition}
```

:::definition "E8-Matrix" (lean := "E8Matrix") (parent := "e8_definitions")
We define the $`E_8`$ basis vectors to be the set of vectors
$$`\B_8 =
  \left\{
    \begin{bmatrix}
      1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ 1 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0
    \end{bmatrix}
  \right\}.`
:::

```tex "E8-Matrix"
\begin{definition}{($E_8$-lattice, Definition 2)}\label{E8-Matrix}\lean{E8Matrix}\leanok
  We define the \emph{$E_8$ basis vectors} to be the set of vectors
  \[ \B_8 =
  \left\{
    \begin{bmatrix}
      1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ 1 \\ 0
    \end{bmatrix},
    \begin{bmatrix}
      -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2 \\ -1/2
    \end{bmatrix},
    \begin{bmatrix}
      0 \\ 0 \\ 0 \\ 0 \\ 0 \\ 1 \\ -1 \\ 0
    \end{bmatrix}
  \right\}
  \]
\end{definition}
```

:::theorem "E8-defs-equivalent" (lean := "span_E8Matrix") (parent := "e8_definitions")
The two definitions above coincide, that is,
$`\Lambda_8 = \mathrm{span}_{\Z}(\B_8)`. This compares {uses "E8-Set"}[] and
{uses "E8-Matrix"}[].
:::

```tex "E8-defs-equivalent"
\begin{theorem}\label{E8-defs-equivalent}\lean{span_E8Matrix}\uses{E8-Set, E8-Matrix}\leanok
  The two definitions above coincide, i.e. $\Lambda_8 = \mathrm{span}_{\Z}(\B_8)$.
\end{theorem}
```

:::proof "E8-defs-equivalent"
We prove that each side contains the other.

For a vector $`\vec{v} \in \Lambda_8 \subseteq \R^8`$, we have
$`\sum_i \vec{v}_i \equiv 0 \pmod{2}`$ and all coordinates are either integers
or half-integers. After some modulo arithmetic, it can be seen that
$`\B_8^{-1}\vec{v}`$ has integer coordinates, so
$`\vec{v} \in \mathrm{span}_{\Z}(\B_8)`.

For the opposite direction, write
$`\vec{v} = \sum_i c_i\B_8^i \in \mathrm{span}_{\Z}(\B_8)`$ with the
$`c_i`$ integers and $`\B_8^i`$ the $`i`$-th basis vector. Expanding the
definition gives
$`\vec{v} = \left(c_1 - \frac{1}{2}c_7, -c_1 + c_2 - \frac{1}{2}c_7, \cdots, -\frac{1}{2}c_7\right)`$.
Again, after some modulo arithmetic, it can be seen that
$`\sum_i \vec{v}_i`$ is $`0`$ modulo $`2`$ and that the coordinates are all
either integers or all half-integers.

This proof does not depend on $`\B_8`$ being linearly independent.
:::

```tex "E8-defs-equivalent" (slot := "proof")
\begin{proof}\leanok
  We prove each side contains the other side.

  For a vector $\vec{v} \in \Lambda_8 \subseteq \R^8$, we have $\sum_i \vec{v}_i \equiv 0 \pmod{2}$ and $\vec{v}_i$ being either all integers or all half-integers. After some modulo arithmetic, it can be seen that $\B_8^{-1}\vec{v}$ as integer coordinates (i.e. it is congruent to $0$ modulo $1$). Hence, $\vec{v} \in \mathrm{span}_{\Z}(\B_8)$.

  For the opposite direction, we write the vector as $\vec{v} = \sum_i c_i\B_8^i \in \mathrm{span}_{\Z}(\B_8)$ with $c_i$ being integers and $\B_8^i$ being the $i$-th basis vector. Expanding the definition then gives $\vec{v} = \left(c_1 - \frac{1}{2}c_7, -c_1 + c_2 - \frac{1}{2}c_7, \cdots, -\frac{1}{2}c_7\right)$. Again, after some modulo arithmetic, it can be seen that $\sum_i \vec{v}_i$ is indeed $0$ modulo $2$ and are all either integers and half-integers, concluding the proof.

  (Note: this proof doesn't depend on that $\B_8$ is linearly independent.)
\end{proof}
```

In this section, we establish basic properties of the $`E_8`$ lattice and the
$`\B_8`$ vectors.

```tex
\subsection{Basic Properties of $E_8$ lattice}

In this section, we establish basic properties of the $E_8$ lattice and the $\B_8$ vectors.
```

:::lemma_ "E8-is-basis" (lean := "span_E8Matrix_eq_top") (parent := "e8_properties")
$`\B_8`$ is an $`\R`$-basis of $`\R^8`$. This uses {uses "E8-Matrix"}[].
:::

```tex "E8-is-basis"
\begin{lemma}\label{E8-is-basis}\lean{span_E8Matrix_eq_top}\uses{E8-Matrix}\leanok
  $B_8$ is a $\R$-basis of $\R^8$.
\end{lemma}
```

:::proof "E8-is-basis"
It suffices to prove that $`\B_8 \in \mathrm{GL}_8(\R)`$.
We do this by explicitly defining the inverse matrix $`\B_8^{-1}`$ and
proving $`\B_8 \B_8^{-1} = I_8`$, which implies that $`\det(\B_8)`$ is
nonzero. See the Lean code for more details.
:::

```tex "E8-is-basis" (slot := "proof")
\begin{proof}\leanok
  It suffices to prove that $\B_8 \in \mathrm{GL}_8(\R)$. We prove this by explicitly defining the inverse matrix $\B_8^{-1}$ and proving $\B_8 \B_8^{-1} = I_8$, which implies that $\det(\B_8)$ is nonzero. See the Lean code for more details.,
\end{proof}
```

:::lemma_ "E8-Lattice" (lean := "E8Lattice") (parent := "e8_properties")
$`\Lambda_8`$ is an additive subgroup of $`\R^8`$.
This uses {uses "E8-Set"}[] and {uses "E8-defs-equivalent"}[].
:::

```tex "E8-Lattice"
\begin{lemma}\label{E8-Lattice}\lean{E8Lattice}\uses{E8-Set, E8-defs-equivalent}\leanok
  $\Lambda_8$ is an additive subgroup of $\R^8$.
\end{lemma}
```

:::proof "E8-Lattice"
This follows trivially from the fact that
$`\Lambda_8 \subseteq \R^8`$ is the $`\Z`$-span of $`\B_8`$ and hence an
additive group.
:::

```tex "E8-Lattice" (slot := "proof")
\begin{proof}\leanok
  Trivially follows from that $\Lambda_8 \subseteq \R^8$ is the $\Z$-span of $\B_8$ and hence an additive group.
\end{proof}
```

:::lemma_ "E8-vector-norms" (lean := "E8_norm_eq_sqrt_even") (parent := "e8_properties")
All vectors in $`\Lambda_8`$ have norm of the form $`\sqrt{2n}`$, where
$`n`$ is a nonnegative integer. This uses {uses "E8-defs-equivalent"}[].
:::

```tex "E8-vector-norms"
\begin{lemma}\label{E8-vector-norms}\lean{E8_norm_eq_sqrt_even}\uses{E8-defs-equivalent}\leanok
  All vectors in $\Lambda_8$ have norm of the form $\sqrt{2n}$, where $n$ is a nonnegative integer.
\end{lemma}
```

:::proof "E8-vector-norms"
Writing $`\vec{v} = \sum_i c_i\B_8^i`$, we have
$`\|v\|^2 = \sum_i \sum_j c_ic_j (\B_8^i \cdot \B_8^j)`$.
Computing all $`64`$ pairs of dot products and simplifying gives a large
quadratic form in the $`c_i`$ with even integer coefficients, concluding the
proof.
:::

```tex "E8-vector-norms" (slot := "proof")
\begin{proof}\leanok
  Writing $\vec{v} = \sum_i c_i\B_8^i$, we have $\|v\|^2 = \sum_i \sum_j c_ic_j (\B_8^i \cdot \B_8^j)$. Computing all $64$ pairs of dot products and simplifying, we get a massive term that is a quadratic form in $c_i$ with even integer coefficients, concluding the proof.
\end{proof}
```

:::lemma_ "instDiscreteE8Lattice" (lean := "instDiscreteE8Lattice") (parent := "e8_properties")
$`c\Lambda_8`$ is discrete, that is, the subspace topology induced by its
inclusion into $`\R^8`$ is the discrete topology.
This uses {uses "E8-vector-norms"}[].
:::

```tex "instDiscreteE8Lattice"
\begin{lemma}\label{instDiscreteE8Lattice}\lean{instDiscreteE8Lattice}\uses{E8-vector-norms}\leanok
  $c\Lambda_8$ is discrete, i.e. that the subspace topology induced by its inclusion into $\R^8$ is the discrete topology.
\end{lemma}
```

:::proof "instDiscreteE8Lattice"
Since $`\Lambda_8`$ is a topological group and $`+`$ is continuous, it
suffices to prove that $`\{0\}`$ is open in $`\Lambda_8`$. This follows from
the existence of an open ball $`\B(\sqrt{2}) \subseteq \R^8`$ around zero
containing no other lattice points, since the shortest nonzero vector has norm
$`\sqrt{2}`$.
:::

```tex "instDiscreteE8Lattice" (slot := "proof")
\begin{proof}\leanok
  Since $\Lambda_8$ is a topological group and $+$ is continuous, it suffices to prove that $\{0\}$ is open in $\Lambda_8$. This follows from the fact that there is an open ball $\B(\sqrt{2}) \subseteq \R^8$ around it containing no other lattice points, since the shortest nonzero vector has norm $\sqrt{2}$.
\end{proof}
```

:::lemma_ "instLatticeE8" (lean := "instIsZLatticeE8Lattice") (parent := "e8_properties")
$`c\Lambda_8`$ is a $`\Z`$-lattice, that is, it is discrete and spans
$`\R^8`$ over $`\R`$.
This uses {uses "instDiscreteE8Lattice"}[] and {uses "E8-is-basis"}[].
:::

```tex "instLatticeE8"
\begin{lemma}\label{instLatticeE8}\lean{instIsZLatticeE8Lattice}\uses{instDiscreteE8Lattice, E8-is-basis}\leanok
  $c\Lambda_8$ is a $\Z$-lattice, i.e. it is discrete and spans $\R^8$ over $\R$.
\end{lemma}
```

:::proof "instLatticeE8"
The first part is by `instDiscreteE8Lattice`, and the second part follows
from the fact that $`\B_8`$ is a basis (`E8-is-basis`) and hence linearly
independent over $`\R`$.
:::

```tex "instLatticeE8" (slot := "proof")
\begin{proof}\leanok
  The first part is by \cref{instDiscreteE8Lattice}, and the second part follows from that $\B_8$ is a basis (\cref{E8-is-basis}) and hence linearly independent over $\R$.
\end{proof}
```

TODO: Prove $`E_8`$ is unimodular.

```tex
\todo{Prove $E_8$ is unimodular.}
```

TODO: Prove $`E_8`$ is positive-definite.

```tex
\todo{Prove $E_8$ is positive-definite.}
```

```tex
\subsection{The $E_8$ sphere packing}
```

:::definition "E8Packing" (lean := "E8Packing") (parent := "e8_density")
The $`E_8`$ sphere packing is the periodic sphere packing with separation
$`\sqrt{2}`$ and set of centers $`\Lambda_8`$.
This uses {uses "E8-Lattice"}[] and {uses "E8-vector-norms"}[].
:::

```tex "E8Packing"
\begin{definition}\label{E8Packing}\lean{E8Packing}\uses{E8-Lattice,E8-vector-norms}\leanok
  The \emph{$E_8$ sphere packing} is the (periodic) sphere packing with separation $\sqrt{2}$, whose set of centres is $\Lambda_8$.
\end{definition}
```

:::lemma_ "E8Packing-covol" (lean := "E8Basis_volume") (parent := "e8_density")
$`\Vol{\Lambda_8} = \mathrm{Covol}(\R^8 / \Lambda_8) = 1`$.
This uses {uses "E8Packing"}[].
:::

```tex "E8Packing-covol"
\begin{lemma}\label{E8Packing-covol}\lean{E8Basis_volume}\uses{E8Packing}\leanok
  $\Vol{\Lambda_8} = \mathrm{Covol}(\R^8 / \Lambda_8) = 1$.
\end{lemma}
```

:::proof "E8Packing-covol"
In theory this should follow directly from $`\det(\Lambda_8) = 1`$, but Lean
hates me and `EuclideanSpace` is being annoying.
:::

```tex "E8Packing-covol" (slot := "proof")
\begin{proof}\leanok
  \todo{In theory this should follow directly from $\det(\Lambda_8) = 1$, but Lean hates me and \texttt{EuclideanSpace} is being annoying.}
\end{proof}
```

:::theorem "E8Packing-density" (lean := "E8Packing_density") (parent := "e8_density")
We have $`\Delta_{\mathcal{P}(E_8)} = \frac{\pi^4}{384}`$.
This uses {uses "theorem:psp-density"}[] and {uses "E8Packing-covol"}[].
:::

```tex "E8Packing-density"
\begin{theorem}\label{E8Packing-density}\uses{theorem:psp-density,E8Packing-covol}\lean{E8Packing_density}\leanok
  We have $\Delta_{\mathcal{P}(E_8)} = \frac{\pi^4}{384}$.
\end{theorem}
```

:::proof "E8Packing-density"
By `theorem:psp-density`, we have
$`\Delta_{\mathcal{P}(E_8)} = |E_8 / E_8| \cdot \frac{\Vol{\mathcal{B}_8(\sqrt{2} / 2)}}{\mathrm{Covol}(E_8)} = \frac{\pi^4}{384}`$,
where the last equality follows from `E8Packing-covol` and the
formula for the volume of a ball,
$`\Vol{\mathcal{B}_d(R)} = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)`$.
:::

```tex "E8Packing-density" (slot := "proof")
\begin{proof}\leanok
  By \cref{theorem:psp-density}, we have $\Delta_{\mathcal{P}(E_8)} = |E_8 / E_8| \cdot \frac{\Vol{\mathcal{B}_8(\sqrt{2} / 2)}}{\mathrm{Covol}(E_8)} = \frac{\pi^4}{384}$, where the last equality follows from \cref{E8Packing-covol} and the formula for volume of a ball: $\Vol{\mathcal{B}_d(R)} = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)$.
\end{proof}
```
