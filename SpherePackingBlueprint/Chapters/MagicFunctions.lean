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


#doc (Manual) "Fourier Eigenfunctions with Double Zeroes" =>


:::group "magic_phi_construction"
Auxiliary modular expressions and integral formulas defining a.
:::

:::group "magic_a_properties"
Schwartz, Fourier-eigenfunction, and double-zero properties of a.
:::

:::group "magic_psi_construction"
Auxiliary forms and integral formulas defining b.
:::

:::group "magic_b_properties"
Schwartz, Fourier-eigenfunction, and double-zero properties of b.
:::

In this section we construct two radial Schwartz functions
$`a,b:\R^8\to i\R`$ such that
$$`\mathcal{F}(a)=a`
$$`\mathcal{F}(b)=-b`
and such that they have double zeroes at all $`\Lambda_8`$-vectors of length
greater than $`\sqrt{2}`$. Recall that each vector of $`\Lambda_8`$ has length
$`\sqrt{2n}`$ for some $`n\in\N_{\geq 0}`$. We define $`a`$ and $`b`$ so that
their values are purely imaginary because this simplifies some of our
computations. We will show in Section the final inequalities section that an appropriate
linear combination of functions $`a`$ and $`b`$ satisfies conditions
`eqn:g1` to `eqn:g3`.

```tex
In this section we construct two radial Schwartz functions $a,b:\R^8\to i\R$ such that
\begin{align}\mathcal{F}(a)&=a\label{eqn:a-fourier}\\
    \mathcal{F}(b)&=-b\label{eqn:b-fourier}
\end{align}
which double zeroes at all $\Lambda_8$-vectors of length greater than $\sqrt{2}$. Recall that each vector of $\Lambda_8$ has length $\sqrt{2n}$ for some $n\in\N_{\geq 0}$.
We define $a$ and $b$ so that their values are purely imaginary because this simplifies some of our computations.
We will show in Section \ref{sec: g} that an appropriate linear combination of functions $a$ and $b$ satisfies conditions \eqref{eqn:g1}--\eqref{eqn:g3}.
```

Both functions will be defined via certain integrals of quasi-modular forms.
Then the eigenfunction property mainly follows from the Poisson summation
formula and the
transformation laws of quasi-modular forms. To apply that theorem, we will show
that $`a(x)`$ and $`b(x)`$ are Schwartz functions, which can be proved by
verifying fast decay of the defining integrals.

```tex
Both of the functions will be defined via certain integrals of (quasi)modular forms.
Then the eigenfunction property mainly follows from the Poisson summation formula (Theorem \ref{thm:Poisson-summation-formula}) and the transformation laws of (quasi)modular forms.
To apply Theorem \ref{thm:Poisson-summation-formula}, we will show that $a(x)$ and $b(x)$ are Schwartz functions, and this can be proved by verifying fast decay of the integrals.
```

First we define the function $`a`$. To this end, we consider the following
functions.

```tex


First, we will define function $a$. To this end we consider the following functions:
```

:::definition "def:phi4-phi2-phi0" (parent := "magic_phi_construction")
Define
$$`\phi_{-4} := \frac{E_4^2}{\Delta}`
$$`\phi_{-2} := \frac{E_4(E_2 E_4 - E_6)}{\Delta}`
$$`\phi_{0} := \frac{(E_2 E_4 - E_6)^2}{\Delta}.`
{uses "def:Ek"}[]{uses "def:E2"}[]
:::

```tex "def:phi4-phi2-phi0"
\begin{definition}\label{def:phi4-phi2-phi0}
\uses{def:Ek,def:E2}
\begin{align}
    \phi_{-4} &:= \frac{E_4^2}{\Delta} \label{eqn: def phi4} \\
    \phi_{-2} &:= \frac{E_4(E_2 E_4 - E_6)}{\Delta} \label{eqn: def phi2} \\
    \phi_{0} &:= \frac{(E_2 E_4 - E_6)^2}{\Delta} \label{eqn: def phi0}
\end{align}
\end{definition}
```

The function $`\phi_0(z)`$ is not modular; however, it satisfies the following
transformation rules.

```tex
The function $\phi_0(z)$ is not modular; however, it satisfies the following transformation rules:
```

:::lemma_ "lemma:phi0-transform" (parent := "magic_phi_construction")
We have
$$`\phi_0(z + 1) = \phi_0(z)`
$$`\phi_0\left(-\frac{1}{z}\right) = \phi_0(z)-\frac{12i}{\pi}\,\frac{1}{z}\,\phi_{-2}(z)-\frac{36}{\pi^2}\,\frac{1}{z^2}\,\phi_{-4}(z).`
{uses "def:phi4-phi2-phi0"}[]{uses "lemma:Ek-is-modular-form"}[]{uses "lemma:E2-transform-S"}[]{uses "lemma:disc-cuspform"}[]
:::

```tex "lemma:phi0-transform"
\begin{lemma}\label{lemma:phi0-transform}\uses{def:phi4-phi2-phi0, lemma:Ek-is-modular-form, lemma:E2-transform-S, lemma:disc-cuspform}
We have
\begin{align}
    \phi_0(z + 1) &= \phi_0(z) \label{eqn:phi0-trans-T} \\
    \phi_0\left(-\frac{1}{z}\right) &= \phi_0(z)-\frac{12i}{\pi}\,\frac{1}{z}\,\phi_{-2}(z)-\frac{36}{\pi^2}\,\frac{1}{z^2}\,\phi_{-4}(z).\label{eqn:phi0-trans-S}
\end{align}
\end{lemma}
```

:::proof "lemma:phi0-transform"
Equation $`\phi_0(z + 1) = \phi_0(z)`$ follows easily from periodicity of the
Eisenstein series and of $`\Delta(z)`$. For the second transformation law,
$$`\phi_{0}\left(-\frac{1}{z}\right) = \frac{(E_2(-1/z) E_4(-1/z) - E_6(-1/z))^{2}}{\Delta(-1/z)}`
$$`= \frac{((z^2 E_2(z) - 6iz / \pi) \cdot z^4 E_4(z) - z^6 E_6(z))^{2}}{z^{12} \Delta(z)}`
$$`= \frac{\left(E_2(z) E_4(z) - E_6(z) - \frac{6i}{\pi z} E_4(z)\right)^2}{\Delta(z)}`
$$`= \frac{(E_2(z) E_4(z) - E_6(z))^{2} - \frac{12i}{\pi z}(E_2(z) E_4(z) - E_6(z)) E_4(z) - \frac{36}{\pi^2 z^2} E_4(z)^{2}}{\Delta(z)}`
$$`= \phi_0(z) - \frac{12 i}{\pi z} \phi_{-2}(z) - \frac{36}{\pi^2 z^2} \phi_{-4}(z).`
:::

```tex "lemma:phi0-transform" (slot := "proof")
\begin{proof}
\eqref{eqn:phi0-trans-T} easily follows from periodicity of Eisenstein series and $\Delta(z)$.
For \eqref{eqn:phi0-trans-S},
\begin{align}
    \phi_{0}\left(-\frac{1}{z}\right) &= \frac{(E_2(-1/z) E_4(-1/z) - E_6(-1/z))^{2}}{\Delta(-1/z)} \\
    &= \frac{((z^2 E_2(z) - 6iz / \pi) \cdot z^4 E_4(z) - z^6 E_6(z))^{2}}{z^{12} \Delta(z)} \\
    &= \frac{\left(E_2(z) E_4(z) - E_6(z) - \frac{6i}{\pi z} E_4(z)\right)^2}{\Delta(z)} \\
    &= \frac{(E_2(z) E_4(z) - E_6(z))^{2} - \frac{12i}{\pi z}(E_2(z) E_4(z) - E_6(z)) E_4(z) - \frac{36}{\pi^2 z^2} E_4(z)^{2}}{\Delta(z)} \\
    &= \phi_0(z) - \frac{12 i}{\pi z} \phi_{-2}(z) - \frac{36}{\pi^2 z^2} \phi_{-4}(z).
\end{align}
\end{proof}
```

For our formalization, we choose rectangular contours for the first and second
integrals, and write the definition as follows.

```tex
For our formalization, we choose rectangular contours for the first and the second integral, and write it as follows.
```

:::definition "def:a-definition" (lean := "MagicFunction.a.RealIntegrals.a',MagicFunction.a.RadialFunctions.a") (parent := "magic_phi_construction")
Define $`a_{\rad} : \R \to \C`$ by
$$`a_\rad(r) := I_1(r) + I_2(r) + I_3(r) + I_4(r) + I_5(r) + I_6(r)`
where
$$`I_1(r) := \int_{-1}^{-1 + i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z`
$$`I_2(r) := \int_{-1 + i}^{i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z`
$$`I_3(r) := \int_{1}^{1 + i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z`
$$`I_4(r) := \int_{1 + i}^{i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z`
$$`I_5(r) := -2 \int_{0}^{i} \phi_0 \left(\frac{-1}{z}\right) z^2 e^{\pi i r z} \dd z`
$$`I_6(r) := 2 \int_{i}^{i\infty} \phi_0(z) e^{\pi i r z} \dd z.`
Here all contours are chosen to be straight line segments. Define
$`a(x) := a_{\rad}(\|x\|^2)`$ for $`x \in \R^8`$.
{uses "def:phi4-phi2-phi0"}[]
:::

```tex "def:a-definition"
\begin{definition}\label{def:a-definition}\lean{MagicFunction.a.RealIntegrals.a',MagicFunction.a.RadialFunctions.a}\leanok
\uses{def:phi4-phi2-phi0}
Define $a_{\rad} : \R \to \C$ by
\begin{align}\label{eqn:a-rad-definition}
    a_\rad(r) := I_1(r) + I_2(r) + I_3(r) + I_4(r) + I_5(r) + I_6(r)
\end{align}
where
\begin{align}
    I_1(r) &:= \int_{-1}^{-1 + i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z \label{eqn:a-I1} \\
    I_2(r) &:= \int_{-1 + i}^{i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z \label{eqn:a-I2} \\
    I_3(r) &:= \int_{1}^{1 + i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z \label{eqn:a-I3} \\
    I_4(r) &:= \int_{1 + i}^{i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z \label{eqn:a-I4} \\
    I_5(r) &:= -2 \int_{0}^{i} \phi_0 \left(\frac{-1}{z}\right) z^2 e^{\pi i r z} \dd z \label{eqn:a-I5} \\
    I_6(r) &:= 2 \int_{i}^{i\infty} \phi_0(z) e^{\pi i r z} \dd z \label{eqn:a-I6}
\end{align}
Here all the contours are chosen to be straight line segments.
Now, define $a(x) := a_{\rad}(\|x\|^2)$ for $x \in \R^8$.
\end{definition}
```

In the original paper, the integrals $`I_1`$ and $`I_2`$ are combined, as are
$`I_3`$ and $`I_4`$. We write them separately to simplify the formalization.

```tex
In the original paper, the integrals $I_1$ and $I_2$ are combined, as well as $I_3$ and $I_4$.
We choose to write them separately to simplify the formalization.
```

Now we prove that $`a`$ satisfies condition `eqn:a-fourier`.
The following lemma will be used to prove Schwartzness of both $`a`$ and
$`b`$.

```tex
Now we prove that $a$ satisfies condition \eqref{eqn:a-fourier}.
The following lemma will be used to prove Schwartzness of $a$ and $b$.
```

:::lemma_ "lemma:mod-div-disc-bound" (lean := "MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff") (parent := "magic_phi_construction")
Let $`f(z)`$ be a holomorphic function with Fourier expansion
$$`f(z) = \sum_{n \ge n_0} c_f(n) e^{\pi i n z}`
with $`c_f(n_0) \ne 0`$. Assume that $`c_f(n)`$ has polynomial growth, that is,
$`|c_f(n)| = O(n^k)`$ for some $`k \in \N`$. Then there exists a constant
$`C_f > 0`$ such that
$$`\left|\frac{f(z)}{\Delta(z)}\right| \le C_f e^{-\pi (n_0 - 2) \Im z}`
for all $`z`$ with $`\Im z > 1/2`$.
:::

```tex "lemma:mod-div-disc-bound"
\begin{lemma}\label{lemma:mod-div-disc-bound}\lean{MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff}\leanok
Let $f(z)$ be a holomorphic function with a Fourier expansion
\begin{equation}
    f(z) = \sum_{n \ge n_0} c_f(n) e^{\pi i n z}
\end{equation}
with $c_f(n_0) \ne 0$.
Assume that $c_f(n)$ has a polynomial growth, i.e. $|c_f(n)| = O(n^k)$ for some $k \in \N$.
Then there exists a constant $C_f > 0$ such that
\begin{equation}
    \left|\frac{f(z)}{\Delta(z)}\right| \le C_f e^{-\pi (n_0 - 2) \Im z}
\end{equation}
for all $z$ with $\Im z > 1/2$.
\end{lemma}
```

When $`f(z)`$ is a quasi-modular form, we can take $`k`$ to be the weight of
$`f`$.

```tex
When $f(z)$ is a (quasi)modular form, we can take $k$ to be the weight of $f$.
```

:::proof "lemma:mod-div-disc-bound"
By the product formula for $`\Delta`$,
$$`\left|\frac{f(z)}{\Delta(z)}\right|
 = \left|\frac{\sum_{n \ge n_0} c_f(n) e^{\pi i n z}}{e^{2 \pi i z}\prod_{n \ge 1} (1 - e^{2\pi i n z})^{24}}\right|`
$$`= |e^{\pi i (n_0 - 2)z}| \cdot \frac{|\sum_{n \ge n_0} c_f(n) e^{\pi i (n - n_0) z}|}{\prod_{n \ge 1} |1 - e^{2\pi i n z}|^{24}}`
$$`\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) \Im z}}{\prod_{n \ge 1} (1 - e^{- 2\pi n \Im z})^{24}}`
$$`\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}}
 = C_f \cdot e^{-\pi (n_0 - 2) \Im z}.`
Here
$$`C_f = \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}}.`
The numerator converges absolutely because of polynomial growth, and the
denominator also converges; indeed it is simply $`e^{\pi}\cdot \Delta(i/2)`$.
{uses "def:disc-definition"}[]
:::

```tex "lemma:mod-div-disc-bound" (slot := "proof")
\begin{proof}\uses{def:disc-definition}\leanok
By the product formula \eqref{eqn:disc-definition},
\begin{align}
    \left|\frac{f(z)}{\Delta(z)}\right| &= \left|\frac{\sum_{n \ge n_0} c_f(n) e^{\pi i n z}}{e^{2 \pi i z}\prod_{n \ge 1} (1 - e^{2\pi i n z})^{24}}\right| \\
    &= |e^{\pi i (n_0 - 2)z}| \cdot \frac{|\sum_{n \ge n_0} c_f(n) e^{\pi i (n - n_0) z}|}{\prod_{n \ge 1} |1 - e^{2\pi i n z}|^{24}} \\
    &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) \Im z}}{\prod_{n \ge 1} (1 - e^{- 2\pi n \Im z})^{24}} \\
    &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}} \\
    &= C_f \cdot e^{-\pi (n_0 - 2) \Im z}
\end{align}
where
\begin{equation}
    C_f = \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}}.
\end{equation}
Note that the summation in the numerator converges absolutely because of polynomial growth.
The denominator also converges, which is simply $e^{\pi} \cdot \Delta(i/2)$.
\end{proof}
```

As corollaries, we obtain the following bounds for $`\phi_0`$,
$`\phi_{-2}`$, and $`\phi_{-4}`$.

```tex
As corollaries, we have the following bound for $\phi_0$, $\phi_{-2}$, and $\phi_{-4}$.
```

:::corollary "cor:phi0-bound" (parent := "magic_phi_construction")
There exists a constant $`C_0 > 0`$ such that
$$`|\phi_0(z)| \le C_0 e^{-2 \pi \Im z}`
for all $`z`$ with $`\Im z > 1/2`$.
{uses "thm:ramanujan-formula"}[]{uses "lemma:mod-div-disc-bound"}[]{uses "lemma:Ek-Fourier"}[]{uses "lemma:mod_form_poly_growth"}[]
:::

```tex "cor:phi0-bound"
\begin{corollary}\label{cor:phi0-bound}\uses{thm:ramanujan-formula, lemma:mod-div-disc-bound, lemma:Ek-Fourier, lemma:mod_form_poly_growth}
There exists a constant $C_0 > 0$ such that
\begin{equation}\label{eqn:phi0-bound}
|\phi_0(z)| \le C_0 e^{-2 \pi \Im z}
\end{equation}
for all $z$ with $\Im z > 1/2$.
\end{corollary}
```

:::proof "cor:phi0-bound"
By Ramanujan's formula,
$`E_2 E_4 - E_6 = 3E_4' = 720 \sum_{n \ge 1} n \sigma_3(n) e^{2 \pi i n z}`$,
and
$$`(E_2(z) E_4(z) - E_6(z))^{2} = 720^{2} e^{4 \pi i z} + O(e^{5 \pi i z}).`
The result then follows from Lemma `lemma:mod-div-disc-bound` with
$`f(z) = (E_2 E_4 - E_6)^2`$ and $`n_0 = 4`$.
:::

```tex "cor:phi0-bound" (slot := "proof")
\begin{proof}
By Ramanujan's formula, $E_2 E_4 - E_6 = 3E_4' = 720 \sum_{n \ge 1} n \sigma_3(n) e^{2 \pi i n z}$ and
\begin{equation}
    (E_2(z) E_4(z) - E_6(z))^{2} = 720^{2} e^{4 \pi i z} + O(e^{5 \pi i z}). \notag
\end{equation}
Then the result follows from Lemma~\ref{lemma:mod-div-disc-bound} with $f(z) = (E_2 E_4 - E_6)^2$ and $n_0 = 4$.
\end{proof}
```

:::corollary "cor:phi2-bound" (parent := "magic_phi_construction")
There exists a constant $`C_{-2} > 0`$ such that
$$`|\phi_{-2}(z)| \le C_{-2}`
for all $`z`$ with $`\Im z > 1/2`$.
{uses "def:phi4-phi2-phi0"}[]{uses "lemma:mod-div-disc-bound"}[]{uses "lemma:Ek-Fourier"}[]
:::

```tex "cor:phi2-bound"
\begin{corollary}\label{cor:phi2-bound}\uses{def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier}
There exists a constant $C_{-2} > 0$ such that
\begin{equation}\label{eqn:phi2-bound}
    |\phi_{-2}(z)| \le C_{-2}
\end{equation}
for all $z$ with $\Im z > 1/2$.
\end{corollary}
```

:::corollary "cor:phi4-bound" (parent := "magic_phi_construction")
There exists a constant $`C_{-4} > 0`$ such that
$$`|\phi_{-4}(z)| \le C_{-4} e^{2 \pi \Im z}`
for all $`z`$ with $`\Im z > 1/2`$.
{uses "def:phi4-phi2-phi0"}[]{uses "lemma:mod-div-disc-bound"}[]{uses "lemma:Ek-Fourier"}[]
:::

```tex "cor:phi4-bound"
\begin{corollary}\label{cor:phi4-bound}\uses{def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier}
There exists a constant $C_{-4} > 0$ such that
\begin{equation}\label{eqn:phi4-bound}
    |\phi_{-4}(z)| \le C_{-4} e^{2 \pi \Im z}
\end{equation}
for all $z$ with $\Im z > 1/2$.
\end{corollary}
```

Note that we can take the constants $`C_0`$, $`C_{-2}`$, and $`C_{-4}`$ as
$$`C_0 = 9 \cdot 240^2 \cdot e^{\pi} \cdot \frac{E_4'(i/2)^{2}}{\Delta(i/2)}`
$$`C_{-2} = 3 \cdot \frac{E_4(i/2) E_4'(i/2)}{\Delta(i/2)}`
$$`C_{-4} = e^{-\pi} \cdot \frac{E_4(i/2)^{2}}{\Delta(i/2)}.`

```tex
Note that we can take the constants $C_0$, $C_{-2}$, and $C_{-4}$ as
\begin{align}
    C_0 &= 9 \cdot 240^2 \cdot e^{\pi} \cdot \frac{E_4'(i/2)^{2}}{\Delta(i/2)} \notag \\
    C_{-2} &= 3 \cdot \frac{E_4(i/2) E_4'(i/2)}{\Delta(i/2)} \notag \\
    C_{-4} &= e^{-\pi} \cdot \frac{E_4(i/2)^{2}}{\Delta(i/2)}. \notag
\end{align}
```

:::lemma_ "lem:integral-bound" (parent := "magic_a_properties")
For all $`n \in \N`$, there exists a constant $`C'`$ such that for all
$`r \geq 0`$,
$$`r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \dd s \leq C'.`
:::

```tex "lem:integral-bound"
\begin{lemma}\label{lem:integral-bound}
    For all $n \in \N$, there exists a constant $C'$ such that for all $r \geq 0$,
    \begin{align}
        r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \dd s \leq C'
    \end{align}
\end{lemma}
```

:::proof "lem:integral-bound"
Fix $`n \in \N`$. There exists a constant $`C`$ such that for all $`x \ge 0`$,
$`|x|^n \cdot |e^{-\pi x}| \le C`$.
In particular, for all $`r \ge 0`$ and $`s \ge 1`$,
$`r^n \cdot e^{-\pi r/s} \le C s^n`$.
Hence
$$`r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \dd{s}
 = \int_{1}^{\infty} e^{-2\pi s} \, \left(|r|^n \cdot e^{-\pi r /s}\right) \, \dd{s}
 \leq C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}.`
The Gamma function is given by
$$`\Gamma(x) = \int_{0}^{\infty} e^{-u} \, u^{x-1} \, \dd{u}`
for all $`x > 0`$. Writing $`u = 2\pi s`$ and using
$`\Gamma(n+1) = n!`$, we obtain
$$`C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}
 \leq C \int_{0}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}
 = C \int_{0}^{\infty} \frac{1}{(2\pi)^{n+1}} e^{-u} \, u^n \, \dd{u}
 = \frac{C \cdot n!}{(2\pi)^n}.`
Defining $`C' := \frac{C \cdot n!}{(2\pi)^n}`$ finishes the proof.
:::

```tex "lem:integral-bound" (slot := "proof")
\begin{proof}
    Fix $n \in \N$. We know there exists a constant $C$ such that for all $x \geq 0$, $\abs{x}^n \cdot \abs{e^{-\pi x}} \leq C$. In particular, for all $r \geq 0$ and $s \geq 1$, $r^n \cdot e^{-\pi r/s} \leq C s^n$. Hence, for all $r \in \R$, we can write
    \begin{align}
        r^n \cdot \int_{1}^{\infty} e^{-2\pi s} \, e^{-\pi r /s} \, \dd{s}
        = \int_{1}^{\infty} e^{-2\pi s} \, \left(\abs{r}^n \cdot e^{-\pi r /s}\right) \, \dd{s}
        \leq C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}
    \end{align}
    The $\Gamma$ function is given by
    \begin{align}
        \Gamma(x) = \int_{0}^{\infty} e^{-u} \, u^{x-1} \, \dd{u}
    \end{align}
    for all $x > 0$. Hence, writing $u = 2\pi s$ and using $\Gamma(n+1) = n!$, we get
    \begin{align}
        C \int_{1}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}
        \leq C \int_{0}^{\infty} e^{-2\pi s} \, s^n \, \dd{s}
        = C \int_{0}^{\infty} \frac{1}{(2\pi)^{n+1}} e^{-u} \, u^n \, \dd{u}
        = \frac{C}{(2\pi)^n} \Gamma(n+1)
        = \frac{C \cdot n!}{(2\pi)^n}
    \end{align}
    Defining $C' := \frac{C \cdot n!}{(2\pi)^n}$ finishes the proof.
\end{proof}
```

:::lemma_ "lem:bound-I1-I3-I5" (parent := "magic_a_properties")
There exists a constant $`C > 0`$ such that for all $`r \geq 0`$,
$$`|I_1(r)|, |I_3(r)|, |I_5(r)| \leq C \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.`
:::

```tex "lem:bound-I1-I3-I5"
\begin{lemma}\label{lem:bound-I1-I3-I5}
    There exists $C > 0$ such that for all $r \geq 0$,
    \begin{equation}
        |I_1(r)|, |I_3(r)|, |I_5(r)| \leq C \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.
    \end{equation}
\end{lemma}
```

:::proof "lem:bound-I1-I3-I5"
We prove the bound only for $`I_1(r)`$, as the others are similar.
With the change of variable $`z = -1 + i t`$ for $`t \in [0,1]`$, we have
$$`I_1(r) = -i \int_0^1 \phi_0\left(\frac{-1}{i t}\right) t^2 e^{-\pi i r} \cdot e^{-\pi r t} \, \dd t.`
With the change of variable $`s = 1 / t`$, this becomes
$$`I_1(r) = i \int_1^{\infty} \phi_0(i s) \cdot s^{-4} \cdot e^{-\pi i r} \cdot e^{-\pi r / s} \, \dd s,`
so
$$`|I_1(r)| \leq \int_1^{\infty} |\phi_0(i s)| \cdot s^{-4} \cdot |e^{-\pi i r}| \cdot e^{-\pi r / s} \, \dd s
\le \int_1^{\infty} |\phi_0(is)| \cdot e^{-\pi r / s} \, \dd s.`
By Corollary `cor:phi0-bound`, we conclude that
$$`|I_1(r)| \leq C_0 \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.`
:::

```tex "lem:bound-I1-I3-I5" (slot := "proof")
\begin{proof}
    We only prove the bound for $I_1(r)$, as the other two are similar.
    By the change of variable $z = -1 + i t$ for $t \in [0,1]$, we have
    $$
    I_1(r) = -i \int_0^1 \phi_0\left(\frac{-1}{i t}\right) t^2 e^{-\pi i r} \cdot e^{-\pi r t} \, \dd t.
    $$
    With the change of variable $s = 1 / t$, we get
    $$
    I_1(r) = i \int_1^{\infty} \phi_0(i s) \cdot s^{-4} \cdot e^{-\pi i r} \cdot e^{-\pi r / s} \, \dd s
    $$
    and the absolute value can be bounded as
    $$
    |I_1(r)| \leq \int_1^{\infty} |\phi_0(i s)| \cdot s^{-4} \cdot |e^{-\pi i r}| \cdot e^{-\pi r / s} \, \dd s \le \int_1^{\infty} |\phi_0(is)| \cdot e^{-\pi r / s} \, \dd s.
    $$
    Now, Corollary~\ref{cor:phi0-bound} shows
    $$
    |I_1(r)| \leq C_0 \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.
    $$
\end{proof}
```

Combined with Lemma `lem:integral-bound`, this shows that the
integrals $`I_1`$, $`I_3`$, and $`I_5`$ decay faster than any polynomial as
$`r \to \infty`$. For the integrals $`I_2`$, $`I_4`$, and $`I_6`$, this is
easier to see since the contours do not touch the real axis.

```tex
Combined with Lemma~\ref{lem:integral-bound}, this shows that the integrals $I_1$, $I_3$, and $I_5$ decay faster than any polynomial as $r \to \infty$.
For the integrals $I_2$, $I_4$, and $I_6$, it is easier to see this since the contours are not touching the real axis.
```

:::lemma_ "lem:bound-I2-I4-I6" (parent := "magic_a_properties")
There exist $`C_1, C_2 > 0`$ such that for all $`r \geq 0`$,
$$`|I_2(r)|, |I_4(r)| \leq C_1 e^{-\pi r}`
and
$$`|I_6(r)| \leq C_2 \frac{e^{-\pi(r + 2)}}{r + 2}.`
:::

```tex "lem:bound-I2-I4-I6"
\begin{lemma}\label{lem:bound-I2-I4-I6}
    There exist $C_1, C_2 > 0$ such that for all $r \geq 0$,
    \begin{equation}
        |I_2(r)|, |I_4(r)| \leq C_1 e^{-\pi r}
    \end{equation}
    and
    \begin{equation}
        |I_6(r)| \leq C_2 \frac{e^{-\pi(r + 2)}}{r + 2}
    \end{equation}
\end{lemma}
```

:::proof "lem:bound-I2-I4-I6"
For $`I_2(r)`$, parametrize $`z`$ by $`z = t + i`$ for $`t \in [-1,0]`$.
Then
$$`I_2(r) = \int_{-1}^0 \phi_0\left(\frac{-1}{t + 1 + i}\right) (t + 1 + i)^2 e^{\pi i r t} e^{-\pi r} \, \dd t.`
Since the function
$`z \mapsto \phi_0\left(\frac{-1}{z+1}\right) (z+1)^2`$ is holomorphic and
bounded on the contour, there exists $`C > 0`$ such that
$`|\phi_0\left(\frac{-1}{z+1}\right) (z + 1)^2| \leq C`$,
and therefore
$$`|I_2(r)| \le \int_{-1}^{0} C e^{-\pi r} \, \dd t = C e^{-\pi r}.`
The bound for $`I_4(r)`$ is similar.

For $`I_6(r)`$, parametrize $`z = i t`$ for $`t \in [1, \infty)`$, giving
$$`I_6(r) = 2 i \int_1^{\infty} \phi_0(i t) e^{-\pi r t} \, \dd t.`
Using Corollary `cor:phi0-bound`, the absolute value is bounded by
$$`|I_6(r)| \leq 2 \int_1^{\infty} |\phi_0(i t)| e^{-\pi r t} \, \dd t \leq \frac{2C_0}{\pi} \int_1^{\infty} e^{-2\pi t} e^{-\pi r t} \, \dd t = \frac{2C_0}{\pi} \frac{e^{-\pi (r + 2)}}{r + 2}.`
:::

```tex "lem:bound-I2-I4-I6" (slot := "proof")
\begin{proof}
    For $I_2(r)$, parametrize $z$ as $z = t + i$ for $t \in [-1,0]$, and we have
    $$
        I_2(r) = \int_{-1}^0 \phi_0\left(\frac{-1}{t + 1 + i}\right) (t + 1 + i)^2 e^{\pi i r t} e^{-\pi r} \, \dd t.
    $$
    Since the function $z \mapsto \phi_0\left(\frac{-1}{z+1}\right) (z+1)^2$ is holomorphic and bounded on the contour,
    there exists $C > 0$ such that $|\phi_0\left(\frac{-1}{z+1}\right) (z + 1)^2| \leq C$, and the absolute value of the integral can be bounded by
    $$
        |I_2(r)| \le \int_{-1}^{0} C e^{-\pi r} \, \dd t = C e^{-\pi r}.
    $$
    The bound for $I_4(r)$ is similar.
    For $I_6(r)$, parametrize $z$ as $z = i t$ for $t \in [1, \infty)$, and we have
    $$
        I_6(r) = 2 i \int_1^{\infty} \phi_0(i t) e^{-\pi r t} \, \dd t
    $$
    and the absolute value can be bounded as (using Corollary~\ref{cor:phi0-bound})
    $$
        |I_6(r)| \leq 2 \int_1^{\infty} |\phi_0(i t)| e^{-\pi r t} \, \dd t \leq \frac{2C_0}{\pi} \int_1^{\infty} e^{-2\pi t} e^{-\pi r t} \, \dd t = \frac{2C_0}{\pi} \frac{e^{-\pi (r + 2)}}{r + 2}.
    $$
\end{proof}
```

Combining these bounds, one can show that $`a`$ is a Schwartz function.

```tex
Combining these, one can show that $a$ is a Schwartz function.
```

:::lemma_ "prop:a-schwartz" (lean := "MagicFunction.FourierEigenfunctions.a") (parent := "magic_a_properties")
$`a(x)`$ is a Schwartz function.
{uses "def:a-definition"}[]{uses "cor:phi0-bound"}[]
:::

```tex "prop:a-schwartz"
\begin{proposition}\label{prop:a-schwartz}\lean{MagicFunction.FourierEigenfunctions.a}\leanok
\uses{def:a-definition, cor:phi0-bound}
$a(x)$ is a Schwartz function.
\end{proposition}
```

:::proof "prop:a-schwartz"
By Theorem {uses "thm:smooth-fast-decay-schwartz"}[], it suffices to show that
the function is smooth and decays faster than any polynomial. Smoothness
follows from differentiation under the integral, already formalized in
`mathlib`. The decay follows from Lemmas {uses "lem:bound-I1-I3-I5"}[] and
{uses "lem:bound-I2-I4-I6"}[], together with
{uses "lem:integral-bound"}[].
:::

```tex "prop:a-schwartz" (slot := "proof")
\begin{proof}
\uses{lem:bound-I1-I3-I5, lem:bound-I2-I4-I6, lem:integral-bound, thm:smooth-fast-decay-schwartz}
By Theorem \ref{thm:smooth-fast-decay-schwartz}, it suffices to show that the function is smooth and decays faster than any polynomial.
The smoothness follows from the ``differentiation under the integral'', which is already formalized in \texttt{mathlib}.
The decay follows from Lemmas \ref{lem:bound-I1-I3-I5} and \ref{lem:bound-I2-I4-I6}, together with Lemma \ref{lem:integral-bound}.
\end{proof}
```

:::lemma_ "prop:a-fourier" (lean := "MagicFunction.a.Fourier.eig_a") (parent := "magic_a_properties")
$`a(x)`$ satisfies equation `eqn:a-fourier`.
{uses "lemma:Ek-Fourier"}[]{uses "def:E2"}[]{uses "def:a-definition"}[]{uses "lemma:Gaussian-Fourier"}[]{uses "prop:a-schwartz"}[]
:::

```tex "prop:a-fourier"
\begin{proposition}\label{prop:a-fourier}
\uses{lemma:Ek-Fourier, def:E2, def:a-definition, lemma:Gaussian-Fourier, prop:a-schwartz}\lean{MagicFunction.a.Fourier.eig_a}
$a(x)$ satisfies \eqref{eqn:a-fourier}.
\end{proposition}
```

:::proof "prop:a-fourier"
We recall that the Fourier transform of a Gaussian function is
$$`\mathcal{F}(e^{\pi i \|x\|^2 z})(y)=z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.`
Next, exchange contour integration in the $`z`$ variable with Fourier
transform in the $`x`$ variable in the definition of $`a`$. This is justified
because the corresponding double integral converges absolutely. In this way we
obtain
$$`\widehat{a}(y)=\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz
    +\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz`
$$`-2\int\limits_{0}^i\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz.`
Making the change of variables $`w=\frac{-1}{z}`$, we arrive at
$$`\widehat{a}(y)=\int\limits_{1}^i\phi_0\Big(1-\frac{1}{w-1}\Big)\,(\frac{-1}{w}+1)^2\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw`
$$`+\int\limits_{-1}^i\phi_0\Big(1-\frac{1}{w+1}\Big)\,(\frac{-1}{w}-1)^2\,w^2\,e^{\pi i \|y\|^2 \,w}\,dw`
$$`-2\int\limits_{i \infty}^i\phi_0(w)\,e^{\pi i \|y\|^2 \,w}\,dw +2\int\limits_{i}^{0}\phi_0\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw.`
Since $`\phi_0`$ is $`1`$-periodic, this becomes exactly the defining
expression for $`a(y)`$.
:::

```tex "prop:a-fourier" (slot := "proof")
\begin{proof}
We recall that the Fourier transform of a Gaussian function is
\begin{equation}
    \mathcal{F}(e^{\pi i \|x\|^2 z})(y)=z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.
\end{equation}
Next, we exchange the contour integration with respect to $z$ variable and Fourier transform with respect to $x$ variable in \eqref{eqn:a-definition}.
This can be done, since the corresponding double integral converges absolutely. In this way we obtain
\begin{align}
    \widehat{a}(y)=&\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz
    +\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz\notag \\
    -&2\int\limits_{0}^i\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z})}\,dz.\notag
\end{align}
Now we make a change of variables $w=\frac{-1}{z}$. We obtain
\begin{align}
    \widehat{a}(y)=&\int\limits_{1}^i\phi_0\Big(1-\frac{1}{w-1}\Big)\,(\frac{-1}{w}+1)^2\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw\notag\\
    +&\int\limits_{-1}^i\phi_0\Big(1-\frac{1}{w+1}\Big)\,(\frac{-1}{w}-1)^2\,w^2\,e^{\pi i \|y\|^2 \,w}\,dw\\
    -&2\int\limits_{i \infty}^i\phi_0(w)\,e^{\pi i \|y\|^2 \,w}\,dw +2\int\limits_{i}^{0}\phi_0\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|y\|^2 \,w}\,dw.\notag
\end{align}
Since $\phi_0$ is $1$-periodic we have
\begin{align}
    \widehat{a}(y)\,=\,&\int\limits_{1}^i\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i \|y\|^2 \,z}\,dz
    +\int\limits_{-1}^i\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
    +&2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i \|y\|^2 \,z}\,dz
    -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^{2}\,e^{\pi i \|y\|^2 \,z}\,dz\notag \\
    \,=\,&a(y).
\end{align}
This finishes the proof of the proposition.
\end{proof}
```

Next, we check that $`a`$ has double zeroes at all $`\Lambda_8`$-lattice points
of length greater than $`\sqrt{2}`$. Using the bounds on
$`\phi_0`$, $`\phi_{-2}`$, and $`\phi_{-4}`$, we can control the behavior of
$`\phi_0`$ near $`0`$ and $`i\infty`$.

```tex
Next, we check that $a$ has double zeroes at all $\Lambda_8$-lattice points of length greater then $\sqrt{2}$.
Using \eqref{eqn:phi0-bound}, \eqref{eqn:phi2-bound}, and \eqref{eqn:phi4-bound}, we can control the behavior of $\phi_0$ near $0$ and $i\infty$.
%Note that by definition function $a$ is radial and therefore in naturally defines a function on $\R_{\geq0}$. For abuse of notation we denote this function also by $a$.
```

:::corollary "cor:phi0-near-0-infty" (parent := "magic_a_properties")
We have
$$`\phi_0\left(\frac{i}{t}\right) = O(e^{-2 \pi / t}) \quad \text{as } t \to 0`
$$`\phi_0\left(\frac{i}{t}\right) = O(t^{-2}e^{2 \pi t}) \quad \text{as } t \to \infty.`
{uses "cor:phi0-bound"}[]{uses "cor:phi2-bound"}[]{uses "cor:phi4-bound"}[]{uses "lemma:phi0-transform"}[]
:::

```tex "cor:phi0-near-0-infty"
\begin{corollary}\label{cor:phi0-near-0-infty}\uses{cor:phi0-bound, cor:phi2-bound, cor:phi4-bound, lemma:phi0-transform}
We have
\begin{align}
    \phi_0\left(\frac{i}{t}\right) &= O(e^{-2 \pi / t}) \quad \text{as } t \to 0 \label{eqn:phi0-near-0} \\
    \phi_0\left(\frac{i}{t}\right) &= O(t^{-2}e^{2 \pi t}) \quad \text{as } t \to \infty. \label{eqn:phi0-near-infty} \\
\end{align}
\end{corollary}
```

:::proof "cor:phi0-near-0-infty"
The first estimate follows from `eqn:phi0-bound` with $`z = i/t`$.
For the second estimate, by `eqn:phi0-trans-S`,
`eqn:phi2-bound`, and `eqn:phi4-bound`,
$$`\left|\phi_0\left(\frac{i}{t}\right)\right| \le |\phi_0(it)| + \frac{12}{\pi t} |\phi_{-2}(it)| + \frac{36}{\pi^2 t^2} |\phi_{-4}(it)|`
$$`\le C_0 e^{-2 \pi t} + \frac{12}{\pi t} \cdot C_{-2} + \frac{36}{\pi^2 t^2} \cdot C_{-4} e^{2 \pi t} = O(t^{-2}e^{2 \pi t}).`
:::

```tex "cor:phi0-near-0-infty" (slot := "proof")
\begin{proof}
The first estimate follows from \eqref{eqn:phi0-bound} with $z = i/t$.
For the second estimate, by \eqref{eqn:phi0-trans-S}, \eqref{eqn:phi2-bound}, and \eqref{eqn:phi4-bound}, we have
\begin{equation}
    \left|\phi_0\left(\frac{i}{t}\right)\right| \le |\phi_0(it)| + \frac{12}{\pi t} |\phi_{-2}(it)| + \frac{36}{\pi^2 t^2} |\phi_{-4}(it)|
    \le C_0 e^{-2 \pi t} + \frac{12}{\pi t} \cdot C_{-2} + \frac{36}{\pi^2 t^2} \cdot C_{-4} e^{2 \pi t} = O(t^{-2}e^{2 \pi t}).
\end{equation}
\end{proof}
```

:::lemma_ "prop:a-double-zeros" (parent := "magic_a_properties")
For $`r>\sqrt{2}`$ we can express $`a(r)`$ in the form
$$`a(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz.`
{uses "cor:phi0-near-0-infty"}[]{uses "def:a-definition"}[]{uses "cor:disc-nonvanishing"}[]
:::

```tex "prop:a-double-zeros"
\begin{proposition}
\label{prop:a-double-zeros}
\uses{cor:phi0-near-0-infty, def:a-definition, cor:disc-nonvanishing}
For $r>\sqrt{2}$ we can express $a(r)$ in the following form
\begin{equation}\label{eqn: a double zeroes}
    a(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz.
\end{equation}
\end{proposition}
```

:::proof "prop:a-double-zeros"
Denote the right-hand side by $`d(r)`$.
Convergence of the integral for $`r > \sqrt{2}`$ follows from
Corollary `cor:phi0-near-0-infty`.
We can write
$$`d(r)=\int\limits_{-1}^{i\infty-1}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz-
    2\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz`
$$`+\int\limits_{1}^{i\infty+1}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.`
From `eqn:phi0-trans-S` we deduce that if $`r>\sqrt{2}`$, then
$`\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\to 0`$ as
$`\Im(z)\to\infty`$. Therefore we can deform the paths of integration and
rewrite
$$`d(r)=\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz`
$$`-2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz`
$$`+\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.`
Now `eqn:phi0-trans-S` implies
$$`\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2-2\phi_0\Big(\frac{-1}{z}\Big)\,z^2+
\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2=2\phi_0(z),`
and hence
$$`d(r)=\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz`
$$`+\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i r^2 \,z}\,dz=a(r).`
:::

```tex "prop:a-double-zeros" (slot := "proof")
\begin{proof}
We denote the right hand side of \eqref{eqn: a double zeroes} by $d(r)$.
Convergence of the integral for $r > \sqrt{2}$ follows from Corollary~\ref{cor:phi0-near-0-infty}.
We can write
\begin{align}
    d(r)=&\int\limits_{-1}^{i\infty-1}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz-
    2\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i\infty+1}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.\notag
\end{align}
From \eqref{eqn:phi0-trans-S} we deduce that if $r>\sqrt{2}$ then
$\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\to 0$ as $\Im(z)\to\infty$. Therefore, we can deform the paths of integration
and rewrite
\begin{align}
    d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    -2&\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz.\notag
\end{align}
Now from \eqref{eqn:phi0-trans-S} we find
\begin{align}
&\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2-2\phi_0\Big(\frac{-1}{z}\Big)\,z^2+
\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2=\notag\\
&\phi_0(z+1)\,(z+1)^2-2\phi_0(z)\,z^2+\phi_0(z-1)\,(z-1)^2\notag\\
&-\frac{12i}{\pi}\,\Big(\phi_{-2}(z+1)\,(z+1)-2\phi_{-2}(z)\,z+\phi_{-2}(z-1)\,(z-1)\Big)\notag\\
&-\frac{36}{\pi^2}\Big(\phi_{-4}(z+1)-2\phi_{-4}(z)+\phi_{-4}(z-1)\Big)=\notag\\
&2\phi_0(z).
\end{align}
Thus, we obtain
\begin{align}
    d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz
    -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\notag\\
    +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz
    +2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i r^2 \,z}\,dz=a(r).\notag
\end{align}
This finishes the proof.
\end{proof}
```

Finally, we find another convenient integral representation for $`a`$ and
compute the value at $`r=0`$.

```tex
Finally, we find another convenient integral representation for $a$ and compute values of $a(r)$ at $r=0$ and $r=\sqrt{2}$.
```

:::lemma_ "prop:a-another-integral" (parent := "magic_a_properties")
For $`r\geq0`$ we have
$$`a(r)=4i\,\sin(\pi r^2/2)^2\,\Bigg(\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}`
$$`+\int\limits_0^\infty\,\left(t^2\,\phi_0\Big(\frac{i}{t}\Big)-\frac{36}{\pi^2}\,e^{2\pi t}+\frac{8640}{\pi}\,t-\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt \Bigg).`
The integral converges absolutely for all $`r\in\R_{\geq 0}`$.
{uses "prop:a-double-zeros"}[]{uses "def:phi4-phi2-phi0"}[]{uses "lemma:phi0-transform"}[]{uses "def:a-definition"}[]
:::

```tex "prop:a-another-integral"
\begin{proposition}\label{prop:a-another-integral}\uses{prop:a-double-zeros, def:phi4-phi2-phi0, lemma:phi0-transform, def:a-definition}
For $r\geq0$ we have
\begin{align}\label{eqn:a-another-integral}a(r)=&4i\,\sin(\pi r^2/2)^2\,\Bigg(\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}\\ +&\int\limits_0^\infty\,\left(t^2\,\phi_0\Big(\frac{i}{t}\Big)-\frac{36}{\pi^2}\,e^{2\pi t}+\frac{8640}{\pi}\,t-\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt \Bigg) .\notag\end{align}
The integral converges absolutely for all $r\in\R_{\geq 0}$.
\end{proposition}
```

:::proof "prop:a-another-integral"
Suppose that $`r>\sqrt{2}`$. Then by Proposition `prop:a-double-zeros`,
$$`a(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\phi_0(i/t)\,t^2\,e^{-\pi r^2 t}\,dt.`
From `eqn:phi0-trans-S` we obtain the asymptotic expansion
$$`\phi_0(i/t)\,t^2=\frac{36}{\pi^2}\,e^{2 \pi t}-\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}+O(t^2\,e^{-2\pi t})`
as $`t\to\infty`$. For $`r>\sqrt{2}`$,
$$`\int\limits_0^\infty \left(\frac{36}{\pi^2}\,e^{2 \pi t}+\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt
=\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}.`
Therefore the claimed identity holds for $`r>\sqrt{2}`$.

On the other hand, the definition of $`a`$ shows that $`a(r)`$ is analytic in
a neighborhood of $`[0,\infty)`$, and the asymptotic expansion above implies
that the right-hand side is also analytic there. Hence the identity holds on
the whole interval $`[0,\infty)`$.
:::

```tex "prop:a-another-integral" (slot := "proof")
\begin{proof}
Suppose that $r>\sqrt{2}$. Then by Proposition~\ref{prop:a-double-zeros}
$$a(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\phi_0(i/t)\,t^2\,e^{-\pi r^2 t}\,dt. $$
From \eqref{eqn:phi0-trans-S} we obtain
\begin{equation}
\phi_0(i/t)\,t^2=\frac{36}{\pi^2}\,e^{2 \pi t}-\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}+O(t^2\,e^{-2\pi t})\quad\mbox{as}\;t\to\infty.
\end{equation}
For $r>\sqrt{2}$ we have
\begin{equation}
\int\limits_0^\infty \left(\frac{36}{\pi^2}\,e^{2 \pi t}+\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt
=\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}.\end{equation}
Therefore, the identity \eqref{eqn:a-another-integral} holds for $r>\sqrt{2}$.

On the other hand, from the definition~\eqref{eqn:a-definition} we see that $a(r)$ is analytic in some neighborhood of $[0,\infty)$. The asymptotic expansion above implies that the right hand side of \eqref{eqn:a-another-integral} is also analytic in some neighborhood of $[0,\infty)$. Hence, the identity \eqref{eqn:a-another-integral} holds on the whole interval $[0,\infty)$. This finishes the proof of the proposition.
\end{proof}
```

From `eqn:a-another-integral` we see that the values $`a(r)`$ lie in
$`i\R`$ for all $`r\in\R_{\geq0}`$.

```tex
From the identity~\eqref{eqn:a-another-integral} we see that the values $a(r)$ are in $i\R$ for all $r\in\R_{\geq0}$.
```

:::lemma_ "prop:a0" (lean := "MagicFunction.a.SpecialValues.a_zero") (parent := "magic_a_properties")
We have $`a(0) = -\frac{i}{8640}`$.
{uses "prop:a-another-integral"}[]
:::

```tex "prop:a0"
\begin{proposition}\label{prop:a0}\uses{prop:a-another-integral}\lean{MagicFunction.a.SpecialValues.a_zero}\leanok
We have $a(0) = -\frac{i}{8640}$.
\end{proposition}
```

:::proof "prop:a0"
These identities follow immediately from the previous proposition.
:::

```tex "prop:a0" (slot := "proof")
\begin{proof}
These identities follow immediately from the previous proposition.
\end{proof}
```

Now we construct function $`b`$. To this end we consider the function.

```tex
Now we construct function $b$. To this end we consider the function
```

:::definition "def:h" (parent := "magic_psi_construction")
Define
$$`h(z) := 128 \frac{H_3(z) + H_4(z)}{H_2(z)^2}.`
{uses "def:H2-H3-H4"}[]
:::

```tex "def:h"
\begin{definition}\label{def:h}\uses{def:H2-H3-H4}
\begin{equation}\label{eqn: h define}
    h(z) := 128 \frac{H_3(z) + H_4(z)}{H_2(z)^2}.
\end{equation}
\end{definition}
```

It is easy to see that $`h\in M^!_{-2}(\Gamma_0(2))`$. Indeed, first check
that $`h|_{-2}\gamma=h`$ for all $`\gamma\in\Gamma_0(2)`$. Since
$`\Gamma_0(2)`$ is generated by
$`\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)`$ and
$`\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)`$, it suffices to
check invariance under their action, which follows immediately from the
transformation laws of the theta-null forms and `eqn: h define`.
Next analyze the poles of $`h`$. It is known that $`\theta_{10}`$ has no zeros
in the upper half-plane, so $`h`$ has poles only at the cusps. At the cusp
$`i\infty`$, this modular form has Fourier expansion
$$`h(z)\,=\,q^{-1} + 16 - 132 q + 640 q^2 - 2550 q^3+O(q^4).`

```tex
It is easy to see that $h\in M^!_{-2}(\Gamma_0(2))$. Indeed, first we check that $h|_{-2}\gamma=h$
for all $\gamma\in\Gamma_0(2)$. Since the group $\Gamma_0(2)$ is generated by elements
$\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ and $\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$
it suffices to check that $h$ is invariant under their action. This follows immediately
from \eqref{eqn:H2-transform-S}--\eqref{eqn:H4-transform-S} and \eqref{eqn: h define}. Next we analyze the poles of $h$.
It is known \cite[Chapter~I Lemma~4.1]{Mumford} that $\theta_{10}$ has no zeros in the upper-half plane and hence $h$ has poles only at the cusps.
At the cusp $i\infty$ this modular form has the Fourier expansion
\begin{equation}
h(z)\,=\,q^{-1} + 16 - 132 q + 640 q^2 - 2550 q^3+O(q^4).\notag
\end{equation}
```

Let
$`I=\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)`$,
$`T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)`$, and
$`S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)`$.

```tex
Let $I=\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$,
$T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$, and
$S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ be elements of $\Gamma_1$.
```

:::definition "def:psiI-psiT-psiS" (parent := "magic_psi_construction")
Define
$$`\psi_I\,:=\,h-h|_{-2}ST`
$$`\psi_T\,:=\,\psi_I|_{-2}T`
$$`\psi_S\,:=\,\psi_I|_{-2}S.`
{uses "def:h"}[]
:::

```tex "def:psiI-psiT-psiS"
\begin{definition}\label{def:psiI-psiT-psiS}\uses{def:h}
We define the following three functions
\begin{align}
    \psi_I\,:=\,&h-h|_{-2}ST \label{eqn:psiI-define}\\
    \psi_T\,:=\,&\psi_I|_{-2}T \label{eqn:psiT-define}\\
    \psi_S\,:=\,&\psi_I|_{-2}S. \label{eqn:psiS-define}
\end{align}
\end{definition}
```

:::lemma_ "lemma:psi-new" (parent := "magic_psi_construction")
$`\psi_I(z)`$, $`\psi_S(z)`$, and $`\psi_T(z)`$ can be written as
$$`\psi_I(z) = \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}`
$$`\psi_S(z) = -\frac{H_2^3 (2 H_2^2 + 5 H_2 H_4 + 5 H_4^2)}{2 \Delta}`
$$`\psi_T(z) = \frac{H_3^3 (5 H_2^2 - 5 H_2 H_3 + 2 H_3^2)}{2 \Delta}.`
:::

```tex "lemma:psi-new"
\begin{lemma}\label{lemma:psi-new}
    $\psi_I(z), \psi_S(z), \psi_T(z)$ can be written as
    \begin{align}
        \psi_I(z) &= \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}, \label{eqn:psiI-new} \\
        \psi_S(z) &= -\frac{H_2^3 (2 H_2^2 + 5 H_2 H_4 + 5 H_4^2)}{2 \Delta}. \label{eqn:psiS-new} \\
        \psi_T(z) &= \frac{H_3^3 (5 H_2^2 - 5 H_2 H_3 + 2 H_3^2)}{2 \Delta}\label{eqn:psiT-new}
    \end{align}
\end{lemma}
```

:::proof "lemma:psi-new"
By the transformation laws of the theta-null functions,
$$`H_2|_{-2}ST = (-H_4)|_{-2}T = -H_3`
$$`H_3|_{-2}ST = (-H_3)|_{-2}T = -H_4`
$$`H_4|_{-2}ST = (-H_2)|_{-2}T = H_2.`
Using these identities and the level-one/level-two identities, we can rewrite
$`\psi_I(z)`$ as
$$`\psi_I(z) = h(z) - h|_{-2}ST(z)
    = 128 \frac{H_3 + H_4}{H_2^2} - 128 \frac{-H_4 + H_2}{H_3^2}`
$$`= 128 \frac{H_3^2 (H_3 + H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2}
    = 128 \frac{(H_2 + H_4)^2 (H_2 + 2 H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2}`
$$`= 128 \frac{H_4(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2}
    = \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}.`
Applying $`|_{-2}S`$ and $`|_{-2}T`$ to the expression for $`\psi_I`$ proves
the formulas for $`\psi_S`$ and $`\psi_T`$.
:::

```tex "lemma:psi-new" (slot := "proof")
\begin{proof}
By Lemma \ref{lemma:theta-transform-S-T}, we have
\begin{align}
    H_2|_{-2}ST = (-H_4)|_{-2}T = -H_3, \\
    H_3|_{-2}ST = (-H_3)|_{-2}T = -H_4, \\
    H_4|_{-2}ST = (-H_2)|_{-2}T = H_2.
\end{align}
Using these equations and Lemma \ref{lemma:lv1-lv2-identities}, we can rewrite $\psi_I(z)$ as
\begin{align}
    \psi_I(z) &= h(z) - h|_{-2}ST(z) \\
    &= 128 \frac{H_3 + H_4}{H_2^2} - 128 \frac{-H_4 + H_2}{H_3^2} \\
    &= 128 \frac{H_3^2 (H_3 + H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\
    &= 128 \frac{(H_2 + H_4)^2 (H_2 + 2 H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\
    &= 128 \frac{H_4(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2} \\
    &= 128 \frac{H_4^3(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2 H_4^3} \\
    &= \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}.
\end{align}
Applying $|_{-2}S$ and $|_{-2}T$ to the expression of $\psi_I$ proves \eqref{eqn:psiS-new} and \eqref{eqn:psiT-new}.
\end{proof}
```

:::lemma_ "lemma:psiI-psiT-psiS-fourier" (parent := "magic_psi_construction")
The Fourier expansions of these functions are
$$`\psi_I(z)\,=\,q^{-1} + 144 + O(q^{1/2})`
$$`\psi_T(z)\,=\,q^{-1} + 144 + O(q^{1/2}).`
{uses "lemma:psi-new"}[]
:::

```tex "lemma:psiI-psiT-psiS-fourier"
\begin{lemma}\label{lemma:psiI-psiT-psiS-fourier}\uses{lemma:psi-new}
The Fourier expansions of these functions are
\begin{align}
    \psi_I(z)\,=\,&q^{-1} + 144 + O(q^{1/2}) \label{eqn: psi fourier I}\\
    \psi_T(z)\,=\,&q^{-1} + 144 + O(q^{1/2}) \label{eqn: psi fourier T}
\end{align}
\end{lemma}
```

Now we are ready to define $`b`$. Again, the definition here is slightly
different from that in {citet Via2017}[], where all contours are chosen to be
straight lines.

```tex
Now, we are ready to define function $b$.
Again, the definition here is slightly different from that in \cite{Via2017}, where all the contours are chosen to be the straight lines.
```

:::definition "def:b-definition" (parent := "magic_psi_construction")
Define $`b_\rad : \R \to \C`$ by
$$`b_\rad(r) := J_1(r) + J_2(r) + J_3(r) + J_4(r) + J_5(r) + J_6(r)`
where
$$`J_1(r) := \int_{-1}^{-1 + i} \psi_T(z) e^{\pi i r z} \, \dd z`
$$`J_2(r) := \int_{-1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z`
$$`J_3(r) := \int_{1}^{1 + i} \psi_T(z) e^{\pi i r z} \, \dd z`
$$`J_4(r) := \int_{1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z`
$$`J_5(r) := -2 \int_{0}^{i} \psi_I(z) e^{\pi i r z} \, \dd z`
$$`J_6(r) := -2 \int_{i}^{i \infty} \psi_S(z) e^{\pi i r z} \, \dd z.`
Here all contours are straight line segments.
Define $`b : \R^8 \to \C`$ by $`b(x) := b_\rad(\|x\|^2)`$.
{uses "def:psiI-psiT-psiS"}[]
:::

```tex "def:b-definition"
\begin{definition}\label{def:b-definition}\uses{def:psiI-psiT-psiS}
Define $b_\rad : \R \to \C$ by
\begin{equation}
    \label{eqn:b-definition}
    b_\rad(r) := J_1(r) + J_2(r) + J_3(r) + J_4(r) + J_5(r) + J_6(r)
\end{equation}
where for $r \in \R$,
\begin{align}
    J_1(r) &:= \int_{-1}^{-1 + i} \psi_T(z) e^{\pi i r z} \, \dd z, \label{eqn:J1} \\
    J_2(r) &:= \int_{-1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z, \label{eqn:J2} \\
    J_3(r) &:= \int_{1}^{1 + i} \psi_T(z) e^{\pi i r z} \, \dd z, \label{eqn:J3} \\
    J_4(r) &:= \int_{1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z, \label{eqn:J4} \\
    J_5(r) &:= -2 \int_{0}^{i} \psi_I(z) e^{\pi i r z} \, \dd z, \label{eqn:J5} \\
    J_6(r) &:= -2 \int_{i}^{i \infty} \psi_S(z) e^{\pi i r z} \, \dd z. \label{eqn:J6}
\end{align}
Here all the contours are straight line segments.
Then we define $b : \R^8 \to \C$ by $b(x) := b_\rad(\|x\|^2)$.
\end{definition}
```

Now we prove that $`b`$ is a Schwartz function and satisfies
`eqn:b-fourier`. As in the case of $`a(x)`$, we start with an
exponential bound for $`\psi_S(z)`$ and $`\psi_I(z)`$.

```tex
Now we prove that $b$ is a Schwartz function and satisfies condition \eqref{eqn:b-fourier}.
As in the case of $a(x)$, we start with the following exponential bound of $\psi_S(z)$ and $\psi_I(z)$.
```

:::lemma_ "lemma:psi-bound" (parent := "magic_b_properties")
There exist constants $`C_I, C_S, C_T > 0`$ such that
$$`|\psi_I(z)| \le C_I e^{2\pi \Im z}`
$$`|\psi_T(z)| \le C_T e^{2\pi \Im z}`
$$`|\psi_S(z)| \le C_S e^{- \pi \Im z}.`
:::

```tex "lemma:psi-bound"
\begin{lemma}\label{lemma:psi-bound}
    There exist constants $C_I, C_S, C_T > 0$ such that
    \begin{align}
        |\psi_I(z)| &\le C_I e^{2\pi \Im z}, \label{eqn:psiI-bound} \\
        |\psi_T(z)| &\le C_T e^{2\pi \Im z}, \label{eqn:psiT-bound} \\
        |\psi_S(z)| &\le C_S e^{- \pi \Im z} \label{eqn:psiS-bound}
    \end{align}
\end{lemma}
```

:::proof "lemma:psi-bound"
The proof is similar to that of Lemma {uses "cor:phi0-bound"}[] and follows
from Lemma `lemma:mod-div-disc-bound` together with the fact that the
vanishing orders of the numerators of $`\psi_I`$, $`\psi_T`$, and $`\psi_S`$
at infinity are respectively $`0`$, $`0`$, and $`\frac{3}{2}`$.
:::

```tex "lemma:psi-bound" (slot := "proof")
\begin{proof}
    The proof is similar to that of Lemma \ref{cor:phi0-bound}, follows from Lemma \ref{lemma:mod-div-disc-bound} and the fact that the vanishing orders of the numerators of $\psi_I$, $\psi_T$, and $\psi_S$ at infinity are $0$, $0$ (i.e. not cusp forms), and $\frac{3}{2}$ respectively.
\end{proof}
```

:::lemma_ "lemma:bound-J1-J3-J5" (parent := "magic_b_properties")
There exists a constant $`C > 0`$ such that
$$`|J_1(r)|, |J_3(r)|, |J_5(r)| \le C \int_1^{\infty} e^{-\pi s} e^{\pi r / s}\, \dd s.`
:::

```tex "lemma:bound-J1-J3-J5"
\begin{lemma}\label{lemma:bound-J1-J3-J5}
There exist a constant $C > 0$ such that
\begin{align}
    |J_1(r)|, |J_3(r)|, |J_5(r)| &\le C \int_1^{\infty} e^{-\pi s} e^{\pi r / s}\, \dd s.
\end{align}
\end{lemma}
```

:::lemma_ "lemma:bound-J2-J4-J6" (parent := "magic_b_properties")
There exist $`C_1, C_2 > 0`$ such that
$$`|J_2(r)|, |J_4(r)| \le C_1 e^{-\pi r}`
$$`|J_6(r)| \le C_2 \frac{e^{\pi (r + 1)}}{r + 1}.`
:::

```tex "lemma:bound-J2-J4-J6"
\begin{lemma}\label{lemma:bound-J2-J4-J6}
    There exist $C_1, C_2 > 0$ such that
    \begin{align}
        |J_2(r)|, |J_4(r)| &\le C_1 e^{-\pi r} \\
        |J_6(r)| &\le C_2 \frac{e^{\pi (r + 1)}}{r + 1}
    \end{align}
\end{lemma}
```

Combining Lemmas `lemma:bound-J1-J3-J5`,
`lemma:bound-J2-J4-J6`, and
Theorem `thm:smooth-fast-decay-schwartz`, we can prove that $`b(x)`$
is a Schwartz function.

```tex
Combining Lemmas \ref{lemma:bound-J1-J3-J5}, \ref{lemma:bound-J2-J4-J6}, and Theorem \ref{thm:smooth-fast-decay-schwartz}, we can prove that $b(x)$ is a Schwartz function.
```

:::lemma_ "prop:b-schwartz" (lean := "MagicFunction.FourierEigenfunctions.b") (parent := "magic_b_properties")
$`b(x)`$ is a Schwartz function.
{uses "lemma:psi-bound"}[]
:::

```tex "prop:b-schwartz"
\begin{proposition}\label{prop:b-schwartz}\uses{lemma:psi-bound}\lean{MagicFunction.FourierEigenfunctions.b}\leanok
$b(x)$ is a Schwartz function.
\end{proposition}
```

:::proof "prop:b-schwartz"
The proof is similar to that of {uses "prop:a-schwartz"}[].
{uses "lemma:bound-J1-J3-J5"}[]{uses "lemma:bound-J2-J4-J6"}[]{uses "thm:smooth-fast-decay-schwartz"}[]
:::

```tex "prop:b-schwartz" (slot := "proof")
\begin{proof}
\uses{lemma:bound-J1-J3-J5, lemma:bound-J2-J4-J6, thm:smooth-fast-decay-schwartz}
Similar to the proof of \ref{prop:a-schwartz}.
\end{proof}
```

:::lemma_ "prop:b-fourier" (lean := "MagicFunction.b.Fourier.eig_b") (parent := "magic_b_properties")
$`b(x)`$ satisfies equation `eqn:b-fourier`.
{uses "def:b-definition"}[]{uses "lemma:Gaussian-Fourier"}[]{uses "def:psiI-psiT-psiS"}[]{uses "prop:b-schwartz"}[]
:::

```tex "prop:b-fourier"
\begin{proposition}\label{prop:b-fourier}\uses{def:b-definition, lemma:Gaussian-Fourier, def:psiI-psiT-psiS, prop:b-schwartz}\lean{MagicFunction.b.Fourier.eig_b}\leanok
$b(x)$ satisfies \eqref{eqn:b-fourier}.
\end{proposition}
```

:::proof "prop:b-fourier"
We repeat the argument used in the proof of Proposition
{uses "prop:a-fourier"}[]. Using the Gaussian Fourier identity and exchanging
the contour integration in $`z`$ with the Fourier transform in $`x`$, we get
$$`\mathcal{F}(b)(x)= \int\limits_{-1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
        + \int\limits_{1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz`
$$`- 2\,\int\limits_{0}^{i}\psi_I(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
    - 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz.`
With the change of variables $`w=\frac{-1}{z}`$, we arrive at
$$`\mathcal{F}(b)(x)= \int\limits_{1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
        + \int\limits_{-1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw`
$$`- 2\,\int\limits_{i\infty}^{i}\psi_I\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
    - 2\,\int\limits_{i}^{0}\psi_S\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw.`
Now the definitions imply
$$`\psi_T|_{-2}S=-\psi_T`
$$`\psi_I|_{-2}S=\psi_S`
$$`\psi_S|_{-2}S=\psi_I,`
so this becomes
$$`\mathcal{F}(b)(x)= \int\limits_{1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz
        + \int\limits_{-1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz`
$$`+ 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i \|x\|^2 z}\,dz
    + 2\,\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i \|x\|^2 z}\,dw.`
From the definition of $`b`$, we conclude that
$$`\mathcal{F}(b)(x)=-b(x).`
:::

```tex "prop:b-fourier" (slot := "proof")
\begin{proof}
Here, we repeat the arguments used in the proof of Proposition~\ref{prop:a-fourier}.
We use identity~\eqref{eqn:gaussian Fourier} and change contour integration in $z$ and Fourier transform in $x$. Thus we obtain
\begin{align}
    \mathcal{F}(b)(x)= & \int\limits_{-1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
        + \int\limits_{1}^{i}\psi_T(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz \notag \\
    -& 2\,\int\limits_{0}^{i}\psi_I(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz
    - 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,z^{-4}\,e^{\pi i \|x\|^2 (\frac{-1}{z})}\,dz. \notag
\end{align}
We make the change of variables $w=\frac{-1}{z}$ and arrive at
\begin{align}
    \mathcal{F}(b)(x)= & \int\limits_{1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
        + \int\limits_{-1}^{i}\psi_T\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw \notag \\
    -& 2\,\int\limits_{i\infty}^{i}\psi_I\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw
    - 2\,\int\limits_{i}^{0}\psi_S\Big(\frac{-1}{w}\Big)\,w^{2}\,e^{\pi i \|x\|^2 w}\,dw.\notag
\end{align}
Now we observe that the definitions \eqref{eqn:psiI-define}--\eqref{eqn:psiS-define} imply
\begin{align}
    \psi_T|_{-2}S=&-\psi_T \notag \\
    \psi_I|_{-2}S=&\psi_S \notag \\
    \psi_S|_{-2}S=&\psi_I. \notag
\end{align}
Therefore, we arrive at
\begin{align}
    \mathcal{F}(b)(x)= & \int\limits_{1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz
        + \int\limits_{-1}^{i}-\psi_T(z)\,e^{\pi i \|x\|^2 z}\,dz \notag \\
    +& 2\,\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i \|x\|^2 z}\,dz
    + 2\,\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i \|x\|^2 w}\,dw.\notag
\end{align}
Now from~\eqref{eqn:b-definition} we see that
$$ \mathcal{F}(b)(x)=-b(x). $$
\end{proof}
```

Now we regard the radial function $`b`$ as a function on $`\R_{\geq0}`$ and
check that it has double roots at the $`\Lambda_8`$ points.

```tex
Now we regard the radial function $b$ as a function on $\R_{\geq0}$. We check that $b$ has double roots at $\Lambda_8$-points.
```

:::corollary "cor:psiI-near-0-infty" (parent := "magic_b_properties")
We have
$$`\psi_I(it) = O(t^2 e^{\pi/t}) \quad \text{as } t \to 0`
$$`\psi_I(it) = O(e^{2 \pi t}) \quad \text{as } t \to \infty.`
{uses "lemma:psi-bound"}[]{uses "def:psiI-psiT-psiS"}[]
:::

```tex "cor:psiI-near-0-infty"
\begin{corollary}\label{cor:psiI-near-0-infty}\uses{lemma:psi-bound, def:psiI-psiT-psiS}
We have
\begin{align}
    \psi_I(it) &= O(t^2 e^{\pi/t}) \quad \text{as } t \to 0 \label{eqn:psiI-near-0} \\
    \psi_I(it) &= O(e^{2 \pi t}) \quad \text{as } t \to \infty. \label{eqn:psiI-near-infty}
\end{align}
\end{corollary}
```

:::proof "cor:psiI-near-0-infty"
By `eqn:psiS-define`,
$$`\psi_I(it) = (it)^{-2} \psi_S\left(\frac{-1}{it}\right) = -t^{-2} \psi_S\left(\frac{i}{t}\right),`
and combined with `eqn:psiS-bound` this gives `eqn:psiI-near-0`.
Equation `eqn:psiI-near-infty` follows from `lemma:psi-bound`.
:::

```tex "cor:psiI-near-0-infty" (slot := "proof")
\begin{proof}
By \eqref{eqn:psiS-define}, we have
\begin{equation}
    \psi_I(it) = (it)^{-2} \psi_S\left(\frac{-1}{it}\right) = -t^{-2} \psi_S\left(\frac{i}{t}\right).
\end{equation}
and combined with \eqref{eqn:psiS-bound} we get \eqref{eqn:psiI-near-0}.
\eqref{eqn:psiI-near-infty} follows from Lemma \ref{lemma:psi-bound}.
\end{proof}
```

:::lemma_ "prop:b-double-zeros" (parent := "magic_b_properties")
For $`r>\sqrt{2}`$, the function $`b(r)`$ can be expressed as
$$`b(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz.`
{uses "lemma:psiI-psiT-psiS-fourier"}[]{uses "def:psiI-psiT-psiS"}[]{uses "cor:psiI-near-0-infty"}[]{uses "cor:disc-nonvanishing"}[]
:::

```tex "prop:b-double-zeros"
\begin{proposition}\label{prop:b-double-zeros}\uses{lemma:psiI-psiT-psiS-fourier, def:psiI-psiT-psiS, cor:psiI-near-0-infty, cor:disc-nonvanishing}
For $r>\sqrt{2}$ function $b(r)$ can be expressed as
\begin{equation}\label{eqn: b double zeroes}
    b(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz.
\end{equation}
\end{proposition}
```

:::proof "prop:b-double-zeros"
Denote the right-hand side by $`c(r)`$.
By Corollary `cor:psiI-near-0-infty`, the integral converges for
$`r>\sqrt{2}`$. Rewrite it as
$$`c(r)=\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz-2\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz+
\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz.`
From the Fourier expansion of $`\psi_I`$, we know that
$`\psi_I(z)=e^{-2\pi i z}+O(1)`$ as $`\Im(z)\to\infty`$.
Because $`r^2>2`$, we can deform the paths of integration and write
$$`\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz=
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz`
$$`\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz=
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz.`
Hence
$$`c(r)=\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz`
$$`+2\int\limits_{i}^{i\infty}(\psi_T(z)-\psi_I(z))\,e^{\pi i r^2 \,z}\,dz.`
Next, the functions $`\psi_I`$, $`\psi_T`$, and $`\psi_S`$ satisfy
$$`\psi_T+\psi_S=\psi_I.`
Using this identity, we find
$$`c(r)=\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz`
$$`-2\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i r^2 \,z}\,dz=b(r).`
:::

```tex "prop:b-double-zeros" (slot := "proof")
\begin{proof}
We denote the right hand side of~\eqref{eqn: b double zeroes} by $c(r)$.
By Corollary \ref{cor:psiI-near-0-infty}, the integral in~\eqref{eqn: b double zeroes} converges for $r>\sqrt{2}$.
Then we rewrite it in the following way:
$$c(r)=\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz-2\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz+
\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz.$$
From the Fourier expansion~\eqref{eqn: psi fourier I} we know that $\psi_I(z)=e^{-2\pi i z}+O(1)$ as $\Im(z)\to\infty$.
By assumption $r^2>2$, hence we can deform the path of integration and write
\begin{align}
\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz=&
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz\\
\int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz=&
\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz.
\end{align}
We have
\begin{align}
c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\\
&+2\int\limits_{i}^{i\infty}(\psi_T(z)-\psi_I(z))\,e^{\pi i r^2 \,z}\,dz.\nonumber
    \end{align}
Next, we check that the functions $\psi_I,\psi_T$, and $\psi_S$ satisfy the following identity:
\begin{equation}\psi_T+\psi_S=\psi_I.\end{equation}
Indeed, from definitions \eqref{eqn:psiI-define}-\eqref{eqn:psiS-define} we get
\begin{align}\psi_T+\psi_S=&(h-h|_{-2}ST)|_{-2}T+(h-h|_{-2}ST)|_{-2}S\notag\\
=&h|_{-2}T-h|_{-2}ST^2+h|_{-2}S-h|_{-2}STS.\notag\end{align}
Note that $ST^2S$ belongs to $\Gamma_0(2)$. Thus, since $h\in M^!_{-2}\Gamma_0(2)$ we get
$$\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS. $$
Now we observe that $T$ and $STS(ST)^{-1}$ are also in $\Gamma_0(2)$. Therefore,
$$\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS=h|_{-2}-h|ST=\psi_I.$$

Combining this identity with the expression for $c(r)$ we find
\begin{align}c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz
-2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\notag\\
&-2\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i r^2 \,z}\,dz\notag\\
=&b(r).\notag
    \end{align}
\end{proof}
```

At the end of this section we find another integral representation of $`b(r)`$
for $`r\in\R_{\geq0}`$ and compute special values of $`b`$.

```tex
At the end of this section we find another integral representation of $b(r)$ for $r\in\R_{\geq0}$ and compute special values of $b$.
```

:::lemma_ "prop:b-another-integral" (parent := "magic_b_properties")
For $`r\geq0`$ we have
$$`b(r)=4i\,\sin(\pi r^2/2)^2\,\left(\frac{144}{\pi\,r^2}+\frac{1}{\pi\,(r^2-2)}+\int\limits_0^\infty\,\left(\psi_I(it)-144-e^{2\pi t}\right)\,e^{-\pi r^2 t}\,dt\right).`
The integral converges absolutely for all $`r\in\R_{\geq 0}`$.
{uses "prop:b-double-zeros"}[]{uses "lemma:psiI-psiT-psiS-fourier"}[]{uses "def:b-definition"}[]
:::

```tex "prop:b-another-integral"
\begin{proposition}\label{prop:b-another-integral}\uses{prop:b-double-zeros, lemma:psiI-psiT-psiS-fourier, def:b-definition}
For $r\geq0$ we have
\begin{equation}\label{eqn:b-another-integral}b(r)=4i\,\sin(\pi r^2/2)^2\,\left(\frac{144}{\pi\,r^2}+\frac{1}{\pi\,(r^2-2)}+\int\limits_0^\infty\,\left(\psi_I(it)-144-e^{2\pi t}\right)\,e^{-\pi r^2 t}\,dt\right).\end{equation}
The integral converges absolutely for all $r\in\R_{\geq 0}$.
\end{proposition}
```

:::proof "prop:b-another-integral"
The proof is analogous to the proof of Proposition
{uses "prop:a-another-integral"}[].
First suppose that $`r>\sqrt{2}`$. Then by Proposition
`prop:b-double-zeros`,
$$`b(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\psi_I(it)\,e^{-\pi r^2 t}\,dt.`
From the Fourier expansion of $`\psi_I`$ we obtain
$$`\psi_I(it)=e^{2\pi t}+144+O(e^{-\pi t})`
as $`t\to\infty`$. For $`r>\sqrt{2}`$,
$$`\int\limits_0^\infty \left(e^{2\pi t}+144\right)\,e^{-\pi r^2 t}\,dt
=\frac{1}{\pi\,(r^2-2)}+\frac{144}{\pi\,r^2}.`
Therefore the identity holds for $`r>\sqrt{2}`$.

On the other hand, the definition of $`b`$ shows that $`b(r)`$ is analytic in
a neighborhood of $`[0,\infty)`$, and the asymptotic expansion above implies
that the right-hand side is also analytic there. Hence the identity holds on
the whole interval $`[0,\infty)`$.
:::

```tex "prop:b-another-integral" (slot := "proof")
\begin{proof}
The proof is analogous to the proof of Proposition~\ref{prop:a-another-integral}.
First, suppose that $r>\sqrt{2}$. Then by Proposition~\ref{prop:b-double-zeros}
$$b(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\psi_I(it)\,e^{-\pi r^2 t}\,dt. $$
From \eqref{eqn: psi fourier I} we obtain
\begin{equation}
\psi_I(it)=e^{2\pi t}+144+O(e^{-\pi t})\quad\mbox{as}\;t\to\infty.
\end{equation}
For $r>\sqrt{2}$ we have
\begin{equation}
\int\limits_0^\infty \left(e^{2\pi t}+144\right)\,e^{-\pi r^2 t}\,dt
=\frac{1}{\pi\,(r^2-2)}+\frac{144}{\pi\,r^2}.\end{equation}
Therefore, the identity \eqref{eqn:b-another-integral} holds for $r>\sqrt{2}$.

On the other hand, from the definition \eqref{eqn:b-definition} we see that $b(r)$ is analytic in some neighborhood of $[0,\infty)$. The asymptotic expansion \eqref{eqn: psi asymptotic} implies that the right hand side of \eqref{eqn:b-another-integral} is also analytic in some neighborhood of $[0,\infty)$. Hence, the identity \eqref{eqn:b-another-integral} holds on the whole interval $[0,\infty)$. This finishes the proof of the proposition.
\end{proof}
```

From `eqn:b-another-integral` we see that $`b(r)\in i\R`$ for all
$`r\in\R_{\geq 0}`$.

```tex
We see from \eqref{eqn:b-another-integral} that $b(r)\in i\R$ far all $r\in\R_\geq{0}$.
```

:::lemma_ "prop:b0" (lean := "MagicFunction.b.SpecialValues.b_zero") (parent := "magic_b_properties")
We have $`b(0) = 0`$.
{uses "prop:b-another-integral"}[]
:::

```tex "prop:b0"
\begin{proposition}\label{prop:b0}\uses{prop:b-another-integral}\lean{MagicFunction.b.SpecialValues.b_zero}\leanok
We have $b(0) = 0$.
\end{proposition}
```

:::proof "prop:b0"
These identities follow immediately from the previous proposition.
:::

```tex "prop:b0" (slot := "proof")
\begin{proof}
    These identities follow immediately from the previous proposition.
\end{proof}
```
