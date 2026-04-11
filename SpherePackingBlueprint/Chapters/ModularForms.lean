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


#doc (Manual) "Modular Forms" =>


:::group "modular_forms_setup"
Congruence groups, slash operators, and modular forms.
:::

:::group "eisenstein_discriminant"
Eisenstein series, the discriminant form, and positivity/nonvanishing tools.
:::

:::group "theta_and_identities"
Theta constants and identities used in the magic-function construction.
:::

:::group "serre_derivative"
Serre derivative identities and differential inequalities.
:::

In this section, we recall and develop some theory of (quasi)modular forms.

```tex
In this section, we recall and develop some theory of (quasi)modular forms.
```

Let $`\mathbb{H}` be the upper half-plane
$`\{z \in \mathbb{C} \mid \Im(z) > 0\}`.

```tex
Let $\h$ be the upper half-plane $\{z\in\C\mid\Im(z)>0\}$.
```

:::lemma_ "def:Gamma-1-Action" (parent := "modular_forms_setup")
The modular group $`\Gamma_1:=\mathrm{SL}_2(\mathbb{Z})` acts on
$`\mathbb{H}` by linear fractional transformations
$$`\begin{pmatrix}a&b\\c&d\end{pmatrix}z:=\frac{az+b}{cz+d}.`
:::

```tex "def:Gamma-1-Action"
\begin{lemma}\label{def:Gamma-1-Action}\leanok
    The modular group $\Gamma_1:=\mathrm{SL}_2(\Z)$ acts on $\h$ by linear fractional transformations
$$\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)z:=\frac{az+b}{cz+d}.$$
\end{lemma}
```

:::proof "def:Gamma-1-Action"
:::

```tex "def:Gamma-1-Action" (slot := "proof")
\begin{proof}
    \leanok
\end{proof}
```

:::definition "def:level-N-princ-cong-subgp" (parent := "modular_forms_setup")
The level $`N` principal congruence subgroup of $`\Gamma_1` is
$$`\Gamma(N):=\left\{\left.\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_1\right|\begin{pmatrix}a&b\\c&d\end{pmatrix}\equiv\begin{pmatrix}1&0\\0&1\end{pmatrix}\; \mathrm{mod}\; N\right\}.`
:::

```tex "def:level-N-princ-cong-subgp"
\begin{definition}\label{def:level-N-princ-cong-subgp}\leanok
The \emph{level $N$ principal congruence subgroup} of $\Gamma_1$ is
$$
    \Gamma(N):=\left\{\left.\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\Gamma_1\right|\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\equiv\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)\;\mathrm{mod}\;N\right\}.
$$
\end{definition}
```

:::definition "def:congruence-subgroup" (parent := "modular_forms_setup")
A subgroup $`\Gamma \subset \Gamma_1` is a congruence subgroup if
$`\Gamma(N) \subset \Gamma` for some $`N \in \mathbb{N}`.
Uses {uses "def:level-N-princ-cong-subgp"}[].
:::

```tex "def:congruence-subgroup"
\begin{definition}\label{def:congruence-subgroup}\uses{def:level-N-princ-cong-subgp}\leanok
    A subgroup $\Gamma\subset\Gamma_1$ is called a \emph{congruence subgroup} if $\Gamma(N)\subset\Gamma$ for some $N\in\N$.
\end{definition}
```

:::definition "def:Gamma-generators" (lean := "ModularGroup.S,ModularGroup.T,α,β") (parent := "modular_forms_setup")
Define the matrices
$$`S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \Gamma_1`
$$`T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \in \Gamma_1`
$$`\alpha = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1`
$$`\beta = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1.`
It is easily verifiable that $`\alpha = T^2` and
$`\beta = -S\alpha^{-1}S = -ST^{-2}S`.
Uses {uses "def:level-N-princ-cong-subgp"}[].
:::

```tex "def:Gamma-generators"
\begin{definition}\label{def:Gamma-generators}\uses{def:level-N-princ-cong-subgp}\lean{ModularGroup.S,ModularGroup.T,α,β}\leanok
  Define the matrices

  \[
    S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \Gamma_1,
    T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \in \Gamma_1,
    \alpha = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1,
    \beta = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1.
  \]

  It is easily verifiable that $\alpha = T^2$ and $\beta = -S\alpha^{-1}S = -ST^{-2}S$.
\end{definition}
```

:::lemma_ "lemma:Gamma-1-generators" (lean := "SL2Z_generate") (parent := "modular_forms_setup")
We have $`\Gamma(1) = \langle S, T, -I \rangle`.
Uses {uses "def:Gamma-generators"}[].
:::

```tex "lemma:Gamma-1-generators"
\begin{lemma}\label{lemma:Gamma-1-generators}\uses{def:Gamma-generators}\lean{SL2Z_generate}\leanok
  We have $\Gamma(1) = \langle S, T, -I \rangle$.
\end{lemma}
```

:::proof "lemma:Gamma-1-generators"
See Exercise `1.1.1` in {citet first.course}[].
:::

```tex "lemma:Gamma-1-generators" (slot := "proof")
\begin{proof}
    \leanok
  See~\cite[Exercise 1.1.1]{first course}.
\end{proof}
```

:::lemma_ "lemma:Gamma-2-generators" (lean := "Γ2_generate") (parent := "modular_forms_setup")
We have $`\Gamma(2) = \langle \alpha, \beta, -I \rangle`.
Uses {uses "def:Gamma-generators"}[].
:::

```tex "lemma:Gamma-2-generators"
\begin{lemma}\label{lemma:Gamma-2-generators}\uses{def:Gamma-generators}\lean{Γ2_generate}\leanok
  We have $\Gamma(2) = \langle \alpha, \beta, -I \rangle$.
\end{lemma}
```

:::proof "lemma:Gamma-2-generators"
See Exercise `1.2.4` in {citet first.course}[].
:::

```tex "lemma:Gamma-2-generators" (slot := "proof")
\begin{proof}
    \leanok
    See~\cite[Exercise 1.2.4]{first course}.
\end{proof}
```

Let $`z\in\mathbb{H}`, $`k\in\mathbb{Z}`, and
$`\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\mathrm{SL}_2(\mathbb{Z})`.
We omit many of the proofs below when they exist in Mathlib already.

```tex
Let $z\in\h$, $k\in\Z$, and $\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\mathrm{SL}_2(\Z)$. We omit many of the proofs below when they exist in Mathlib already.
```

:::definition "def:automorphy-factor" (lean := "UpperHalfPlane.denom") (parent := "modular_forms_setup")
The automorphy factor of weight $`k` is defined as
$$`j_k(z,\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)):=(cz+d)^{-k}.`
:::

```tex "def:automorphy-factor"
\begin{definition}\label{def:automorphy-factor}\leanok \lean{UpperHalfPlane.denom}
    The \emph{automorphy factor} of weight $k$ is defined as
$$j_k(z,\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)):=(cz+d)^{-k}.$$
\end{definition}
```

:::lemma_ "lemma:automorphy-factor-chain-rule" (lean := "UpperHalfPlane.denom_cocycle") (parent := "modular_forms_setup")
The automorphy factor satisfies the chain rule
$$`j_k(z,\gamma_1\gamma_2)=j_k(z,\gamma_1)\,j_k(\gamma_2z,\gamma_1).`
Uses {uses "def:automorphy-factor"}[].
:::

```tex "lemma:automorphy-factor-chain-rule"
\begin{lemma}\label{lemma:automorphy-factor-chain-rule}\uses{def:automorphy-factor}\leanok \lean{UpperHalfPlane.denom_cocycle}
    The automorphy factor satisfies the \emph{chain rule}
$$j_k(z,\gamma_1\gamma_2)=j_k(z,\gamma_1)\,j_k(\gamma_2z,\gamma_1). $$
\end{lemma}
```

:::proof "lemma:automorphy-factor-chain-rule"
:::

```tex "lemma:automorphy-factor-chain-rule" (slot := "proof")
\begin{proof}
    \leanok
\end{proof}
```

:::definition "def:slash-operator" (parent := "modular_forms_setup")
Let $`F` be a function on $`\mathbb{H}` and
$`\gamma \in \mathrm{SL}_2(\mathbb{Z})`.
Then the slash operator acts on $`F` by
$$`(F|_k\gamma)(z):=j_k(z,\gamma)\,F(\gamma z).`
Uses {uses "def:automorphy-factor"}[] and {uses "def:Gamma-1-Action"}[].
:::

```tex "def:slash-operator"
\begin{definition}\label{def:slash-operator}\uses{def:automorphy-factor, def:Gamma-1-Action}\leanok
    Let $F$ be a function on $\h$ and $\gamma\in\mathrm{SL}_2(\Z)$. Then the \emph{slash operator} acts on $F$ by
$$(F|_k\gamma)(z):=j_k(z,\gamma)\,F(\gamma z). $$
\end{definition}
```

:::lemma_ "lemma:slash-operator-chain-rule" (lean := "SlashAction.slash_mul") (parent := "modular_forms_setup")
The chain rule implies
$$`F|_k\gamma_1\gamma_2=(F|_k\gamma_1)|_k\gamma_2.`
Uses {uses "lemma:automorphy-factor-chain-rule"}[].
:::

```tex "lemma:slash-operator-chain-rule"
\begin{lemma}\label{lemma:slash-operator-chain-rule}\uses{lemma:automorphy-factor-chain-rule}\lean{SlashAction.slash_mul}\leanok
  The chain rule implies $$F|_k\gamma_1\gamma_2=(F|_k\gamma_1)|_k\gamma_2.$$
\end{lemma}
```

:::proof "lemma:slash-operator-chain-rule"
:::

```tex "lemma:slash-operator-chain-rule" (slot := "proof")
\begin{proof}
    \leanok
\end{proof}
```

:::lemma_ "lemma:slash-negI-even-weight" (lean := "modular_slash_negI_of_even") (parent := "modular_forms_setup")
For even $`k`, $`F|_{k}(-I) = F`.
Uses {uses "def:slash-operator"}[].
:::

```tex "lemma:slash-negI-even-weight"
\begin{lemma}\label{lemma:slash-negI-even-weight}\uses{def:slash-operator}\lean{modular_slash_negI_of_even}\leanok
   For even $k$, $F|_{k}(-I) = F$.
\end{lemma}
```

:::proof "lemma:slash-negI-even-weight"
Follows from the definition of the slash operator:
$`(F|_{k}(-I))(z) = (-1)^{-k}F((-I)z) = F(z)`.
:::

```tex "lemma:slash-negI-even-weight" (slot := "proof")
\begin{proof}
    \leanok
Follows from the definition of the slash operator:
$(F|_{k}(-I))(z) = (-1)^{-k}F((-I)z) = F(z)$.
\end{proof}
```

:::definition "def:Mk" (parent := "modular_forms_setup")
Let $`\Gamma` be a subgroup of $`\mathrm{SL}_2(\mathbb{Z})`.
A modular form of level $`\Gamma` and weight $`k \in \mathbb{Z}` is a
function $`f : \mathbb{H} \to \mathbb{C}` such that:
1. for all $`\gamma \in \Gamma`, we have $`f\mid_k \gamma = f`
2. $`f` is holomorphic on $`\mathbb{H}`
3. for all $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`, there exist
   $`A, B \in \mathbb{R}` such that for all $`z \in \mathbb{H}` with
   $`A \le \mathrm{Im}(z)`, we have $`|(f \mid_k \gamma) (z) |\le B`.
This defines a complex vector space denoted by $`M_k(\Gamma)`.
Uses {uses "def:congruence-subgroup"}[].
:::

```tex "def:Mk"
\begin{definition}\label{def:Mk}\uses{def:congruence-subgroup}\lean{ModularForm}\leanok
	Let  $\Gamma$ denote a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, then a modular form  of level $\Gamma$ and weight $k \in \mathbb{Z}$ is a function $f : \mathbb{H} \to \mathbb{C}$ such that:
	\begin{enumerate}
		\item For all $\gamma \in \Gamma$ we have $f\mid_k \gamma = f$  (such functions are called slash invariant).
		\item $f$ is holomorphic on $\mathbb{H}$.
		\item For all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, there exist $A, B \in \mathbb{R}$ such that for all $z \in \mathbb{H}$, with $ A \le \mathrm{Im}(z)$, we have $|(f \mid_k \gamma) (z) |\le B$. Here $| - |$ denotes the standard complex absolute value.
	\end{enumerate}
    This defines a complex vector space which we denote by $M_{k}(\Gamma)$.
\end{definition}
```

:::definition "def:Ek" (lean := "ModularForm.eisensteinSeries_MF") (parent := "eisenstein_discriminant")
For an even integer $`k\geq 4` define the weight-$`k` Eisenstein series by
$$`E_k(z):=\frac{1}{2}\sum_{(c,d)\in\Z^2, (c,d)=1}(cz+d)^{-k}.`
:::

```tex "def:Ek"
\begin{definition}\label{def:Ek} \lean{ModularForm.eisensteinSeries_MF }
For an even integer $k\geq 4$ we define the \emph{weight $k$ Eisenstein series} as
\begin{equation}\label{eqn:Ek-definition}
E_k(z):=\frac{1}{2}\sum_{(c,d)\in\Z^2, (c,d)=1}(cz+d)^{-k}.\end{equation}
\end{definition}
```

:::lemma_ "lemma:Ek-is-modular-form" (lean := "EisensteinSeries.eisensteinSeries_SIF") (parent := "eisenstein_discriminant")
For all $`k`, $`E_k\in M_k(\Gamma_1)`.
Especially, we have
$$`E_k \left(-\frac{1}{z}\right) = z^k E_k(z).`
Uses {uses "def:Mk"}[] and {uses "def:Ek"}[].
:::

```tex "lemma:Ek-is-modular-form"
\begin{lemma}\label{lemma:Ek-is-modular-form}\uses{def:Mk, def:Ek}\lean{EisensteinSeries.eisensteinSeries_SIF}
For all $k$, $E_k\in M_k(\Gamma_1)$.
Especially, we have
\begin{equation}\label{eqn:Ek-trans-S}
    E_k \left(-\frac{1}{z}\right) = z^k E_k(z).
\end{equation}
\end{lemma}
```

:::proof "lemma:Ek-is-modular-form"
This follows from the fact that the sum converges absolutely.
Applying the slash operator with
$`\gamma = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)`
gives `eqn:Ek-trans-S`.
:::

```tex "lemma:Ek-is-modular-form" (slot := "proof")
\begin{proof}
    \leanok
This follows from the fact that the sum converges absolutely.
Now apply slash operator with $\gamma = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)$ gives \eqref{eqn:Ek-trans-S}.
\end{proof}
```

:::lemma_ "lemma:mod_form_poly_growth" (parent := "eisenstein_discriminant")
Let $`\Gamma` be a finite-index subgroup of $`\mathrm{SL}_2(\mathbb{Z})`
and let $`f \in \mathcal{M}_k(\Gamma)` be a modular form of weight $`k`.
Then the Fourier coefficients $`a_n(f)` have polynomial growth, i.e.
$`|a_n(f)| = O(n^k)`.
:::

```tex "lemma:mod_form_poly_growth"
\begin{lemma}\label{lemma:mod_form_poly_growth}\leanok : Let $\Gamma$ be a finite index subgroup of $\mathrm{SL}_2(\Z)$ and $f \in \mathcal{M}_k(\Gamma)$ be a modular form of weight $k$. Then the Fourier coefficients $a_n(f)$ has a polynomial growth, i.e. $|a_n(f)| = O(n^k)$.
\end{lemma}
```

:::proof "lemma:mod_form_poly_growth"
Note that the assumption on polynomial growth holds when $`f` is a
holomorphic modular form, where the proof can be found in {citet Serre73}[] for
the case of level-one modular forms. This has been done in Lean 4 by David
Loeffler.
:::

```tex "lemma:mod_form_poly_growth" (slot := "proof")
\begin{proof}\leanok
Note that the assumption on the polynomial growth holds when $f$ is a holomorphic modular form, where the proof can be found in \cite[p. 94]{Serre73} for the case of level 1 modular forms. This has been done in Lean 4 by David Loeffler.
\end{proof}
```

:::lemma_ "lemma:Ek-Fourier" (lean := "E_k_q_expansion") (parent := "eisenstein_discriminant")
The Eisenstein series possesses the Fourier expansion
$$`E_k(z)=1+\frac{2}{\zeta(1-k)}\sum_{n=1}^\infty \sigma_{k-1}(n)\,e^{2\pi i z},`
where $`\sigma_{k-1}(n)=\sum_{d|n} d^{k-1}`. In particular,
$$`E_4(z)= 1+240\sum_{n=1}^\infty \sigma_3(n)\,e^{2\pi i n z}`
$$`E_6(z)= 1-504\sum_{n=1}^\infty \sigma_5(n)\,e^{2\pi i n z}.`
Uses {uses "def:Ek"}[].
:::

```tex "lemma:Ek-Fourier"
\begin{lemma}\label{lemma:Ek-Fourier}\uses{def:Ek}\lean{E_k_q_expansion}\leanok
The Eisenstein series possesses the Fourier expansion
\begin{equation}\label{eqn:Ek-Fourier}E_k(z)=1+\frac{2}{\zeta(1-k)}\sum_{n=1}^\infty \sigma_{k-1}(n)\,e^{2\pi i z}, \end{equation}
where $\sigma_{k-1}(n)\,=\,\sum_{d|n} d^{k-1}$. In particular, we have
\begin{align}
  E_4(z)\,=\,& 1+240\sum_{n=1}^\infty \sigma_3(n)\,e^{2\pi i n z} \notag \\
  E_6(z)\,=\,& 1-504\sum_{n=1}^\infty \sigma_5(n)\,e^{2\pi i n z}. \notag
\end{align}
\end{lemma}
```

:::proof "lemma:Ek-Fourier"
:::

```tex "lemma:Ek-Fourier" (slot := "proof")
\begin{proof}
\leanok
\end{proof}
```

:::definition "def:E2" (lean := "E₂_eq") (parent := "eisenstein_discriminant")
Set
$$`E_2(z):= 1-24\sum_{n=1}^\infty \sigma_1(n)\,e^{2\pi i n z}.`
:::

```tex "def:E2"
\begin{definition}\label{def:E2}\lean{E₂_eq}\leanok
We set
\begin{equation}\label{eqn:E2}
    E_2(z):= 1-24\sum_{n=1}^\infty \sigma_1(n)\,e^{2\pi i n z}.
\end{equation}
\end{definition}
```

:::lemma_ "lemma:E2-transform-S" (lean := "E₂_transform") (parent := "eisenstein_discriminant")
This function is not modular; however, it satisfies
$$`z^{-2}\,E_2\left(-\frac{1}{z}\right) = E_2(z) -\frac{6i}{\pi}\, \frac{1}{z}.`
Uses {uses "def:E2"}[].
:::

```tex "lemma:E2-transform-S"
\begin{lemma}\label{lemma:E2-transform-S}\uses{def:E2}\leanok\lean{E₂_transform}
This function is not modular, however it satisfies
\begin{equation}\label{eqn:E2-S-transform}
    z^{-2}\,E_2\left(-\frac{1}{z}\right) = E_2(z) -\frac{6i}{\pi}\, \frac{1}{z}.
\end{equation}
\end{lemma}
```

:::proof "lemma:E2-transform-S"
This is Exercise `1.2.8` in {citet first.course}[].
:::

```tex "lemma:E2-transform-S" (slot := "proof")
\begin{proof}\leanok
This is exercise 1.2.8 of \cite{first course}.
\end{proof}
```

:::lemma_ "lemma:E2-transform-general" (lean := "G₂_transform") (parent := "eisenstein_discriminant")
We have
$$`(cz + d)^{-2} E_2\left(\frac{az + b}{cx + d}\right) = E_2(z) - \frac{6ic}{\pi (cz + d)}, \quad \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_{2}(\mathbb{Z}).`
Uses {uses "lemma:E2-transform-S"}[] and {uses "def:E2"}[].
:::

```tex "lemma:E2-transform-general"
\begin{lemma}\label{lemma:E2-transform-general}\leanok\lean{G₂_transform}\uses{lemma:E2-transform-S, def:E2}
\begin{equation}\label{eqn:E2-transform-general}
(cz + d)^{-2} E_2\left(\frac{az + b}{cx + d}\right) = E_2(z) - \frac{6ic}{\pi (cz + d)}, \quad \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_{2}(\mathbb{Z}).
\end{equation}
\end{lemma}
```

:::proof "lemma:E2-transform-general"
Use the fact that $`\mathrm{SL}_2(\mathbb{Z})` is generated by $`S` and
$`T`. Then `eqn:E2-transform-general` follows from
`eqn:E2-S-transform` together with $`E_2|_T = E_2`.
:::

```tex "lemma:E2-transform-general" (slot := "proof")
\begin{proof}
    \leanok
    Use the fact that $\mathrm{SL}_2(\mathbb{Z})$ is generated by $S$ and $T$.
    Then \eqref{eqn:E2-transform-general} follows from \eqref{eqn:E2-S-transform} and $E_2|_T = E_2$.
\end{proof}
```

:::definition "def:dedekind_eta" (lean := "η") (parent := "eisenstein_discriminant")
The Dedekind eta function is defined as
$$`\eta(z) = q^{1/24} \prod_{n \ge 1} (1 - q^n)`
where $`q = e^{2\pi i z}`.
:::

```tex "def:dedekind_eta"
\begin{definition}\label{def:dedekind_eta}\leanok \lean{η}
The Dedekind eta function is defined as
$$
    \eta(z) = q^{1/24} \prod_{n \ge 1} (1 - q^n)
$$
where $q = e^{2\pi i z}$.
\end{definition}
```

:::lemma_ "lemma:dedekind_eta_transformation" (lean := "eta_equality") (parent := "eisenstein_discriminant")
The Dedekind eta function transforms as
$$`\eta\left(-\frac{1}{z}\right) = \sqrt{-iz} \eta(z).`
Uses {uses "def:dedekind_eta"}[].
:::

```tex "lemma:dedekind_eta_transformation"
\begin{lemma}\label{lemma:dedekind_eta_transformation}\lean{eta_equality}\uses{def:dedekind_eta}
The Dedekind eta function transforms as
$$
    \eta\left(-\frac{1}{z}\right) = \sqrt{-iz} \eta(z).
$$
\end{lemma}
```

:::proof "lemma:dedekind_eta_transformation"
Consider the logarithmic derivative of $`\eta`, which is equal to
$`\frac{\pi i}{12} E_2`. The result then follows from the transformation of
$`E_2`. See {citet first.course}[], Proposition `1.2.5`.
:::

```tex "lemma:dedekind_eta_transformation" (slot := "proof")
\begin{proof}
    \leanok
    Consider the logarithmic derivative of $\eta$, which one can easily see is equal to $\frac{\pi i}{12} E_2$.
    The result then follows from the transformation of $E_2$.

    See \cite[proposition 1.2.5]{first course}.
\end{proof}
```

:::definition "def:disc-definition" (lean := "Δ") (parent := "eisenstein_discriminant")
The discriminant form $`\Delta(z)` is given by
$$`\Delta(z) = e^{2 \pi i z} \prod_{n \ge 1} (1 - e^{2 \pi i n z})^{24}.`
Uses {uses "def:dedekind_eta"}[].
:::

```tex "def:disc-definition"
\begin{definition}\label{def:disc-definition}\lean{Δ}\leanok\uses{def:dedekind_eta}
The \emph{discriminant form} $\Delta(z)$ is given by
\begin{equation}\label{eqn:disc-definition}
\Delta(z) = e^{2 \pi i z} \prod_{n \ge 1} (1 - e^{2 \pi i n z})^{24}.
\end{equation}
\end{definition}
```

:::lemma_ "lemma:disc-cuspform" (lean := "Delta") (parent := "eisenstein_discriminant")
$`\Delta(z) \in M_{12}(\Gamma_1)`.
Especially,
$$`\Delta\left(-\frac{1}{z}\right) = z^{12} \Delta(z).`
Also, it vanishes at the unique cusp, i.e. it is a cusp form of level
$`\Gamma_1` and weight $`12`.
Uses {uses "def:disc-definition"}[] and {uses "lemma:dedekind_eta_transformation"}[].
:::

```tex "lemma:disc-cuspform"
\begin{lemma}\label{lemma:disc-cuspform}\uses{def:disc-definition, lemma:dedekind_eta_transformation}\leanok\lean{Delta}
$\Delta(z) \in M_{12}(\Gamma_1)$.
Especially, we have
\begin{equation}\label{eqn:disc-trans-S}
    \Delta\left(-\frac{1}{z}\right) = z^{12} \Delta(z).
\end{equation}
Also, it vanishes at the unique cusp, i.e. it is a cusp form of level $\Gamma_1$ and weight $12$.
\end{lemma}
```

:::proof "lemma:disc-cuspform"
Invariance under translation is clear from the definition, so it remains only
to check the transformation under $`S`. Since $`\eta^{24} = \Delta` and
{uses "lemma:dedekind_eta_transformation"}[] gives
$`\eta(-1/z) = \sqrt{-iz} \eta(z)`,
we obtain $`\Delta(-1/z) = z^{12}\Delta(z)`.
:::

```tex "lemma:disc-cuspform" (slot := "proof")
\begin{proof}
    \leanok
    The fact that it is invariant under translation is clear from the definition, so we only need to check transformation under $S$. Now, note that $\eta^{24} = \Delta$, and from \ref{lemma:dedekind_eta_transformation} we have $\eta(-1/z) = \sqrt{-iz} \eta(z)$, so $\Delta(-1/z) = z^{12} \Delta(z)$ as required.
\end{proof}
```

:::lemma_ "lemma:disc-E4E6" (lean := "Delta_E4_eqn") (parent := "eisenstein_discriminant")
We have
$$`\Delta(z) = (E_4^3-E_6^2)/1728.`
Uses {uses "def:disc-definition"}[].
:::

```tex "lemma:disc-E4E6"
\begin{lemma}\label{lemma:disc-E4E6}\uses{def:disc-definition}\lean{Delta_E4_eqn}\leanok
We have
\begin{equation}
\Delta(z) = (E_4^3-E_6^2)/1728.
\end{equation}
\end{lemma}
```

:::proof "lemma:disc-E4E6"
We only need to show that the right-hand side is a cusp form, since dividing it
by $`\Delta` would give a modular form of weight $`0` and hence a constant.
To check that it is a cusp form, we look at the $`q`-expansions of $`E_4` and
$`E_6` and verify directly that the first term vanishes.
:::

```tex "lemma:disc-E4E6" (slot := "proof")
\begin{proof}\leanok
    We only need to show its a cuspform, since once we have this, dividing the rhs by $\Delta$ would give a modular form of weight $0$ which is a constant, and so we can determine the constant easily.

    To check its a cuspform, we just look at  the $q$-expansions of $E_4$ and $E_6$ and prove directly that the first term vanishes.
\end{proof}
```

:::corollary "cor:disc-pos" (lean := "Delta_imag_axis_pos") (parent := "eisenstein_discriminant")
$`\Delta(it) > 0` for all $`t > 0`.
Uses {uses "def:disc-definition"}[].
:::

```tex "cor:disc-pos"
\begin{corollary}\label{cor:disc-pos}\uses{def:disc-definition}\lean{Delta_imag_axis_pos}\leanok
$\Delta(it) > 0$ for all $t > 0$.
\end{corollary}
```

:::proof "cor:disc-pos"
By {uses "def:disc-definition"}[],
$$`\Delta(it) = e^{-2 \pi t} \prod_{n \ge 1} (1 - e^{-2 \pi n t})^{24} > 0.`
:::

```tex "cor:disc-pos" (slot := "proof")
\begin{proof}\leanok
By \ref{def:disc-definition}, we have
$$
\Delta(it) = e^{-2 \pi t} \prod_{n \ge 1} (1 - e^{-2 \pi n t})^{24} > 0.
$$
\end{proof}
```

:::corollary "cor:disc-nonvanishing" (lean := "Δ_ne_zero") (parent := "eisenstein_discriminant")
$`\Delta(z) \neq 0` for all $`z \in \mathfrak{H}`.
Uses {uses "def:disc-definition"}[].
:::

```tex "cor:disc-nonvanishing"
\begin{corollary}\label{cor:disc-nonvanishing}\uses{def:disc-definition}\leanok\lean{Δ_ne_zero}
$\Delta(z) \neq 0$ for all $z \in \h$.
\end{corollary}
```

:::proof "cor:disc-nonvanishing"
This follows from the product formula.
:::

```tex "cor:disc-nonvanishing" (slot := "proof")
\begin{proof}
    \leanok
This follows from the product formula.
\end{proof}
```

:::theorem "thm:nonpos_wt" (lean := "ModularFormClass.levelOne_neg_weight_eq_zero, ModularForm.levelOne_weight_zero_rank_one") (parent := "eisenstein_discriminant")
Let $`k \in \mathbb{Z}` with $`k < 0`.
Then $`M_k(\Gamma_1) = \{0\}` and moreover
$`\dim M_0(\Gamma(1)) = 1`.
Uses {uses "def:Mk"}[].
:::

```tex "thm:nonpos_wt"
\begin{theorem}\label{thm:nonpos_wt}\uses{def:Mk}\lean{ModularFormClass.levelOne_neg_weight_eq_zero, ModularForm.levelOne_weight_zero_rank_one}\leanok
    Let $k \in \Z$ with $k < 0$. Then $M_k(\Gamma_1) = \{0\}$ and moreover $\dim M_0(\Gamma(1)) = 1$.
\end{theorem}
```

:::proof "thm:nonpos_wt"
The proof makes use of the maximum modulus principle. Since this is already
formalized, we skip the details here, but see the Lean proof for them.
:::

```tex "thm:nonpos_wt" (slot := "proof")
\begin{proof}
    \leanok
    The proof makes use of the maximum modulus principle, as its already been formalised we skip the details here but see the lean proof for details.
\end{proof}
```

:::theorem "thm:lvl1_dims" (lean := "ModularForm.dimension_level_one") (parent := "eisenstein_discriminant")
Let $`k \in \Z` with $`k \ge 0` and even. Then
$`\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor` if
$`k \equiv 2 \mod 12`, and
$`\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor + 1` if
$`k \not\equiv 2 \mod 12`.
Uses {uses "def:Mk"}[], {uses "lemma:disc-E4E6"}[], and {uses "def:disc-definition"}[].
:::

```tex "thm:lvl1_dims"
\begin{theorem}\label{thm:lvl1_dims}\uses{def:Mk, lemma:disc-E4E6, def:disc-definition}\lean{ModularForm.dimension_level_one}\leanok
    Let $k \in \Z$ with $k \ge 0$ and even. Then $\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor $ if $k \equiv 2 \mod 12$ and $\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor + 1$ if $k \not\equiv 2 \mod 12$.
\end{theorem}
```

:::proof "thm:lvl1_dims"
First note that for $`2 < k` we have
$`\dim(M_k(\Gamma_1)) = 1 + \dim S_k(\Gamma_1)`.
This follows because the Eisenstein series $`E_k` lies in $`M_k`, so after
scaling appropriately, any non-cusp form $`f \in M_k` satisfies
$`f - aE_k \in S_k` for some $`a`.
/- source paragraph break -/
Next, $`S_k(\Gamma_1)` is isomorphic to $`M_{k-12}(\Gamma_1)`, since for
$`f \in S_k`, the quotient $`f/\Delta` is a modular form of weight
$`k-12`. Here it is essential that $`f` is cuspidal, so that dividing by
$`\Delta` preserves modularity.
/- source paragraph break -/
Thus it remains to know the dimensions of $`M_k(\Gamma_1)` for
$`0 \le k \le 12`. For $`k = 0` we have
$`\dim M_0(\Gamma_1) = 1` by {uses "thm:nonpos_wt"}[].
For $`k = 4`, any cusp form $`f` of weight $`4` would give
$`f/\Delta` of negative weight, hence $`f=0`; similarly for
$`k = 6, 8, 10`.
For $`k=12` we have $`\dim S_{12}(\Gamma_1) = 1` since the discriminant
form is a cusp form of weight $`12` and any other cusp form of weight $`12`
is a scalar multiple of $`\Delta`. Hence
$`\dim M_{12}(\Gamma_1) = 2`.
/- source paragraph break -/
Finally, we need to check that $`\dim M_2(\Gamma_1) = 0`.
There can be no cusp forms here by the same argument as above, so suppose
$`f` is a non-cuspidal modular form of weight $`2`.
Then $`f^2` is a non-cuspidal form of weight $`4`, so
$`f^2 = aE_4`, with $`a=a_0(f)^2`.
Similarly, $`f^3 = a_0(f)^3 E_6`.
Taking powers to obtain weight-$`12` forms yields
$`a_0(f)^6(E_4^3 - E_6^2) = 0 = 1728 a_0(f)^6 \Delta`,
but $`a_0(f) \ne 0` since $`f` is not cuspidal, contradicting the
nonvanishing of $`\Delta`.
:::

```tex "thm:lvl1_dims" (slot := "proof")
\begin{proof}
\leanok
First we note that for $2 < k$ we have $\dim(M_k(\Gamma_1)) = 1 + \dim S_k(\Gamma_1)$. This follows since we know the $E_k$ are in $M_k$ so by scaling appropriately, any non-cuspform $f \in M_k$ we would have $f - a E_k \in S_k$ for some $a$.

Next, note that  $S_k(\Gamma_1)$ is isomorphic to $M_{k-12}(\Gamma_1)$, since if $f \in S_k$ then $f/ \Delta$ is now a modular form (using the product expansion of $\Delta$ and its non-vanishing on $\mathfrak{H}$) of weight $k-12$. Note its important that $f$ is a cuspform so that the quotient by $\Delta$ is a modular form.

So we only need to know the dimensions of $M_k(\Gamma_1)$ for $0 \le k \le 12$. For $k = 0$ we have $\dim M_0(\Gamma_1) = 1$ by \Cref{thm:nonpos_wt}.  For $k = 4$ we have $\dim M_4(\Gamma_1) = 1$ since if there was a cuspform $f$ of weight $4$ then $f/ \Delta$ would be a modular form of negative weight, i.e. zero, so $f=0$. Similarly for $k=6,8,10$. For $k=12$ we have $\dim S_{12}(\Gamma_1) = 1$ since the discriminant form is a cusp form of weight $12$ and any other cusp form of weight $12$ would be a scalar multiple of $\Delta$ (since their ratio would be a modular form of weight $0$). So we have $\dim M_{12}(\Gamma_1) = 2$.

Finally we need to check that $\dim M_2(\Gamma_1) = 0$. Firstly, there can't be any cuspforms here by the same argument as above. So we need to check that there are no modular forms of weight $2$. If we did have one, call it $f$ then $f^2$ would be a non-cuspform of weight $4$ and so $f^2 = a E_4$, where in fact $a=a_0(f)^2$ (since $(f^2-a_0(f)E_4)$ is now a cuspform of weight $4$ which means its zero). Similarly, $f^3 = a_0(f)^3 E_6$. But now taking powers to make them weight $12$ forms we see that $a_0(f)^6(E_4^3 - E_6^2) = 0 = 1728 a_0(f)^6 \Delta$
but $a_0(f) \ne 0$ (since its assumed to not be a cuspform), this would mean $\Delta =0$ which we know can't happen.
\end{proof}
```

:::theorem "thm:dim-mf-general-level" (lean := "dim_gen_cong_levels") (parent := "eisenstein_discriminant")
Let $`\Gamma` be a congruence subgroup. Then $`M_k(\Gamma)` is
finite-dimensional.
Uses {uses "def:Mk"}[] and {uses "thm:lvl1_dims"}[].
:::

```tex "thm:dim-mf-general-level"
\begin{theorem}\label{thm:dim-mf-general-level}\uses{def:Mk, thm:lvl1_dims}\leanok \lean{dim_gen_cong_levels}
Let $\Gamma$ be a congruence subgroup. Then $M_k(\Gamma)$ is finite-dimensional.
\end{theorem}
```

:::proof "thm:dim-mf-general-level"
We know that $`\dim(M_k(\Gamma_1))` is finite-dimensional, hence there is
some $`r_k` such that any element of $`M_k(\Gamma_1)` vanishing at infinity
to degree greater than $`r_k` must be zero.
Now take $`f \in M_k(\Gamma)` vanishing to degree $`n` at infinity, and set
$`F = \prod_\gamma f\mid_k \gamma`, where the product is over a set of
representatives of $`\Gamma_1 \backslash \Gamma`.
Then $`F` is a modular form of weight $`kd` where
$`d = [\Gamma_1 : \Gamma]`, and it vanishes at infinity to degree at least
$`n`.
So if $`n > r_{kd}`, then $`F=0`, and hence $`f=0`.
:::

```tex "thm:dim-mf-general-level" (slot := "proof")
\begin{proof}
We know that $\dim(M_k(\Gamma_1))$ is finite dimensional from the above, now this means that there is some $r_k$ such that any element of $M_k(\Gamma_1)$ vanishing at infinity to degree $> r_k$ must be zero. Now take $f \in M_k(\Gamma)$ and vanishes to degree $n$ at infinity, then consider $F = \prod_\gamma f\mid_k \gamma$ where the product is over a set of representatives of $\Gamma_1 \backslash \Gamma$. Then $F$ is a modular form of weight $k d$ where $d = [\Gamma_1: \Gamma]$ and vanishes at infinity to degree at least $n$. So if $n > r_{kd}$ then $F=0$ meaning the $f=0$.
\end{proof}
```

:::corollary "cor:dim-mf" (parent := "eisenstein_discriminant")
We have
$$`\dim M_2(\mathrm{SL}_{2}(\mathbb{Z})) = 0`
$$`\dim M_4(\mathrm{SL}_{2}(\mathbb{Z})) = \dim M_6(\mathrm{SL}_{2}(\mathbb{Z})) = \dim M_8(\mathrm{SL}_{2}(\mathbb{Z})) = 1`
$$`\dim S_4(\mathrm{SL}_{2}(\mathbb{Z})) = \dim S_6(\mathrm{SL}_{2}(\mathbb{Z})) = \dim S_8(\mathrm{SL}_{2}(\mathbb{Z})) = 0.`
Uses {uses "def:Mk"}[] and {uses "thm:lvl1_dims"}[].
:::

```tex "cor:dim-mf"
\begin{corollary}\label{cor:dim-mf}\uses{def:Mk, thm:lvl1_dims}\leanok
We have
\begin{align}
    \dim M_2(\mathrm{SL}_{2}(\mathbb{Z})) &= 0, \label{eqn:dimM2} \\
    \dim M_4(\mathrm{SL}_{2}(\mathbb{Z})) &= 1, \label{eqn:dimM4} \\
    \dim M_6(\mathrm{SL}_{2}(\mathbb{Z})) &= 1, \label{eqn:dimM6} \\
    \dim M_8(\mathrm{SL}_{2}(\mathbb{Z})) &= 1, \label{eqn:dimM8} \\
    \dim S_4(\mathrm{SL}_{2}(\mathbb{Z})) &= 0, \label{eqn:dimS4} \\
    \dim S_6(\mathrm{SL}_{2}(\mathbb{Z})) &= 0, \label{eqn:dimS6} \\
    \dim S_8(\mathrm{SL}_{2}(\mathbb{Z})) &= 0. \label{eqn:dimS8}
\end{align}
\end{corollary}
```

:::proof "cor:dim-mf"
:::

```tex "cor:dim-mf" (slot := "proof")
\begin{proof}
\leanok
\end{proof}
```

:::definition "def:th00-th01-th10" (lean := "Θ₂, Θ₃, Θ₄") (parent := "theta_and_identities")
We define three different theta functions, the "Thetanullwerte",
$`\Theta_2,\Theta_3,\Theta_4`, by
$$`\Theta_{2}(z) = \theta_{10}(z) = \sum_{n\in\mathbb{Z}}e^{\pi i (n+\frac12)^2 z}`
$$`\Theta_{3}(z) = \theta_{00}(z) = \sum_{n\in\mathbb{Z}}e^{\pi i n^2 z}`
$$`\Theta_{4}(z) = \theta_{01}(z) = \sum_{n\in\mathbb{Z}}(-1)^n\,e^{\pi i n^2 z}.`
:::

```tex "def:th00-th01-th10"
\begin{definition}\label{def:th00-th01-th10}\lean{Θ₂, Θ₃, Θ₄}\leanok
We define three different theta functions (so called ``Thetanullwerte'') as
\begin{align}
  \Theta_{2}(z) = \theta_{10}(z)\,=\, & \sum_{n\in\Z}e^{\pi i (n+\frac12)^2 z}. \notag \\
  \Theta_{3}(z) = \theta_{00}(z)\,=\, & \sum_{n\in\Z}e^{\pi i n^2 z} \notag \\
  \Theta_{4}(z) = \theta_{01}(z)\,=\, & \sum_{n\in\Z}(-1)^n\,e^{\pi i n^2 z} \notag \\
\end{align}
\end{definition}
```

:::definition "def:H2-H3-H4" (lean := "H₂, H₃, H₄") (parent := "theta_and_identities")
Define $`H_2 = \Theta_2^4`, $`H_3 = \Theta_3^4`, $`H_4 = \Theta_4^4`.
Uses {uses "def:th00-th01-th10"}[].
:::

```tex "def:H2-H3-H4"
\begin{definition}\label{def:H2-H3-H4}\uses{def:th00-th01-th10}\lean{H₂, H₃, H₄}\leanok
Define
\begin{equation}
    H_2 = \Theta_2^4, \quad H_3 = \Theta_3^4, \quad H_4 = \Theta_4^4. \label{eqn:H2-H3-H4}
\end{equation}
\end{definition}
```

:::lemma_ "lemma:theta-transform-S-T" (lean := "H₂_T_action,H₃_T_action,H₄_T_action,H₂_S_action,H₃_S_action,H₄_S_action") (parent := "theta_and_identities")
These elements act on the theta functions in the following way.
$$`H_2 | S = -H_4,\quad H_3 | S = -H_3,\quad H_4 | S = -H_2`
and
$$`H_2 | T = -H_2,\quad H_3 | T = H_4,\quad H_4 | T = H_3.`
Uses {uses "def:th00-th01-th10"}[] and {uses "def:H2-H3-H4"}[].
:::

```tex "lemma:theta-transform-S-T"
\begin{lemma}\label{lemma:theta-transform-S-T}\uses{def:th00-th01-th10, def:H2-H3-H4}\lean{H₂_T_action,H₃_T_action,H₄_T_action,H₂_S_action,H₃_S_action,H₄_S_action}\leanok
These elements act on the theta functions in the following way
\begin{align}
    H_2 | S &= -H_4 \label{eqn:H2-transform-S} \\
    H_3 | S &= -H_3 \label{eqn:H3-transform-S} \\
    H_4 | S &= -H_2 \label{eqn:H4-transform-S}
\end{align}
and
\begin{align}
    H_2 | T &= -H_2 \label{eqn:H2-transform-T} \\
    H_3 | T &= H_4 \label{eqn:H3-transform-T} \\
    H_4 | T &= H_3 \label{eqn:H4-transform-T}
\end{align}
\end{lemma}
```

:::proof "lemma:theta-transform-S-T"
The last three identities easily follow from the definition.
For example, `eqn:H2-transform-T` follows from
$$`\Theta_{2}(z + 1) = \sum_{n\in\Z}e^{\pi i (n+\frac12)^2 (z + 1)}
    = \sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2}} e^{\pi i (n + \frac{1}{2})^{2} z}`
$$`= \sum_{n \in \Z} e^{\pi i (n^2 + n + \frac{1}{4})} e^{\pi i (n + \frac{1}{2})^{2} z}
    = \sum_{n \in \Z} (-1)^{n^2 + n}e^{\pi i / 4} e^{\pi i (n + \frac{1}{2})^{2} z}`
$$`= e^{\pi i / 4} \Theta_{2}(z),`
and taking fourth powers.
The identities `eqn:H2-transform-S` and `eqn:H4-transform-S` are equivalent
under $`z \leftrightarrow -1/z`, so it is enough to show
`eqn:H2-transform-S` and `eqn:H3-transform-S`.
These identities follow from the identities of the two-variable Jacobi theta
function, which is defined as
$$`\theta(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n z + \pi i n^2 \tau}.`
This function specializes to the theta functions as
$$`\Theta_{2}(\tau) = e^{\pi i \tau / 4} \theta(-\tau / 2, \tau),`
$$`\Theta_{3}(\tau) = \theta(0, \tau),`
$$`\Theta_{4}(\tau) = \theta(1/2, \tau),`
and Poisson summation gives
$$`\theta(z, \tau) = \frac{1}{\sqrt{-i \tau}} e^{-\frac{\pi i z^2}{\tau}} \theta\left(\frac{z}{\tau}, -\frac{1}{\tau}\right).`
Applying these specializations yields the identities. For example,
`eqn:H4-transform-S` follows from
$$`\Theta_{4}(\tau) = \theta\left(\frac{1}{2}, \tau\right) = \frac{1}{\sqrt{-i\tau}} e^{- \frac{\pi i }{4 \tau}} \theta\left(\frac{1}{2 \tau}, -\frac{1}{\tau}\right) = \frac{1}{\sqrt{-i\tau}} \Theta_{2}\left(-\frac{1}{\tau}\right),`
and taking fourth powers.
:::

```tex "lemma:theta-transform-S-T" (slot := "proof")
\begin{proof}\leanok
The last three identities easily follow from the definition.
For example, \eqref{eqn:H2-transform-T} follows from
\begin{align}
    \Theta_{2}(z + 1) &= \sum_{n\in\Z}e^{\pi i (n+\frac12)^2 (z + 1)}
    = \sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2}} e^{\pi i (n + \frac{1}{2})^{2} z} \\
    &= \sum_{n \in \Z} e^{\pi i (n^2 + n + \frac{1}{4})} e^{\pi i (n + \frac{1}{2})^{2} z} = \sum_{n \in \Z} (-1)^{n^2 + n}e^{\pi i / 4} e^{\pi i (n + \frac{1}{2})^{2} z} \\
    &= e^{\pi i / 4} \Theta_{2}(z)
\end{align}
and taking 4th power.
\eqref{eqn:H2-transform-S} and \eqref{eqn:H4-transform-S} are equivalent under $z \leftrightarrow -1/z$, so it is enough to show \eqref{eqn:H2-transform-S} and \eqref{eqn:H3-transform-S}.
These identities follow from the identities of the \emph{two-variable} Jacobi theta function, which is defined as (be careful for the variables, where we use $\tau$ instead of $z$)
\begin{equation}
    \theta(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n z + \pi i n^2 \tau}
\end{equation}
and already formalized by David Loeffler.
This function specialize to the theta functions as
\begin{align}
    \Theta_{2}(\tau) &= e^{\pi i \tau / 4} \theta(-\tau / 2, \tau) \\
    \Theta_{3}(\tau) &= \theta(0, \tau) \\
    \Theta_{4}(\tau) &= \theta(1/2, \tau) \\
\end{align}

Poisson summation formula gives
\begin{equation}
    \theta(z, \tau) = \frac{1}{\sqrt{-i \tau}} e^{-\frac{\pi i z^2}{\tau}} \theta\left(\frac{z}{\tau}, -\frac{1}{\tau}\right)
\end{equation}
and applying the specializations above yield the identities.
For example, \eqref{eqn:H4-transform-S} follows from
\begin{equation}
    \Theta_{4}(\tau) = \theta\left(\frac{1}{2}, \tau\right) = \frac{1}{\sqrt{-i\tau}} e^{- \frac{\pi i }{4 \tau}} \theta\left(\frac{1}{2 \tau}, -\frac{1}{\tau}\right) = \frac{1}{\sqrt{-i\tau}} \Theta_{2}\left(-\frac{1}{\tau}\right)
\end{equation}
and taking 4th power.
\end{proof}
```

:::lemma_ "lemma:theta-slash-invariant" (lean := "H₂_SIF,H₃_SIF,H₄_SIF") (parent := "theta_and_identities")
$`H_{2}`, $`H_{3}`, and $`H_{4}` are slash invariant under $`\Gamma(2)`,
that is, for all $`\gamma \in \Gamma(2)` and
$`i \in \{2, 3, 4\}`, we have
$`H_i|\gamma = H_i|\gamma^{-1} = H_i`.
Uses {uses "lemma:slash-operator-chain-rule"}[], {uses "lemma:slash-negI-even-weight"}[], {uses "lemma:theta-transform-S-T"}[], and {uses "lemma:Gamma-2-generators"}[].
:::

```tex "lemma:theta-slash-invariant"
\begin{lemma}\label{lemma:theta-slash-invariant}\uses{lemma:slash-operator-chain-rule,lemma:slash-negI-even-weight,lemma:theta-transform-S-T,lemma:Gamma-2-generators}\lean{H₂_SIF,H₃_SIF,H₄_SIF}\leanok
  $H_{2}$, $H_{3}$, and $H_{4}$ are slash invariant under $\Gamma(2)$, i.e. for all $\gamma \in \Gamma(2)$ and $i \in \{2, 3, 4\}$, we have $H_i|\gamma = H_i|\gamma^{-1} = H_i$.
\end{lemma}
```

:::proof "lemma:theta-slash-invariant"
By {uses "lemma:Gamma-2-generators"}[] and
{uses "lemma:slash-operator-chain-rule"}[], it suffices to show that the
$`H_i` are invariant under slash actions with respect to $`\alpha`,
$`\beta`, and $`-I`.
Invariance under $`-I` follows from
{uses "lemma:slash-negI-even-weight"}[].
The rest follows from {uses "lemma:slash-operator-chain-rule"}[],
{uses "lemma:theta-transform-S-T"}[], and the matrix identities
$`\alpha = T^2` and
$`\beta = -S\alpha^{-1}S = -ST^{-2}S`.
For example, invariance for $`H_2` follows from
$`H_2|\alpha = H_2 |T^{2} = -H_2 |T = H_2` and
$`H_2|\beta = H_2 |(-S\alpha^{-1}S) = H_2 | (S\alpha^{-1}S) =-H_4 |(\alpha^{-1}S) = -H_4 |S  = H_2`.
:::

```tex "lemma:theta-slash-invariant" (slot := "proof")
\begin{proof}\leanok
  By \cref{lemma:Gamma-2-generators} and \cref{lemma:slash-operator-chain-rule}, it suffices to show that the $H_i$ are invariant under slash actions with respect to $\alpha$, $\beta$, and $-I$.
Invariance under $-I$ follows from Lemma \ref{lemma:slash-negI-even-weight}.
The rest follows from Lemma \ref{lemma:slash-operator-chain-rule}, \ref{lemma:theta-transform-S-T}, and the matrix identities
\begin{equation}
    \alpha = T^2, \quad \beta = -S\alpha^{-1}S = -ST^{-2}S.
\end{equation}
For example, invariance for $H_2$ can be proved by
\begin{align}
    H_2|\alpha &= H_2 |T^{2} = -H_2 |T = H_2 \\
    H_2|\beta &= H_2 |(-S\alpha^{-1}S) = H_2 | (S\alpha^{-1}S) =-H_4 |(\alpha^{-1}S) = -H_4 |S  = H_2.
\end{align}
\end{proof}
```

:::lemma_ "lemma:theta-bounded-im-infty" (lean := "isBoundedAtImInfty_H_slash") (parent := "theta_and_identities")
For all $`\gamma \in \Gamma_1`, the slash-translates
$`H_{2}|_2 \gamma`, $`H_{3}|_2 \gamma`, and $`H_{4}|_2 \gamma` are
holomorphic at $`i\infty`.
Uses {uses "lemma:theta-slash-invariant"}[] and {uses "lemma:Gamma-1-generators"}[].
:::

```tex "lemma:theta-bounded-im-infty"
\begin{lemma}\label{lemma:theta-bounded-im-infty}\uses{lemma:theta-slash-invariant, lemma:Gamma-1-generators}\lean{isBoundedAtImInfty_H_slash}\leanok
  For all $\gamma \in \Gamma_1$, $H_{2}|_2 \gamma$, $H_{3}|_2 \gamma$, and $H_{4}|_2 \gamma$ are holomorphic at $i\infty$.
\end{lemma}
```

:::proof "lemma:theta-bounded-im-infty"
We want to show that for $`\gamma \in \Gamma_1`,
$`\|H_2|_2\gamma(z)\|` is bounded as $`z \in \mathbb{H} \to i\infty`.
By {uses "lemma:theta-transform-S-T"}[], {uses "lemma:Gamma-2-generators"}[],
and induction on group elements, the set
$`\{\pm H_2, \pm H_3, \pm H_4\}` is closed under the action of
$`\Gamma_1`.
Hence it suffices to prove that $`H_2,H_3,H_4` are bounded at $`i\infty`.
For $`z \in \mathbb{H}` with $`\Im(z) \ge A`,
$$`\|H_2(z)\|
 = \left\|\sum_{n \in \Z} \exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right\|^4`
$$`\leq \left(\sum_{n \in \Z} \left\|\exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right\|\right)^4
 = \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 \Im(z)\right)\right\|\right)^4`
$$`\leq \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 A\right)\right\|\right)^4.`
The final term is convergent because it equals
$`\exp(-\pi A / 4)\theta(iA / 2, iA)`.
The proofs for $`H_3` and $`H_4` are similar.
:::

```tex "lemma:theta-bounded-im-infty" (slot := "proof")
\begin{proof}
    \leanok
    We want to show that for $\gamma \in \Gamma_1$, $\|H_2|_2\gamma(z)\|$ is bounded as $z \in \mathbb{H} \to i\infty$. Firstly, by \Cref{lemma:theta-transform-S-T}, \Cref{lemma:Gamma-2-generators} and induction on group elements, we notice that $\{\pm H_2, \pm H_3, \pm H_4\}$ is closed under action by $\Gamma_1$. Hence, it suffices to prove that $H_2$, $H_3$ and $H_4$ are bounded at $i\infty$. Consider $z \in \mathbb{H}$ with $\Im(z) \geq A$. We proceed by direct algebraic manipulation:
    \begin{align}
        \|H_2(z)\|
        &= \left\|\sum_{n \in \Z} \exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right\|^4
        \leq \left(\sum_{n \in \Z} \left\|\exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right)\right\|^4 \\
        &= \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 \Im(z)\right)\right)\right\|^4
        \leq \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 A\right)\right)\right\|^4
    \end{align}

    Where we prove the final term is convergent by noticing that it equals $\exp(-\pi A / 4)\theta(iA / 2, iA)$, which has been shown to converge in \texttt{Mathlib}. The proofs for $H_3$ and $H_4$ are similar (actually easier) and have been omitted.

    \todo{It seems the \texttt{MDifferentiable} requirement is missing.}
\end{proof}
```

:::lemma_ "lemma:theta-modular" (lean := "H₂_MF,H₃_MF,H₄_MF") (parent := "theta_and_identities")
$`H_{2}`, $`H_{3}`, and $`H_{4}` belong to $`M_2(\Gamma(2))`.
Uses {uses "lemma:theta-slash-invariant"}[] and {uses "lemma:theta-bounded-im-infty"}[].
:::

```tex "lemma:theta-modular"
\begin{lemma}\label{lemma:theta-modular}\uses{lemma:theta-slash-invariant,lemma:theta-bounded-im-infty}\lean{H₂_MF,H₃_MF,H₄_MF}\leanok
$H_{2}$, $H_{3}$, and $H_{4}$ belong to $M_2(\Gamma(2))$.
\end{lemma}
```

:::proof "lemma:theta-modular"
From {uses "lemma:theta-slash-invariant"}[] and
{uses "lemma:theta-bounded-im-infty"}[], it remains to prove that
$`H_2`, $`H_3`, and $`H_4` are holomorphic on $`\mathbb{H}`.
Fill in proof.
:::

```tex "lemma:theta-modular" (slot := "proof")
\begin{proof}
    \leanok
    From \cref{lemma:theta-slash-invariant} and \cref{lemma:theta-bounded-im-infty}, it remains ot prove that $H_2$, $H_3$ and $H_4$ are holomorphic on $\mathbb{H}$. \todo{fill in proof.}
\end{proof}
```

:::lemma_ "prop:H2-fourier" (parent := "theta_and_identities")
$`H_2` admits a Fourier series of the form
$$`H_2(z) = \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}`
for some $`c_{H_2}(n) \in \mathbb{R}_{\ge 0}`, with $`c_{H_2}(1) = 16` and
$`c_{H_2}(n) = O(n^k)` for some $`k \in \mathbb{N}`.
Uses {uses "def:H2-H3-H4"}[].
:::

```tex "prop:H2-fourier"
\begin{proposition}\label{prop:H2-fourier}\uses{def:H2-H3-H4}
$H_2$ admits a Fourier series of the form
\begin{equation}
    H_2(z) = \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}
\end{equation}
for some $c_{H_2}(n) \in \R_{\ge 0}$, with $c_{H_2}(1) = 16$ and $c_{H_2}(n) = O(n^k)$ for some $k \in \N$.
\end{proposition}
```

:::proof "prop:H2-fourier"
We have
$`H_2(z) = \Theta_2(z)^4
 = \left(\sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4}
 = \left(2\sum_{n \ge 0} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4}`$,
and then
$`\left(2 e^{\pi i z / 4} + 2 \sum_{n \ge 1} e^{\pi i (n^2 + n + \frac{1}{4}) z}\right)^{4}
 = 16 e^{\pi i z}\left(1 + \sum_{n \ge 1} e^{\pi i (n^2 + n)z}\right)^{4}`$,
so
$`H_2(z)=16 e^{\pi i z} + \sum_{n \ge 2} c_{H_2}(n) e^{\pi i n z}
 = \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}`$.
:::

```tex "prop:H2-fourier" (slot := "proof")
\begin{proof}
We have
\begin{align}
    H_2(z) &= \Theta_2(z)^4 \\
    &= \left(\sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\
    &= \left(2\sum_{n \ge 0} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\
    &= \left(2 e^{\pi i z / 4} + 2 \sum_{n \ge 1} e^{\pi i (n^2 + n + \frac{1}{4}) z}\right)^{4} \\
    &= 16 e^{\pi i z}\left(1 + \sum_{n \ge 1} e^{\pi i (n^2 + n)z}\right)^{4} \\
    &= 16 e^{\pi i z} + \sum_{n \ge 2} c_{H_2}(n) e^{\pi i n z} \\
    &= \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}.
\end{align}
\end{proof}
```

:::lemma_ "prop:H3-fourier" (parent := "theta_and_identities")
$`H_3` admits a Fourier series of the form
$$`H_3(z) = \sum_{n \ge 0} c_{H_3}(n) e^{\pi i n z}`
for some $`c_{H_3}(n) \in \R_{\ge 0}` with $`c_{H_3}(0) = 1` and
$`c_{H_3}(n) = O(n^k)` for some $`k \in \N`.
Especially, $`H_3` is not cuspidal.
Uses {uses "def:H2-H3-H4"}[].
:::

```tex "prop:H3-fourier"
\begin{proposition}\label{prop:H3-fourier}\uses{def:H2-H3-H4}
$H_3$ admits a Fourier series of the form
\begin{equation}
    H_3(z) = \sum_{n \ge 0} c_{H_3}(n) e^{\pi i n z}
\end{equation}
for some $c_{H_3}(n) \in \R_{\ge 0}$ with $c_{H_3}(0) = 1$ and $c_{H_3}(n) = O(n^k)$ for some $k \in \N$.
Especially, $H_3$ is not cuspidal.
\end{proposition}
```

:::proof "prop:H3-fourier"
We have
$`H_3(z) = \Theta_3(z)^{4}
 = \left(\sum_{n \in \Z} e^{\pi i n^2 z}\right)^{4}
 = \left(1 + 2 \sum_{n \ge 1} e^{\pi i n^2 z}\right)^{4}
 = 1 + O(e^{\pi i z}).`
:::

```tex "prop:H3-fourier" (slot := "proof")
\begin{proof}
We have
\begin{equation}
    H_3(z) = \Theta_3(z)^{4} = \left(\sum_{n \in \Z} e^{\pi i n^2 z}\right)^{4} = \left(1 + 2 \sum_{n \ge 1} e^{\pi i n^2 z}\right)^{4} = 1 + O(e^{\pi i z}).
\end{equation}
\end{proof}
```

:::lemma_ "prop:H4-fourier" (parent := "theta_and_identities")
$`H_4` admits a Fourier series of the form
$$`H_4(z) = \sum_{n \ge 0} c_{H_4}(n) e^{\pi i n z}`
for some $`c_{H_4}(n) \in \R` with $`c_{H_4}(0) = 1` and
$`c_{H_4}(n) = O(n^k)` for some $`k \in \N`.
Especially, $`H_4` is not cuspidal.
Uses {uses "def:H2-H3-H4"}[].
:::

```tex "prop:H4-fourier"
\begin{proposition}\label{prop:H4-fourier}\uses{def:H2-H3-H4}
$H_4$ admits a Fourier series of the form
\begin{equation}
    H_4(z) = \sum_{n \ge 0} c_{H_4}(n) e^{\pi i n z}
\end{equation}
for some $c_{H_4}(n) \in \R$ with $c_{H_4}(0) = 1$ and $c_{H_4}(n) = O(n^k)$ for some $k \in \N$.
Especially, $H_4$ is not cuspidal.
\end{proposition}
```

:::lemma_ "lemma:jacobi-identity" (lean := "jacobi_identity") (parent := "theta_and_identities")
These three theta functions satisfy the Jacobi identity
$$`H_{2} + H_{4} = H_{3} \Leftrightarrow \Theta_{2}^4 + \Theta_{4}^4 = \Theta_{3}^4.`
Uses {uses "lemma:theta-modular"}[] and {uses "cor:dim-mf"}[].
:::

```tex "lemma:jacobi-identity"
\begin{lemma}\label{lemma:jacobi-identity}\uses{lemma:theta-modular, cor:dim-mf}\lean{jacobi_identity}\leanok
These three theta functions satisfy the \emph{Jacobi identity}
\begin{equation}\label{eqn:jacobi-identity}
H_{2} + H_{4} = H_{3} \Leftrightarrow \Theta_{2}^4 + \Theta_{4}^4 = \Theta_{3}^4.
\end{equation}
\end{lemma}
```

:::proof "lemma:jacobi-identity"
Let $`f = (H_2 + H_4 - H_3)^{2}`.
Obviously, $`f` is a modular form of weight $`4` and level $`\Gamma(2)`.
Using the transformation rules of $`H_2,H_3,H_4`, we have
$`f|_{S} = (-H_4 - H_2 + H_3)^{2} = f` and
$`f|_{T} = (-H_2 + H_3 - H_4)^{2} = f`,
so $`f` is actually a modular form of level $`1`.
By considering the limit as $`z \to i\infty`, $`f` is a cusp form, and
hence $`f = 0` by `eqn:dimS4`.
:::

```tex "lemma:jacobi-identity" (slot := "proof")
\begin{proof}
    \leanok
    Let $f = (H_2 + H_4 - H_3)^{2}$.
    Obviously, $f$ is a modular form of weight $4$ and level $\Gamma(2)$.
    However, by using the transformation rules of $H_2, H_3, H_4$, one have
    \begin{align}
        f|_{S} &= (-H_4 - H_2 + H_3)^{2} = f\\
        f|_{T} &= (-H_2 + H_3 - H_4)^{2} = f
    \end{align}
    so $f$ is actually a modular form of level $1$.
    By considering the limit as $z \to i\infty$, $f$ is a cusp form, so we get $f = 0$ from \eqref{eqn:dimS4}.
\end{proof}
```

:::lemma_ "lemma:lv1-lv2-identities" (parent := "theta_and_identities")
We have
$$`E_4 = \frac{1}{2}(H_{2}^{2} + H_{3}^{2} + H_{4}^{2}) = H_{2}^{2} + H_{2}H_{4} + H_{4}^{2}`
$$`E_6 = \frac{1}{2} (H_{2} + H_{3})(H_{3} + H_{4}) (H_{4} - H_{2}) = \frac{1}{2}(H_2 + 2H_4)(2H_2 + H_4)(H_4 - H_2)`
$$`\Delta = \frac{1}{256} (H_{2}H_{3}H_{4})^2.`
Uses {uses "lemma:theta-transform-S-T"}[], {uses "lemma:theta-modular"}[], and {uses "lemma:disc-cuspform"}[].
:::

```tex "lemma:lv1-lv2-identities"
\begin{lemma}\label{lemma:lv1-lv2-identities}\uses{lemma:theta-transform-S-T, lemma:theta-modular, lemma:disc-cuspform}
We have
\begin{align}
    E_4 &= \frac{1}{2}(H_{2}^{2} + H_{3}^{2} + H_{4}^{2}) = H_{2}^{2} + H_{2}H_{4} + H_{4}^{2} \label{eqn:e4theta} \\
    E_6 &= \frac{1}{2} (H_{2} + H_{3})(H_{3} + H_{4}) (H_{4} - H_{2}) = \frac{1}{2}(H_2 + 2H_4)(2H_2 + H_4)(H_4 - H_2) \label{eqn:e6theta} \\
    \Delta &= \frac{1}{256} (H_{2}H_{3}H_{4})^2. \label{eqn:disctheta}
\end{align}
\end{lemma}
```

:::proof "lemma:lv1-lv2-identities"
We can prove these similarly as Lemma {uses "lemma:jacobi-identity"}[].
The right-hand sides of `eqn:e4theta`, `eqn:e6theta`, and
`eqn:disctheta` are all modular forms of level $`\Gamma_1` and of the
desired weights, where `eqn:disctheta` is a cusp form since $`H_2` is.
Now the identities follow from the dimension calculations
$`\dim M_4(\Gamma_1) = \dim M_6(\Gamma_1) = \dim S_{12}(\Gamma_1) = 1`
and comparing the first nonzero $`q`-coefficients.
:::

```tex "lemma:lv1-lv2-identities" (slot := "proof")
\begin{proof}
We can prove these similarly as Lemma \ref{lemma:jacobi-identity}.
Right hand sides of \eqref{eqn:e4theta}, \eqref{eqn:e6theta}, and \eqref{eqn:disctheta} are all modular forms of level $\Gamma_1$ and desired weights, where \eqref{eqn:disctheta} is a cusp form since $H_2$ is.
Now the identities follow from the dimension calculations $\dim M_4(\Gamma_1) = \dim M_6(\Gamma_1) = \dim S_{12}(\Gamma_1) = 1$ and comparing the first nonzero $q$-coefficients.
\end{proof}
```

:::corollary "cor:theta-pos" (lean := "H₂_imag_axis_pos, H₄_imag_axis_pos") (parent := "theta_and_identities")
All three functions $`t \mapsto H_2(it), H_3(it), H_4(it)` are positive for
$`t > 0`.
Uses {uses "lemma:jacobi-identity"}[] and {uses "lemma:theta-transform-S-T"}[].
:::

```tex "cor:theta-pos"
\begin{corollary}\label{cor:theta-pos}\uses{lemma:jacobi-identity, lemma:theta-transform-S-T}\lean{H₂_imag_axis_pos, H₄_imag_axis_pos}
All three functions $t \mapsto H_2(it), H_3(it), H_4(it)$ are positive for $t > 0$.
\end{corollary}
```

:::proof "cor:theta-pos"
By Lemma {uses "lemma:jacobi-identity"}[] and the transformation law
`eqn:H2-transform-S`, it is enough to prove the positivity for
$`\Theta_2(it)`, which is clear from its definition:
$$`\Theta_{2}(it) = \sum_{n \in \mathbb{Z}} e^{- \pi (n + \frac{1}{2})^{2} t} > 0.`
:::

```tex "cor:theta-pos" (slot := "proof")
\begin{proof}
By Lemma \ref{lemma:jacobi-identity} and the transformation law \eqref{eqn:H2-transform-S}, it is enough to prove the positivity for $\Theta_2(it)$, which is clear from its definition:
\begin{equation}
    \Theta_{2}(it) = \sum_{n \in \Z} e^{- \pi (n + \frac{1}{2})^{2} t} > 0.
\end{equation}
\end{proof}
```

:::definition "def:derivative" (lean := "D") (parent := "serre_derivative")
Let $`F` be a quasimodular form.
We define the (normalized) derivative of $`F` as
$$`F' = DF := \frac{1}{2\pi i} \frac{\dd}{\dd z} F.`
:::

```tex "def:derivative"
\begin{definition}\label{def:derivative} \lean{D} \leanok
Let $F$ be a quasimodular form.
We define the (normalized) derivative of $F$ as
\begin{equation}\label{eqn:derivative}
    F' = DF := \frac{1}{2\pi i} \frac{\dd}{\dd z} F.
\end{equation}
\end{definition}
```

:::lemma_ "lemma:der-q-series" (lean := "D_qexp_tsum_pnat") (parent := "serre_derivative")
We have an equality of operators $`D = q \frac{\dd}{\dd q}`.
In particular, if $`F(z) = \sum_{n \ge n_0} a_n q^n`, then
$`F'(z) = \sum_{n \ge n_0} n a_n q^n`.
Uses {uses "def:derivative"}[].
:::

```tex "lemma:der-q-series"
\begin{lemma}\label{lemma:der-q-series}\uses{def:derivative}\lean{D_qexp_tsum_pnat}\leanok
We have an equality of operators $D = q \frac{\dd}{\dd q}$.
In particular, the $q$-series of the derivative of a quasimodular form $F(z) = \sum_{n \ge n_0} a_n q^n$ is $F'(z) = \sum_{n \ge n_0} n a_n q^n$.
\end{lemma}
```

:::proof "lemma:der-q-series"
This follows directly from the definition {uses "def:derivative"}[], since
$`\frac{1}{2 \pi i}\frac{\dd}{\dd z}e^{2\pi i n z} = n e^{2\pi i n z}`.
:::

```tex "lemma:der-q-series" (slot := "proof")
\begin{proof}\leanok
Directly follows from the definition \eqref{def:derivative}, where $\frac{1}{2 \pi i}\frac{\dd}{\dd z}e^{2\pi i n z} = n e^{2\pi i n z}$.
\end{proof}
```

:::definition "def:serre-der" (lean := "serre_D") (parent := "serre_derivative")
For $`k \in \mathbb{R}`, define the weight-$`k` Serre derivative
$`\partial_k` of a modular form $`F` by
$$`\partial_k F := F' - \frac{k}{12} E_2 F.`
Uses {uses "def:derivative"}[] and {uses "def:E2"}[].
:::

```tex "def:serre-der"
\begin{definition}\label{def:serre-der}\uses{def:derivative, def:E2}\leanok \lean{serre_D}
For $k \in \mathbb{R}$, define the weight $k$ Serre derivative $\partial_{k}$ of a modular form $F$ as
\begin{equation}\label{eqn:serre-der}
    \partial_{k}F := F' - \frac{k}{12} E_2 F.
\end{equation}
\end{definition}
```

:::theorem "thm:serre-der-equiv-action" (lean := "serre_D_slash_equivariant") (parent := "serre_derivative")
Serre derivative $`\partial_k` is equivariant with the slash action of
$`\mathrm{SL}_{2}(\mathbb{Z})` in the sense that
$$`\partial_{k} (F|_{k}\gamma) = (\partial_{k} F)|_{k+2}\gamma, \quad \forall \gamma \in \mathrm{SL}_{2}(\mathbb{Z}).`
Uses {uses "def:serre-der"}[], {uses "def:E2"}[], and {uses "lemma:E2-transform-general"}[].
:::

```tex "thm:serre-der-equiv-action"
\begin{theorem}
\label{thm:serre-der-equiv-action}\uses{def:serre-der, def:E2, lemma:E2-transform-general}\lean{serre_D_slash_equivariant}\leanok
Serre derivative $\partial_{k}$ is equivariant with the slash action of $\mathrm{SL}_{2}(\mathbb{Z})$ in the following sense:
\begin{equation}
    \partial_{k} (F|_{k}\gamma) = (\partial_{k} F)|_{k+2}\gamma, \quad \forall \gamma \in \mathrm{SL}_{2}(\mathbb{Z}).
\end{equation}
\end{theorem}
```

:::proof "thm:serre-der-equiv-action"
Let $`G = \partial_kF = F' - \frac{k}{12}E_2F`.
From $`F \in M_k(\Gamma)`, we have
$$`(F|_{k}\gamma)(z) := (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right), \quad \gamma = \begin{pmatrix}a & b \\ c & d\end{pmatrix} \in \Gamma.`
Differentiating gives
$$`\frac{\dd}{\dd z}(F|_{k} \gamma)(z)
= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} \frac{\dd F}{\dd z}\left(\frac{az + b}{cz + d}\right)`
and hence
$$`(F|_{k} \gamma)'(z)
= -\frac{kc}{2 \pi i} (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right).`
Combining this with the transformation law of $`E_2` yields
$$`((\partial_k F)|_{k+2}\gamma)(z)
= (cz + d)^{-k-2} \left(F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12}E_2\left(\frac{az + b}{cz + d}\right)F\left(\frac{az + b}{cz + d}\right)\right)`
$$`= (F|_{k}\gamma)'(z) - \frac{k}{12} E_2(z) (F|_{k}\gamma)(z)
= \partial_{k} (F|_{k}\gamma)(z).`
:::

```tex "thm:serre-der-equiv-action" (slot := "proof")
\begin{proof}
Let $G = \partial_{k}F = F' - \frac{k}{12}E_2 F$.
From $F \in M_k(\Gamma)$, we have
\begin{equation}
    (F|_{k}\gamma)(z) := (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right), \quad \gamma = \begin{pmatrix}a & b \\ c & d\end{pmatrix} \in \Gamma.
\end{equation}
By taking the derivative of the above equation, we get
\begin{align}
    \frac{\dd}{\dd z}(F|_{k} \gamma)(z) &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k} (cz + d)^{-2} \frac{\dd F}{\dd z}\left(\frac{az + b}{cz + d}\right) \\
    &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} \frac{\dd F}{\dd z}\left(\frac{az + b}{cz + d}\right) \\
    &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + 2 \pi i (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right) \\
    \Leftrightarrow (F|_{k} \gamma)'(z) &= -\frac{kc}{2 \pi i} (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right).
\end{align}
Combined with \eqref{eqn:E2-transform-general}, we get
\begin{align}
    ((\partial_k F)|_{k+2}\gamma)(z) &= (cz + d)^{-k-2} \left(F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12}E_2\left(\frac{az + b}{cz + d}\right)F\left(\frac{az + b}{cz + d}\right)\right) \\
    &= (cz + d)^{-k-2} F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12} \left(E_2(z) - \frac{6ic}{\pi(cz + d)}\right) \cdot (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right) \\
    &= (F|_{k}\gamma)'(z) - \frac{k}{12} E_2(z) (F|_{k}\gamma)(z) \\
    &= \partial_{k} (F|_{k}\gamma)(z).
\end{align}
\end{proof}
```

:::theorem "thm:serre-der-modularity" (lean := "serre_D_slash_invariant") (parent := "serre_derivative")
Let $`F` be a modular form of weight $`k` and level $`\Gamma`.
Then $`\partial_{k}F` is a modular form of weight $`k + 2` of the same
level.
Uses {uses "def:serre-der"}[], {uses "def:Mk"}[], and {uses "thm:serre-der-equiv-action"}[].
:::

```tex "thm:serre-der-modularity"
\begin{theorem}\label{thm:serre-der-modularity}\uses{def:serre-der, def:Mk, thm:serre-der-equiv-action}\lean{serre_D_slash_invariant}\leanok
Let $F$ be a modular form of weight $k$ and level $\Gamma$.
Then, $\partial_{k}F$ is a modular form of weight $k + 2$ of the same level.
\end{theorem}
```

:::proof "thm:serre-der-modularity"
Immediate from Theorem {uses "thm:serre-der-equiv-action"}[] since
$`F|_k\gamma = F` for all $`\gamma \in \Gamma`.
:::

```tex "thm:serre-der-modularity" (slot := "proof")
\begin{proof}
    \leanok
    Immediate from Theorem \ref{thm:serre-der-equiv-action} since $F|_k\gamma = F$ for all $\gamma \in \Gamma$.
\end{proof}
```

:::theorem "thm:ramanujan-formula" (lean := "ramanujan_E₂, ramanujan_E₄, ramanujan_E₆, ramanujan_E₂', ramanujan_E₄', ramanujan_E₆'") (parent := "serre_derivative")
We have
$$`E_2' = \frac{E_2^2 - E_4}{12}`
$$`E_4' = \frac{E_2 E_4 - E_6}{3}`
$$`E_6' = \frac{E_2 E_6 - E_4^2}{2}.`
Uses {uses "thm:serre-der-modularity"}[], {uses "def:serre-der"}[], {uses "lemma:E2-transform-general"}[], and {uses "cor:dim-mf"}[].
:::

```tex "thm:ramanujan-formula"
\begin{theorem}\label{thm:ramanujan-formula}\uses{thm:serre-der-modularity, def:serre-der, lemma:E2-transform-general, cor:dim-mf} \lean{ramanujan_E₂, ramanujan_E₄, ramanujan_E₆, ramanujan_E₂', ramanujan_E₄', ramanujan_E₆'} \leanok
We have
\begin{align}
    E_2' &= \frac{E_2^2 - E_4}{12} \label{eqn:DE2} \\
    E_4' &= \frac{E_2 E_4 - E_6}{3} \label{eqn:DE4} \\
    E_6' &= \frac{E_2 E_6 - E_4^2}{2} \label{eqn:DE6}
\end{align}
\end{theorem}
```

:::proof "thm:ramanujan-formula"
In terms of Serre derivatives, these are equivalent to
$$`\partial_{1}E_2 = -\frac{1}{12} E_4`
$$`\partial_{4}E_4 = -\frac{1}{3} E_6`
$$`\partial_{6}E_6 = -\frac{1}{2} E_4^2.`
By Theorem `thm:serre-der-modularity`, all the Serre derivatives are modular.
More precisely, modularity of $`\partial_4E_4` and $`\partial_6E_6` follows
directly from that theorem, while modularity of $`\partial_1E_2` follows from
the transformation law of $`E_2`.
Differentiating and squaring yields
$$`E_2'|_{4}\gamma = E_2' - \frac{ic}{\pi(cz + d)} E_2 - \frac{3c^2}{\pi^2 (cz + d)^2}`
$$`E_2^2|_{4}\gamma = E_2^2 - \frac{12ic}{\pi(cz + d)} E_2 - \frac{36c^2}{\pi^2 (cz + d)^2}.`
Hence the difference of the first formula and one-twelfth of the second is a
modular form of weight $`4`.
By the dimension computation {uses "cor:dim-mf"}[], it must be a multiple of
$`E_4`; similarly for the
other identities, and the constants are determined by the constant terms of the
$`q`-expansions.
:::

```tex "thm:ramanujan-formula" (slot := "proof")
\begin{proof}
In terms of Serre derivatives, these are equivalent to
\begin{align}
    \partial_{1}E_2 &= -\frac{1}{12} E_4 \\
    \partial_{4}E_4 &= -\frac{1}{3} E_6 \\
    \partial_{6}E_6 &= -\frac{1}{2} E_4^2
\end{align}
By Theorem \ref{thm:serre-der-modularity}, all the Serre derivatives are, in fact, modular.
To be precise, the modularity of $\partial_{4} E_4$ and $\partial_6 E_6$ directly follows from Theorem \ref{thm:serre-der-modularity}, and that of $\partial_{1}E_2$ follows from \eqref{eqn:E2-transform-general}.
Differentiating and squaring then gives us the following:
\begin{align}
    E_2'|_{4}\gamma &= E_2' - \frac{ic}{\pi(cz + d)} E_2 - \frac{3c^2}{\pi^2 (cz + d)^2} \\
    E_2^2|_{4}\gamma &= E_2^2 - \frac{12ic}{\pi(cz + d)} E_2 - \frac{36c^2}{\pi^2 (cz + d)^2}
\end{align}
Hence, \eqref{eqn:DE2}$-\frac{1}{12}$\eqref{eqn:E2sq-transform} is a modular form of weight 4.
By \Cref{cor:dim-mf}, they should be multiples of $E_4, E_6, E_4^2$, and the proportionality constants can be determined by observing the constant terms of $q$-expansions.
\end{proof}
```

:::corollary "cor:logder-disc-E2" (parent := "serre_derivative")
We have
$$`\Delta' = E_2 \Delta.`
Uses {uses "thm:ramanujan-formula"}[] and {uses "def:disc-definition"}[].
:::

```tex "cor:logder-disc-E2"
\begin{corollary}\label{cor:logder-disc-E2}\uses{thm:ramanujan-formula, def:disc-definition}
\begin{equation}\label{eqn:logder-disc-E2}
    \Delta' = E_2 \Delta.
\end{equation}
\end{corollary}
```

:::proof "cor:logder-disc-E2"
By {uses "thm:ramanujan-formula"}[],
$$`\Delta' = \frac{3 E_4^2 E_4' - 2 E_6 E_6'}{1728}
= \frac{1}{1728} \left(3 E_4^2 \cdot \frac{E_2 E_4 - E_6}{3} - 2 E_6 \cdot \frac{E_2 E_6 - E_4^2}{2}\right)
= \frac{E_2(E_4^3 - E_6^2)}{1728}
= E_2\Delta.`
:::

```tex "cor:logder-disc-E2" (slot := "proof")
\begin{proof}
By Ramanujan's formula \eqref{eqn:DE4} and \eqref{eqn:DE6},
\begin{equation}
\Delta' = \frac{3 E_4^2 E_4' - 2 E_6 E_6'}{1728} = \frac{1}{1728} \left(3 E_4^2 \cdot \frac{E_2 E_4 - E_6}{3} - 2 E_6 \cdot \frac{E_2 E_6 - E_4^2}{2}\right) = \frac{E_2(E_4^3 - E_6^2)}{1728} = E_2\Delta.
\end{equation}
\end{proof}
```

:::lemma_ "prop:theta-der" (parent := "serre_derivative")
We have
$$`H_2' = \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4} + E_2 H_2)`
$$`H_3' = \frac{1}{6} (H_{2}^{2} - H_{4}^{2} + E_2 H_3)`
$$`H_4' = -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2} - E_2 H_4)`
or equivalently,
$$`\partial_{2} H_{2} = \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4})`
$$`\partial_{2} H_{3} = \frac{1}{6} (H_{2}^{2} - H_{4}^{2})`
$$`\partial_{2} H_{4} = -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2}).`
Uses {uses "def:serre-der"}[], {uses "lemma:theta-transform-S-T"}[], and {uses "lemma:jacobi-identity"}[].
:::

```tex "prop:theta-der"
\begin{proposition}\label{prop:theta-der}\uses{def:serre-der, lemma:theta-transform-S-T, lemma:jacobi-identity}
We have
\begin{align}
    H_2' &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4} + E_2 H_2) \label{eqn:H2-der}\\
    H_3' &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2} + E_2 H_3) \label{eqn:H3-der}\\
    H_4' &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2} - E_2 H_4) \label{eqn:H4-der}
\end{align}
or equivalently,
\begin{align}
    \partial_{2} H_{2} &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4}) \label{eqn:H2-serre-der} \\
    \partial_{2} H_{3} &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2}) \label{eqn:H3-serre-der} \\
    \partial_{2} H_{4} &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2}) \label{eqn:H4-serre-der}
\end{align}
\end{proposition}
```

:::proof "prop:theta-der"
Equivalences are obvious from the definition of the Serre derivative.
Define $`f_2,f_3,f_4` as the differences between the left- and right-hand
sides of the three Serre-derivative identities. These are modular forms of
weight $`4` and level $`\Gamma(2)`.
By Jacobi's identity, we have $`f_2 + f_4 = f_3`.
The transformation rules of $`H_2,H_3,H_4` imply
$$`f_{2}|_{S} = -f_{4}`
$$`f_{2}|_{T} = -f_{2}`
$$`f_{4}|_{S} = -f_{2}`
$$`f_{4}|_{T} = f_{3} = f_{2} + f_{4}.`
Now define
$$`g := (2 H_2 + H_4) f_2 + (H_2 + 2 H_4) f_4`
$$`h := f_{2}^{2} + f_{2}f_{4} + f_{4}^{2}.`
Then both $`g` and $`h` are invariant under $`S` and $`T` and hence are
level-one modular forms. By analyzing the limit as $`z \to i\infty`, they are
cusp forms, hence $`g = h = 0` by the dimension results.
This gives
$$`3 E_4 f_2^{2} = 3 (H_2^2 + H_2 H_4 + H_4^2) f_2^{2}
= ((2 H_2 + H_4)^{2} - (2H_2 + H_4)(H_2 + 2H_4) + (H_2 + 2H_4)^{2}) f_2^{2}`
$$`= (2 H_2 + H_4)^{2} (f_2^2 + f_2 f_4 + f_4^2) = 0,`
and since $`E_4` has an invertible $`q`-series, it follows that $`f_2=0`.
:::

```tex "prop:theta-der" (slot := "proof")
\begin{proof}
Equivalences are obvious from the definition of the Serre derivative.
Define $f_{2}, f_{3}, f_{4}$ be the differences of the left and right hand sides of \eqref{eqn:H2-serre-der}, \eqref{eqn:H3-serre-der}, \eqref{eqn:H4-serre-der}.
\begin{align}
    f_{2} &:= \partial_{2} H_{2} - \frac{1}{6} H_{2}(H_{2} + 2H_{4}) \\
    f_{3} &:= \partial_{2} H_{3} - \frac{1}{6} (H_{2}^2 - H_{4}^2) \\
    f_{4} &:= \partial_{2} H_{4} + \frac{1}{6} H_{4}(2H_{2} + H_{4}).
\end{align}
Then these are a priori modular forms of weight $4$ and level $\Gamma(2)$, and our goal is to prove that they are actually zeros.
By Jacobi's identity \eqref{eqn:jacobi-identity}, we have $f_{2} + f_{4} = f_{3}$.
Also, the transformation rules of $H_2, H_3, H_4$ give
\begin{align}
    f_{2}|_{S} &= -f_{4} \\
    f_{2}|_{T} &= -f_{2} \\
    f_{4}|_{S} &= -f_{2} \\
    f_{4}|_{T} &= f_{3} = f_{2} + f_{4}.
\end{align}
Now, define
\begin{align}
    g &:= (2 H_2 + H_4) f_2 + (H_2 + 2 H_4) f_4 \\
    h &:= f_{2}^{2} + f_{2}f_{4} + f_{4}^{2}.
\end{align}
Then one can check that both $g$ and $h$ are invariant under the actions of $S$ and $T$, hence they are modular forms of level $1$.
Also, by analyzing the limit of $g$ and $h$ as $z \to i \infty$, one can see that $g$ and $h$ are cusp forms, hence $g = h = 0$ by \eqref{eqn:dimS6} and \eqref{eqn:dimS8}.
This implies
\begin{align}
    3 E_4 f_2^{2} &= 3 (H_2^2 + H_2 H_4 + H_4^2) f_2^{2} = ((2 H_2 + H_4)^{2} - (2H_2 + H_4)(H_2 + 2H_4) + (H_2 + 2H_4)^{2}) f_2^{2}\\
    &= (2 H_2 + H_4)^{2} (f_2^2 + f_2 f_4 + f_4^2) = 0
\end{align}
and by considering $q$-series ($E_4$ has an invertible $q$-series), we get $f_2 = 0$.
\end{proof}
```

:::theorem "thm:serre-der-prod-rule" (lean := "serre_D_mul") (parent := "serre_derivative")
The Serre derivative satisfies the following product rule: for any quasimodular
forms $`F` and $`G`,
$$`\partial_{w_1 + w_2} (FG) = (\partial_{w_1}F)G + F (\partial_{w_2}G).`
Uses {uses "def:serre-der"}[].
:::

```tex "thm:serre-der-prod-rule"
\begin{theorem}\label{thm:serre-der-prod-rule}\uses{def:serre-der} \lean{serre_D_mul} \leanok
The Serre derivative satisfies the following product rule: for any quasimodular forms $F$ and $G$,
\begin{equation}
    \partial_{w_1 + w_2} (FG) = (\partial_{w_1}F)G + F (\partial_{w_2}G).
\end{equation}
\end{theorem}
```

:::proof "thm:serre-der-prod-rule"
It follows from the definition:
$$`\partial_{w_1 + w_2} (FG) = (FG)' - \frac{w_1 + w_2}{12} E_2 (FG)`
$$`= F'G + FG' - \frac{w_1 + w_2}{12} E_2(FG)`
$$`= \left(F' - \frac{w_1}{12}E_2 F\right)G + F \left(G' - \frac{w_2}{12}E_2 G\right)`
$$`= (\partial_{w_1}F)G + F(\partial_{w_2}G).`
:::

```tex "thm:serre-der-prod-rule" (slot := "proof")
\begin{proof}
    \leanok
    It follows from the definition:
    \begin{align}
        \partial_{w_1 + w_2} (FG) &= (FG)' - \frac{w_1 + w_2}{12} E_2 (FG) \\
        &= F'G + FG' - \frac{w_1 + w_2}{12} E_2(FG) \\
        &= \left(F' - \frac{w_1}{12}E_2 F\right)G + F \left(G' - \frac{w_2}{12}E_2 G\right) \\
        &= (\partial_{w_1}F)G + F(\partial_{w_2}G).
    \end{align}
\end{proof}
```

:::theorem "thm:anti-serre-der-pos" (parent := "serre_derivative")
Let $`F` be a holomorphic quasimodular cusp form with real Fourier
coefficients. Assume that there exists $`k` such that
$`(\partial_{k}F)(it) > 0` for all $`t > 0`.
If the first Fourier coefficient of $`F` is positive, then $`F(it) > 0` for
all $`t > 0`.
Uses {uses "def:serre-der"}[] and {uses "cor:logder-disc-E2"}[].
:::

```tex "thm:anti-serre-der-pos"
\begin{theorem}\label{thm:anti-serre-der-pos}\uses{def:serre-der, cor:logder-disc-E2}
Let $F$ be a holomorphic quasimodular cusp form with real Fourier coefficients.
Assume that there exists $k$ such that $(\partial_{k}F)(it) > 0$ for all $t > 0$.
If the first Fourier coefficient of $F$ is positive, then $F(it) > 0$ for all $t > 0$.
\end{theorem}
```

:::proof "thm:anti-serre-der-pos"
By `eqn:logder-disc-E2` we have
$$`\frac{\dd}{\dd t} \left( \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}\right)
    = (-2 \pi) \frac{F'(it) \Delta(it)^{\frac{k}{12}} - F(it) \frac{k}{12} E_{2}(it) \Delta(it)^{\frac{k}{12}}}{\Delta(it)^{\frac{k}{6}}}
    = (-2 \pi) \frac{(\partial_{k} F)(it)}{\Delta(it)^{\frac{k}{12}}}  < 0.`
Hence the function
$`t \mapsto \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}` is monotone decreasing.
Because the first nonzero Fourier coefficient of $`F` is positive,
$`F(it) > 0` for sufficiently large $`t`:
$$`F = \sum_{n \geq n_{0}} a_{n} q^{n} \Rightarrow e^{2 \pi n_{0} t} F(it) = a_{n_{0}} + e^{-2 \pi t}\sum_{n\geq n_{0} + 1} a_{n} e^{-2 \pi (n - n_{0} - 1)t},`
and
$`\lim_{t \to \infty} e^{2 \pi n_{0}t} F(it) = a_{n_0} > 0`.
The result follows.
:::

```tex "thm:anti-serre-der-pos" (slot := "proof")
\begin{proof}
By \eqref{eqn:logder-disc-E2}, we have
\begin{align}
    \frac{\dd}{\dd t} \left( \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}\right)
    &= (-2 \pi) \frac{F'(it) \Delta(it)^{\frac{k}{12}} - F(it) \frac{k}{12} E_{2}(it) \Delta(it)^{\frac{k}{12}}}{\Delta(it)^{\frac{k}{6}}} \\
    &= (-2 \pi) \frac{(\partial_{k} F)(it)}{\Delta(it)^{\frac{k}{12}}}  < 0,
\end{align}
hence
\[
t \mapsto \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}
\]
is monotone decreasing.
Because of the assumption on the positivity of the first nonzero Fourier coefficient of $F$, $F(it) > 0$ for sufficiently large $t$ since
\[
F = \sum_{n \geq n_{0}} a_{n} q^{n} \Rightarrow e^{2 \pi n_{0} t} F(it) = a_{n_{0}} + e^{-2 \pi t}\sum_{n\geq n_{0} + 1} a_{n} e^{-2 \pi (n - n_{0} - 1)t}
\]
and $\lim_{t \to \infty} e^{2 \pi n_{0}t} F(it) = a_{n_0} > 0$, hence the result follows.
\end{proof}
```
