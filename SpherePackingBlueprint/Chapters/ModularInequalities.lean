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


#doc (Manual) "Proof of the Optimal Function Inequalities" =>


:::group "fg_setup"
Auxiliary functions F and G and reformulation of inequalities.
:::

:::group "fg_differential"
Differential equations and monotonicity control.
:::

:::group "g_theorem"
Assembly of the final theorem producing the optimal function.
:::

Our proof of Theorem `thm:g` relies on the following two inequalities
for modular objects.

```tex
\section{Proof of Theorem \ref{thm:g}}\label{sec: g}
Our proof of the Theorem~\ref{thm:g} relies on the following two inequalities for modular objects.
```

:::lemma_ "prop:ineqA" (parent := "fg_setup")
Consider the function $`A:(0,\infty)\to\C` defined as
$$`A(t):=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).`
Then
$$`A(t) < 0`
for all $`t > 0`.
{uses "lemma:ineqABnew-equiv"}[]{uses "lemma:F-G-phi-psi-identities"}[]{uses "lemma:F-G-pos"}[]{uses "cor:ineqAnew"}[]
:::

```tex "prop:ineqA"
\begin{proposition}\label{prop:ineqA}\uses{lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, lemma:F-G-pos, cor:ineqAnew}
Consider the function $A:(0,\infty)\to\C$ defined as
\begin{equation}\label{eqn:defA}
A(t):=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).
\end{equation}
Then
\begin{equation}\label{eqn:ineqA}
    A(t) < 0
\end{equation}
for all $t > 0$.
\end{proposition}
```

:::lemma_ "prop:ineqB" (parent := "fg_setup")
Consider the function $`B:(0,\infty)\to\C` defined as
$$`B(t) := -t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it).`
Then
$$`B(t) > 0`
for all $`t > 0`.
{uses "lemma:ineqABnew-equiv"}[]{uses "lemma:F-G-phi-psi-identities"}[]{uses "cor:ineqBnew"}[]
:::

```tex "prop:ineqB"
\begin{proposition}\label{prop:ineqB}\uses{lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, cor:ineqBnew}
Consider the function $B:(0,\infty)\to\C$ defined as
\begin{equation}\label{eqn:defB}
    B(t) := -t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it)
\end{equation}
Then
\begin{equation}\label{eqn:ineqB}
    B(t) > 0
\end{equation}
for all $t > 0$.
\end{proposition}
```

Here we formalize the proof of the inequalities by {citet Lee}[].
First, we can rewrite the inequality in Proposition `prop:ineqA` as follows.

```tex
Here we formalize the proof of the inequalities by Lee \cite{Lee}.
First, we can rewrite the inequality in \ref{prop:ineqA} as follows.
```

:::definition "def:FG-definition" (lean := "F,G") (parent := "fg_setup")
Define two quasi-modular forms by
$$`F(z) = (E_2(z) E_4(z) - E_6(z))^2`
$$`G(z) = H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}).`
{uses "def:E2"}[]{uses "def:Ek"}[]{uses "def:H2-H3-H4"}[]
:::

```tex "def:FG-definition"
\begin{definition}\label{def:FG-definition}\uses{def:E2, def:Ek, def:H2-H3-H4}\lean{F,G}\leanok
Define two (quasi) modular forms as
\begin{align}
    F(z) &= (E_2(z) E_4(z) - E_6(z))^2 \label{eqn:defF} \\
    G(z) &= H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}). \label{eqn:defG}
\end{align}
\end{definition}
```

:::lemma_ "lemma:F-G-phi-psi-identities" (parent := "fg_setup")
We have
$$`\phi_0 = \frac{F}{\Delta}`
$$`\psi_S = -\frac{1}{2} \frac{G}{\Delta}.`
{uses "def:FG-definition"}[]{uses "lemma:psi-new"}[]
:::

```tex "lemma:F-G-phi-psi-identities"
\begin{lemma}\label{lemma:F-G-phi-psi-identities}\uses{def:FG-definition, lemma:psi-new}
We have
\begin{align}
    \phi_0 &= \frac{F}{\Delta} \label{eqn:phi0-F} \\
    \psi_S &= -\frac{1}{2} \frac{G}{\Delta}\label{eqn:psiS-G}
\end{align}
\end{lemma}
```

:::proof "lemma:F-G-phi-psi-identities"
Equation `eqn:phi0-F` is clear. Equation `eqn:psiS-G` is already shown in
Lemma `lemma:psi-new`.
:::

```tex "lemma:F-G-phi-psi-identities" (slot := "proof")
\begin{proof}
\eqref{eqn:phi0-F} is clear.
\eqref{eqn:psiS-G} is already shown in Lemma \ref{lemma:psi-new}.
\end{proof}
```

:::lemma_ "lemma:ineqABnew-equiv" (parent := "fg_setup")
Inequalities $`A(t) < 0` and $`B(t) > 0` are equivalent to
$$`F(it) + \frac{18}{\pi^2} G(it) > 0`
$$`F(it) - \frac{18}{\pi^2} G(it) > 0`
respectively.
{uses "lemma:F-G-phi-psi-identities"}[]{uses "def:psiI-psiT-psiS"}[]{uses "cor:disc-pos"}[]
:::

```tex "lemma:ineqABnew-equiv"
\begin{lemma}\label{lemma:ineqABnew-equiv}\uses{lemma:F-G-phi-psi-identities, def:psiI-psiT-psiS, cor:disc-pos}
Inequality \eqref{eqn:ineqA} and \eqref{eqn:ineqB} are equivalent to
\begin{align}
    F(it) + \frac{18}{\pi^2} G(it) > 0 \label{eqn:ineqAnew} \\
    F(it) - \frac{18}{\pi^2} G(it) > 0 \label{eqn:ineqBnew}
\end{align}
respectively.
\end{lemma}
```

:::proof "lemma:ineqABnew-equiv"
By the definition of $`\psi_I`,
$$`\psi_I(it) = (\psi_S|_{-2}S)(it) = (it)^{2}\psi_S\left(-\frac{1}{it}\right) = -t^2 \psi_S\left(\frac{i}{t}\right).`
Combined with Lemma `lemma:F-G-phi-psi-identities`, this rewrites
$`A(t) < 0` as
$$`-t^2 \phi_0\left(\frac{i}{t}\right) + \frac{36}{\pi^2} \psi_S\left(\frac{i}{t}\right) < 0 \Leftrightarrow \frac{F(it)}{\Delta(it)} + \frac{18}{\pi^2} \frac{G(it)}{\Delta(it)} > 0,`
which is equivalent to the first inequality by Corollary `cor:disc-pos`. The
second equivalence follows similarly, changing only the sign.
:::

```tex "lemma:ineqABnew-equiv" (slot := "proof")
\begin{proof}
By \eqref{eqn:psiS-define},
\begin{equation}
    \psi_I(it) = (\psi_S|_{-2}S)(it) = (it)^{2}\psi_S\left(-\frac{1}{it}\right) = -t^2 \psi_S\left(\frac{i}{t}\right).
\end{equation}
Combined with Lemma \ref{lemma:F-G-phi-psi-identities} we can rewrite \eqref{eqn:ineqA} as
\begin{equation}
    A(t) = -t^2 \phi_0\left(\frac{i}{t}\right) + \frac{36}{\pi^2} \psi_S\left(\frac{i}{t}\right) < 0 \Leftrightarrow \frac{F(it)}{\Delta(it)} + \frac{18}{\pi^2} \frac{G(it)}{\Delta(it)} > 0
\end{equation}
for $t > 0$, which is equivalent to \eqref{eqn:ineqAnew} by Corollary \ref{cor:disc-pos}.
Equivalences of \eqref{eqn:ineqB} and \eqref{eqn:ineqBnew} follows similarly; just change the sign.
\end{proof}
```

Now, the first inequality $`F(it) + \frac{18}{\pi^2} G(it) > 0` follows from
the positivity of each $`F(it)` and $`G(it)`.

```tex
Now, the first inequality \eqref{eqn:ineqAnew} follows from the positivity of each $F(it)$ and $G(it)$.
```

:::lemma_ "lemma:F-G-pos" (lean := "F_imag_axis_pos, G_imag_axis_pos") (parent := "fg_setup")
For all $`t > 0`, we have $`F(it) > 0` and $`G(it) > 0`.
{uses "thm:ramanujan-formula"}[]{uses "cor:theta-pos"}[]
:::

```tex "lemma:F-G-pos"
\begin{lemma}\label{lemma:F-G-pos}\uses{thm:ramanujan-formula, cor:theta-pos}\lean{F_imag_axis_pos, G_imag_axis_pos}\leanok
For all $t > 0$, we have $F(it) > 0$ and $G(it) > 0$.
\end{lemma}
```

:::proof "lemma:F-G-pos"
By Ramanujan's identity, we have $`F(z) = 9 E_4'(z)^2`, and hence
$$`F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.`
The inequality $`G(it) > 0` follows from positivity of $`H_2(it)` and
$`H_4(it)` in `cor:theta-pos`.
:::

```tex "lemma:F-G-pos" (slot := "proof")
\begin{proof}\leanok
By Ramanujan's identity \eqref{eqn:DE4}, we have $F(z) = 9 E_4'(z)^2$ and
\begin{equation}
    F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.
\end{equation}
$G(it) > 0$ follows from positivity of $H_2(it)$ and $H_4(it)$ (Lemma \ref{cor:theta-pos}).
\end{proof}
```

:::corollary "cor:ineqAnew" (lean := "FG_inequality_1") (parent := "fg_setup")
Equation `eqn:ineqAnew` holds.
{uses "lemma:F-G-pos"}[]
:::

```tex "cor:ineqAnew"
\begin{corollary}\label{cor:ineqAnew}\uses{lemma:F-G-pos}\lean{FG_inequality_1}\leanok
\eqref{eqn:ineqAnew} holds.
\end{corollary}
```

:::proof "cor:ineqAnew"
This directly follows from Lemma `lemma:F-G-pos`.
:::

```tex "cor:ineqAnew" (slot := "proof")
\begin{proof}
This directly follows from Lemma \ref{lemma:F-G-pos}.
\end{proof}
```

To prove the second inequality, we need some identities satisfied by $`F` and
$`G`.

```tex
To prove the second inequality \eqref{eqn:ineqBnew}, we need some identities satisfied by $F$ and $G$.
```

:::lemma_ "lemma:FG-de" (lean := "MLDE_F, MLDE_G") (parent := "fg_differential")
$`F` and $`G` satisfy the following differential equations:
$$`\partial_{12}\partial_{10} F - \frac{5}{6} E_{4} F = 7200 \Delta (-E_{2}')`
$$`\partial_{12}\partial_{10} G - \frac{5}{6} E_{4} G = -640 \Delta H_{2}.`
{uses "thm:ramanujan-formula"}[]{uses "thm:serre-der-prod-rule"}[]{uses "prop:theta-der"}[]{uses "lemma:lv1-lv2-identities"}[]
:::

```tex "lemma:FG-de"
\begin{lemma}\label{lemma:FG-de}\uses{thm:ramanujan-formula, thm:serre-der-prod-rule, prop:theta-der, lemma:lv1-lv2-identities}\lean{MLDE_F, MLDE_G}\leanok
$F$ and $G$ satisfy the following differential equations:
\begin{align}
    \partial_{12}\partial_{10} F - \frac{5}{6} E_{4} F &= 7200 \Delta (-E_{2}') \label{eqn:ddf} \\
    \partial_{12}\partial_{10} G - \frac{5}{6} E_{4} G &= -640 \Delta H_{2} \label{eqn:ddg}
\end{align}
\end{lemma}
```

:::proof "lemma:FG-de"
Both identities can be shown by direct computations.
By Ramanujan's identities (Theorem `thm:ramanujan-formula`) and the product
rule for Serre derivatives (Theorem `thm:serre-der-prod-rule`), we have
$$`\partial_{5} (E_2 E_4 - E_6)
 = (E_2 E_4 - E_6)' - \frac{5}{12} E_2 (E_2 E_4 - E_6)`
$$`= \frac{E_2^2 - E_4}{12} \cdot E_4 + E_2 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{E_2 E_6 - E_4^2}{2} - \frac{5}{12}E_2 (E_2 E_4 - E_6)
 = -\frac{5}{12} (E_2 E_6 - E_4^2)`
and
$$`\partial_{7} (E_2 E_6 - E_4^2)
 = (E_2 E_6 - E_4^2)' - \frac{7}{12} E_2 (E_2 E_6 - E_4^2)`
$$`= \frac{E_2^2 - E_4}{12} \cdot E_6 + E_2 \cdot \frac{E_2 E_6 - E_4^2}{2} - 2 E_4 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{7}{12} E_2 (E_2 E_6 - E_4^2)
 = -\frac{7}{12} E_4 (E_2 E_4 - E_6).`
Using these, we compute
$$`\partial_{10} F = \partial_{10} (E_2 E_4 - E_6)^2
 = 2 (E_2 E_4 - E_6) \partial_{5} (E_2 E_4 - E_6)
 = -\frac{6}{5} (E_2 E_4 - E_6) (E_2 E_6 - E_4^2),`
and then
$$`\partial_{12}\partial_{10} F
 = -\frac{5}{6} \partial_{12} ((E_2 E_4 - E_6) (E_2 E_6 - E_4))`
$$`= -\frac{5}{6} (\partial_{5}(E_2 E_4 - E_6)) (E_2 E_6 - E_4^2) - \frac{5}{6} (E_2 E_4 - E_6) (\partial_{7} (E_2 E_6 - E_4))
 = \frac{25}{72} (E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2.`
Hence
$$`\partial_{12}\partial_{10}F - \frac{5}{6} E_4 F
 = \frac{25}{72} ((E_2 E_6 - E_4^2)^2 - E_4 (E_2 E_4 - E_6)^2)
 = \frac{25}{72} (- E_2^2 E_4^3 + E_2^2 E_6^2 + E_4^4 - E_4 E_6^3)
 = -\frac{25}{72} (E_4^3 - E_6^2) (E_2^2 - E_4)
 = 7200 \Delta (-E_2').`
This proves equation `eqn:ddf`. The second is proved similarly,
using Proposition `prop:theta-der` and Lemma `lemma:lv1-lv2-identities`.
:::

```tex "lemma:FG-de" (slot := "proof")
\begin{proof}
Both can be shown by direct computations.
By Ramanujan's identities (Theorem \ref{thm:ramanujan-formula}) and the product rule of Serre derivatives (Theorem \ref{thm:serre-der-prod-rule}), we have
\begin{align}
    \partial_{5} (E_2 E_4 - E_6) &= (E_2 E_4 - E_6)' - \frac{5}{12} E_2 (E_2 E_4 - E_6) \\
    &= \frac{E_2^2 - E_4}{12} \cdot E_4 + E_2 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{E_2 E_6 - E_4^2}{2} - \frac{5}{12}E_2 (E_2 E_4 - E_6) \\
    &= -\frac{5}{12} (E_2 E_6 - E_4^2) \\
    \partial_{7} (E_2 E_6 - E_4^2) &= (E_2 E_6 - E_4^2)' - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
    &= \frac{E_2^2 - E_4}{12} \cdot E_6 + E_2 \cdot \frac{E_2 E_6 - E_4^2}{2} - 2 E_4 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\
    &= -\frac{7}{12} E_4 (E_2 E_4 - E_6)
\end{align}
and using these we can compute
\begin{align}
    \partial_{10} F &= \partial_{10} (E_2 E_4 - E_6)^2 \\
    &= 2 (E_2 E_4 - E_6) \partial_{5} (E_2 E_4 - E_6) \\
    &= -\frac{6}{5} (E_2 E_4 - E_6) (E_2 E_6 - E_4^2), \\
    \partial_{12}\partial_{10} F &= -\frac{5}{6} \partial_{12} ((E_2 E_4 - E_6) (E_2 E_6 - E_4)) \\
    &= -\frac{5}{6} (\partial_{5}(E_2 E_4 - E_6)) (E_2 E_6 - E_4^2) - \frac{5}{6} (E_2 E_4 - E_6) (\partial_{7} (E_2 E_6 - E_4)) \\
    &= \frac{25}{72} (E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2, \\
    \partial_{12}\partial_{10}F - \frac{5}{6} E_4 F &= \frac{25}{72}(E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2 - \frac{5}{6} E_4 (E_2 E_4 - E_6)^2 \\
    &= \frac{25}{72} ((E_2 E_6 - E_4^2)^2 - E_4 (E_2 E_4 - E_6)^2) \\
    &= \frac{25}{72} (- E_2^2 E_4^3 + E_2^2 E_6^2 + E_4^4 - E_4 E_6^3) \\
    &= -\frac{25}{72} (E_4^3 - E_6^2) (E_2^2 - E_4) \\
    &= 7200 \cdot \frac{E_4^3 - E_6^2}{1728} \cdot \frac{-E_2^2 + E_4}{12}\\
    &= 7200 \Delta (-E_2')
\end{align}
which proves \eqref{eqn:ddf}.
Similarly, \eqref{eqn:ddg} can be proved using Proposition \ref{prop:theta-der} and Lemma \ref{lemma:lv1-lv2-identities}.
\end{proof}
```

:::corollary "cor:MLDE-pos" (parent := "fg_differential")
Equation `eqn:ddf` is positive and equation `eqn:ddg` is negative on the
positive imaginary axis.
{uses "lemma:FG-de"}[]{uses "cor:disc-pos"}[]{uses "cor:theta-pos"}[]{uses "def:E2"}[]
:::

```tex "cor:MLDE-pos"
\begin{corollary}\label{cor:MLDE-pos}\uses{lemma:FG-de, cor:disc-pos, cor:theta-pos, def:E2}\leanok
\eqref{eqn:ddf} (resp. \eqref{eqn:ddg}) is positive (resp. negative) on the (positive) imaginary axis.
\end{corollary}
```

:::proof "cor:MLDE-pos"
From equation `eqn:E2` and Lemma `cor:disc-pos`,
$$`7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n t}\right) \cdot \Delta(it) > 0.`
Negativity of equation `eqn:ddg`, namely
$`-640 \Delta(it) H_2(it) < 0`, follows from
`cor:theta-pos` and `cor:disc-pos`.
:::

```tex "cor:MLDE-pos" (slot := "proof")
\begin{proof}
From \eqref{eqn:E2} and Lemma \ref{cor:disc-pos},
\begin{equation}
    7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n t}\right) \cdot \Delta(it) > 0. \notag
\end{equation}
Negativity of \eqref{eqn:ddg}, i.e. $-640 \Delta(it) H_2(it) < 0$ follows from Corollary \ref{cor:theta-pos} and \ref{cor:disc-pos}.
\end{proof}
```

The second inequality follows from the following two observations.
Since $`G(it) > 0` for all $`t > 0`, we can define the quotient
$$`Q(t) := \frac{F(it)}{G(it)}`
as a function on $`(0, \infty)`.

```tex

The second inequality \eqref{eqn:ineqBnew} follows from the following two observations.
Since $G(it) > 0$ for all $t > 0$, we can define the quotient
\begin{equation}\label{eqn:Q}
    Q(t) := \frac{F(it)}{G(it)}
\end{equation}
as a function on $(0, \infty)$.
```

:::lemma_ "lemma:Qlim" (lean := "FmodG_rightLimitAt_zero") (parent := "fg_differential")
We have
$$`\lim_{t \to 0^+} Q(t) = \frac{18}{\pi^2}.`
{uses "lemma:E2-transform-S"}[]{uses "lemma:Ek-is-modular-form"}[]{uses "lemma:theta-transform-S-T"}[]
:::

```tex "lemma:Qlim"
\begin{lemma}\label{lemma:Qlim}\uses{lemma:E2-transform-S, lemma:Ek-is-modular-form, lemma:theta-transform-S-T}\lean{FmodG_rightLimitAt_zero}\leanok
We have
\begin{equation}
    \lim_{t \to 0^+} Q(t) = \frac{18}{\pi^2}.
\end{equation}
\end{lemma}
```

:::proof "lemma:Qlim"
We have
$$`\lim_{t \to 0^+} Q(t) = \lim_{t \to 0^+} \frac{F(it)}{G(it)} = \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}.`
Using the transformation laws of Eisenstein series and theta-null functions, we
obtain
$$`F\left(\frac{i}{t}\right) = t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2`
and
$$`G\left(\frac{i}{t}\right) = t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2}).`
Since $`F`, $`E_2E_4-E_6`, and $`H_2` are cusp forms, we have
$`\lim_{t \to \infty} t^k A(it) = 0` when $`A(z)` is one of these forms and
$`k \ge 0`. From
$`\lim_{t \to \infty} E_4(it) = 1 = \lim_{t \to \infty} H_4(it)`, we conclude
that
$$`\lim_{t \to \infty} \frac{F(i/t)}{G(i/t)} = \frac{18}{\pi^2}.`
:::

```tex "lemma:Qlim" (slot := "proof")
\begin{proof}
We have
\begin{equation}
    \lim_{t \to 0^+} Q(t) = \lim_{t \to 0^+} \frac{F(it)}{G(it)} = \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}.
\end{equation}
By using the transformation laws of Eisenstein series \eqref{eqn:E2-S-transform}, \eqref{eqn:Ek-trans-S} (for $k = 4, 6$) and the thetanull functions, \eqref{eqn:H2-transform-S}, \eqref{eqn:H4-transform-S}, we get
\begin{align}
    F\left(\frac{i}{t}\right) &= t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2, \\
    G\left(\frac{i}{t}\right) &= t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2}).
\end{align}
Since $F$, $E_2 E_4 - E_6$ and $H_2$ are cusp forms, we have $\lim_{t \to \infty}t^k A(it) = 0$ when $A(z)$ is one of these forms and $k \geq 0$.
From $\lim_{t \to \infty} E_4(it) = 1 = \lim_{t \to \infty}H_{4}(it)$, we get
\begin{align}
    \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}
    &= \lim_{t \to \infty} \frac{t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2}{t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\
    &= \lim_{t \to \infty} \frac{t^{2} F(it) - \frac{12t}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36}{\pi^2}E_4(it)^2}{H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\
    &= \frac{18}{\pi^2}.
\end{align}
\end{proof}
```

:::lemma_ "lemma:log-der-inf" (parent := "fg_differential")
Let $`F` be a quasimodular form whose vanishing order at infinity is
$`n_0 > 0`, that is,
$`F(z) = \sum_{n \geq n_0} a_n q^{n}` with $`a_{n_0} \ne 0`. Then
$$`\lim_{t \to \infty} \frac{F'(it)}{F(it)} = n_0.`
{uses "lemma:der-q-series"}[]
:::

```tex "lemma:log-der-inf"
\begin{lemma}\label{lemma:log-der-inf}\uses{lemma:der-q-series}
Let $F$ be a quasimodular form where the vanishing order of $F$ at infinity is $n_0 > 0$, i.e. $F(z) = \sum_{n \geq n_0} a_n q^{n}$ with $a_{n_0} \ne 0$. Then
\begin{equation}
    \lim_{t \to \infty} \frac{F'(it)}{F(it)} = n_0.
\end{equation}
\end{lemma}
```

:::proof "lemma:log-der-inf"
By Lemma `lemma:der-q-series`,
$$`\lim_{t \to \infty} \frac{F'(it)}{F(it)}
 = \lim_{t \to \infty} \frac{\sum_{n \ge n_0} n a_n e^{-2 \pi n t}}{\sum_{n \ge n_0} a_n e^{-2 \pi n t}}
 = \lim_{t \to \infty} \frac{n_0 a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})}{a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})}
 = n_0.`
:::

```tex "lemma:log-der-inf" (slot := "proof")
\begin{proof}
    By Lemma \ref{lemma:der-q-series},
    \begin{equation}
        \lim_{t \to \infty} \frac{F'(it)}{F(it)} = \lim_{t \to \infty} \frac{\sum_{n \ge n_0} n a_n e^{-2 \pi n t}}{\sum_{n \ge n_0} a_n e^{-2 \pi n t}} = \lim_{t \to \infty} \frac{n_0 a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})}{a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})} = n_0.
    \end{equation}
\end{proof}
```

:::lemma_ "prop:Qdec" (lean := "FmodG_strictAntiOn") (parent := "fg_differential")
The function $`t \mapsto Q(t)` is strictly decreasing.
{uses "thm:ramanujan-formula"}[]{uses "thm:serre-der-prod-rule"}[]{uses "cor:MLDE-pos"}[]{uses "thm:anti-serre-der-pos"}[]{uses "lemma:log-der-inf"}[]
:::

```tex "prop:Qdec"
\begin{proposition}\label{prop:Qdec}\uses{thm:ramanujan-formula, thm:serre-der-prod-rule, cor:MLDE-pos, thm:anti-serre-der-pos, lemma:log-der-inf}\lean{FmodG_strictAntiOn}\leanok
The function $t \mapsto Q(t)$ is strictly decreasing.
\end{proposition}
```

:::proof "prop:Qdec"
It is enough to show that
$$`\frac{\dd}{\dd t} \left(\frac{F(it)}{G(it)}\right) < 0
\Leftrightarrow (- 2\pi) \frac{F'(it)G(it) - F(it) G'(it)}{G(it)^{2}} < 0
\Leftrightarrow F'(it) G(it) - F(it) G'(it) > 0
\Leftrightarrow (\partial_{10}F)(it) G(it) - F(it) (\partial_{10}G)(it) > 0.`
Let $`\mathcal{L}_{1, 0} := (\partial_{10}F) G - F (\partial_{10} G) = F'G - FG'`.
Then
$$`\frac{\mathcal{L}_{1, 0}}{FG} = \frac{F'G - FG'}{FG} = \frac{F'}{F} - \frac{G'}{G}.`
The vanishing orders of $`F` and $`G` at infinity are $`2` and
$`\frac{3}{2}` respectively, so by `lemma:log-der-inf` we have
$$`\lim_{t \to \infty} \frac{\mathcal{L}_{1, 0}(it)}{F(it) G(it)}
 = \lim_{t \to \infty} \left(\frac{F'(it)}{F(it)} - \frac{G'(it)}{G(it)}\right)
 = 2 - \frac{3}{2} = \frac{1}{2} > 0,`
so $`\mathcal{L}_{1, 0}(it) > 0` for sufficiently large $`t`.
Its Serre derivative is positive by `cor:MLDE-pos`:
$$`\partial_{22} \mathcal{L}_{1, 0} = (\partial_{12} \partial_{10} F) G - F (\partial_{12}\partial_{10} G)
    = \Delta (7200 (-E_{2}') G + 640 H_2 F) > 0.`
Hence $`\mathcal{L}_{1, 0}(it) > 0` by `thm:anti-serre-der-pos`, and the
monotonicity follows.
:::

```tex "prop:Qdec" (slot := "proof")
\begin{proof}
It is enough to show that
\begin{align}
    \frac{\dd}{\dd t} \left(\frac{F(it)}{G(it)}\right) < 0 &\Leftrightarrow (- 2\pi) \frac{F'(it)G(it) - F(it) G'(it)}{G(it)^{2}} < 0 \\
    &\Leftrightarrow F'(it) G(it) - F(it) G'(it) > 0 \\
    &\Leftrightarrow (\partial_{10}F)(it) G(it) - F(it) (\partial_{10}G)(it) > 0.
\end{align}
Let $\mathcal{L}_{1, 0} := (\partial_{10}F) G - F (\partial_{10} G) = F'G - FG'$.
Then
\begin{align}
\frac{\mathcal{L}_{1, 0}}{FG} = \frac{F'G - FG'}{FG} = \frac{F'}{F} - \frac{G'}{G}
\end{align}
The vanishing order of $F$ and $G$ at the infinity are $2$ and $\frac{3}{2}$ respectively, so by Lemma \ref{lemma:log-der-inf}, we have
\begin{align}
    \lim_{t \to \infty} \frac{\mathcal{L}_{1, 0}(it)}{F(it) G(it)} = \lim_{t \to \infty} \left(\frac{F'(it)}{F(it)} - \frac{G'(it)}{G(it)}\right) = 2 - \frac{3}{2} = \frac{1}{2} > 0
\end{align}
so $\mathcal{L}_{1, 0}(it) > 0$ for sufficiently large $t$.
Its Serre derivative $\partial_{22} \mathcal{L}_{1, 0}$ is positive by Corollary \ref{cor:MLDE-pos}:
\begin{align}
    \partial_{22} \mathcal{L}_{1, 0} = (\partial_{12} \partial_{10} F) G - F (\partial_{12}\partial_{10} G)
    = \Delta (7200 (-E_{2}') G + 640 H_2 F) > 0.
\end{align}
Hence $\mathcal{L}_{1, 0}(it) > 0$ by Theorem \ref{thm:anti-serre-der-pos}, and the monotonicity follows.
\end{proof}
```

:::corollary "cor:ineqBnew" (lean := "FG_inequality_2") (parent := "fg_differential")
Equation `eqn:ineqBnew` holds.
{uses "lemma:Qlim"}[]{uses "prop:Qdec"}[]{uses "lemma:F-G-pos"}[]
:::

```tex "cor:ineqBnew"
\begin{corollary}\label{cor:ineqBnew} \uses{lemma:Qlim, prop:Qdec, lemma:F-G-pos}\lean{FG_inequality_2}
\eqref{eqn:ineqBnew} holds.
\end{corollary}
```

:::proof "cor:ineqBnew"
We have
$$`\frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2},`
and by Lemma `lemma:F-G-pos` the desired inequality follows.
:::

```tex "cor:ineqBnew" (slot := "proof")
\begin{proof}
\begin{equation}
    \frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2}
\end{equation}
and by Lemma \ref{lemma:F-G-pos}, \eqref{eqn:ineqBnew} follows.
\end{proof}
```

Finally, we are ready to prove Theorem `thm:g`.

```tex

Finally, we are ready to prove Theorem~\ref{thm:g}.
```

:::theorem "thm:g1" (parent := "g_theorem")
The function
$$`g(x):=\frac{\pi\,i}{8640}a(x)+\frac{i}{240\pi}\,b(x)`
satisfies the conditions of Theorem `thm:g`.
{uses "prop:a-fourier"}[]{uses "prop:b-fourier"}[]{uses "prop:a-double-zeros"}[]{uses "prop:b-double-zeros"}[]{uses "prop:ineqA"}[]{uses "prop:ineqB"}[]{uses "prop:a0"}[]{uses "prop:b0"}[]
:::

```tex "thm:g1"
\begin{theorem}\label{thm:g1}
\uses{prop:a-fourier, prop:b-fourier, prop:a-double-zeros, prop:b-double-zeros, prop:ineqA, prop:ineqB, prop:a0, prop:b0}
The function
$$g(x):=\frac{\pi\,i}{8640}a(x)+\frac{i}{240\pi}\,b(x)$$
satisfies conditions \eqref{eqn:g1}--\eqref{eqn:g3}.
\end{theorem}
```

:::proof "thm:g1"
First, we prove the first sign condition. By Propositions
`prop:a-double-zeros` and `prop:b-double-zeros` we know
that for $`r>\sqrt{2}`,
$$`g(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty A(t)\,e^{-\pi r^2 t}\,dt`
where
$$`A(t)=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).`
From Proposition `prop:ineqA` we know that $`A(t)<0` for
$`t\in(0,\infty)`, so this identity implies the first sign condition.

Next, we prove the Fourier-side sign condition. By Propositions
`prop:a-another-integral` and `prop:b-another-integral` we
know that for $`r>0`,
$$`\widehat{g}(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty B(t)\,e^{-\pi r^2 t}\,dt`
where
$$`B(t)=-t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it).`

Finally, the normalization $`g(0)=\widehat g(0)=1` follows readily from
Propositions `prop:a0` and `prop:b0`.
This finishes the proof of Theorems `thm:g1` and `thm:g`.
:::

```tex "thm:g1" (slot := "proof")
\begin{proof}
First, we prove that \eqref{eqn:g1} holds. By Propositions~\ref{prop:a-double-zeros} and \ref{prop:b-double-zeros} we know that for $r>\sqrt{2}$
\begin{equation} g(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty A(t)\,e^{-\pi r^2 t}\,dt\end{equation}
where $$A(t)=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it).$$
from the Proposition~\ref{prop:ineqA} we know that $A(t)<0\quad\mbox{for}\;t\in(0,\infty).$
Therefore identity \eqref{eqn:g A} implies \eqref{eqn:g1}.

Next, we prove \eqref{eqn:g2}. By Propositions~\ref{prop:a-another-integral} and~\ref{prop:b-another-integral} we know that for $r>0$
\begin{equation} \widehat{g}(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty B(t)\,e^{-\pi r^2 t}\,dt\end{equation}
where $$B(t)=-t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it).$$


Finally, the property \eqref{eqn:g3} readily follows from Proposition~\ref{prop:a0} and Proposition~\ref{prop:b0}.
This finishes the proof of Theorems~\ref{thm:g1} and~\ref{thm:g}.
\end{proof}
```
