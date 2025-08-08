# Hopf 2-cocycles of type $A_2$

## Abstract

We compute the Hopf 2-cocycles involved in the classification of pointed Hopf algebras of diagonal type $A_2$. 
When the quantum Serre relations are deformed, we characterize those cocycles that can be recovered from Hochschild cohomology, via exponentiation.
We identify some hypotheses that allow us to present general formulas that apply in our setting.


### About the files

- `generic.g`: This code computes the values of the cocycle $\sigma_{\boldsymbol{\lambda}}$ associated with generic deformations of type $A_2$, with parameter $q$, a primitive root of unity of order $n \geq 3$. The code is preconfigured with $n = 3$, but it can be set to any $n \geq 3$.
The function "tigma(n2, n12, n1, m2, m12, m1)" returns the value $\sigma_{\boldsymbol{\lambda}}\big(x_2^{n_2} x_{12}^{n_{12}} x_1^{n_1}, x_2^{m_2} x_{12}^{m_{12}} x_1^{m_1}\big)$, provided that $n_2, n_{12}, n_1, m_2, m_{12}, m_1\in \mathbb{I}_{N-1}^\circ$. This function covers every possible case in

$$\epsilon_0(\gamma_{\boldsymbol{\lambda}}(x_2^{n_2}x_{12}^{n_{12}}x_1^{n_1})\gamma_{\boldsymbol{\lambda}}(x_2^{m_2}x_{12}^{m_{12}}x_1^{m_1})).$$

- `atypical.g`: This code computes the value of the cocycle $\sigma_{\boldsymbol{\lambda}}$ of Cartan type $A_2$, associated with atypical deformations, i.e., when the quantum Serre relations are deformed.
The function "osigma(a, b, c, A, B, C)" returns the value of the cocycle on the basis element  $x_2^a x_{12}^b x_1^c \otimes x_2^A x_{12}^B x_1^C$ for $0 \leq a, b, c, A, B, C \leq 2$.  
The computation is based on the description of the coproduct in the basis of the algebra $\mathfrak{B} \otimes \mathfrak{B}$ and subsequently applies the formula, for $x = x_2^a x_{12}^b x_1^c$ and $y = x_2^A x_{12}^B x_1^C$,

$$\alpha(x_{(1)}) \alpha(y_{(1)}) \sigma(x_{(2)}, y_{(2)}) \alpha^{-1}(x_{(3)} y_{(3)}).$$

- `exponential.g`: This code computes the value of any exponential of a Hochschild cocycle $\eta$ for $\mathfrak{B}$, such that $\eta(1,1) = 0$. Here, $\mathfrak{B}$ is the Nichols algebra of type $A_2$ associated with the atypical braiding $\mathfrak{q}$, where $q_{12} = q_{21} = q$.  

The function "exponential(a, b, c, A, B, C)" returns the value  $e^\eta(x_2^{a} x_{12}^{b} x_1^{c},\; x_2^{A} x_{12}^{B} x_1^{C})$ for $0 \leq a, b, c, A, B, C \leq 2$.  

Its computation is based on describing the coproduct $\Delta^k$ for $k=1,2,3,4$ and applying the formula for the exponential of $\eta$. The code also includes the truncated versions of the exponential: exponential2, ..., exponential4.

For more details, see preprint [ArXiv](https://arxiv.org/user/).
