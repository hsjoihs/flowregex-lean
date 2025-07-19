# flowregex-lean

This repository is intended to serve as a formalization of https://github.com/atsushi-yamamoto2/flowregex 

## Overview of what FlowRegex does

Let $\Sigma$ be an alphabet, and $R(\Sigma)$ be the set of all regular expressions over $\Sigma$.

Fix a string $\mathrm{target} : \Sigma^N$ and then $\mathrm{FlowRegex}_{\mathrm{target}}$ is a mapping from $R(\Sigma)$ to $\lbrace 0, 1\rbrace^{N+1} \to \lbrace 0, 1\rbrace^{N+1}$, defined recursively as follows:

- $\emptyset : R(\Sigma) \mapsto (v \mapsto 0^{N+1})$ 
- $\mathrm{char}(a : \Sigma) : R(\Sigma) \mapsto (v \mapsto v')$, where $v'[0] = 0;\ \ v'[i + 1] = \mathrm{if} (\mathrm{target}[i] = a) \mathrm{then} v[i] \mathrm{else} 0$
- $\alpha + \beta \mapsto (v \mapsto \mathrm{BitOr}\left(\mathrm{FlowRegex}_ {\mathrm{target}}(\alpha)(v), \mathrm{FlowRegex}_{\mathrm{target}}(\beta)(v)\right))$
- $\alpha\beta \mapsto \mathrm{FlowRegex}_ {\mathrm{target}}(\beta) \circ \mathrm{FlowRegex}_ {\mathrm{target}}(\alpha)$
- $\alpha^* \mapsto \Bigl(v \mapsto \mathrm{BitOr}\left( v, \mathrm{FlowRegex}_{\mathrm{target}}(\alpha)(v)\right)\Bigr)^{\circ (N+1)}$

In English, 
- The regular expression that represents an empty set is sent to a function that always returns an empty bit vector
- The regular expression that represents a single character $a$ is sent to a function that inspects each bit in the input vector and shifts it to the right under the condition that the corresponding character in the target string matches $a$.
- The regular expression that represents a union of two expressions is sent to a function that computes the bitwise OR of the results of the two expressions.
- The regular expression that represents a concatenation of two expressions is sent to a function composition of the two expressions.
- The regular expression that represents a Kleene star is sent to a function that computes the bitwise OR of the input vector and the result of applying the expression to the input vector, and then applies this operation $N+1$ times.

The only non-trivial part is the Kleene star: it must equal to the fixed point reached by repeatedly applying $\Bigl(v \mapsto \mathrm{BitOr}\left( v, \mathrm{FlowRegex}_{\mathrm{target}}(\alpha)(v)\right)\Bigr)$. The fixed point always exists, since the bit can only change from 0 to 1, and there are only $N+1$ bits. In other words, this is because of the Kleene fixed-point theorem on the power set lattice: by applying the function, you can either stay at the same set or climb up to a larger set, and in the power set lattice of $\lbrace 0, 1\rbrace^{N+1}$ you can only climb up to $N+1$ times.