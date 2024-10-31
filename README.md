# nbe-edsl

This repo contains the complete code for snippets in the article *Practical Normalization by Evaluation for EDSLs*, published at [Haskell '21](https://dl.acm.org/doi/proceedings/10.1145/3471874).

The published version of this article can be found [here](https://dl.acm.org/doi/10.1145/3471874.3472983) and the authors' version can be found [here](https://nachivpn.me/nbe-edsl.pdf).

Update (Nachi, Oct '24) : The objective of this work was to illustrate by example that Normalization by Evaluation (NbE) is a versatile program transformation technique that is amenable to programming in Haskell. I hope that the code here can serve as a useful starting point to play with NbE. This article suggests connections to staging and compiling eDSLs, but does not give any formal treatment to these claims. The suggested connections can be adopted for pedagogical purposes, but should not be given any serious consideration beyond that. The eDSL used here was chosen to make the implementation easier to illustrate, and should also not be taken very seriously :)

In ghci, load `Demo.hs` and try:

```
*Demo> norm cube
(\x0. (x0 * (x0 * x0)))
```
