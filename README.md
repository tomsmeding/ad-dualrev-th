# Parallel dual-numbers reverse AD using Template Haskell

*Documentation has been rendered [here][docrender].*

This is an implementation of the algorithm described in [our paper at POPL '23][popl23] ([with appendices][popl23arxiv]), extended with basic support for task parallelism as described in our upcoming JFP publication.
The sequential algorithm is what you get if you take standard dual-numbers reverse AD as described e.g. by [Brunel et al. (2019)][brunel] and [Huot et al. (2020, §6)][huot], as well as in [Fig. 6 of our paper][popl23], and optimise it to be efficient.
For details on how exactly these code transformations look and what the reasoning behind them is, we refer to [our paper][popl23].


[popl23]: https://dl.acm.org/doi/10.1145/3571247
[popl23arxiv]: https://arxiv.org/pdf/2207.03418.pdf
[brunel]: https://arxiv.org/pdf/1909.13768.pdf
[huot]: https://arxiv.org/pdf/2001.02209.pdf
[docrender]: https://tomsmeding.com/f/ad-dualrev-th-parallel-docs/Language-Haskell-ReverseAD-TH.html
