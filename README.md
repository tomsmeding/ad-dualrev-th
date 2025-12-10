# Parallel dual-numbers reverse AD using Template Haskell

*Documentation has been rendered [here][docrender].*

This is an implementation of the algorithm described in [our paper at POPL '23][popl23] ([with appendices][popl23arxiv]), extended with basic support for task parallelism as described in an [extended version in JFP][jfp25].
The sequential algorithm is what you get if you take standard dual-numbers reverse AD as described e.g. by [Brunel et al. (2019)][brunel] and [Huot et al. (2020, §6)][huot], as well as in [Fig. 6 of our paper][popl23], and optimise it to be efficient.
For details on how exactly these code transformations look and what the reasoning behind them is, we refer to [our paper][jfp25].

The non-parallel version of the implementation submitted as artifact for the POPL '23 paper can be found at [commit 88854d0f2][seqcommit].

This is a reference implementation.
While it correctly implements the algorithms, better performance can probably be obtained using basic taping as done in [ad](https://hackage.haskell.org/package/ad), although implementing the transformation at compile time (as this library does) does yield better performance in some cases, as GHC can optimise some intermediate computations.
Any library with first-class support for arrays will be orders of magnitude faster than this library for array-heavy code.

## Usage

This is a normal Haskell library, to be used in the standard fashion with Cabal or Stack.

The user API is exported from the `Language.Haskell.ReverseAD.TH` module.
There is a test suite (`test`) and a Criterion benchmark suite (`bench`) included in the package.
The script `generate_table_1.py` runs the benchmarks and generates something like Table 1 in [the paper][jfp25].

## Licence and citing

The code in this repository is available under the MIT licence from the authors of the [paper][jfp25].

```bibtex
@article{smeding-vakar-2025-parallel-dualrev,
  author={Smeding, Tom J. and V{\'a}k{\'a}r, Matthijs I. L.},
  title={Parallel dual-numbers reverse {AD}},
  volume={35},
  doi={10.1017/S0956796825100051},
  journal={Journal of Functional Programming},
  year={2025},
  pages={e16}
}
```

To cite this implementation specifically, you may also use:
```bibtex
@misc{2025-ad-dualrev-th,
  author = {Smeding, Tom J. and V{\'{a}}k{\'{a}}r, Matthijs I. L.},
  title = {Implementation of parallel dual-numbers reverse AD in Haskell},
  month = {8},
  year = {2025},
  url = {https://github.com/tomsmeding/ad-dualrev-th}
}
```

In case of questions or interest, feel free to reach out to me ([tomsmeding.com](https://tomsmeding.com/)).

This project received funding from NWO Veni grant number VI.Veni.202.124 and the ERC project FoRECAST.


[popl23]: https://dl.acm.org/doi/10.1145/3571247
[popl23arxiv]: https://arxiv.org/pdf/2207.03418.pdf
[jfp25]: https://doi.org/10.1017/S0956796825100051
[brunel]: https://arxiv.org/pdf/1909.13768.pdf
[huot]: https://arxiv.org/pdf/2001.02209.pdf
[docrender]: https://tomsmeding.com/f/ad-dualrev-th-parallel-docs/Language-Haskell-ReverseAD-TH.html
[seqcommit]: https://github.com/tomsmeding/ad-dualrev-th/commit/88854d0f20177afec0b979298dd25ffea069827e
