# RGBeta: Evaluator of Renormalization Group Beta-Functions
Modified version including results for 3-loop Yukawa and 4-loop gauge beta functions from [arXiv:2105.09918](https://arxiv.org/abs/2105.09918) and color algebra for general group

Test for new features are provided inside `TestArbG/`

---

RGBeta is a Mathematica package that allows the user to extract RG beta-functions up to loop order 3-2-2 for gauge, Yukawa, and quartic couplings, respectively, for a large class of 4D renormalizable models.

If you use RGBeta, please cite [arXiv:2101.08265](https://arxiv.org/abs/2101.08265). When using RGBeta to extract the 3-loop gauge beta functions, please also consider citing [arXiv:hep-ph/0104247](https://arxiv.org/abs/hep-ph/0104247) and [arXiv:1906.04625](https://arxiv.org/abs/1906.04625) for multi-coupling theories.

## Installation and use
The simplest way to download and install RGBeta is to run the command
> Import["https://raw.githubusercontent.com/aethomsen/RGBeta/master/Install.m"]

to install RGBeta directly to the Applications folder in Mathematica's base directory, *$UserBaseDirectory*. After the install RGBeta can be loaded into any Mathematica notebook with
> << RGBeta`

As an alternative to the more permanent installation, simply download the github repository. RGBeta can then be run from a Mathematica notebook in the base directory with the following lines:
> SetDirectory@NotebookDirectory[];
> << RGBeta`

The core use of RGBeta is described in the manual. The *Documentation* folder contains a tutorial notebook and a notebook with sample models, which can be used by the user. 

## Author
 - Anders Eller Thomsen (@aethomsen)

## License
RGBeta is free software under the MIT license.
