Description
--

This repository contains Magma code for calculating with CM curves, as well as some results that were obtained by using the routines in it.

Installation 
--

You can enable the functionality of this code in Magma by attaching the `spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding a line such as
```
AttachSpec("~/Programs/cm-calculations/spec");
```
Please be sure to install the prerequisites [`edgarcosta/endomorphisms`](https://github.com/edgarcosta/endomorphisms) and [`JRSijsling/curve_reconstruction`](https://github.com/JRSijsling/curve_reconstruction) beforehand.

Usage
--

Examples are given in the directory `examples/`.
