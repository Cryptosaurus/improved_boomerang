# Improved Boomerang Attacks on 6-round AES

This repository contains code for the paper:

> *Improved Boomerang Attacks on 6-round AES*
> Augustin Bariant, Orr Dunkelman, Nathan Keller, Gaëtan Leurent, Victor Mollimard

## Description

We have experimentally implemented (a simplified version of) the attack
of Section 4.2 (Algorithm 3) against a reduced AES with 4-bit SBoxes.

For simplicity we fix in advance the value of the inactive byte 'a' and
the position of the inactive antidiagonals (step 2).  Following the
analysis in the paper, we expect that a fraction 2^-13 of the structures
contain a right pair, and this should be detected with probability 63%,
leading to a recovery of the partial key.

The implementation of the reduced AES is from https://github.com/AugustinBariant/Truncated_boomerangs

In order to compile the code, just run `make`.  Then run `./boomerang6`

## Parallelization

The code is parallelized using OpenMP.  However, the complexity
estimation when using several core is slightly off because some cores
will have processed a partial structure when another core find the
correct key.  To get the best complexity estimate you should disable
OpenMP.
