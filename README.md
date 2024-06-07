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
leading to a recovery of the partial key.  In practice, we ran the
attack 8 times over 2^16 structures, with a different random key for
each run.  We observed on average 5.6 (min: 3, max: 9) structures
leading to a key recovery.  This matches our analysis.

The code on the reduced AES from https://github.com/AugustinBariant/Truncated_boomerangs

In order to compile the code, just run `make`.  Then run `./boomerang6`
