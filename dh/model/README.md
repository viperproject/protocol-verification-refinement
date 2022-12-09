# Tamarin model for Diffie-Hellman
[![DH & WireGuard Protocol Model Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)


## Files

- The `dh.spthy` file contains the Tamarin model, including the security properties and the auxiliary lemmas.


## Prerequisite

To verify our model of DH, you need **Tamarin**
which can be obtained from [its website](https://tamarin-prover.github.io).
Version 1.6.0 is known to work.

**Python2** is also required to run the oracle.



## Instructions

To verify the model with Tamarin, use the following command:

`tamarin-prover --prove dh.spthy`


## Verification with Docker
The model together with Tamarin and its dependencies are provided as a Docker image.
The image can be pulled and the Tamarin model can be verified as follows (assuming that Docker has been installed):
```
docker run -it ghcr.io/viperproject/protocol-verification-refinement-tamarin:latest tamarin-prover --prove dh.spthy
```
