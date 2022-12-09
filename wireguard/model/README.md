# Tamarin model for WireGuard key exchange
[![DH & WireGuard Protocol Model Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)


## Files

- The `wireguard.spthy` file contains the Tamarin model, including the security properties and the auxiliary lemmas.

- The `wireguard.oracle` file contains an oracle (an auxiliary python script providing a heuristic to guide Tamarin's proof search).


## Prerequisite

To verify our model of the WireGuard key exchange, you need **Tamarin**
which can be obtained from [its website](https://tamarin-prover.github.io).
Version 1.6.0 is known to work.

**Python2** is also required to run the oracle.



## Instructions

To verify the model with Tamarin, use the following command:

`tamarin-prover --heuristic=O --oraclename="wireguard.oracle" --prove wireguard.spthy`


## Verification with Docker
The model together with Tamarin and its dependencies are provided as a Docker image.
The image can be pulled and the Tamarin model can be verified as follows (assuming that Docker has been installed):
```
docker run -it ghcr.io/viperproject/protocol-verification-refinement-tamarin:latest tamarin-prover --heuristic=O --oraclename="wireguard.oracle" --prove wireguard.spthy
```
