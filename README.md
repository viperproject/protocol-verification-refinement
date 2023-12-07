# Sound Verication of Security Protocols: From Design to Interoperable Implementations (artifact)

[![DH & WireGuard Protocol Model Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/model.yml?query=branch%3Amain)
[![DH Code Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml?query=branch%3Amain)
[![WireGuard Code Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/wireguard-code.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/wireguard-code.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](./LICENSE)

## I/O Specification Generator & Diffie-Hellman (DH) and WireGuard Case Studies

This repository contains the artifact for the paper "Sound Verication of Security Protocols: From Design to Interoperable Implementations", which appeared at the IEEE Symposium on Security and Privacy (S&P), 2023.
[[published version]](https://doi.org/10.1109/SP46215.2023.10179325)
[[extended version]](https://pm.inf.ethz.ch/publications/ArquintWolfLallemandSasseSprengerWiesnerBasinMueller22.pdf)

This artifact provides the following content:
- Subdirectory `wireguard/model` contains the Tamarin model together with instructions how to verify it
- Subdirectory `wireguard/implementation` contains the verified Go implementation together with instructions how to verify and execute it.
- The subdirectory `dh` contains the verified DH protocol model together with a verified Go and Java implementations. Additionally, `dh/faulty-go-implementation` contains a Go implementation that tries to send the DH private key in plaintext for which verification fails because the IO specification does not permit such a send operation.
- The subdirectory `specification-generator` contains the sources of our tool to generate I/O specifications for Gobra & VeriFast from a Tamarin model.

This artifact has been archived on Zenodo (DOI: [10.5281/zenodo.7409524](https://doi.org/10.5281/zenodo.7409524)). The paper can be cited as follows (for BibTeX):

```BibTex
@inproceedings{ArquintWLSSWBM23,
  author = {Arquint, Linard and Wolf, Felix A. and Lallemand, Joseph and Sasse, Ralf and Sprenger, Christoph and Wiesner, Sven N. and Basin, David and M\"uller, Peter},
  booktitle = {2023 IEEE Symposium on Security and Privacy (SP)},
  title = {Sound Verification of Security Protocols: From Design to Interoperable Implementations},
  year = {2023},
  volume = {},
  number = {},
  pages = {1077-1093},
  keywords = {protocol-verification;symbolic-security;automated-verification;tamarin;separation-logic;implementation},
  publisher = {IEEE},
  month = may,
  doi = {10.1109/SP46215.2023.10179325},
  url = {https://doi.org/10.1109/SP46215.2023.10179325},
  urltext = {Publisher},
  url1 = {https://pm.inf.ethz.ch/publications/ArquintWolfLallemandSasseSprengerWiesnerBasinMueller23.pdf},
  url1text = {PDF}
}
```
