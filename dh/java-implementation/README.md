# Java Diffie-Hellman Implementation
[![DH Code Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)

## Building & Running the Responder Role
Build:
```
gradle build
```

Run:
```
java -jar dh-gobra.jar --port 12345 --privateKey "k2gUarJExuxjji+KlwD8NfclZ+ZCZ8xZk3NGzN3ypwgfiia9pqMQ16rFtGI5UItmgZSsRYhWtUC0k+TkmCgRXw==" --peerPublicKey "VYOmAKbR7EDuexTc3nktgbRsB2rOdcEa7o+tvsuFqY0="
```

The command above configures the Responder to use Keypair 2 for its own secret key and tries to communicate with the Initiator by using Keypair 1's public key.

Note that the Responder has to be started first.


Keypair 1:
    - sk: "ACvCw0fb1mqTQikmXOas+YEbJnC9O/N4H12k4w/ADVRVg6YAptHsQO57FNzeeS2BtGwHas51wRruj62+y4WpjQ=="
    - pk: "VYOmAKbR7EDuexTc3nktgbRsB2rOdcEa7o+tvsuFqY0="

Keypair 2:
    - sk: "k2gUarJExuxjji+KlwD8NfclZ+ZCZ8xZk3NGzN3ypwgfiia9pqMQ16rFtGI5UItmgZSsRYhWtUC0k+TkmCgRXw=="
    - pk: "H4omvaajENeqxbRiOVCLZoGUrEWIVrVAtJPk5JgoEV8="

## Verifying the Responder Role
The responder role can successfully be verified using VeriFast release 18.02 using the following command:
```
verifast -allow_assume -c src/main/java/dhgobra/responder/Responder.jarsrc
```
