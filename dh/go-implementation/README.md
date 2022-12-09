# Go Diffie-Hellman Implementation
[![DH Code Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/dh-code.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)

## Building & Running the Initiator Role
Build:
```
go build
```

Run:
```
./dh-gobra --isInitiator --endpoint localhost:12345 --privateKey "ACvCw0fb1mqTQikmXOas+YEbJnC9O/N4H12k4w/ADVRVg6YAptHsQO57FNzeeS2BtGwHas51wRruj62+y4WpjQ==" --peerPublicKey "H4omvaajENeqxbRiOVCLZoGUrEWIVrVAtJPk5JgoEV8="
```

The command above configures the Initiator to use Keypair 1 for its own secret key and tries to communicate with the Responder by using Keypair 2's public key.

Note that the Responder has to be started first.


Keypair 1:
    - sk: "ACvCw0fb1mqTQikmXOas+YEbJnC9O/N4H12k4w/ADVRVg6YAptHsQO57FNzeeS2BtGwHas51wRruj62+y4WpjQ=="
    - pk: "VYOmAKbR7EDuexTc3nktgbRsB2rOdcEa7o+tvsuFqY0="

Keypair 2:
    - sk: "k2gUarJExuxjji+KlwD8NfclZ+ZCZ8xZk3NGzN3ypwgfiia9pqMQ16rFtGI5UItmgZSsRYhWtUC0k+TkmCgRXw=="
    - pk: "H4omvaajENeqxbRiOVCLZoGUrEWIVrVAtJPk5JgoEV8="

## Verifying the Initiator Role
Gobra can be used as follows to successfully verify this implementation.
Detailed explanations and Gobra's JAR file are given in WireGuard's implementation folder.
```
java -Xss128m -jar ../../wireguard/implementation/gobra.jar -I verification -I ./ --module dh-gobra --directory initiator
```
