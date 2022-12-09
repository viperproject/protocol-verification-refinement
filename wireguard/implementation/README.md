# Verified Wireguard Implementation
[![WireGuard Code Verification](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/wireguard-code.yml/badge.svg?branch=main)](https://github.com/viperproject/protocol-verification-refinement/actions/workflows/wireguard-code.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)

## Verifying & Running Initiator & Responder in Docker
The sources of this verified implementation together with the code verifier Gobra and its dependencies are provided as a Docker image.
The image can be pulled and started in interactive mode as follows (assuming that Docker has been installed):
```
docker run -it ghcr.io/viperproject/protocol-verification-refinement-wireguard:latest bash
```
An interactive shell at the working directory `/gobra` is started.
In this directory, you find the source code of our WireGuard case study.
Furthermore, several scripts provide easy access to the common operations:
- `./compile.sh` compiles the source code and creates a binary called `wireguard-gobra`
- `./verify.sh` verifies the initiator and responder roles. Due to the virtualized environment and differing hardware, verification of both roles might take a while. We have observed ~11min (compared to 7.8min when verifying them in a non-virtualized environment, as reported in the paper).
- `./test.sh` runs the initiator and responder as two separate processes. The script pipes two messages via standard input to each role that are then sent via VPN to the other role.

### Limitations of the Docker Image
We recommend using the ready-to-use Docker image over a local installation.
Note however that the Docker image only provides a limited environment for executing the implementation.
In particular, executing the initiator and responder in an interactive way would require two processes each accepting input.
Also, routing traffic from the OS (such as ping packets) requires additional setup for the network interfaces that we do not support in the Docker image.
Therefore, the remainder of this document provides detailed steps for verifying and executing the verified WireGuard implementation in a non-virtualized environment.


## Verifying Initiator & Responder Non-Virtualized
Note that the commands have been tested on macOS.
For verification outside of docker, Gobra JAR (provided in the repository) and an executable of the Z3 SMT solver (version 4.8.7) is required. An environment variable named `Z3_EXE` has to point to the Z3 executable.
The version of Z3 can be checked by running `z3 -version`.

Change into the directory `case_studies/wireguard/src`. All subsequent commands are assumed to be executed in this directory.
To verify the initiator's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I verification -I ./ --module wireguard-gobra/wireguard --directory initiator
```

Similarly, to verify the responder's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I verification -I ./ --module wireguard-gobra/wireguard --directory responder
```

Description of the flags:
- `-Xss128m` increases the stack size used to run the verifier. The default argument does not suffice and will cause a runtime exception.
- `-I verification -I ./` instructs Gobra to consider the current directory and the `verification` subfolders when performing lookups of imported packages. Note that `verification` takes precende over the current directory meaning that packages found in these subfolders will be selected over those found in the current directory.
- `--module wireguard-gobra/wireguard` informs Gobra that we are currently in this module. This impacts the package resolution as it basically means that Gobra will ignore this prefix. For example, the import statement `import lib "wireguard-gobra/wireguard/library"` results in Gobra looking for the folder `library` in the specified include directories (`-I` option).
- `--directory initiator` specifies the package that is verified


## Building & Running this WireGuard Implementation Non-Virtualized
Note that the commands have been tested on macOS.

### Requirements
1. Get Go >= 1.6 (e.g. `brew install go` for MacOS)
To run our WireGuard implementation together with the official WireGuard implementation, further:
2. Clone repo: `git clone https://git.zx2c4.com/wireguard-go`
3. Build it: `make` (in the cloned repository)
4. Get Wireguard-Tools (e.g. `brew install wireguard-tools` for MacOS)

### Building this WireGuard Implementation
1. Change into the directory `case_studies/wireguard/src`. 
2. Build a binary: `go build -v -o wireguard-gobra`
3. Print usage of all parameters: `./wireguard-gobra -h` 
Note that the binary has to be executed with sudo rights if an interface should be created, i.e. the argument `useStandardIO` is set to false.

### Running this WireGuard Implementation with STD I/O
You will need two terminals to run both, responder and initiator.
The order in which responder and initiator are started is important.
Start the responder first and then start the initiator.

After building the binary, to start the responder, run in one terminal:
  ```
  ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint 127.0.0.1:12345 \
    --port 12344 \
    --useStandardIO
  ```

After starting the responder, to start the initiator, run in a different terminal:
  ```
  ./wireguard-gobra \
    --interfaceName utun10 \
    --privateKey YIQ1ZXYUVs6OjE2GjDhJgAqoJDaPPdReVtSQ1zOy7n8= \
    --publicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --peerPublicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --endpoint 127.0.0.1:12344 \
    --port 12345 \
    --isInitiator \
    --useStandardIO
  ```

Messages can now be entered via standard input in both terminals. Note however that the initiator is expected to send the first message, then the responder replies with the second message, etc. For the initiator and the responder, messages can be entered at any point, but the entered messages will be forwarded in the aforementioned pattern.


### Running this WireGuard Implementation against official WireGuard Implementation
Note again that the commands have been tested on macOS. Some commands for Linux are slightly different and can be found in [WireGuard's Quick Start](https://www.wireguard.com/quickstart/). The subsequent commands assume that steps 2--4 of the Requirements have been completed.

To start the official implementation, run the following commands in one terminal (which we will refer to as terminal A):
1. Change into the `src` directory of the cloned official WireGuard repository (from `https://git.zx2c4.com/wireguard-go`).
2. `sudo ./wireguard-go -f utun6`
3. `wg genkey > client1.private`
4. `sudo ifconfig utun6 inet 192.168.2.1 192.168.2.2`
5. `sudo wg set utun6 private-key ./client1.private`
6. `sudo ifconfig utun6 up`
7. `sudo wg set utun6 peer poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= allowed-ips 192.168.2.2/32 endpoint 127.0.0.1:12344` 

To start this verifier implementation, run the following commands in a different terminal (which we will refer to as terminal B):
1. Use `sudo wg` in terminal A to get the listening port of client 1, which will be used as parameter `--endpoint`.
2. Run the following command in terminal B:
```
  sudo ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint <listening port returned from the step 1, e.g. 127.0.0.1:62751> \
    --port 12344 \
    --isInitiator
```

After having started the official and our verified implementation, `ping 192.168.2.1` can be executed in terminal B.
This command pings the official implementation from our implementation, which includes performing the handshake.
The command `sudo wg` in terminal B displays the time of the last handshake.

To ping in the other direction, i.e. `ping 192.168.2.2`, `--isInitiator` has to be dropped from the command starting the verified implementation.
