#!/bin/bash

tamarin-prover --derivcheck-timeout=0 --heuristic=O --oraclename="wireguard.oracle" --prove wireguard.spthy
