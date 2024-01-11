
# HasTEE⁺

A Haskell DSL for programming Trusted Execution Environments (TEEs).

Papers on HasTEE⁺:

[HasTEE: Programming Trusted Execution Environments with Haskell](https://dl.acm.org/doi/10.1145/3609026.3609731) - Version 1 of the DSL.

HasTEE⁺: Confidential Cloud Computing and Analytics with Haskell - Submitted to ESORICS 2024, ArXiV link coming soon. Version 2 of the DSL.


### Building

NOTE: The current `cabal.project` expects the trusted GHC at a particular location. For building this on your local machine that doesn't have SGX or the custom GHC, use - `cabal build --project-file=cabal-nosgx.project`.

The executable supports conditional compilation and can compile into 2 binaries
#### Using cabal
```
-- For the enclave
cabal run -f enclave

-- For the client
cabal run
```

Follow the above order - run enclave first and then the client. The enclave is stateful and can be tested by running the enclave first and then calling the client repeatedly for the program in `Main.hs`.


#### Installed Binary Location

```
cabal exec which EnclaveIFC-exe
```


#### Using stack

LATEST: DO NOT USE `stack`. Stick to `cabal`, all recent developments have been done with `cabal`

Very hard (or impossible) to make the latest `stack` pick up a custom GHC because of the snapshot mechanism (perhaps that requires all the necessary packages be compiled with the custom GHC). Approaches in this thread https://github.com/commercialhaskell/stack/issues/725#issuecomment-364624897 are no longer functional in the latest `stack` incarnations.

```
-- Build and run the enclave (the flag is called `enclave`)
stack build --flag EnclaveIFC:enclave
.stack-work/install/x86_64-linux-tinfo6/16c183811171455bbb9119194450e5a4a4679f74605e9f4e1a47fbd54088f2b5/9.2.5/bin/EnclaveIFC-exe

-- Build and run the client (default build is for client)
stack run EnclaveIFC-exe
```

