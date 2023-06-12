---
title: A tour of biscuit-haskell
#light: true
#ratio43: true
overlay: "@clementd"
author:
  - name: Clément Delafargue
    desc:
      - Software developer at <a href="https://outscale.com">3DS Outscale</a>
      - <a href="https://framapiaf.org/clementd">@clementd</a>
---

# biscuit-haskell

- biscuit (recap)
- biscuit-haskell (three different ones)
- WWFMDD?

---

# fun parts

- cryptographic primitives
- protobuf serialization
- parsing datalog
- (uni)type-safe datalog
- type safe ASTs
- datalog evaluation

---

# biscuit

- specification + implementations

- logic langage
- token format

---

# Logic language

```datalog
user("1234");
right($user, $right) <- right($group, $right), member($user, $group);

check if operation("read");
check if followers($n), $n > 1000 trusting {twitter_public_key};
allow if user($user), right($user, "send-missiles");
```

---

# biscuit token

- ed25519 signatures
- protobuf envelope
- protobuf-serialized AST

---

# biscuit: first try

- C FFI
- C2HS
- Foreign pointers

---

# biscuit: first try

```haskell
{#pointer *Biscuit foreign finalizer biscuit_free newtype#}

serialize :: Biscuit
          -> IO ByteString
serialize = flip withBiscuit $ \b -> do
  size <- fromIntegral <$> {#call biscuit_serialized_size #} b
  allocaBytes size $ \buf -> do
    {#call biscuit_serialize #} b buf
    packCStringLen (castPtr buf, size)
```

---

# biscuit: first try

- FFI documentation is lacking (but getting better)
- works-ish
- poor UX
- tricky programming model with foreign pointers
- unsavory C idioms
- packaging is a nightmare

---

# biscuit: libsodium

- cryptographic primitive (ristretto) still not supported in haskell
- everything else is
- libsodium supports ristretto

---

# biscuit: libsodium

- low-level libsodium bindings for crypto
- native haskell implementation for the rest

---

# libsodium

```haskell
signBlock :: Keypair -> ByteString -> IO Signature
signBlock Keypair{publicKey,privateKey} message = do
  let PublicKey pubBs = publicKey
      PrivateKey prvBs = privateKey
  randomScalar $ \r ->
    scalarToPoint r $ \aa ->
      hashPoints [aa] $ \d ->
        hashMessage pubBs message $ \e ->
          withScalar $ \rd -> do
            crypto_core_ristretto255_scalar_mul rd r d
            withScalar $ \epk ->
              withBSLen prvBs $ \(pk, _) -> do
                crypto_core_ristretto255_scalar_mul epk e pk
                withScalar $ \z -> do
                  crypto_core_ristretto255_scalar_sub z rd epk
                  aaBs <- pointToByteString aa
                  zBs <- scalarToByteString z
                  pure Signature { parameters = [aaBs]
                                 , z = zBs
                                 }
```

---

# `ContT` goes brrrrrrrr

```haskell
signBlock :: Keypair -> ByteString -> IO Signature
signBlock Keypair{publicKey,privateKey} message = do
  let PublicKey pubBs = publicKey
      PrivateKey prvBs = privateKey
  (`runContT` pure) $ do
     (pk, _) <- withBSLen prvBs

     r   <- randomScalar
     aa  <- scalarToPoint r
     d   <- hashPoint aa
     e   <- hashMessage pubBs message
     rd  <- scalarMul r d
     epk <- scalarMul e pk
     z   <- scalarSub rd epk
     aaBs <- pointToByteString aa
     zBs  <- scalarToByteString z
     pure Signature { parameters = [aaBs]
                    , z = zBs
                    }
```

---

# biscuit v2

- simpler crypto (ed25519 signatures)
- new datalog model

---

# Cryptonite

```haskell
signBlock :: SecretKey
          -> ByteString
          -> Maybe (Signature, PublicKey)
          -> IO (SignedBlock, SecretKey)
signBlock sk payload eSig = do
  let pk = toPublic sk
  (nextPk, nextSk) <- (toPublic &&& id) <$> generateSecretKey
  let toSign = getToSig (payload, (), nextPk, eSig)
      sig = sign sk pk toSign
  pure ((payload, sig, nextPk, eSig), nextSk)
```

---

# Cryptonite (yes):

- de-facto crypto standard in haskell
- relatively good coverage of modern day crypto

---

# Cryptonite (but):

- unaudited C code
- small contributor base
- UNAUDITED C CODE
- essentially dead in the water
- new fork, crypton

---

# libsodium (yes):

- robust code base
- made to be portable
- used as basic block in other languages

---

# libsodium (but):

- comprehensive bindings were low-level
- higher-level bindings existed but were not comprehensive

---

# libsodium (hope):

- haskell crypto WG
- work on nice, high-level bindings

---

# Protobuf

- efficient and compact binary serialization
- used everywhere
- google tech (so google design)

---

# Protobuf

- protobuf-simple (codegen)
- protobuf (annotation)

---

# Datalog parser

- first implementation in attoparsec (because "it's fast lol")
- current implementation in megaparsec (better error messages)
- parser combinators may not be the best choice

---

# Compile-time checks: QuasiQuotes

- super easy to set up
- doc is a bit out of date
- usual TH issues

---

# AST representation

- some common structures (but not exactly the same)
- stage-dependent representation

---

# AST representation: trees that grow

```haskell
data Term' (inSet :: IsWithinSet) (pof :: PredicateOrFact) (ctx :: DatalogContext) =
    Variable (VariableType inSet pof)
  | LInteger Int64
  | LString Text
  | LDate UTCTime
  | LBytes ByteString
  | LBool Bool
  | Antiquote (SliceType ctx)
  | TermSet (SetType inSet ctx)
```

---

# AST representation: trees that grow

```haskell
type family VariableType (inSet :: IsWithinSet) (pof :: PredicateOrFact) where
  VariableType 'NotWithinSet 'InPredicate = Text
  VariableType inSet          pof         = Void

type family SliceType (ctx :: DatalogContext) where
  SliceType 'Representation = Void
  SliceType 'WithSlices     = Slice

type family BlockIdType (evalCtx :: EvaluationContext) (ctx :: DatalogContext) where
  BlockIdType 'Repr 'WithSlices     = PkOrSlice
  BlockIdType 'Repr 'Representation = PublicKey
  BlockIdType 'Eval 'Representation = (Set Natural, PublicKey)
```

---

# AST representation: trees that grow

```haskell
valueToTerm :: Term' 'NotWithinSet 'InPredicate 'Representation
            -> Term' 'NotWithinSet 'InFact 'Representation
valueToTerm = \case
  LInteger i  -> LInteger i
  LString i   -> LString i
  LDate i     -> LDate i
  LBytes i    -> LBytes i
  LBool i     -> LBool i
  TermSet i   -> TermSet i
  Variable v  -> absurd v
  Antiquote v -> absurd v
```

---

# AST representation: trees that grow

- strong AST well-formedness guarantees
- type-safety without repetition
- better consistency

---

# AST representation: trees that grow

- somehow advanced
- still a bit of boilerplate
- makes working with recursion schemes harder (I don't care)
- overall I'm glad I used them

---

# Datalog evaluation

- (well-defined) fixpoint
- scoped evaluation
- runtime limitations

---

# Datalog evaluation: the easy part, really

```haskell
getCombinations :: [[Scoped Bindings]]
                -> [Scoped [Bindings]]
getCombinations = getCompose . traverse Compose
```

---

# WWFMDD? Well I already did it:

- megaparsec
- two-phase parsing (parsing, then semantic checks)
- try to unroll AST indicators (3 separate enums for now)


<!--
---

# Centered title

---

# Centered title even when it's long and spans multiple lines

---

# Centered [[incremental]{}]{.incremental} title

---

# Top title

- With
- content

---

# Top title

::: incremental
- a
- b
- c
:::

---

# [Jumbo text]{.jumbo}

---

::: jumbogroup

## [a group of]{.jumbo}
## [big jumbo text]{.jumbo}
## [because it's fun]{.jumbo}

::::::::::

---

# Color switch []{.make-alternate}

---

```haskell
test :: Test
test = do
  traverse (`xor` b) [test]
  
```

---

# Titles are centered correctly even in the presence of notes

::: notes
| notes that are displayed because the right flag is added to the pandoc
| invocation. The leading `|` character allows to preserve line breaks,
| that's convenient in notes.
| notes can be toggled with `n`
:::

---

:::bigimage
![](./assets/puna.jpg)
:::
-->
