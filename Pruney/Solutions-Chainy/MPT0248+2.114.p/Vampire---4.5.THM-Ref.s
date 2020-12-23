%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 (1362 expanded)
%              Number of leaves         :   14 ( 364 expanded)
%              Depth                    :   29
%              Number of atoms          :  331 (6256 expanded)
%              Number of equality atoms :  171 (4343 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f697])).

fof(f697,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f654,f686])).

fof(f686,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f661,f677])).

fof(f677,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f673,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f673,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f616,f672])).

fof(f672,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(resolution,[],[f671,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f671,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f670])).

fof(f670,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | r2_hidden(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f620,f638])).

fof(f638,plain,(
    k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f634])).

fof(f634,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f300,f603])).

fof(f603,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f602])).

fof(f602,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f564])).

fof(f564,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f95,f548])).

fof(f548,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f547])).

fof(f547,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f485])).

fof(f485,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f96,f257])).

fof(f257,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f236,f114])).

fof(f114,plain,
    ( sK2 = k2_xboole_0(sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f86,plain,
    ( sP0(sK3,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f71,f74])).

fof(f74,plain,
    ( sK2 = k1_tarski(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f72,plain,(
    r1_tarski(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f56,f41])).

fof(f41,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k1_xboole_0 != sK3
      | sK2 != k1_tarski(sK1) )
    & ( sK3 != k1_tarski(sK1)
      | k1_xboole_0 != sK2 )
    & ( sK3 != k1_tarski(sK1)
      | sK2 != k1_tarski(sK1) )
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK3
        | sK2 != k1_tarski(sK1) )
      & ( sK3 != k1_tarski(sK1)
        | k1_xboole_0 != sK2 )
      & ( sK3 != k1_tarski(sK1)
        | sK2 != k1_tarski(sK1) )
      & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f71,plain,(
    sP0(sK3,sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f70,f41])).

fof(f70,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f236,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f82,f150])).

fof(f150,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f147,f53])).

fof(f147,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f48,f138])).

fof(f138,plain,
    ( sK1 = sK4(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f107,plain,
    ( r2_hidden(sK4(sK3),k1_tarski(sK1))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f79,f48])).

fof(f79,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | r2_hidden(X2,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & ~ r2_hidden(sK6(X0,X1,X2),X1) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & ~ r2_hidden(sK6(X0,X1,X2),X1) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f82,plain,(
    ! [X0] : k2_xboole_0(k1_tarski(sK1),X0) = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK1),X0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f54,f41])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f96,plain,
    ( sK2 != sK3
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( sK2 != sK3
    | sK2 != sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f42,f74])).

fof(f42,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f44,f74])).

fof(f44,plain,
    ( sK2 != k1_tarski(sK1)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f300,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f267])).

fof(f267,plain,
    ( sK3 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f43,f258])).

fof(f258,plain,
    ( sK3 = k1_tarski(sK1)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f236,f41])).

fof(f43,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f620,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | r2_hidden(sK1,sK3) ),
    inference(backward_demodulation,[],[f123,f603])).

fof(f123,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f77,f68])).

fof(f68,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK1))
      | r2_hidden(X0,sK2)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f616,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),X0)) ),
    inference(backward_demodulation,[],[f81,f603])).

fof(f661,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f606,f638])).

fof(f606,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f41,f603])).

fof(f654,plain,(
    k1_xboole_0 != k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f639,f638])).

fof(f639,plain,(
    sK3 != k1_tarski(sK1) ),
    inference(trivial_inequality_removal,[],[f608])).

fof(f608,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK3 != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f43,f603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:55:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (23851)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (23867)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (23848)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (23849)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (23852)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (23853)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (23859)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (23846)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (23864)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (23856)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (23857)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (23844)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (23845)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (23858)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (23847)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (23855)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (23873)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (23870)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (23873)Refutation not found, incomplete strategy% (23873)------------------------------
% 0.22/0.55  % (23873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23873)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23873)Memory used [KB]: 1663
% 0.22/0.55  % (23873)Time elapsed: 0.130 s
% 0.22/0.55  % (23873)------------------------------
% 0.22/0.55  % (23873)------------------------------
% 0.22/0.55  % (23865)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (23872)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (23866)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (23868)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (23862)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (23869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (23863)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (23854)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (23850)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (23860)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (23860)Refutation not found, incomplete strategy% (23860)------------------------------
% 0.22/0.56  % (23860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23860)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23860)Memory used [KB]: 10618
% 0.22/0.56  % (23860)Time elapsed: 0.150 s
% 0.22/0.56  % (23860)------------------------------
% 0.22/0.56  % (23860)------------------------------
% 0.22/0.56  % (23861)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (23845)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f704,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f697])).
% 0.22/0.56  fof(f697,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0),
% 0.22/0.56    inference(superposition,[],[f654,f686])).
% 0.22/0.56  fof(f686,plain,(
% 0.22/0.56    k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f661,f677])).
% 0.22/0.56  fof(f677,plain,(
% 0.22/0.56    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(resolution,[],[f673,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.56  fof(f673,plain,(
% 0.22/0.56    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f616,f672])).
% 0.22/0.56  fof(f672,plain,(
% 0.22/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 0.22/0.56    inference(resolution,[],[f671,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.22/0.56  fof(f671,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f670])).
% 0.22/0.56  fof(f670,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_xboole_0) | r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.56    inference(forward_demodulation,[],[f620,f638])).
% 0.22/0.56  fof(f638,plain,(
% 0.22/0.56    k1_xboole_0 = sK3),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f634])).
% 0.22/0.56  fof(f634,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3),
% 0.22/0.56    inference(backward_demodulation,[],[f300,f603])).
% 0.22/0.56  fof(f603,plain,(
% 0.22/0.56    k1_xboole_0 = sK2),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f602])).
% 0.22/0.56  fof(f602,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f564])).
% 0.22/0.56  fof(f564,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f95,f548])).
% 0.22/0.56  fof(f548,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f547])).
% 0.22/0.56  fof(f547,plain,(
% 0.22/0.56    sK2 != sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f485])).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    sK2 != sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f96,f257])).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    sK2 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f236,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    sK2 = k2_xboole_0(sK2,sK3) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(resolution,[],[f86,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.56    inference(definition_folding,[],[f2,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    sP0(sK3,sK2,sK2) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f71,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    sK2 = k1_tarski(sK1) | k1_xboole_0 = sK2),
% 0.22/0.56    inference(resolution,[],[f72,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    r1_tarski(sK2,k1_tarski(sK1))),
% 0.22/0.56    inference(superposition,[],[f56,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.56    inference(negated_conjecture,[],[f16])).
% 0.22/0.56  fof(f16,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    sP0(sK3,sK2,k1_tarski(sK1))),
% 0.22/0.56    inference(superposition,[],[f70,f41])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f236,plain,(
% 0.22/0.56    sK3 = k2_xboole_0(sK2,sK3) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(superposition,[],[f82,f150])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    sK3 = k2_xboole_0(k1_tarski(sK1),sK3) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(resolution,[],[f147,f53])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f146])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 0.22/0.56    inference(superposition,[],[f48,f138])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    sK1 = sK4(sK3) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(resolution,[],[f107,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    r2_hidden(sK4(sK3),k1_tarski(sK1)) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(resolution,[],[f79,f48])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X2] : (~r2_hidden(X2,sK3) | r2_hidden(X2,k1_tarski(sK1))) )),
% 0.22/0.56    inference(resolution,[],[f71,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f23])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X0] : (k2_xboole_0(k1_tarski(sK1),X0) = k2_xboole_0(sK2,k2_xboole_0(k1_tarski(sK1),X0))) )),
% 0.22/0.56    inference(resolution,[],[f81,f55])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(k1_tarski(sK1),X0))) )),
% 0.22/0.56    inference(resolution,[],[f73,f56])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_tarski(sK1),X0) | r1_tarski(sK2,X0)) )),
% 0.22/0.56    inference(superposition,[],[f54,f41])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    sK2 != sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f83])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    sK2 != sK3 | sK2 != sK2 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f42,f74])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    k1_xboole_0 != sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    sK2 != sK2 | k1_xboole_0 != sK3 | k1_xboole_0 = sK2),
% 0.22/0.56    inference(superposition,[],[f44,f74])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    sK2 != k1_tarski(sK1) | k1_xboole_0 != sK3),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f300,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | k1_xboole_0 = sK3),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f267])).
% 0.22/0.56  fof(f267,plain,(
% 0.22/0.56    sK3 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 = sK3),
% 0.22/0.56    inference(superposition,[],[f43,f258])).
% 0.22/0.56  fof(f258,plain,(
% 0.22/0.56    sK3 = k1_tarski(sK1) | k1_xboole_0 = sK3),
% 0.22/0.56    inference(superposition,[],[f236,f41])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f620,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_xboole_0) | r2_hidden(sK1,sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f123,f603])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    r2_hidden(sK1,sK3) | r2_hidden(sK1,sK2)),
% 0.22/0.56    inference(resolution,[],[f77,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.56    inference(equality_resolution,[],[f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.56    inference(equality_resolution,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK1)) | r2_hidden(X0,sK2) | r2_hidden(X0,sK3)) )),
% 0.22/0.56    inference(resolution,[],[f71,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f616,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(k1_tarski(sK1),X0))) )),
% 0.22/0.56    inference(backward_demodulation,[],[f81,f603])).
% 0.22/0.56  fof(f661,plain,(
% 0.22/0.56    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.56    inference(forward_demodulation,[],[f606,f638])).
% 0.22/0.56  fof(f606,plain,(
% 0.22/0.56    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f41,f603])).
% 0.22/0.56  fof(f654,plain,(
% 0.22/0.56    k1_xboole_0 != k1_tarski(sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f639,f638])).
% 0.22/0.56  fof(f639,plain,(
% 0.22/0.56    sK3 != k1_tarski(sK1)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f608])).
% 0.22/0.56  fof(f608,plain,(
% 0.22/0.56    k1_xboole_0 != k1_xboole_0 | sK3 != k1_tarski(sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f43,f603])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (23845)------------------------------
% 0.22/0.56  % (23845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23845)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (23845)Memory used [KB]: 1918
% 0.22/0.56  % (23845)Time elapsed: 0.134 s
% 0.22/0.56  % (23845)------------------------------
% 0.22/0.56  % (23845)------------------------------
% 0.22/0.56  % (23841)Success in time 0.199 s
%------------------------------------------------------------------------------
