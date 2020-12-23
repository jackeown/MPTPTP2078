%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:08 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   83 (2079 expanded)
%              Number of leaves         :    7 ( 514 expanded)
%              Depth                    :   27
%              Number of atoms          :  284 (14099 expanded)
%              Number of equality atoms :  144 (6688 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(subsumption_resolution,[],[f689,f627])).

fof(f627,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f561])).

fof(f561,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f457,f549])).

fof(f549,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f507,f426])).

fof(f426,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f400,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f400,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f71,f399])).

fof(f399,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f384,f98])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK1)
      | ~ r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X3)
      | k1_tarski(sK0) = k2_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f93,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_tarski(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f82,f45])).

fof(f45,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f384,plain,
    ( r2_hidden(sK4(sK2,sK1,k1_tarski(sK0)),sK1)
    | k1_tarski(sK0) = k2_xboole_0(sK2,sK1) ),
    inference(factoring,[],[f187])).

fof(f187,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK1)
      | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),X1)
      | k1_tarski(sK0) = k2_xboole_0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f171,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,k1_tarski(sK0)),sK2)
      | ~ r2_hidden(sK4(X0,X1,k1_tarski(sK0)),X0)
      | k2_xboole_0(X0,X1) = k1_tarski(sK0) ) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_tarski(sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(superposition,[],[f81,f45])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f171,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK2)
      | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),X1)
      | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK1)
      | k1_tarski(sK0) = k2_xboole_0(sK2,X1) ) ),
    inference(factoring,[],[f104])).

fof(f104,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK2)
      | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X3)
      | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X2)
      | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK1)
      | k1_tarski(sK0) = k2_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f83,f45])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f507,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f456])).

fof(f456,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f47,f454])).

fof(f454,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f453,f118])).

fof(f118,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( sK1 != sK1
    | sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f90,f95])).

fof(f95,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f91,f49])).

fof(f91,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f71,f45])).

fof(f90,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f89])).

fof(f89,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f46])).

fof(f46,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f453,plain,
    ( k1_xboole_0 = sK1
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f452,f119])).

fof(f119,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f48,f95])).

fof(f48,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f452,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f428,f115])).

fof(f115,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k1_xboole_0 = X3
      | sK1 = X3
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f49,f95])).

fof(f428,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f400,f95])).

fof(f47,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f457,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(backward_demodulation,[],[f48,f454])).

fof(f689,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f462,f688])).

fof(f688,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f686,f602])).

fof(f602,plain,(
    r2_hidden(sK4(k1_xboole_0,k1_tarski(sK0),k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f509,f549])).

fof(f509,plain,(
    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f503,f507])).

fof(f503,plain,
    ( r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),k1_xboole_0)
    | sK2 = k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f429,f454])).

fof(f429,plain,
    ( sK2 = k1_tarski(sK0)
    | r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1) ),
    inference(backward_demodulation,[],[f424,f427])).

fof(f427,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f400,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f424,plain,
    ( r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1)
    | sK2 = k2_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f414,f234])).

fof(f234,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK2)
      | r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK1)
      | k2_xboole_0(X2,k1_tarski(sK0)) = X2 ) ),
    inference(subsumption_resolution,[],[f223,f60])).

fof(f223,plain,(
    ! [X2] :
      ( r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK2)
      | r2_hidden(sK4(X2,k1_tarski(sK0),X2),X2)
      | r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK1)
      | k2_xboole_0(X2,k1_tarski(sK0)) = X2 ) ),
    inference(factoring,[],[f105])).

fof(f105,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,k1_tarski(sK0),X5),sK2)
      | r2_hidden(sK4(X4,k1_tarski(sK0),X5),X5)
      | r2_hidden(sK4(X4,k1_tarski(sK0),X5),X4)
      | r2_hidden(sK4(X4,k1_tarski(sK0),X5),sK1)
      | k2_xboole_0(X4,k1_tarski(sK0)) = X5 ) ),
    inference(resolution,[],[f92,f59])).

fof(f414,plain,
    ( r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1)
    | sK2 = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1)
    | sK2 = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK2)
    | sK2 = k2_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f234,f60])).

fof(f686,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,k1_tarski(sK0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(resolution,[],[f602,f60])).

fof(f462,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f96,f454])).

fof(f96,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f91,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (11532)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (11536)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.53  % (11549)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.24/0.53  % (11541)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.24/0.53  % (11544)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.24/0.54  % (11551)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.54  % (11556)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.24/0.54  % (11533)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.24/0.54  % (11543)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.54  % (11552)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.54  % (11531)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (11529)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.54  % (11534)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.55  % (11535)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (11537)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (11548)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (11557)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.55  % (11538)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (11547)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (11550)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (11540)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.56  % (11553)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.56  % (11539)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.56  % (11542)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.56  % (11545)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.56  % (11554)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.56  % (11555)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (11530)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.56  % (11545)Refutation not found, incomplete strategy% (11545)------------------------------
% 1.39/0.56  % (11545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (11545)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (11545)Memory used [KB]: 10618
% 1.39/0.56  % (11545)Time elapsed: 0.148 s
% 1.39/0.56  % (11545)------------------------------
% 1.39/0.56  % (11545)------------------------------
% 1.39/0.56  % (11558)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.56  % (11558)Refutation not found, incomplete strategy% (11558)------------------------------
% 1.39/0.56  % (11558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (11558)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (11558)Memory used [KB]: 1663
% 1.39/0.56  % (11558)Time elapsed: 0.147 s
% 1.39/0.56  % (11558)------------------------------
% 1.39/0.56  % (11558)------------------------------
% 1.39/0.57  % (11546)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.57  % (11543)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.58  % SZS output start Proof for theBenchmark
% 1.39/0.58  fof(f690,plain,(
% 1.39/0.58    $false),
% 1.39/0.58    inference(subsumption_resolution,[],[f689,f627])).
% 1.39/0.58  fof(f627,plain,(
% 1.39/0.58    k1_xboole_0 != k1_tarski(sK0)),
% 1.39/0.58    inference(trivial_inequality_removal,[],[f561])).
% 1.39/0.58  fof(f561,plain,(
% 1.39/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k1_tarski(sK0)),
% 1.39/0.58    inference(backward_demodulation,[],[f457,f549])).
% 1.39/0.58  fof(f549,plain,(
% 1.39/0.58    k1_xboole_0 = sK2),
% 1.39/0.58    inference(trivial_inequality_removal,[],[f544])).
% 1.39/0.58  fof(f544,plain,(
% 1.39/0.58    sK2 != sK2 | k1_xboole_0 = sK2),
% 1.39/0.58    inference(superposition,[],[f507,f426])).
% 1.39/0.58  fof(f426,plain,(
% 1.39/0.58    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2),
% 1.39/0.58    inference(resolution,[],[f400,f49])).
% 1.39/0.58  fof(f49,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.39/0.58    inference(cnf_transformation,[],[f30])).
% 1.39/0.58  fof(f30,plain,(
% 1.39/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.39/0.58    inference(flattening,[],[f29])).
% 1.39/0.58  fof(f29,plain,(
% 1.39/0.58    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.39/0.58    inference(nnf_transformation,[],[f19])).
% 1.39/0.58  fof(f19,axiom,(
% 1.39/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.39/0.58  fof(f400,plain,(
% 1.39/0.58    r1_tarski(sK2,k1_tarski(sK0))),
% 1.39/0.58    inference(superposition,[],[f71,f399])).
% 1.39/0.58  fof(f399,plain,(
% 1.39/0.58    k1_tarski(sK0) = k2_xboole_0(sK2,sK1)),
% 1.39/0.58    inference(subsumption_resolution,[],[f384,f98])).
% 1.39/0.58  fof(f98,plain,(
% 1.39/0.58    ( ! [X2,X3] : (~r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK1) | ~r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X3) | k1_tarski(sK0) = k2_xboole_0(X2,X3)) )),
% 1.39/0.58    inference(resolution,[],[f93,f61])).
% 1.39/0.58  fof(f61,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f37,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.39/0.58  fof(f36,plain,(
% 1.39/0.58    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f35,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/0.58    inference(rectify,[],[f34])).
% 1.39/0.58  fof(f34,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/0.58    inference(flattening,[],[f33])).
% 1.39/0.58  fof(f33,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/0.58    inference(nnf_transformation,[],[f1])).
% 1.39/0.58  fof(f1,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.39/0.58  fof(f93,plain,(
% 1.39/0.58    ( ! [X1] : (r2_hidden(X1,k1_tarski(sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.39/0.58    inference(superposition,[],[f82,f45])).
% 1.39/0.58  fof(f45,plain,(
% 1.39/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.39/0.58    inference(cnf_transformation,[],[f28])).
% 1.39/0.58  fof(f28,plain,(
% 1.39/0.58    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.39/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 1.39/0.58  fof(f27,plain,(
% 1.39/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f24,plain,(
% 1.39/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.58    inference(ennf_transformation,[],[f23])).
% 1.39/0.58  fof(f23,negated_conjecture,(
% 1.39/0.58    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.58    inference(negated_conjecture,[],[f22])).
% 1.39/0.58  fof(f22,conjecture,(
% 1.39/0.58    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.39/0.58  fof(f82,plain,(
% 1.39/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.39/0.58    inference(equality_resolution,[],[f57])).
% 1.39/0.58  fof(f57,plain,(
% 1.39/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f384,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,sK1,k1_tarski(sK0)),sK1) | k1_tarski(sK0) = k2_xboole_0(sK2,sK1)),
% 1.39/0.58    inference(factoring,[],[f187])).
% 1.39/0.58  fof(f187,plain,(
% 1.39/0.58    ( ! [X1] : (r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK1) | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),X1) | k1_tarski(sK0) = k2_xboole_0(sK2,X1)) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f171,f99])).
% 1.39/0.58  fof(f99,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,k1_tarski(sK0)),sK2) | ~r2_hidden(sK4(X0,X1,k1_tarski(sK0)),X0) | k2_xboole_0(X0,X1) = k1_tarski(sK0)) )),
% 1.39/0.58    inference(resolution,[],[f94,f60])).
% 1.39/0.58  fof(f60,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f94,plain,(
% 1.39/0.58    ( ! [X2] : (r2_hidden(X2,k1_tarski(sK0)) | ~r2_hidden(X2,sK2)) )),
% 1.39/0.58    inference(superposition,[],[f81,f45])).
% 1.39/0.58  fof(f81,plain,(
% 1.39/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.39/0.58    inference(equality_resolution,[],[f58])).
% 1.39/0.58  fof(f58,plain,(
% 1.39/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f171,plain,(
% 1.39/0.58    ( ! [X1] : (r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK2) | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),X1) | r2_hidden(sK4(sK2,X1,k1_tarski(sK0)),sK1) | k1_tarski(sK0) = k2_xboole_0(sK2,X1)) )),
% 1.39/0.58    inference(factoring,[],[f104])).
% 1.39/0.58  fof(f104,plain,(
% 1.39/0.58    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK2) | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X3) | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),X2) | r2_hidden(sK4(X2,X3,k1_tarski(sK0)),sK1) | k1_tarski(sK0) = k2_xboole_0(X2,X3)) )),
% 1.39/0.58    inference(resolution,[],[f92,f59])).
% 1.39/0.58  fof(f59,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f92,plain,(
% 1.39/0.58    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.39/0.58    inference(superposition,[],[f83,f45])).
% 1.39/0.58  fof(f83,plain,(
% 1.39/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.39/0.58    inference(equality_resolution,[],[f56])).
% 1.39/0.58  fof(f56,plain,(
% 1.39/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f71,plain,(
% 1.39/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f7])).
% 1.39/0.58  fof(f7,axiom,(
% 1.39/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.39/0.58  fof(f507,plain,(
% 1.39/0.58    sK2 != k1_tarski(sK0)),
% 1.39/0.58    inference(trivial_inequality_removal,[],[f456])).
% 1.39/0.58  fof(f456,plain,(
% 1.39/0.58    k1_xboole_0 != k1_xboole_0 | sK2 != k1_tarski(sK0)),
% 1.39/0.58    inference(backward_demodulation,[],[f47,f454])).
% 1.39/0.58  fof(f454,plain,(
% 1.39/0.58    k1_xboole_0 = sK1),
% 1.39/0.58    inference(subsumption_resolution,[],[f453,f118])).
% 1.39/0.58  fof(f118,plain,(
% 1.39/0.58    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.39/0.58    inference(trivial_inequality_removal,[],[f110])).
% 1.39/0.58  fof(f110,plain,(
% 1.39/0.58    sK1 != sK1 | sK1 != sK2 | k1_xboole_0 = sK1),
% 1.39/0.58    inference(superposition,[],[f90,f95])).
% 1.39/0.58  fof(f95,plain,(
% 1.39/0.58    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.39/0.58    inference(resolution,[],[f91,f49])).
% 1.39/0.58  fof(f91,plain,(
% 1.39/0.58    r1_tarski(sK1,k1_tarski(sK0))),
% 1.39/0.58    inference(superposition,[],[f71,f45])).
% 1.39/0.58  fof(f90,plain,(
% 1.39/0.58    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 1.39/0.58    inference(inner_rewriting,[],[f89])).
% 1.39/0.58  fof(f89,plain,(
% 1.39/0.58    sK2 != k1_tarski(sK0) | sK1 != sK2),
% 1.39/0.58    inference(inner_rewriting,[],[f46])).
% 1.39/0.58  fof(f46,plain,(
% 1.39/0.58    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.39/0.58    inference(cnf_transformation,[],[f28])).
% 1.39/0.58  fof(f453,plain,(
% 1.39/0.58    k1_xboole_0 = sK1 | sK1 = sK2),
% 1.39/0.58    inference(subsumption_resolution,[],[f452,f119])).
% 1.39/0.58  fof(f119,plain,(
% 1.39/0.58    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.39/0.58    inference(trivial_inequality_removal,[],[f109])).
% 1.39/0.58  fof(f109,plain,(
% 1.39/0.58    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.39/0.58    inference(superposition,[],[f48,f95])).
% 1.39/0.58  fof(f48,plain,(
% 1.39/0.58    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.39/0.58    inference(cnf_transformation,[],[f28])).
% 1.39/0.58  fof(f452,plain,(
% 1.39/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK1 = sK2),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f450])).
% 1.39/0.58  fof(f450,plain,(
% 1.39/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK1 = sK2 | k1_xboole_0 = sK1),
% 1.39/0.58    inference(resolution,[],[f428,f115])).
% 1.39/0.58  fof(f115,plain,(
% 1.39/0.58    ( ! [X3] : (~r1_tarski(X3,sK1) | k1_xboole_0 = X3 | sK1 = X3 | k1_xboole_0 = sK1) )),
% 1.39/0.58    inference(superposition,[],[f49,f95])).
% 1.39/0.58  fof(f428,plain,(
% 1.39/0.58    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 1.39/0.58    inference(superposition,[],[f400,f95])).
% 1.39/0.58  fof(f47,plain,(
% 1.39/0.58    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.39/0.58    inference(cnf_transformation,[],[f28])).
% 1.39/0.58  fof(f457,plain,(
% 1.39/0.58    k1_xboole_0 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.39/0.58    inference(backward_demodulation,[],[f48,f454])).
% 1.39/0.58  fof(f689,plain,(
% 1.39/0.58    k1_xboole_0 = k1_tarski(sK0)),
% 1.39/0.58    inference(backward_demodulation,[],[f462,f688])).
% 1.39/0.58  fof(f688,plain,(
% 1.39/0.58    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.39/0.58    inference(subsumption_resolution,[],[f686,f602])).
% 1.39/0.58  fof(f602,plain,(
% 1.39/0.58    r2_hidden(sK4(k1_xboole_0,k1_tarski(sK0),k1_xboole_0),k1_xboole_0)),
% 1.39/0.58    inference(backward_demodulation,[],[f509,f549])).
% 1.39/0.58  fof(f509,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),k1_xboole_0)),
% 1.39/0.58    inference(subsumption_resolution,[],[f503,f507])).
% 1.39/0.58  fof(f503,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),k1_xboole_0) | sK2 = k1_tarski(sK0)),
% 1.39/0.58    inference(backward_demodulation,[],[f429,f454])).
% 1.39/0.58  fof(f429,plain,(
% 1.39/0.58    sK2 = k1_tarski(sK0) | r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1)),
% 1.39/0.58    inference(backward_demodulation,[],[f424,f427])).
% 1.39/0.58  fof(f427,plain,(
% 1.39/0.58    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))),
% 1.39/0.58    inference(resolution,[],[f400,f69])).
% 1.39/0.58  fof(f69,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.39/0.58    inference(cnf_transformation,[],[f26])).
% 1.39/0.58  fof(f26,plain,(
% 1.39/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.39/0.58    inference(ennf_transformation,[],[f4])).
% 1.39/0.58  fof(f4,axiom,(
% 1.39/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.39/0.58  fof(f424,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1) | sK2 = k2_xboole_0(sK2,k1_tarski(sK0))),
% 1.39/0.58    inference(subsumption_resolution,[],[f414,f234])).
% 1.39/0.58  fof(f234,plain,(
% 1.39/0.58    ( ! [X2] : (r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK2) | r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK1) | k2_xboole_0(X2,k1_tarski(sK0)) = X2) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f223,f60])).
% 1.39/0.58  fof(f223,plain,(
% 1.39/0.58    ( ! [X2] : (r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK2) | r2_hidden(sK4(X2,k1_tarski(sK0),X2),X2) | r2_hidden(sK4(X2,k1_tarski(sK0),X2),sK1) | k2_xboole_0(X2,k1_tarski(sK0)) = X2) )),
% 1.39/0.58    inference(factoring,[],[f105])).
% 1.39/0.58  fof(f105,plain,(
% 1.39/0.58    ( ! [X4,X5] : (r2_hidden(sK4(X4,k1_tarski(sK0),X5),sK2) | r2_hidden(sK4(X4,k1_tarski(sK0),X5),X5) | r2_hidden(sK4(X4,k1_tarski(sK0),X5),X4) | r2_hidden(sK4(X4,k1_tarski(sK0),X5),sK1) | k2_xboole_0(X4,k1_tarski(sK0)) = X5) )),
% 1.39/0.58    inference(resolution,[],[f92,f59])).
% 1.39/0.58  fof(f414,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1) | sK2 = k2_xboole_0(sK2,k1_tarski(sK0)) | ~r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK2)),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f408])).
% 1.39/0.58  fof(f408,plain,(
% 1.39/0.58    r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK1) | sK2 = k2_xboole_0(sK2,k1_tarski(sK0)) | ~r2_hidden(sK4(sK2,k1_tarski(sK0),sK2),sK2) | sK2 = k2_xboole_0(sK2,k1_tarski(sK0))),
% 1.39/0.58    inference(resolution,[],[f234,f60])).
% 1.39/0.58  fof(f686,plain,(
% 1.39/0.58    ~r2_hidden(sK4(k1_xboole_0,k1_tarski(sK0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.39/0.58    inference(resolution,[],[f602,f60])).
% 1.39/0.58  fof(f462,plain,(
% 1.39/0.58    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.39/0.58    inference(backward_demodulation,[],[f96,f454])).
% 1.39/0.58  fof(f96,plain,(
% 1.39/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.39/0.58    inference(resolution,[],[f91,f69])).
% 1.39/0.58  % SZS output end Proof for theBenchmark
% 1.39/0.58  % (11543)------------------------------
% 1.39/0.58  % (11543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (11543)Termination reason: Refutation
% 1.39/0.58  
% 1.39/0.58  % (11543)Memory used [KB]: 2046
% 1.39/0.58  % (11543)Time elapsed: 0.087 s
% 1.39/0.58  % (11543)------------------------------
% 1.39/0.58  % (11543)------------------------------
% 1.39/0.58  % (11523)Success in time 0.214 s
%------------------------------------------------------------------------------
