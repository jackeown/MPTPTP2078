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
% DateTime   : Thu Dec  3 12:37:51 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  102 (1249 expanded)
%              Number of leaves         :   20 ( 363 expanded)
%              Depth                    :   21
%              Number of atoms          :  302 (4038 expanded)
%              Number of equality atoms :  148 (2467 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f851,plain,(
    $false ),
    inference(subsumption_resolution,[],[f850,f844])).

fof(f844,plain,(
    k1_xboole_0 != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f803,f829])).

fof(f829,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f792,f827])).

fof(f827,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f176,f803])).

fof(f176,plain,
    ( ~ r2_hidden(sK1,sK2)
    | sK2 = k1_tarski(sK1) ),
    inference(resolution,[],[f174,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f174,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | sK2 = k1_tarski(sK1) ),
    inference(resolution,[],[f83,f119])).

fof(f119,plain,(
    r1_tarski(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f72,f63])).

fof(f63,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k1_xboole_0 != sK3
      | sK2 != k1_tarski(sK1) )
    & ( sK3 != k1_tarski(sK1)
      | k1_xboole_0 != sK2 )
    & ( sK3 != k1_tarski(sK1)
      | sK2 != k1_tarski(sK1) )
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42])).

fof(f42,plain,
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

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f792,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f791])).

fof(f791,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f69,f759])).

fof(f759,plain,
    ( sK1 = sK4(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f754,f69])).

fof(f754,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = X0 ) ),
    inference(resolution,[],[f583,f113])).

fof(f113,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f583,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f275,f574])).

fof(f574,plain,(
    sK2 = k3_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f327,f558])).

fof(f558,plain,(
    ! [X8,X9] : k5_xboole_0(k5_xboole_0(X8,X9),X9) = X8 ),
    inference(superposition,[],[f531,f507])).

fof(f507,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f477,f334])).

fof(f334,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f333,f70])).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f333,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f316,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f316,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f79,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f477,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f96,f67])).

fof(f96,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f531,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f507,f73])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f327,plain,(
    k3_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(superposition,[],[f79,f145])).

fof(f145,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(resolution,[],[f80,f119])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f98,f114])).

fof(f114,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f803,plain,(
    sK2 != k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f66,f802])).

fof(f802,plain,(
    k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f65,f64,f177,f794,f800])).

fof(f800,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f799])).

fof(f799,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f69,f767])).

fof(f767,plain,
    ( sK1 = sK4(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f762,f69])).

fof(f762,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK1 = X0 ) ),
    inference(resolution,[],[f591,f113])).

fof(f591,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f275,f575])).

fof(f575,plain,(
    sK3 = k3_xboole_0(sK3,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f328,f558])).

fof(f328,plain,(
    k3_xboole_0(sK3,k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(superposition,[],[f79,f146])).

fof(f146,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f80,f126])).

fof(f126,plain,(
    r1_tarski(sK3,k1_tarski(sK1)) ),
    inference(superposition,[],[f121,f63])).

fof(f121,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f72,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f794,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK1) ),
    inference(resolution,[],[f792,f176])).

fof(f177,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK3 = k1_tarski(sK1) ),
    inference(resolution,[],[f175,f93])).

fof(f175,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK3)
    | sK3 = k1_tarski(sK1) ),
    inference(resolution,[],[f83,f126])).

fof(f64,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,
    ( sK2 != k1_tarski(sK1)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f850,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f849,f71])).

fof(f849,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f804,f829])).

fof(f804,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (22678)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (22677)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (22660)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (22662)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (22666)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (22669)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (22657)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (22681)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (22685)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (22656)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (22668)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22658)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (22659)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (22661)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22672)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (22683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (22671)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (22664)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22670)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (22684)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (22665)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (22663)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (22666)Refutation not found, incomplete strategy% (22666)------------------------------
% 0.21/0.55  % (22666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22666)Memory used [KB]: 10618
% 0.21/0.55  % (22666)Time elapsed: 0.117 s
% 0.21/0.55  % (22666)------------------------------
% 0.21/0.55  % (22666)------------------------------
% 0.21/0.55  % (22673)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22667)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22680)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (22679)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (22676)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (22674)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (22675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (22682)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.60  % (22663)Refutation found. Thanks to Tanya!
% 1.69/0.60  % SZS status Theorem for theBenchmark
% 1.69/0.60  % SZS output start Proof for theBenchmark
% 1.69/0.60  fof(f851,plain,(
% 1.69/0.60    $false),
% 1.69/0.60    inference(subsumption_resolution,[],[f850,f844])).
% 1.69/0.60  fof(f844,plain,(
% 1.69/0.60    k1_xboole_0 != k1_tarski(sK1)),
% 1.69/0.60    inference(backward_demodulation,[],[f803,f829])).
% 1.69/0.60  fof(f829,plain,(
% 1.69/0.60    k1_xboole_0 = sK2),
% 1.69/0.60    inference(subsumption_resolution,[],[f792,f827])).
% 1.69/0.60  fof(f827,plain,(
% 1.69/0.60    ~r2_hidden(sK1,sK2)),
% 1.69/0.60    inference(subsumption_resolution,[],[f176,f803])).
% 1.69/0.60  fof(f176,plain,(
% 1.69/0.60    ~r2_hidden(sK1,sK2) | sK2 = k1_tarski(sK1)),
% 1.69/0.60    inference(resolution,[],[f174,f93])).
% 1.69/0.60  fof(f93,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f56])).
% 1.69/0.60  fof(f56,plain,(
% 1.69/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.69/0.60    inference(nnf_transformation,[],[f26])).
% 1.69/0.60  fof(f26,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.69/0.60  fof(f174,plain,(
% 1.69/0.60    ~r1_tarski(k1_tarski(sK1),sK2) | sK2 = k1_tarski(sK1)),
% 1.69/0.60    inference(resolution,[],[f83,f119])).
% 1.69/0.60  fof(f119,plain,(
% 1.69/0.60    r1_tarski(sK2,k1_tarski(sK1))),
% 1.69/0.60    inference(superposition,[],[f72,f63])).
% 1.69/0.60  fof(f63,plain,(
% 1.69/0.60    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.69/0.60    inference(cnf_transformation,[],[f43])).
% 1.69/0.60  fof(f43,plain,(
% 1.69/0.60    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42])).
% 1.69/0.60  fof(f42,plain,(
% 1.69/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f33,plain,(
% 1.69/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    inference(ennf_transformation,[],[f29])).
% 1.69/0.60  fof(f29,negated_conjecture,(
% 1.69/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    inference(negated_conjecture,[],[f28])).
% 1.69/0.60  fof(f28,conjecture,(
% 1.69/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.69/0.60  fof(f72,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f14])).
% 1.69/0.60  fof(f14,axiom,(
% 1.69/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.69/0.60  fof(f83,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f47])).
% 1.69/0.60  fof(f47,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(flattening,[],[f46])).
% 1.69/0.60  fof(f46,plain,(
% 1.69/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.60    inference(nnf_transformation,[],[f9])).
% 1.69/0.60  fof(f9,axiom,(
% 1.69/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.60  fof(f792,plain,(
% 1.69/0.60    r2_hidden(sK1,sK2) | k1_xboole_0 = sK2),
% 1.69/0.60    inference(duplicate_literal_removal,[],[f791])).
% 1.69/0.60  fof(f791,plain,(
% 1.69/0.60    r2_hidden(sK1,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.69/0.60    inference(superposition,[],[f69,f759])).
% 1.69/0.60  fof(f759,plain,(
% 1.69/0.60    sK1 = sK4(sK2) | k1_xboole_0 = sK2),
% 1.69/0.60    inference(resolution,[],[f754,f69])).
% 1.69/0.60  fof(f754,plain,(
% 1.69/0.60    ( ! [X0] : (~r2_hidden(X0,sK2) | sK1 = X0) )),
% 1.69/0.60    inference(resolution,[],[f583,f113])).
% 1.69/0.60  fof(f113,plain,(
% 1.69/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.69/0.60    inference(equality_resolution,[],[f88])).
% 1.69/0.60  fof(f88,plain,(
% 1.69/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f55])).
% 1.69/0.60  fof(f55,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f53,f54])).
% 1.69/0.60  fof(f54,plain,(
% 1.69/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f53,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(rectify,[],[f52])).
% 1.69/0.60  fof(f52,plain,(
% 1.69/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.69/0.60    inference(nnf_transformation,[],[f18])).
% 1.69/0.60  fof(f18,axiom,(
% 1.69/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.69/0.60  fof(f583,plain,(
% 1.69/0.60    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.69/0.60    inference(superposition,[],[f275,f574])).
% 1.69/0.60  fof(f574,plain,(
% 1.69/0.60    sK2 = k3_xboole_0(sK2,k1_tarski(sK1))),
% 1.69/0.60    inference(backward_demodulation,[],[f327,f558])).
% 1.69/0.60  fof(f558,plain,(
% 1.69/0.60    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X8,X9),X9) = X8) )),
% 1.69/0.60    inference(superposition,[],[f531,f507])).
% 1.69/0.60  fof(f507,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.69/0.60    inference(forward_demodulation,[],[f477,f334])).
% 1.69/0.60  fof(f334,plain,(
% 1.69/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.69/0.60    inference(forward_demodulation,[],[f333,f70])).
% 1.69/0.60  fof(f70,plain,(
% 1.69/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f30])).
% 1.69/0.60  fof(f30,plain,(
% 1.69/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.69/0.60    inference(rectify,[],[f7])).
% 1.69/0.60  fof(f7,axiom,(
% 1.69/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.69/0.60  fof(f333,plain,(
% 1.69/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.69/0.60    inference(forward_demodulation,[],[f316,f71])).
% 1.69/0.60  fof(f71,plain,(
% 1.69/0.60    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.69/0.60    inference(cnf_transformation,[],[f31])).
% 1.69/0.60  fof(f31,plain,(
% 1.69/0.60    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.69/0.60    inference(rectify,[],[f6])).
% 1.69/0.60  fof(f6,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.69/0.60  fof(f316,plain,(
% 1.69/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.69/0.60    inference(superposition,[],[f79,f67])).
% 1.69/0.60  fof(f67,plain,(
% 1.69/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f16])).
% 1.69/0.60  fof(f16,axiom,(
% 1.69/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.69/0.60  fof(f79,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f17])).
% 1.69/0.60  fof(f17,axiom,(
% 1.69/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.69/0.60  fof(f477,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(superposition,[],[f96,f67])).
% 1.69/0.60  fof(f96,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f15])).
% 1.69/0.60  fof(f15,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.69/0.60  fof(f531,plain,(
% 1.69/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.69/0.60    inference(superposition,[],[f507,f73])).
% 1.69/0.60  fof(f73,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f2])).
% 1.69/0.60  fof(f2,axiom,(
% 1.69/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.69/0.60  fof(f327,plain,(
% 1.69/0.60    k3_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1))),
% 1.69/0.60    inference(superposition,[],[f79,f145])).
% 1.69/0.60  fof(f145,plain,(
% 1.69/0.60    k1_tarski(sK1) = k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.69/0.60    inference(resolution,[],[f80,f119])).
% 1.69/0.60  fof(f80,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.69/0.60    inference(cnf_transformation,[],[f35])).
% 1.69/0.60  fof(f35,plain,(
% 1.69/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.69/0.60    inference(ennf_transformation,[],[f12])).
% 1.69/0.60  fof(f12,axiom,(
% 1.69/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.69/0.60  fof(f275,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X2)) )),
% 1.69/0.60    inference(resolution,[],[f98,f114])).
% 1.69/0.60  fof(f114,plain,(
% 1.69/0.60    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.69/0.60    inference(equality_resolution,[],[f103])).
% 1.69/0.60  fof(f103,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.69/0.60    inference(cnf_transformation,[],[f62])).
% 1.69/0.60  fof(f62,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.69/0.60    inference(nnf_transformation,[],[f41])).
% 1.69/0.60  fof(f41,plain,(
% 1.69/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.69/0.60    inference(definition_folding,[],[f4,f40])).
% 1.69/0.60  fof(f40,plain,(
% 1.69/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.69/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.69/0.60  fof(f4,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.69/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.69/0.60  fof(f98,plain,(
% 1.69/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f61])).
% 1.69/0.60  fof(f61,plain,(
% 1.69/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f60])).
% 1.69/0.61  fof(f60,plain,(
% 1.69/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f59,plain,(
% 1.69/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.69/0.61    inference(rectify,[],[f58])).
% 1.69/0.61  fof(f58,plain,(
% 1.69/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.69/0.61    inference(flattening,[],[f57])).
% 1.69/0.61  fof(f57,plain,(
% 1.69/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.69/0.61    inference(nnf_transformation,[],[f40])).
% 1.69/0.61  fof(f69,plain,(
% 1.69/0.61    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.69/0.61    inference(cnf_transformation,[],[f45])).
% 1.69/0.61  fof(f45,plain,(
% 1.69/0.61    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f44])).
% 1.69/0.61  fof(f44,plain,(
% 1.69/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f34,plain,(
% 1.69/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.69/0.61    inference(ennf_transformation,[],[f8])).
% 1.69/0.61  fof(f8,axiom,(
% 1.69/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.69/0.61  fof(f803,plain,(
% 1.69/0.61    sK2 != k1_tarski(sK1)),
% 1.69/0.61    inference(subsumption_resolution,[],[f66,f802])).
% 1.69/0.61  fof(f802,plain,(
% 1.69/0.61    k1_xboole_0 = sK3),
% 1.69/0.61    inference(global_subsumption,[],[f65,f64,f177,f794,f800])).
% 1.69/0.61  fof(f800,plain,(
% 1.69/0.61    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3),
% 1.69/0.61    inference(duplicate_literal_removal,[],[f799])).
% 1.69/0.61  fof(f799,plain,(
% 1.69/0.61    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 1.69/0.61    inference(superposition,[],[f69,f767])).
% 1.69/0.61  fof(f767,plain,(
% 1.69/0.61    sK1 = sK4(sK3) | k1_xboole_0 = sK3),
% 1.69/0.61    inference(resolution,[],[f762,f69])).
% 1.69/0.61  fof(f762,plain,(
% 1.69/0.61    ( ! [X0] : (~r2_hidden(X0,sK3) | sK1 = X0) )),
% 1.69/0.61    inference(resolution,[],[f591,f113])).
% 1.69/0.61  fof(f591,plain,(
% 1.69/0.61    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,sK3)) )),
% 1.69/0.61    inference(superposition,[],[f275,f575])).
% 1.69/0.61  fof(f575,plain,(
% 1.69/0.61    sK3 = k3_xboole_0(sK3,k1_tarski(sK1))),
% 1.69/0.61    inference(backward_demodulation,[],[f328,f558])).
% 1.69/0.61  fof(f328,plain,(
% 1.69/0.61    k3_xboole_0(sK3,k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK1))),
% 1.69/0.61    inference(superposition,[],[f79,f146])).
% 1.69/0.61  fof(f146,plain,(
% 1.69/0.61    k1_tarski(sK1) = k2_xboole_0(sK3,k1_tarski(sK1))),
% 1.69/0.61    inference(resolution,[],[f80,f126])).
% 1.69/0.61  fof(f126,plain,(
% 1.69/0.61    r1_tarski(sK3,k1_tarski(sK1))),
% 1.69/0.61    inference(superposition,[],[f121,f63])).
% 1.69/0.61  fof(f121,plain,(
% 1.69/0.61    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 1.69/0.61    inference(superposition,[],[f72,f74])).
% 1.69/0.61  fof(f74,plain,(
% 1.69/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f1])).
% 1.69/0.61  fof(f1,axiom,(
% 1.69/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.69/0.61  fof(f794,plain,(
% 1.69/0.61    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK1)),
% 1.69/0.61    inference(resolution,[],[f792,f176])).
% 1.69/0.61  fof(f177,plain,(
% 1.69/0.61    ~r2_hidden(sK1,sK3) | sK3 = k1_tarski(sK1)),
% 1.69/0.61    inference(resolution,[],[f175,f93])).
% 1.69/0.61  fof(f175,plain,(
% 1.69/0.61    ~r1_tarski(k1_tarski(sK1),sK3) | sK3 = k1_tarski(sK1)),
% 1.69/0.61    inference(resolution,[],[f83,f126])).
% 1.69/0.61  fof(f64,plain,(
% 1.69/0.61    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 1.69/0.61    inference(cnf_transformation,[],[f43])).
% 1.69/0.61  fof(f65,plain,(
% 1.69/0.61    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 1.69/0.61    inference(cnf_transformation,[],[f43])).
% 1.69/0.61  fof(f66,plain,(
% 1.69/0.61    sK2 != k1_tarski(sK1) | k1_xboole_0 != sK3),
% 1.69/0.61    inference(cnf_transformation,[],[f43])).
% 1.69/0.61  fof(f850,plain,(
% 1.69/0.61    k1_xboole_0 = k1_tarski(sK1)),
% 1.69/0.61    inference(forward_demodulation,[],[f849,f71])).
% 1.69/0.61  fof(f849,plain,(
% 1.69/0.61    k1_tarski(sK1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.69/0.61    inference(forward_demodulation,[],[f804,f829])).
% 1.69/0.61  fof(f804,plain,(
% 1.69/0.61    k1_tarski(sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.69/0.61    inference(backward_demodulation,[],[f63,f802])).
% 1.69/0.61  % SZS output end Proof for theBenchmark
% 1.69/0.61  % (22663)------------------------------
% 1.69/0.61  % (22663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (22663)Termination reason: Refutation
% 1.69/0.61  
% 1.69/0.61  % (22663)Memory used [KB]: 6908
% 1.69/0.61  % (22663)Time elapsed: 0.204 s
% 1.69/0.61  % (22663)------------------------------
% 1.69/0.61  % (22663)------------------------------
% 1.69/0.61  % (22651)Success in time 0.248 s
%------------------------------------------------------------------------------
