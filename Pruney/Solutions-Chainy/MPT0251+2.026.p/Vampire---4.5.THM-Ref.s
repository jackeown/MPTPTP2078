%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:38 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 364 expanded)
%              Number of leaves         :   23 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  339 ( 969 expanded)
%              Number of equality atoms :   67 ( 282 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f923,plain,(
    $false ),
    inference(subsumption_resolution,[],[f922,f411])).

fof(f411,plain,(
    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f94,f97])).

fof(f97,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f58,f91,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f94,plain,(
    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f52,f92,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f91])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f91])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f922,plain,(
    sK3 = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f921,f95])).

fof(f95,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f53,f92])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f921,plain,(
    k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f907,f467])).

fof(f467,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f464,f111])).

fof(f111,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f66,f103])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f464,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(resolution,[],[f462,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f80,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f462,plain,(
    ! [X22] : sP0(X22,X22,k1_xboole_0) ),
    inference(global_subsumption,[],[f457])).

fof(f457,plain,(
    ! [X21] : sP0(X21,X21,k1_xboole_0) ),
    inference(resolution,[],[f276,f347])).

fof(f347,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f346,f268])).

fof(f268,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f137,f222])).

fof(f222,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f120,f208])).

fof(f208,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f95,f97])).

fof(f120,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = X2 ),
    inference(resolution,[],[f96,f66])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f57,f92])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f82,f106])).

fof(f106,plain,(
    ! [X0,X1] : sP1(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
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

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
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
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f346,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f336,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f336,plain,(
    ! [X6] : r1_xboole_0(k1_xboole_0,X6) ),
    inference(resolution,[],[f306,f129])).

fof(f129,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k5_xboole_0(X4,X4)) ),
    inference(subsumption_resolution,[],[f128,f123])).

fof(f123,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X4))
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f73,f113])).

fof(f113,plain,(
    ! [X0] : sP0(X0,X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f105,f111])).

fof(f105,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f79,f61])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f128,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f74,f113])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f306,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(k1_xboole_0,X5),X6)
      | r1_xboole_0(k1_xboole_0,X5) ) ),
    inference(resolution,[],[f268,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f276,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK6(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK6(X2,X2,X3),X3)
      | r2_hidden(sK6(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f907,plain,(
    k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f98,f701])).

fof(f701,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f152,f51])).

fof(f51,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) ) ),
    inference(resolution,[],[f99,f66])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f93])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f62,f92,f61,f92])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.50  % (16419)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (16419)Refutation not found, incomplete strategy% (16419)------------------------------
% 0.21/0.50  % (16419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16419)Memory used [KB]: 1663
% 0.21/0.50  % (16419)Time elapsed: 0.073 s
% 0.21/0.50  % (16419)------------------------------
% 0.21/0.50  % (16419)------------------------------
% 0.21/0.52  % (16421)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (16427)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (16417)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (16423)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (16435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (16435)Refutation not found, incomplete strategy% (16435)------------------------------
% 0.21/0.53  % (16435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16435)Memory used [KB]: 1663
% 0.21/0.53  % (16435)Time elapsed: 0.085 s
% 0.21/0.53  % (16435)------------------------------
% 0.21/0.53  % (16435)------------------------------
% 0.21/0.53  % (16442)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (16420)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (16422)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (16426)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (16443)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (16441)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (16424)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (16445)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (16439)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (16440)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (16444)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (16433)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (16447)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (16432)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (16447)Refutation not found, incomplete strategy% (16447)------------------------------
% 0.21/0.55  % (16447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16447)Memory used [KB]: 1663
% 0.21/0.55  % (16447)Time elapsed: 0.138 s
% 0.21/0.55  % (16447)------------------------------
% 0.21/0.55  % (16447)------------------------------
% 0.21/0.55  % (16432)Refutation not found, incomplete strategy% (16432)------------------------------
% 0.21/0.55  % (16432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16437)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (16436)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (16425)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (16432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16432)Memory used [KB]: 1663
% 0.21/0.56  % (16432)Time elapsed: 0.140 s
% 0.21/0.56  % (16432)------------------------------
% 0.21/0.56  % (16432)------------------------------
% 0.21/0.56  % (16428)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (16429)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (16430)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (16431)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (16430)Refutation not found, incomplete strategy% (16430)------------------------------
% 0.21/0.56  % (16430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16430)Memory used [KB]: 10618
% 0.21/0.56  % (16430)Time elapsed: 0.150 s
% 0.21/0.56  % (16430)------------------------------
% 0.21/0.56  % (16430)------------------------------
% 0.21/0.56  % (16434)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (16434)Refutation not found, incomplete strategy% (16434)------------------------------
% 0.21/0.56  % (16434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16434)Memory used [KB]: 10618
% 0.21/0.56  % (16434)Time elapsed: 0.152 s
% 0.21/0.56  % (16434)------------------------------
% 0.21/0.56  % (16434)------------------------------
% 0.21/0.56  % (16428)Refutation not found, incomplete strategy% (16428)------------------------------
% 0.21/0.56  % (16428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (16428)Memory used [KB]: 10746
% 0.21/0.57  % (16428)Time elapsed: 0.150 s
% 0.21/0.57  % (16428)------------------------------
% 0.21/0.57  % (16428)------------------------------
% 0.21/0.57  % (16446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (16446)Refutation not found, incomplete strategy% (16446)------------------------------
% 0.21/0.57  % (16446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16446)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (16446)Memory used [KB]: 10746
% 0.21/0.57  % (16446)Time elapsed: 0.143 s
% 0.21/0.57  % (16446)------------------------------
% 0.21/0.57  % (16446)------------------------------
% 1.60/0.58  % (16466)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.77/0.61  % (16424)Refutation found. Thanks to Tanya!
% 1.77/0.61  % SZS status Theorem for theBenchmark
% 1.77/0.61  % SZS output start Proof for theBenchmark
% 1.77/0.61  fof(f923,plain,(
% 1.77/0.61    $false),
% 1.77/0.61    inference(subsumption_resolution,[],[f922,f411])).
% 1.77/0.61  fof(f411,plain,(
% 1.77/0.61    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.77/0.61    inference(forward_demodulation,[],[f94,f97])).
% 1.77/0.61  fof(f97,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.77/0.61    inference(definition_unfolding,[],[f58,f91,f91])).
% 1.77/0.61  fof(f91,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.77/0.61    inference(definition_unfolding,[],[f59,f90])).
% 1.77/0.61  fof(f90,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.77/0.61    inference(definition_unfolding,[],[f72,f89])).
% 1.77/0.61  fof(f89,plain,(
% 1.77/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f15])).
% 1.77/0.61  fof(f15,axiom,(
% 1.77/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.77/0.61  fof(f72,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f14])).
% 1.77/0.61  fof(f14,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.77/0.61  fof(f59,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f13])).
% 1.77/0.61  fof(f13,axiom,(
% 1.77/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.77/0.61  fof(f58,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f11])).
% 1.77/0.61  fof(f11,axiom,(
% 1.77/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.77/0.61  fof(f94,plain,(
% 1.77/0.61    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))),
% 1.77/0.61    inference(definition_unfolding,[],[f52,f92,f93])).
% 1.77/0.61  fof(f93,plain,(
% 1.77/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.77/0.61    inference(definition_unfolding,[],[f54,f91])).
% 1.77/0.61  fof(f54,plain,(
% 1.77/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f12])).
% 1.77/0.61  fof(f12,axiom,(
% 1.77/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.77/0.61  fof(f92,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.77/0.61    inference(definition_unfolding,[],[f60,f91])).
% 1.77/0.61  fof(f60,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f17])).
% 1.77/0.61  fof(f17,axiom,(
% 1.77/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.77/0.61  fof(f52,plain,(
% 1.77/0.61    sK3 != k2_xboole_0(k1_tarski(sK2),sK3)),
% 1.77/0.61    inference(cnf_transformation,[],[f29])).
% 1.77/0.61  fof(f29,plain,(
% 1.77/0.61    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3)),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28])).
% 1.77/0.61  fof(f28,plain,(
% 1.77/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f21,plain,(
% 1.77/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f19])).
% 1.77/0.61  fof(f19,negated_conjecture,(
% 1.77/0.61    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.77/0.61    inference(negated_conjecture,[],[f18])).
% 1.77/0.61  fof(f18,conjecture,(
% 1.77/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.77/0.61  fof(f922,plain,(
% 1.77/0.61    sK3 = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.77/0.61    inference(forward_demodulation,[],[f921,f95])).
% 1.77/0.61  fof(f95,plain,(
% 1.77/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.77/0.61    inference(definition_unfolding,[],[f53,f92])).
% 1.77/0.61  fof(f53,plain,(
% 1.77/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.61    inference(cnf_transformation,[],[f7])).
% 1.77/0.61  fof(f7,axiom,(
% 1.77/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.77/0.61  fof(f921,plain,(
% 1.77/0.61    k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k1_xboole_0))),
% 1.77/0.61    inference(forward_demodulation,[],[f907,f467])).
% 1.77/0.61  fof(f467,plain,(
% 1.77/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.77/0.61    inference(forward_demodulation,[],[f464,f111])).
% 1.77/0.61  fof(f111,plain,(
% 1.77/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.77/0.61    inference(resolution,[],[f66,f103])).
% 1.77/0.61  fof(f103,plain,(
% 1.77/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.77/0.61    inference(equality_resolution,[],[f68])).
% 1.77/0.61  fof(f68,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.77/0.61    inference(cnf_transformation,[],[f37])).
% 1.77/0.61  fof(f37,plain,(
% 1.77/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.61    inference(flattening,[],[f36])).
% 1.77/0.61  fof(f36,plain,(
% 1.77/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.77/0.61    inference(nnf_transformation,[],[f5])).
% 1.77/0.61  fof(f5,axiom,(
% 1.77/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.61  fof(f66,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.77/0.61    inference(cnf_transformation,[],[f23])).
% 1.77/0.61  fof(f23,plain,(
% 1.77/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f8])).
% 1.77/0.61  fof(f8,axiom,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.77/0.61  fof(f464,plain,(
% 1.77/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.77/0.61    inference(resolution,[],[f462,f101])).
% 1.77/0.61  fof(f101,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.77/0.61    inference(definition_unfolding,[],[f80,f61])).
% 1.77/0.61  fof(f61,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f6])).
% 1.77/0.61  fof(f6,axiom,(
% 1.77/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.77/0.61  fof(f80,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f44])).
% 1.77/0.61  fof(f44,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(nnf_transformation,[],[f25])).
% 1.77/0.61  fof(f25,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.77/0.61    inference(definition_folding,[],[f3,f24])).
% 1.77/0.61  fof(f24,plain,(
% 1.77/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.77/0.61  fof(f3,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.77/0.61  fof(f462,plain,(
% 1.77/0.61    ( ! [X22] : (sP0(X22,X22,k1_xboole_0)) )),
% 1.77/0.61    inference(global_subsumption,[],[f457])).
% 1.77/0.61  fof(f457,plain,(
% 1.77/0.61    ( ! [X21] : (sP0(X21,X21,k1_xboole_0)) )),
% 1.77/0.61    inference(resolution,[],[f276,f347])).
% 1.77/0.61  fof(f347,plain,(
% 1.77/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f346,f268])).
% 1.77/0.61  fof(f268,plain,(
% 1.77/0.61    ( ! [X8,X9] : (~r2_hidden(X9,k1_xboole_0) | r2_hidden(X9,X8)) )),
% 1.77/0.61    inference(superposition,[],[f137,f222])).
% 1.77/0.61  fof(f222,plain,(
% 1.77/0.61    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.77/0.61    inference(superposition,[],[f120,f208])).
% 1.77/0.61  fof(f208,plain,(
% 1.77/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.77/0.61    inference(superposition,[],[f95,f97])).
% 1.77/0.61  fof(f120,plain,(
% 1.77/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = X2) )),
% 1.77/0.61    inference(resolution,[],[f96,f66])).
% 1.77/0.61  fof(f96,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.77/0.61    inference(definition_unfolding,[],[f57,f92])).
% 1.77/0.61  fof(f57,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f10])).
% 1.77/0.61  fof(f10,axiom,(
% 1.77/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.77/0.61  fof(f137,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X2)) )),
% 1.77/0.61    inference(resolution,[],[f82,f106])).
% 1.77/0.61  fof(f106,plain,(
% 1.77/0.61    ( ! [X0,X1] : (sP1(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.77/0.61    inference(equality_resolution,[],[f87])).
% 1.77/0.61  fof(f87,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f50])).
% 1.77/0.61  fof(f50,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.77/0.61    inference(nnf_transformation,[],[f27])).
% 1.77/0.61  fof(f27,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.77/0.61    inference(definition_folding,[],[f2,f26])).
% 1.77/0.61  fof(f26,plain,(
% 1.77/0.61    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.77/0.61  fof(f2,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.77/0.61  fof(f82,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f49])).
% 1.77/0.61  fof(f49,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 1.77/0.61  fof(f48,plain,(
% 1.77/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f47,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.77/0.61    inference(rectify,[],[f46])).
% 1.77/0.61  fof(f46,plain,(
% 1.77/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.77/0.61    inference(flattening,[],[f45])).
% 1.77/0.61  fof(f45,plain,(
% 1.77/0.61    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.77/0.61    inference(nnf_transformation,[],[f26])).
% 1.77/0.61  fof(f346,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.77/0.61    inference(resolution,[],[f336,f65])).
% 1.77/0.61  fof(f65,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f35])).
% 1.77/0.61  fof(f35,plain,(
% 1.77/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f34])).
% 1.77/0.61  fof(f34,plain,(
% 1.77/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f22,plain,(
% 1.77/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.77/0.61    inference(ennf_transformation,[],[f20])).
% 1.77/0.61  fof(f20,plain,(
% 1.77/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.61    inference(rectify,[],[f4])).
% 1.77/0.61  fof(f4,axiom,(
% 1.77/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.77/0.61  fof(f336,plain,(
% 1.77/0.61    ( ! [X6] : (r1_xboole_0(k1_xboole_0,X6)) )),
% 1.77/0.61    inference(resolution,[],[f306,f129])).
% 1.77/0.61  fof(f129,plain,(
% 1.77/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4))) )),
% 1.77/0.61    inference(subsumption_resolution,[],[f128,f123])).
% 1.77/0.61  fof(f123,plain,(
% 1.77/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4)) | r2_hidden(X3,X4)) )),
% 1.77/0.61    inference(resolution,[],[f73,f113])).
% 1.77/0.61  fof(f113,plain,(
% 1.77/0.61    ( ! [X0] : (sP0(X0,X0,k5_xboole_0(X0,X0))) )),
% 1.77/0.61    inference(superposition,[],[f105,f111])).
% 1.77/0.61  fof(f105,plain,(
% 1.77/0.61    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.77/0.61    inference(equality_resolution,[],[f102])).
% 1.77/0.61  fof(f102,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.77/0.61    inference(definition_unfolding,[],[f79,f61])).
% 1.77/0.61  fof(f79,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.77/0.61    inference(cnf_transformation,[],[f44])).
% 1.77/0.61  fof(f73,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f43])).
% 1.77/0.61  fof(f43,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.77/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 1.77/0.61  fof(f42,plain,(
% 1.77/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.77/0.61    introduced(choice_axiom,[])).
% 1.77/0.61  fof(f41,plain,(
% 1.77/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.77/0.61    inference(rectify,[],[f40])).
% 1.77/0.61  fof(f40,plain,(
% 1.77/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.77/0.61    inference(flattening,[],[f39])).
% 1.77/0.61  fof(f39,plain,(
% 1.77/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.77/0.61    inference(nnf_transformation,[],[f24])).
% 1.77/0.61  fof(f128,plain,(
% 1.77/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4)) | ~r2_hidden(X3,X4)) )),
% 1.77/0.61    inference(resolution,[],[f74,f113])).
% 1.77/0.61  fof(f74,plain,(
% 1.77/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f43])).
% 1.77/0.61  fof(f306,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r2_hidden(sK5(k1_xboole_0,X5),X6) | r1_xboole_0(k1_xboole_0,X5)) )),
% 1.77/0.61    inference(resolution,[],[f268,f63])).
% 1.77/0.61  fof(f63,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f35])).
% 1.77/0.61  fof(f276,plain,(
% 1.77/0.61    ( ! [X2,X3] : (r2_hidden(sK6(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.77/0.61    inference(duplicate_literal_removal,[],[f275])).
% 1.77/0.61  fof(f275,plain,(
% 1.77/0.61    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK6(X2,X2,X3),X3) | r2_hidden(sK6(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.77/0.61    inference(resolution,[],[f77,f76])).
% 1.77/0.61  fof(f76,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f43])).
% 1.77/0.61  fof(f77,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f43])).
% 1.77/0.61  fof(f907,plain,(
% 1.77/0.61    k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2))))),
% 1.77/0.61    inference(superposition,[],[f98,f701])).
% 1.77/0.61  fof(f701,plain,(
% 1.77/0.61    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 1.77/0.61    inference(resolution,[],[f152,f51])).
% 1.77/0.61  fof(f51,plain,(
% 1.77/0.61    r2_hidden(sK2,sK3)),
% 1.77/0.61    inference(cnf_transformation,[],[f29])).
% 1.77/0.61  fof(f152,plain,(
% 1.77/0.61    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) )),
% 1.77/0.61    inference(resolution,[],[f99,f66])).
% 1.77/0.61  fof(f99,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.77/0.61    inference(definition_unfolding,[],[f71,f93])).
% 1.77/0.61  fof(f71,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f38])).
% 1.77/0.61  fof(f38,plain,(
% 1.77/0.61    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.77/0.61    inference(nnf_transformation,[],[f16])).
% 1.77/0.61  fof(f16,axiom,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.77/0.61  fof(f98,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.77/0.61    inference(definition_unfolding,[],[f62,f92,f61,f92])).
% 1.77/0.61  fof(f62,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f9])).
% 1.77/0.61  fof(f9,axiom,(
% 1.77/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.77/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.77/0.61  % SZS output end Proof for theBenchmark
% 1.77/0.61  % (16424)------------------------------
% 1.77/0.61  % (16424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (16424)Termination reason: Refutation
% 1.77/0.61  
% 1.77/0.61  % (16424)Memory used [KB]: 11513
% 1.77/0.61  % (16424)Time elapsed: 0.155 s
% 1.77/0.61  % (16424)------------------------------
% 1.77/0.61  % (16424)------------------------------
% 1.77/0.61  % (16412)Success in time 0.243 s
%------------------------------------------------------------------------------
