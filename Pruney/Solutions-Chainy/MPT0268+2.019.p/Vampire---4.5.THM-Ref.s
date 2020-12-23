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
% DateTime   : Thu Dec  3 12:40:38 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 227 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  297 ( 517 expanded)
%              Number of equality atoms :  135 ( 280 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(subsumption_resolution,[],[f726,f100])).

fof(f100,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f99,f48])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f99,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f95,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK5(X0,X1,X2,X3) != X0
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X0
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X2
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X0
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X0
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X2
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f81,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f726,plain,(
    ~ r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(resolution,[],[f649,f652])).

fof(f652,plain,(
    sP0(k1_tarski(sK3),sK2,sK2) ),
    inference(superposition,[],[f77,f624])).

fof(f624,plain,(
    sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f613,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f613,plain,(
    k4_xboole_0(sK2,k1_tarski(sK3)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f52,f607])).

fof(f607,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3))
    | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f596,f129])).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f123,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f85,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f123,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f53,f116])).

fof(f116,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f114,f47])).

fof(f114,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f52,f86])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f596,plain,
    ( k3_xboole_0(sK2,k1_tarski(sK3)) = k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(superposition,[],[f53,f582])).

fof(f582,plain,
    ( sK2 = k4_xboole_0(sK2,k1_tarski(sK3))
    | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f581,f50])).

fof(f581,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK3),sK2)
    | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f572,f129])).

fof(f572,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK2) = k4_xboole_0(k1_tarski(sK3),k1_tarski(sK3))
    | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(superposition,[],[f53,f218])).

fof(f218,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK2)
    | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(resolution,[],[f94,f44])).

fof(f44,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( r2_hidden(sK3,sK2)
      | sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) )
    & ( ~ r2_hidden(sK3,sK2)
      | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) )
      & ( ~ r2_hidden(sK3,sK2)
        | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f649,plain,(
    ! [X2,X3] :
      ( ~ sP0(X2,X3,sK2)
      | ~ r2_hidden(sK3,X2) ) ),
    inference(resolution,[],[f625,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f625,plain,(
    r2_hidden(sK3,sK2) ),
    inference(subsumption_resolution,[],[f45,f624])).

fof(f45,plain,
    ( sK2 != k4_xboole_0(sK2,k1_tarski(sK3))
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (24458)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (24474)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (24452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (24466)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.54  % (24449)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (24460)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (24477)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.54  % (24450)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.54  % (24456)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.54  % (24453)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.55  % (24450)Refutation not found, incomplete strategy% (24450)------------------------------
% 1.25/0.55  % (24450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.55  % (24450)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.55  
% 1.25/0.55  % (24450)Memory used [KB]: 10746
% 1.25/0.55  % (24450)Time elapsed: 0.123 s
% 1.25/0.55  % (24450)------------------------------
% 1.25/0.55  % (24450)------------------------------
% 1.25/0.55  % (24465)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.55  % (24455)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.55  % (24469)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.55  % (24464)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.55  % (24470)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.55  % (24467)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.55  % (24476)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.55  % (24462)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.55  % (24451)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.55  % (24461)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (24468)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (24454)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.56  % (24475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.56  % (24472)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.56  % (24471)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.56  % (24457)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  % (24459)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (24473)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.57  % (24456)Refutation not found, incomplete strategy% (24456)------------------------------
% 1.48/0.57  % (24456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (24456)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (24456)Memory used [KB]: 10618
% 1.48/0.57  % (24456)Time elapsed: 0.150 s
% 1.48/0.57  % (24456)------------------------------
% 1.48/0.57  % (24456)------------------------------
% 1.48/0.57  % (24463)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.57  % (24465)Refutation not found, incomplete strategy% (24465)------------------------------
% 1.48/0.57  % (24465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (24465)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (24465)Memory used [KB]: 10618
% 1.48/0.57  % (24465)Time elapsed: 0.148 s
% 1.48/0.57  % (24465)------------------------------
% 1.48/0.57  % (24465)------------------------------
% 1.48/0.57  % (24448)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.61  % (24455)Refutation found. Thanks to Tanya!
% 1.48/0.61  % SZS status Theorem for theBenchmark
% 1.48/0.61  % SZS output start Proof for theBenchmark
% 1.48/0.61  fof(f727,plain,(
% 1.48/0.61    $false),
% 1.48/0.61    inference(subsumption_resolution,[],[f726,f100])).
% 1.48/0.61  fof(f100,plain,(
% 1.48/0.61    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.48/0.61    inference(superposition,[],[f99,f48])).
% 1.48/0.61  fof(f48,plain,(
% 1.48/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f11])).
% 1.48/0.61  fof(f11,axiom,(
% 1.48/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.61  fof(f99,plain,(
% 1.48/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.48/0.61    inference(superposition,[],[f95,f51])).
% 1.48/0.61  fof(f51,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f12])).
% 1.48/0.61  fof(f12,axiom,(
% 1.48/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.61  fof(f95,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.48/0.61    inference(resolution,[],[f81,f80])).
% 1.48/0.61  fof(f80,plain,(
% 1.48/0.61    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.48/0.61    inference(equality_resolution,[],[f68])).
% 1.48/0.61  fof(f68,plain,(
% 1.48/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f42])).
% 1.48/0.61  fof(f42,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.48/0.61  fof(f41,plain,(
% 1.48/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f40,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.48/0.61    inference(rectify,[],[f39])).
% 1.48/0.61  fof(f39,plain,(
% 1.48/0.61    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.48/0.61    inference(flattening,[],[f38])).
% 1.48/0.61  fof(f38,plain,(
% 1.48/0.61    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.48/0.61    inference(nnf_transformation,[],[f27])).
% 1.48/0.61  fof(f27,plain,(
% 1.48/0.61    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.48/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.48/0.61  fof(f81,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.48/0.61    inference(equality_resolution,[],[f75])).
% 1.48/0.61  fof(f75,plain,(
% 1.48/0.61    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.48/0.61    inference(cnf_transformation,[],[f43])).
% 1.48/0.61  fof(f43,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.48/0.61    inference(nnf_transformation,[],[f28])).
% 1.48/0.61  fof(f28,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 1.48/0.61    inference(definition_folding,[],[f24,f27])).
% 1.48/0.61  fof(f24,plain,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.48/0.61    inference(ennf_transformation,[],[f10])).
% 1.48/0.61  fof(f10,axiom,(
% 1.48/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.48/0.61  fof(f726,plain,(
% 1.48/0.61    ~r2_hidden(sK3,k1_tarski(sK3))),
% 1.48/0.61    inference(resolution,[],[f649,f652])).
% 1.48/0.61  fof(f652,plain,(
% 1.48/0.61    sP0(k1_tarski(sK3),sK2,sK2)),
% 1.48/0.61    inference(superposition,[],[f77,f624])).
% 1.48/0.61  fof(f624,plain,(
% 1.48/0.61    sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(forward_demodulation,[],[f613,f47])).
% 1.48/0.61  fof(f47,plain,(
% 1.48/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f8])).
% 1.48/0.61  fof(f8,axiom,(
% 1.48/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.48/0.61  fof(f613,plain,(
% 1.48/0.61    k4_xboole_0(sK2,k1_tarski(sK3)) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.48/0.61    inference(superposition,[],[f52,f607])).
% 1.48/0.61  fof(f607,plain,(
% 1.48/0.61    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(duplicate_literal_removal,[],[f606])).
% 1.48/0.61  fof(f606,plain,(
% 1.48/0.61    k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3)) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(forward_demodulation,[],[f596,f129])).
% 1.48/0.61  fof(f129,plain,(
% 1.48/0.61    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.48/0.61    inference(forward_demodulation,[],[f123,f86])).
% 1.48/0.61  fof(f86,plain,(
% 1.48/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.48/0.61    inference(superposition,[],[f85,f50])).
% 1.48/0.61  fof(f50,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f1])).
% 1.48/0.61  fof(f1,axiom,(
% 1.48/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.48/0.61  fof(f85,plain,(
% 1.48/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.48/0.61    inference(resolution,[],[f55,f46])).
% 1.48/0.61  fof(f46,plain,(
% 1.48/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f6])).
% 1.48/0.61  fof(f6,axiom,(
% 1.48/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.48/0.61  fof(f55,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f22])).
% 1.48/0.61  fof(f22,plain,(
% 1.48/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.61    inference(ennf_transformation,[],[f5])).
% 1.48/0.61  fof(f5,axiom,(
% 1.48/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.61  fof(f123,plain,(
% 1.48/0.61    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 1.48/0.61    inference(superposition,[],[f53,f116])).
% 1.48/0.61  fof(f116,plain,(
% 1.48/0.61    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 1.48/0.61    inference(forward_demodulation,[],[f114,f47])).
% 1.48/0.61  fof(f114,plain,(
% 1.48/0.61    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 1.48/0.61    inference(superposition,[],[f52,f86])).
% 1.48/0.61  fof(f53,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f7])).
% 1.48/0.61  fof(f7,axiom,(
% 1.48/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.48/0.61  fof(f596,plain,(
% 1.48/0.61    k3_xboole_0(sK2,k1_tarski(sK3)) = k4_xboole_0(sK2,sK2) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(superposition,[],[f53,f582])).
% 1.48/0.61  fof(f582,plain,(
% 1.48/0.61    sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) | k1_xboole_0 = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(forward_demodulation,[],[f581,f50])).
% 1.48/0.61  fof(f581,plain,(
% 1.48/0.61    k1_xboole_0 = k3_xboole_0(k1_tarski(sK3),sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(forward_demodulation,[],[f572,f129])).
% 1.48/0.61  fof(f572,plain,(
% 1.48/0.61    k3_xboole_0(k1_tarski(sK3),sK2) = k4_xboole_0(k1_tarski(sK3),k1_tarski(sK3)) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(superposition,[],[f53,f218])).
% 1.48/0.61  fof(f218,plain,(
% 1.48/0.61    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(resolution,[],[f94,f44])).
% 1.48/0.61  fof(f44,plain,(
% 1.48/0.61    ~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.48/0.61    inference(cnf_transformation,[],[f31])).
% 1.48/0.61  fof(f31,plain,(
% 1.48/0.61    (r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k1_tarski(sK3))) & (~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3)))),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).
% 1.48/0.61  fof(f30,plain,(
% 1.48/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | sK2 != k4_xboole_0(sK2,k1_tarski(sK3))) & (~r2_hidden(sK3,sK2) | sK2 = k4_xboole_0(sK2,k1_tarski(sK3))))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f29,plain,(
% 1.48/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.48/0.61    inference(nnf_transformation,[],[f20])).
% 1.48/0.61  fof(f20,plain,(
% 1.48/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.48/0.61    inference(ennf_transformation,[],[f17])).
% 1.48/0.61  fof(f17,negated_conjecture,(
% 1.48/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.48/0.61    inference(negated_conjecture,[],[f16])).
% 1.48/0.61  fof(f16,conjecture,(
% 1.48/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.48/0.61  fof(f94,plain,(
% 1.48/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.48/0.61    inference(resolution,[],[f56,f54])).
% 1.48/0.61  fof(f54,plain,(
% 1.48/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f21])).
% 1.48/0.61  fof(f21,plain,(
% 1.48/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.48/0.61    inference(ennf_transformation,[],[f15])).
% 1.48/0.61  fof(f15,axiom,(
% 1.48/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.48/0.61  fof(f56,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.48/0.61    inference(cnf_transformation,[],[f23])).
% 1.48/0.61  fof(f23,plain,(
% 1.48/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.48/0.61    inference(ennf_transformation,[],[f19])).
% 1.48/0.61  fof(f19,plain,(
% 1.48/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.48/0.61    inference(unused_predicate_definition_removal,[],[f9])).
% 1.48/0.61  fof(f9,axiom,(
% 1.48/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.48/0.61  fof(f52,plain,(
% 1.48/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.61    inference(cnf_transformation,[],[f4])).
% 1.48/0.61  fof(f4,axiom,(
% 1.48/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.48/0.61  fof(f77,plain,(
% 1.48/0.61    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.61    inference(equality_resolution,[],[f64])).
% 1.48/0.61  fof(f64,plain,(
% 1.48/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.48/0.61    inference(cnf_transformation,[],[f37])).
% 1.48/0.61  fof(f37,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.48/0.61    inference(nnf_transformation,[],[f26])).
% 1.48/0.61  fof(f26,plain,(
% 1.48/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.48/0.61    inference(definition_folding,[],[f2,f25])).
% 1.48/0.61  fof(f25,plain,(
% 1.48/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.61  fof(f2,axiom,(
% 1.48/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.48/0.61  fof(f649,plain,(
% 1.48/0.61    ( ! [X2,X3] : (~sP0(X2,X3,sK2) | ~r2_hidden(sK3,X2)) )),
% 1.48/0.61    inference(resolution,[],[f625,f59])).
% 1.48/0.61  fof(f59,plain,(
% 1.48/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f36])).
% 1.48/0.61  fof(f36,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.48/0.61  fof(f35,plain,(
% 1.48/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f34,plain,(
% 1.48/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.48/0.61    inference(rectify,[],[f33])).
% 1.48/0.61  fof(f33,plain,(
% 1.48/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.48/0.61    inference(flattening,[],[f32])).
% 1.48/0.61  fof(f32,plain,(
% 1.48/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.48/0.61    inference(nnf_transformation,[],[f25])).
% 1.48/0.61  fof(f625,plain,(
% 1.48/0.61    r2_hidden(sK3,sK2)),
% 1.48/0.61    inference(subsumption_resolution,[],[f45,f624])).
% 1.48/0.61  fof(f45,plain,(
% 1.48/0.61    sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) | r2_hidden(sK3,sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f31])).
% 1.48/0.61  % SZS output end Proof for theBenchmark
% 1.48/0.61  % (24455)------------------------------
% 1.48/0.61  % (24455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (24455)Termination reason: Refutation
% 1.48/0.61  
% 1.48/0.61  % (24455)Memory used [KB]: 6652
% 1.48/0.61  % (24455)Time elapsed: 0.174 s
% 1.48/0.61  % (24455)------------------------------
% 1.48/0.61  % (24455)------------------------------
% 1.48/0.61  % (24445)Success in time 0.24 s
%------------------------------------------------------------------------------
