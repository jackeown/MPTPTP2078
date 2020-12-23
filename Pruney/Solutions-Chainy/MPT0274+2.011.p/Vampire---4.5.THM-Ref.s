%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:21 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 939 expanded)
%              Number of leaves         :   24 ( 279 expanded)
%              Depth                    :   28
%              Number of atoms          :  383 (1801 expanded)
%              Number of equality atoms :  160 (1030 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5581,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5580,f162])).

fof(f162,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f158,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f158,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f135,f134])).

fof(f134,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK7(X0,X1,X2,X3) != X0
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X0
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X2
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).

fof(f68,plain,(
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
     => ( ( ( sK7(X0,X1,X2,X3) != X0
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X0
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X2
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f135,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f45,f48])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f5580,plain,(
    ~ r2_hidden(sK2,k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f5579,f5467])).

fof(f5467,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK4)
      | ~ r2_hidden(X10,k2_tarski(sK2,sK3)) ) ),
    inference(superposition,[],[f4786,f5443])).

fof(f5443,plain,(
    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(subsumption_resolution,[],[f5442,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f52])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK3,sK4)
        | r2_hidden(sK2,sK4)
        | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
      & ( ( ~ r2_hidden(sK3,sK4)
          & ~ r2_hidden(sK2,sK4) )
        | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f5442,plain,
    ( k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[],[f72,f4804])).

fof(f4804,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4) ),
    inference(subsumption_resolution,[],[f73,f4799])).

fof(f4799,plain,(
    ! [X4,X2,X3] :
      ( k2_tarski(X4,X2) = k4_xboole_0(k2_tarski(X4,X2),X3)
      | r2_hidden(X2,X3)
      | r2_hidden(X4,X3) ) ),
    inference(backward_demodulation,[],[f4395,f4767])).

fof(f4767,plain,(
    ! [X28,X27] : k4_xboole_0(X27,X28) = k5_xboole_0(X28,k2_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f4736,f85])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4736,plain,(
    ! [X28,X27] : k5_xboole_0(X28,k2_xboole_0(X27,X28)) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(superposition,[],[f815,f802])).

fof(f802,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f95,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f815,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f794,f576])).

fof(f576,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f575,f79])).

fof(f79,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f575,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f562,f80])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f562,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f88,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f794,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f95,f74])).

fof(f4395,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X2,X3)
      | r2_hidden(X4,X3)
      | k2_tarski(X4,X2) = k5_xboole_0(X3,k2_xboole_0(k2_tarski(X4,X2),X3)) ) ),
    inference(resolution,[],[f112,f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f92,f1198])).

fof(f1198,plain,(
    ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X10),X10) = k5_xboole_0(X10,k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f1196,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1196,plain,(
    ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X10),X10) = k5_xboole_0(k2_xboole_0(X9,X10),X10) ),
    inference(superposition,[],[f85,f1142])).

fof(f1142,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f1134,f193])).

fof(f193,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f142,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f142,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f84,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1134,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = X2 ),
    inference(forward_demodulation,[],[f1104,f840])).

fof(f840,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f819,f819])).

fof(f819,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f815,f82])).

fof(f1104,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X2),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f88,f920])).

fof(f920,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f908,f75])).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f908,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f87,f871])).

fof(f871,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f869,f74])).

fof(f869,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X6) = k4_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f85,f853])).

fof(f853,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f570,f839])).

fof(f839,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f819,f815])).

fof(f570,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f88,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f73,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f72,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f4786,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(X8,X7))
      | ~ r2_hidden(X9,X7) ) ),
    inference(backward_demodulation,[],[f4137,f4767])).

fof(f4137,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,k5_xboole_0(X7,k2_xboole_0(X8,X7)))
      | ~ r2_hidden(X9,X7) ) ),
    inference(superposition,[],[f4117,f854])).

fof(f854,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7 ),
    inference(backward_demodulation,[],[f571,f839])).

fof(f571,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f88,f250])).

fof(f250,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f86,f193])).

fof(f4117,plain,(
    ! [X33,X34,X32] :
      ( ~ r2_hidden(X34,k3_xboole_0(X32,X33))
      | ~ r2_hidden(X34,k5_xboole_0(X32,X33)) ) ),
    inference(subsumption_resolution,[],[f4104,f3432])).

fof(f3432,plain,(
    ! [X33,X34,X32] :
      ( ~ r2_hidden(X34,k3_xboole_0(X32,X33))
      | r2_hidden(X34,k2_xboole_0(X32,X33)) ) ),
    inference(global_subsumption,[],[f533,f867])).

fof(f867,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f538,f853])).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f98,f131])).

fof(f131,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f533,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f97,f131])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4104,plain,(
    ! [X33,X34,X32] :
      ( ~ r2_hidden(X34,k3_xboole_0(X32,X33))
      | ~ r2_hidden(X34,k5_xboole_0(X32,X33))
      | ~ r2_hidden(X34,k2_xboole_0(X32,X33)) ) ),
    inference(superposition,[],[f109,f88])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f5579,plain,(
    r2_hidden(sK2,sK4) ),
    inference(subsumption_resolution,[],[f5578,f164])).

fof(f164,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(superposition,[],[f162,f81])).

fof(f5578,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK2,sK3))
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[],[f5467,f4804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.09/0.52  % (14514)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.09/0.53  % (14494)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.53  % (14490)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (14487)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (14506)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.54  % (14487)Refutation not found, incomplete strategy% (14487)------------------------------
% 1.31/0.54  % (14487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (14485)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (14501)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (14487)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (14487)Memory used [KB]: 10746
% 1.31/0.54  % (14487)Time elapsed: 0.108 s
% 1.31/0.54  % (14487)------------------------------
% 1.31/0.54  % (14487)------------------------------
% 1.31/0.54  % (14489)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (14493)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.54  % (14492)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (14510)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.54  % (14497)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (14493)Refutation not found, incomplete strategy% (14493)------------------------------
% 1.31/0.55  % (14493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (14493)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (14493)Memory used [KB]: 10746
% 1.31/0.55  % (14493)Time elapsed: 0.130 s
% 1.31/0.55  % (14493)------------------------------
% 1.31/0.55  % (14493)------------------------------
% 1.31/0.55  % (14488)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (14509)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.55  % (14502)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.55  % (14486)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.55  % (14503)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.56  % (14508)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.56  % (14511)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.56  % (14513)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.56  % (14499)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.56  % (14507)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.56  % (14500)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.57  % (14495)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.57  % (14495)Refutation not found, incomplete strategy% (14495)------------------------------
% 1.31/0.57  % (14495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (14512)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.57  % (14495)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (14495)Memory used [KB]: 10618
% 1.31/0.57  % (14495)Time elapsed: 0.154 s
% 1.31/0.57  % (14495)------------------------------
% 1.31/0.57  % (14495)------------------------------
% 1.31/0.57  % (14498)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.58  % (14505)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.58  % (14491)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.58  % (14504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.59  % (14496)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.59  % (14496)Refutation not found, incomplete strategy% (14496)------------------------------
% 1.31/0.59  % (14496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.59  % (14496)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.59  
% 1.31/0.59  % (14496)Memory used [KB]: 10618
% 1.31/0.59  % (14496)Time elapsed: 0.173 s
% 1.31/0.59  % (14496)------------------------------
% 1.31/0.59  % (14496)------------------------------
% 1.98/0.67  % (14559)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.98/0.68  % (14573)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.44/0.70  % (14563)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.44/0.74  % (14583)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.35/0.87  % (14490)Time limit reached!
% 3.35/0.87  % (14490)------------------------------
% 3.35/0.87  % (14490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.88  % (14492)Refutation found. Thanks to Tanya!
% 3.35/0.88  % SZS status Theorem for theBenchmark
% 3.35/0.88  % SZS output start Proof for theBenchmark
% 3.35/0.88  fof(f5581,plain,(
% 3.35/0.88    $false),
% 3.35/0.88    inference(subsumption_resolution,[],[f5580,f162])).
% 3.35/0.88  fof(f162,plain,(
% 3.35/0.88    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 3.35/0.88    inference(superposition,[],[f158,f83])).
% 3.35/0.88  fof(f83,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f23])).
% 3.35/0.88  fof(f23,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.35/0.88  fof(f158,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 3.35/0.88    inference(resolution,[],[f135,f134])).
% 3.35/0.88  fof(f134,plain,(
% 3.35/0.88    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 3.35/0.88    inference(equality_resolution,[],[f116])).
% 3.35/0.88  fof(f116,plain,(
% 3.35/0.88    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f69])).
% 3.35/0.88  fof(f69,plain,(
% 3.35/0.88    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 3.35/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).
% 3.35/0.88  fof(f68,plain,(
% 3.35/0.88    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 3.35/0.88    introduced(choice_axiom,[])).
% 3.35/0.88  fof(f67,plain,(
% 3.35/0.88    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 3.35/0.88    inference(rectify,[],[f66])).
% 3.35/0.88  fof(f66,plain,(
% 3.35/0.88    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 3.35/0.88    inference(flattening,[],[f65])).
% 3.35/0.88  fof(f65,plain,(
% 3.35/0.88    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 3.35/0.88    inference(nnf_transformation,[],[f48])).
% 3.35/0.88  fof(f48,plain,(
% 3.35/0.88    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.35/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.35/0.88  fof(f135,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 3.35/0.88    inference(equality_resolution,[],[f123])).
% 3.35/0.88  fof(f123,plain,(
% 3.35/0.88    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.35/0.88    inference(cnf_transformation,[],[f70])).
% 3.35/0.88  fof(f70,plain,(
% 3.35/0.88    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 3.35/0.88    inference(nnf_transformation,[],[f49])).
% 3.35/0.88  fof(f49,plain,(
% 3.35/0.88    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 3.35/0.88    inference(definition_folding,[],[f45,f48])).
% 3.35/0.88  fof(f45,plain,(
% 3.35/0.88    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.35/0.88    inference(ennf_transformation,[],[f18])).
% 3.35/0.88  fof(f18,axiom,(
% 3.35/0.88    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.35/0.88  fof(f5580,plain,(
% 3.35/0.88    ~r2_hidden(sK2,k2_tarski(sK2,sK3))),
% 3.35/0.88    inference(resolution,[],[f5579,f5467])).
% 3.35/0.88  fof(f5467,plain,(
% 3.35/0.88    ( ! [X10] : (~r2_hidden(X10,sK4) | ~r2_hidden(X10,k2_tarski(sK2,sK3))) )),
% 3.35/0.88    inference(superposition,[],[f4786,f5443])).
% 3.35/0.88  fof(f5443,plain,(
% 3.35/0.88    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.35/0.88    inference(subsumption_resolution,[],[f5442,f71])).
% 3.35/0.88  fof(f71,plain,(
% 3.35/0.88    ~r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.35/0.88    inference(cnf_transformation,[],[f53])).
% 3.35/0.88  fof(f53,plain,(
% 3.35/0.88    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 3.35/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f52])).
% 3.35/0.88  fof(f52,plain,(
% 3.35/0.88    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)))),
% 3.35/0.88    introduced(choice_axiom,[])).
% 3.35/0.88  fof(f51,plain,(
% 3.35/0.88    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.35/0.88    inference(flattening,[],[f50])).
% 3.35/0.88  fof(f50,plain,(
% 3.35/0.88    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.35/0.88    inference(nnf_transformation,[],[f38])).
% 3.35/0.88  fof(f38,plain,(
% 3.35/0.88    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.35/0.88    inference(ennf_transformation,[],[f34])).
% 3.35/0.88  fof(f34,negated_conjecture,(
% 3.35/0.88    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.35/0.88    inference(negated_conjecture,[],[f33])).
% 3.35/0.88  fof(f33,conjecture,(
% 3.35/0.88    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 3.35/0.88  fof(f5442,plain,(
% 3.35/0.88    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) | r2_hidden(sK2,sK4)),
% 3.35/0.88    inference(resolution,[],[f72,f4804])).
% 3.35/0.88  fof(f4804,plain,(
% 3.35/0.88    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4)),
% 3.35/0.88    inference(subsumption_resolution,[],[f73,f4799])).
% 3.35/0.88  fof(f4799,plain,(
% 3.35/0.88    ( ! [X4,X2,X3] : (k2_tarski(X4,X2) = k4_xboole_0(k2_tarski(X4,X2),X3) | r2_hidden(X2,X3) | r2_hidden(X4,X3)) )),
% 3.35/0.88    inference(backward_demodulation,[],[f4395,f4767])).
% 3.35/0.88  fof(f4767,plain,(
% 3.35/0.88    ( ! [X28,X27] : (k4_xboole_0(X27,X28) = k5_xboole_0(X28,k2_xboole_0(X27,X28))) )),
% 3.35/0.88    inference(forward_demodulation,[],[f4736,f85])).
% 3.35/0.88  fof(f85,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.35/0.88    inference(cnf_transformation,[],[f7])).
% 3.35/0.88  fof(f7,axiom,(
% 3.35/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.35/0.88  fof(f4736,plain,(
% 3.35/0.88    ( ! [X28,X27] : (k5_xboole_0(X28,k2_xboole_0(X27,X28)) = k5_xboole_0(X27,k3_xboole_0(X27,X28))) )),
% 3.35/0.88    inference(superposition,[],[f815,f802])).
% 3.35/0.88  fof(f802,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 3.35/0.88    inference(superposition,[],[f95,f88])).
% 3.35/0.88  fof(f88,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.35/0.88    inference(cnf_transformation,[],[f16])).
% 3.35/0.88  fof(f16,axiom,(
% 3.35/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.35/0.88  fof(f95,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.35/0.88    inference(cnf_transformation,[],[f14])).
% 3.35/0.88  fof(f14,axiom,(
% 3.35/0.88    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.35/0.88  fof(f815,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.35/0.88    inference(forward_demodulation,[],[f794,f576])).
% 3.35/0.88  fof(f576,plain,(
% 3.35/0.88    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.35/0.88    inference(forward_demodulation,[],[f575,f79])).
% 3.35/0.88  fof(f79,plain,(
% 3.35/0.88    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.35/0.88    inference(cnf_transformation,[],[f35])).
% 3.35/0.88  fof(f35,plain,(
% 3.35/0.88    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.35/0.88    inference(rectify,[],[f4])).
% 3.35/0.88  fof(f4,axiom,(
% 3.35/0.88    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.35/0.88  fof(f575,plain,(
% 3.35/0.88    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 3.35/0.88    inference(forward_demodulation,[],[f562,f80])).
% 3.35/0.88  fof(f80,plain,(
% 3.35/0.88    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.35/0.88    inference(cnf_transformation,[],[f36])).
% 3.35/0.88  fof(f36,plain,(
% 3.35/0.88    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.35/0.88    inference(rectify,[],[f3])).
% 3.35/0.88  fof(f3,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.35/0.88  fof(f562,plain,(
% 3.35/0.88    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 3.35/0.88    inference(superposition,[],[f88,f74])).
% 3.35/0.88  fof(f74,plain,(
% 3.35/0.88    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f15])).
% 3.35/0.88  fof(f15,axiom,(
% 3.35/0.88    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.35/0.88  fof(f794,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.35/0.88    inference(superposition,[],[f95,f74])).
% 3.35/0.88  fof(f4395,plain,(
% 3.35/0.88    ( ! [X4,X2,X3] : (r2_hidden(X2,X3) | r2_hidden(X4,X3) | k2_tarski(X4,X2) = k5_xboole_0(X3,k2_xboole_0(k2_tarski(X4,X2),X3))) )),
% 3.35/0.88    inference(resolution,[],[f112,f1203])).
% 3.35/0.88  fof(f1203,plain,(
% 3.35/0.88    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0) )),
% 3.35/0.88    inference(backward_demodulation,[],[f92,f1198])).
% 3.35/0.88  fof(f1198,plain,(
% 3.35/0.88    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X10),X10) = k5_xboole_0(X10,k2_xboole_0(X9,X10))) )),
% 3.35/0.88    inference(forward_demodulation,[],[f1196,f82])).
% 3.35/0.88  fof(f82,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f1])).
% 3.35/0.88  fof(f1,axiom,(
% 3.35/0.88    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.35/0.88  fof(f1196,plain,(
% 3.35/0.88    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X10),X10) = k5_xboole_0(k2_xboole_0(X9,X10),X10)) )),
% 3.35/0.88    inference(superposition,[],[f85,f1142])).
% 3.35/0.88  fof(f1142,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1) )),
% 3.35/0.88    inference(superposition,[],[f1134,f193])).
% 3.35/0.88  fof(f193,plain,(
% 3.35/0.88    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 3.35/0.88    inference(superposition,[],[f142,f84])).
% 3.35/0.88  fof(f84,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.35/0.88    inference(cnf_transformation,[],[f30])).
% 3.35/0.88  fof(f30,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.35/0.88  fof(f142,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 3.35/0.88    inference(superposition,[],[f84,f81])).
% 3.35/0.88  fof(f81,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f17])).
% 3.35/0.88  fof(f17,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.35/0.88  fof(f1134,plain,(
% 3.35/0.88    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = X2) )),
% 3.35/0.88    inference(forward_demodulation,[],[f1104,f840])).
% 3.35/0.88  fof(f840,plain,(
% 3.35/0.88    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 3.35/0.88    inference(superposition,[],[f819,f819])).
% 3.35/0.88  fof(f819,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 3.35/0.88    inference(superposition,[],[f815,f82])).
% 3.35/0.88  fof(f1104,plain,(
% 3.35/0.88    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X2),k2_xboole_0(X2,X3))) )),
% 3.35/0.88    inference(superposition,[],[f88,f920])).
% 3.35/0.88  fof(f920,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 3.35/0.88    inference(forward_demodulation,[],[f908,f75])).
% 3.35/0.88  fof(f75,plain,(
% 3.35/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.35/0.88    inference(cnf_transformation,[],[f8])).
% 3.35/0.88  fof(f8,axiom,(
% 3.35/0.88    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.35/0.88  fof(f908,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 3.35/0.88    inference(superposition,[],[f87,f871])).
% 3.35/0.88  fof(f871,plain,(
% 3.35/0.88    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 3.35/0.88    inference(forward_demodulation,[],[f869,f74])).
% 3.35/0.88  fof(f869,plain,(
% 3.35/0.88    ( ! [X6,X7] : (k5_xboole_0(X6,X6) = k4_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 3.35/0.88    inference(superposition,[],[f85,f853])).
% 3.35/0.88  fof(f853,plain,(
% 3.35/0.88    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 3.35/0.88    inference(backward_demodulation,[],[f570,f839])).
% 3.35/0.88  fof(f839,plain,(
% 3.35/0.88    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 3.35/0.88    inference(superposition,[],[f819,f815])).
% 3.35/0.88  fof(f570,plain,(
% 3.35/0.88    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 3.35/0.88    inference(superposition,[],[f88,f86])).
% 3.35/0.88  fof(f86,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.35/0.88    inference(cnf_transformation,[],[f12])).
% 3.35/0.88  fof(f12,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 3.35/0.88  fof(f87,plain,(
% 3.35/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f9])).
% 3.35/0.88  fof(f9,axiom,(
% 3.35/0.88    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.35/0.88  fof(f92,plain,(
% 3.35/0.88    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 3.35/0.88    inference(cnf_transformation,[],[f41])).
% 3.35/0.88  fof(f41,plain,(
% 3.35/0.88    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.35/0.88    inference(ennf_transformation,[],[f13])).
% 3.35/0.88  fof(f13,axiom,(
% 3.35/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 3.35/0.88  fof(f112,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f44])).
% 3.35/0.88  fof(f44,plain,(
% 3.35/0.88    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 3.35/0.88    inference(ennf_transformation,[],[f32])).
% 3.35/0.88  fof(f32,axiom,(
% 3.35/0.88    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 3.35/0.88  fof(f73,plain,(
% 3.35/0.88    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.35/0.88    inference(cnf_transformation,[],[f53])).
% 3.35/0.88  fof(f72,plain,(
% 3.35/0.88    ~r2_hidden(sK3,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.35/0.88    inference(cnf_transformation,[],[f53])).
% 3.35/0.88  fof(f4786,plain,(
% 3.35/0.88    ( ! [X8,X7,X9] : (~r2_hidden(X9,k4_xboole_0(X8,X7)) | ~r2_hidden(X9,X7)) )),
% 3.35/0.88    inference(backward_demodulation,[],[f4137,f4767])).
% 3.35/0.88  fof(f4137,plain,(
% 3.35/0.88    ( ! [X8,X7,X9] : (~r2_hidden(X9,k5_xboole_0(X7,k2_xboole_0(X8,X7))) | ~r2_hidden(X9,X7)) )),
% 3.35/0.88    inference(superposition,[],[f4117,f854])).
% 3.35/0.88  fof(f854,plain,(
% 3.35/0.88    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7) )),
% 3.35/0.88    inference(backward_demodulation,[],[f571,f839])).
% 3.35/0.88  fof(f571,plain,(
% 3.35/0.88    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7))) )),
% 3.35/0.88    inference(superposition,[],[f88,f250])).
% 3.35/0.88  fof(f250,plain,(
% 3.35/0.88    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 3.35/0.88    inference(superposition,[],[f86,f193])).
% 3.35/0.88  fof(f4117,plain,(
% 3.35/0.88    ( ! [X33,X34,X32] : (~r2_hidden(X34,k3_xboole_0(X32,X33)) | ~r2_hidden(X34,k5_xboole_0(X32,X33))) )),
% 3.35/0.88    inference(subsumption_resolution,[],[f4104,f3432])).
% 3.35/0.88  fof(f3432,plain,(
% 3.35/0.88    ( ! [X33,X34,X32] : (~r2_hidden(X34,k3_xboole_0(X32,X33)) | r2_hidden(X34,k2_xboole_0(X32,X33))) )),
% 3.35/0.88    inference(global_subsumption,[],[f533,f867])).
% 3.35/0.88  fof(f867,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 3.35/0.88    inference(superposition,[],[f538,f853])).
% 3.35/0.88  fof(f538,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X2)) )),
% 3.35/0.88    inference(resolution,[],[f98,f131])).
% 3.35/0.88  fof(f131,plain,(
% 3.35/0.88    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 3.35/0.88    inference(equality_resolution,[],[f103])).
% 3.35/0.88  fof(f103,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.35/0.88    inference(cnf_transformation,[],[f61])).
% 3.35/0.88  fof(f61,plain,(
% 3.35/0.88    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 3.35/0.88    inference(nnf_transformation,[],[f47])).
% 3.35/0.88  fof(f47,plain,(
% 3.35/0.88    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 3.35/0.88    inference(definition_folding,[],[f2,f46])).
% 3.35/0.88  fof(f46,plain,(
% 3.35/0.88    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.35/0.88    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.35/0.88  fof(f2,axiom,(
% 3.35/0.88    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.35/0.88  fof(f98,plain,(
% 3.35/0.88    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f60])).
% 3.35/0.88  fof(f60,plain,(
% 3.35/0.88    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.35/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 3.35/0.88  fof(f59,plain,(
% 3.35/0.88    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 3.35/0.88    introduced(choice_axiom,[])).
% 3.35/0.88  fof(f58,plain,(
% 3.35/0.88    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 3.35/0.88    inference(rectify,[],[f57])).
% 3.35/0.88  fof(f57,plain,(
% 3.35/0.88    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.35/0.88    inference(flattening,[],[f56])).
% 3.35/0.88  fof(f56,plain,(
% 3.35/0.88    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 3.35/0.88    inference(nnf_transformation,[],[f46])).
% 3.35/0.88  fof(f533,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 3.35/0.88    inference(resolution,[],[f97,f131])).
% 3.35/0.88  fof(f97,plain,(
% 3.35/0.88    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f60])).
% 3.35/0.88  fof(f4104,plain,(
% 3.35/0.88    ( ! [X33,X34,X32] : (~r2_hidden(X34,k3_xboole_0(X32,X33)) | ~r2_hidden(X34,k5_xboole_0(X32,X33)) | ~r2_hidden(X34,k2_xboole_0(X32,X33))) )),
% 3.35/0.88    inference(superposition,[],[f109,f88])).
% 3.35/0.88  fof(f109,plain,(
% 3.35/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.35/0.88    inference(cnf_transformation,[],[f64])).
% 3.35/0.88  fof(f64,plain,(
% 3.35/0.88    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.35/0.88    inference(nnf_transformation,[],[f43])).
% 3.35/0.88  fof(f43,plain,(
% 3.35/0.88    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.35/0.88    inference(ennf_transformation,[],[f5])).
% 3.35/0.88  fof(f5,axiom,(
% 3.35/0.88    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.35/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 3.35/0.88  fof(f5579,plain,(
% 3.35/0.88    r2_hidden(sK2,sK4)),
% 3.35/0.88    inference(subsumption_resolution,[],[f5578,f164])).
% 3.35/0.88  fof(f164,plain,(
% 3.35/0.88    ( ! [X2,X1] : (r2_hidden(X1,k2_tarski(X2,X1))) )),
% 3.35/0.88    inference(superposition,[],[f162,f81])).
% 3.35/0.88  fof(f5578,plain,(
% 3.35/0.88    ~r2_hidden(sK3,k2_tarski(sK2,sK3)) | r2_hidden(sK2,sK4)),
% 3.35/0.88    inference(resolution,[],[f5467,f4804])).
% 3.35/0.88  % SZS output end Proof for theBenchmark
% 3.35/0.88  % (14492)------------------------------
% 3.35/0.88  % (14492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.88  % (14492)Termination reason: Refutation
% 3.35/0.88  
% 3.35/0.88  % (14492)Memory used [KB]: 9466
% 3.35/0.88  % (14492)Time elapsed: 0.465 s
% 3.35/0.88  % (14492)------------------------------
% 3.35/0.88  % (14492)------------------------------
% 3.35/0.88  % (14484)Success in time 0.513 s
%------------------------------------------------------------------------------
