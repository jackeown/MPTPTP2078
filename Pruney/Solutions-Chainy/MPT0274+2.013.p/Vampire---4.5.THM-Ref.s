%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:22 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 383 expanded)
%              Number of leaves         :   24 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          :  294 ( 942 expanded)
%              Number of equality atoms :  148 ( 496 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5357,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5354,f5325])).

fof(f5325,plain,(
    r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f5294,f136])).

fof(f136,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f135,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f135,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f124,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f124,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f94,f93])).

fof(f93,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
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

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f94,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f36,f37])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f5294,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | r2_hidden(sK1,sK3) ),
    inference(superposition,[],[f1755,f5293])).

fof(f5293,plain,(
    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(subsumption_resolution,[],[f5292,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( r2_hidden(sK2,sK3)
      | r2_hidden(sK1,sK3)
      | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
    & ( ( ~ r2_hidden(sK2,sK3)
        & ~ r2_hidden(sK1,sK3) )
      | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK2,sK3)
        | r2_hidden(sK1,sK3)
        | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) )
      & ( ( ~ r2_hidden(sK2,sK3)
          & ~ r2_hidden(sK1,sK3) )
        | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f5292,plain,
    ( k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f52,f1752])).

fof(f1752,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f53,f1749])).

fof(f1749,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,X7)
      | r2_hidden(X8,X7)
      | k2_tarski(X8,X6) = k4_xboole_0(k2_tarski(X8,X6),X7) ) ),
    inference(resolution,[],[f76,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(backward_demodulation,[],[f72,f245])).

fof(f245,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f219,f157])).

fof(f157,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f122,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f122,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f64,f60])).

fof(f219,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X8,X7),X8) ),
    inference(forward_demodulation,[],[f218,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f218,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X8,k4_xboole_0(X7,X8)),X8) ),
    inference(forward_demodulation,[],[f206,f157])).

fof(f206,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X8),X8) ),
    inference(resolution,[],[f72,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f53,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3)
    | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f1755,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k4_xboole_0(X0,sK3))
      | r2_hidden(sK1,sK3) ) ),
    inference(resolution,[],[f1753,f646])).

fof(f646,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f644,f641])).

fof(f641,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f518,f625])).

fof(f625,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f603,f599])).

fof(f599,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f576,f98])).

fof(f98,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f576,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f74,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f603,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f599,f61])).

fof(f518,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f644,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f559,f641])).

fof(f559,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f273,f558])).

fof(f558,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X15) = k3_xboole_0(X15,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f557,f518])).

fof(f557,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X15) = k5_xboole_0(k5_xboole_0(X15,k2_xboole_0(X15,X16)),k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f524,f61])).

fof(f524,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X15) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X15,X16),X15),k2_xboole_0(X15,X16)) ),
    inference(superposition,[],[f68,f341])).

fof(f341,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(forward_demodulation,[],[f339,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f339,plain,(
    ! [X6,X7] : k2_xboole_0(k2_xboole_0(X6,X7),X6) = k2_xboole_0(k2_xboole_0(X6,X7),k1_xboole_0) ),
    inference(superposition,[],[f67,f322])).

fof(f322,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f311,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f128,f54])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f65,f57])).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f311,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f245,f66])).

fof(f273,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X3),X2),k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f130,f219])).

fof(f130,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f109,f65])).

fof(f109,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f62,f61])).

fof(f62,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f1753,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | r2_hidden(sK1,sK3) ) ),
    inference(resolution,[],[f1752,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f5354,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f5295,f194])).

fof(f194,plain,(
    ! [X19,X20,X18] :
      ( ~ r1_xboole_0(k2_tarski(X18,X20),X19)
      | ~ r2_hidden(X18,X19) ) ),
    inference(resolution,[],[f71,f135])).

fof(f5295,plain,(
    r1_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(superposition,[],[f59,f5293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (24758)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (24750)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (24742)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (24740)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (24739)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (24738)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (24737)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (24748)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.53  % (24755)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.53  % (24753)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.53  % (24735)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (24746)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.53  % (24761)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.54  % (24751)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.54  % (24764)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.54  % (24762)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.54  % (24763)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.54  % (24759)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.54  % (24756)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.54  % (24747)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (24754)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (24745)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.55  % (24745)Refutation not found, incomplete strategy% (24745)------------------------------
% 1.44/0.55  % (24745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (24745)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (24745)Memory used [KB]: 10618
% 1.44/0.55  % (24745)Time elapsed: 0.140 s
% 1.44/0.55  % (24745)------------------------------
% 1.44/0.55  % (24745)------------------------------
% 1.44/0.55  % (24736)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.55  % (24741)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.55  % (24743)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.56  % (24757)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.56  % (24752)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.56  % (24744)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.57  % (24760)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.57  % (24749)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.10/0.67  % (24742)Refutation found. Thanks to Tanya!
% 2.10/0.67  % SZS status Theorem for theBenchmark
% 2.10/0.67  % SZS output start Proof for theBenchmark
% 2.10/0.67  fof(f5357,plain,(
% 2.10/0.67    $false),
% 2.10/0.67    inference(subsumption_resolution,[],[f5354,f5325])).
% 2.10/0.67  fof(f5325,plain,(
% 2.10/0.67    r2_hidden(sK1,sK3)),
% 2.10/0.67    inference(subsumption_resolution,[],[f5294,f136])).
% 2.10/0.67  fof(f136,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.10/0.67    inference(superposition,[],[f135,f60])).
% 2.10/0.67  fof(f60,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f17])).
% 2.10/0.67  fof(f17,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.10/0.67  fof(f135,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.10/0.67    inference(superposition,[],[f124,f63])).
% 2.10/0.67  fof(f63,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f19])).
% 2.10/0.67  fof(f19,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.10/0.67  fof(f124,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 2.10/0.67    inference(resolution,[],[f94,f93])).
% 2.10/0.67  fof(f93,plain,(
% 2.10/0.67    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 2.10/0.67    inference(equality_resolution,[],[f79])).
% 2.10/0.67  fof(f79,plain,(
% 2.10/0.67    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f49])).
% 2.10/0.67  fof(f49,plain,(
% 2.10/0.67    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 2.10/0.67  fof(f48,plain,(
% 2.10/0.67    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X0 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X2) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X0 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X2 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f47,plain,(
% 2.10/0.67    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.10/0.67    inference(rectify,[],[f46])).
% 2.10/0.67  fof(f46,plain,(
% 2.10/0.67    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.10/0.67    inference(flattening,[],[f45])).
% 2.10/0.67  fof(f45,plain,(
% 2.10/0.67    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.10/0.67    inference(nnf_transformation,[],[f37])).
% 2.10/0.67  fof(f37,plain,(
% 2.10/0.67    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.10/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.10/0.67  fof(f94,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 2.10/0.67    inference(equality_resolution,[],[f86])).
% 2.10/0.67  fof(f86,plain,(
% 2.10/0.67    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.10/0.67    inference(cnf_transformation,[],[f50])).
% 2.10/0.67  fof(f50,plain,(
% 2.10/0.67    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.10/0.67    inference(nnf_transformation,[],[f38])).
% 2.10/0.67  fof(f38,plain,(
% 2.10/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 2.10/0.67    inference(definition_folding,[],[f36,f37])).
% 2.10/0.67  fof(f36,plain,(
% 2.10/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.10/0.67    inference(ennf_transformation,[],[f18])).
% 2.10/0.67  fof(f18,axiom,(
% 2.10/0.67    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.10/0.67  fof(f5294,plain,(
% 2.10/0.67    ~r2_hidden(sK2,k2_tarski(sK1,sK2)) | r2_hidden(sK1,sK3)),
% 2.10/0.67    inference(superposition,[],[f1755,f5293])).
% 2.10/0.67  fof(f5293,plain,(
% 2.10/0.67    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.10/0.67    inference(subsumption_resolution,[],[f5292,f51])).
% 2.10/0.67  fof(f51,plain,(
% 2.10/0.67    ~r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.10/0.67    inference(cnf_transformation,[],[f42])).
% 2.10/0.67  fof(f42,plain,(
% 2.10/0.67    (r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3)) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f41])).
% 2.10/0.67  fof(f41,plain,(
% 2.10/0.67    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)) & ((~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3)) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f40,plain,(
% 2.10/0.67    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.10/0.67    inference(flattening,[],[f39])).
% 2.10/0.67  fof(f39,plain,(
% 2.10/0.67    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.10/0.67    inference(nnf_transformation,[],[f32])).
% 2.10/0.67  fof(f32,plain,(
% 2.10/0.67    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.10/0.67    inference(ennf_transformation,[],[f28])).
% 2.10/0.67  fof(f28,negated_conjecture,(
% 2.10/0.67    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.10/0.67    inference(negated_conjecture,[],[f27])).
% 2.10/0.67  fof(f27,conjecture,(
% 2.10/0.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.10/0.67  fof(f5292,plain,(
% 2.10/0.67    k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3) | r2_hidden(sK1,sK3)),
% 2.10/0.67    inference(resolution,[],[f52,f1752])).
% 2.10/0.67  fof(f1752,plain,(
% 2.10/0.67    r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3)),
% 2.10/0.67    inference(subsumption_resolution,[],[f53,f1749])).
% 2.10/0.67  fof(f1749,plain,(
% 2.10/0.67    ( ! [X6,X8,X7] : (r2_hidden(X6,X7) | r2_hidden(X8,X7) | k2_tarski(X8,X6) = k4_xboole_0(k2_tarski(X8,X6),X7)) )),
% 2.10/0.67    inference(resolution,[],[f76,f254])).
% 2.10/0.67  fof(f254,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.10/0.67    inference(backward_demodulation,[],[f72,f245])).
% 2.10/0.67  fof(f245,plain,(
% 2.10/0.67    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 2.10/0.67    inference(superposition,[],[f219,f157])).
% 2.10/0.67  fof(f157,plain,(
% 2.10/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 2.10/0.67    inference(superposition,[],[f122,f64])).
% 2.10/0.67  fof(f64,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f25])).
% 2.10/0.67  fof(f25,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.10/0.67  fof(f122,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 2.10/0.67    inference(superposition,[],[f64,f60])).
% 2.10/0.67  fof(f219,plain,(
% 2.10/0.67    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X8,X7),X8)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f218,f67])).
% 2.10/0.67  fof(f67,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f8])).
% 2.10/0.67  fof(f8,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.10/0.67  fof(f218,plain,(
% 2.10/0.67    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X8,k4_xboole_0(X7,X8)),X8)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f206,f157])).
% 2.10/0.67  fof(f206,plain,(
% 2.10/0.67    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X8),X8)) )),
% 2.10/0.67    inference(resolution,[],[f72,f59])).
% 2.10/0.67  fof(f59,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f12])).
% 2.10/0.67  fof(f12,axiom,(
% 2.10/0.67    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.10/0.67  fof(f72,plain,(
% 2.10/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 2.10/0.67    inference(cnf_transformation,[],[f34])).
% 2.10/0.67  fof(f34,plain,(
% 2.10/0.67    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.10/0.67    inference(ennf_transformation,[],[f13])).
% 2.10/0.67  fof(f13,axiom,(
% 2.10/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 2.10/0.67  fof(f76,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f35])).
% 2.10/0.67  fof(f35,plain,(
% 2.10/0.67    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 2.10/0.67    inference(ennf_transformation,[],[f26])).
% 2.10/0.67  fof(f26,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 2.10/0.67  fof(f53,plain,(
% 2.10/0.67    r2_hidden(sK2,sK3) | r2_hidden(sK1,sK3) | k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.10/0.67    inference(cnf_transformation,[],[f42])).
% 2.10/0.67  fof(f52,plain,(
% 2.10/0.67    ~r2_hidden(sK2,sK3) | k2_tarski(sK1,sK2) = k4_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.10/0.67    inference(cnf_transformation,[],[f42])).
% 2.10/0.67  fof(f1755,plain,(
% 2.10/0.67    ( ! [X0] : (~r2_hidden(sK2,k4_xboole_0(X0,sK3)) | r2_hidden(sK1,sK3)) )),
% 2.10/0.67    inference(resolution,[],[f1753,f646])).
% 2.10/0.67  fof(f646,plain,(
% 2.10/0.67    ( ! [X2,X3] : (r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.10/0.67    inference(forward_demodulation,[],[f644,f641])).
% 2.10/0.67  fof(f641,plain,(
% 2.10/0.67    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 2.10/0.67    inference(backward_demodulation,[],[f518,f625])).
% 2.10/0.67  fof(f625,plain,(
% 2.10/0.67    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.10/0.67    inference(superposition,[],[f603,f599])).
% 2.10/0.67  fof(f599,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.10/0.67    inference(forward_demodulation,[],[f576,f98])).
% 2.10/0.67  fof(f98,plain,(
% 2.10/0.67    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.10/0.67    inference(superposition,[],[f61,f55])).
% 2.10/0.67  fof(f55,plain,(
% 2.10/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.67    inference(cnf_transformation,[],[f10])).
% 2.10/0.67  fof(f10,axiom,(
% 2.10/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.10/0.67  fof(f61,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f1])).
% 2.10/0.67  fof(f1,axiom,(
% 2.10/0.67    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.10/0.67  fof(f576,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(superposition,[],[f74,f54])).
% 2.10/0.67  fof(f54,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f15])).
% 2.10/0.67  fof(f15,axiom,(
% 2.10/0.67    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.10/0.67  fof(f74,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f14])).
% 2.10/0.67  fof(f14,axiom,(
% 2.10/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.10/0.67  fof(f603,plain,(
% 2.10/0.67    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.10/0.67    inference(superposition,[],[f599,f61])).
% 2.10/0.67  fof(f518,plain,(
% 2.10/0.67    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 2.10/0.67    inference(superposition,[],[f68,f66])).
% 2.10/0.67  fof(f66,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f11])).
% 2.10/0.67  fof(f11,axiom,(
% 2.10/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.10/0.67  fof(f68,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f16])).
% 2.10/0.67  fof(f16,axiom,(
% 2.10/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.10/0.67  fof(f644,plain,(
% 2.10/0.67    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2))) )),
% 2.10/0.67    inference(backward_demodulation,[],[f559,f641])).
% 2.10/0.67  fof(f559,plain,(
% 2.10/0.67    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2))) )),
% 2.10/0.67    inference(backward_demodulation,[],[f273,f558])).
% 2.10/0.67  fof(f558,plain,(
% 2.10/0.67    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X15) = k3_xboole_0(X15,k2_xboole_0(X15,X16))) )),
% 2.10/0.67    inference(forward_demodulation,[],[f557,f518])).
% 2.10/0.67  fof(f557,plain,(
% 2.10/0.67    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X15) = k5_xboole_0(k5_xboole_0(X15,k2_xboole_0(X15,X16)),k2_xboole_0(X15,X16))) )),
% 2.10/0.67    inference(forward_demodulation,[],[f524,f61])).
% 2.10/0.67  fof(f524,plain,(
% 2.10/0.67    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X15) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X15,X16),X15),k2_xboole_0(X15,X16))) )),
% 2.10/0.67    inference(superposition,[],[f68,f341])).
% 2.10/0.67  fof(f341,plain,(
% 2.10/0.67    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f339,f56])).
% 2.10/0.67  fof(f56,plain,(
% 2.10/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.10/0.67    inference(cnf_transformation,[],[f7])).
% 2.10/0.67  fof(f7,axiom,(
% 2.10/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.10/0.67  fof(f339,plain,(
% 2.10/0.67    ( ! [X6,X7] : (k2_xboole_0(k2_xboole_0(X6,X7),X6) = k2_xboole_0(k2_xboole_0(X6,X7),k1_xboole_0)) )),
% 2.10/0.67    inference(superposition,[],[f67,f322])).
% 2.10/0.67  fof(f322,plain,(
% 2.10/0.67    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 2.10/0.67    inference(forward_demodulation,[],[f311,f133])).
% 2.10/0.67  fof(f133,plain,(
% 2.10/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.10/0.67    inference(forward_demodulation,[],[f128,f54])).
% 2.10/0.67  fof(f128,plain,(
% 2.10/0.67    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.10/0.67    inference(superposition,[],[f65,f57])).
% 2.10/0.67  fof(f57,plain,(
% 2.10/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.10/0.67    inference(cnf_transformation,[],[f29])).
% 2.10/0.67  fof(f29,plain,(
% 2.10/0.67    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.10/0.67    inference(rectify,[],[f3])).
% 2.10/0.67  fof(f3,axiom,(
% 2.10/0.67    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.10/0.67  fof(f65,plain,(
% 2.10/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f6])).
% 2.10/0.67  fof(f6,axiom,(
% 2.10/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.10/0.67  fof(f311,plain,(
% 2.10/0.67    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 2.10/0.67    inference(superposition,[],[f245,f66])).
% 2.10/0.67  fof(f273,plain,(
% 2.10/0.67    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(k2_xboole_0(X2,X3),X2),k2_xboole_0(X2,X3)),k4_xboole_0(X3,X2))) )),
% 2.10/0.67    inference(superposition,[],[f130,f219])).
% 2.10/0.67  fof(f130,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(superposition,[],[f109,f65])).
% 2.10/0.67  fof(f109,plain,(
% 2.10/0.67    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 2.10/0.67    inference(superposition,[],[f62,f61])).
% 2.10/0.67  fof(f62,plain,(
% 2.10/0.67    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.10/0.67    inference(cnf_transformation,[],[f5])).
% 2.10/0.67  fof(f5,axiom,(
% 2.10/0.67    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.10/0.67  fof(f1753,plain,(
% 2.10/0.67    ( ! [X0] : (~r1_xboole_0(sK3,X0) | ~r2_hidden(sK2,X0) | r2_hidden(sK1,sK3)) )),
% 2.10/0.67    inference(resolution,[],[f1752,f71])).
% 2.10/0.67  fof(f71,plain,(
% 2.10/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.10/0.67    inference(cnf_transformation,[],[f44])).
% 2.10/0.67  fof(f44,plain,(
% 2.10/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.10/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f43])).
% 2.10/0.67  fof(f43,plain,(
% 2.10/0.67    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.10/0.67    introduced(choice_axiom,[])).
% 2.10/0.67  fof(f33,plain,(
% 2.10/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.10/0.67    inference(ennf_transformation,[],[f31])).
% 2.10/0.67  fof(f31,plain,(
% 2.10/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.67    inference(rectify,[],[f4])).
% 2.10/0.67  fof(f4,axiom,(
% 2.10/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.10/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.10/0.67  fof(f5354,plain,(
% 2.10/0.67    ~r2_hidden(sK1,sK3)),
% 2.10/0.67    inference(resolution,[],[f5295,f194])).
% 2.10/0.67  fof(f194,plain,(
% 2.10/0.67    ( ! [X19,X20,X18] : (~r1_xboole_0(k2_tarski(X18,X20),X19) | ~r2_hidden(X18,X19)) )),
% 2.10/0.67    inference(resolution,[],[f71,f135])).
% 2.10/0.67  fof(f5295,plain,(
% 2.10/0.67    r1_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.10/0.67    inference(superposition,[],[f59,f5293])).
% 2.10/0.67  % SZS output end Proof for theBenchmark
% 2.10/0.67  % (24742)------------------------------
% 2.10/0.67  % (24742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.67  % (24742)Termination reason: Refutation
% 2.10/0.67  
% 2.10/0.67  % (24742)Memory used [KB]: 8699
% 2.10/0.67  % (24742)Time elapsed: 0.232 s
% 2.10/0.67  % (24742)------------------------------
% 2.10/0.67  % (24742)------------------------------
% 2.10/0.67  % (24734)Success in time 0.32 s
%------------------------------------------------------------------------------
