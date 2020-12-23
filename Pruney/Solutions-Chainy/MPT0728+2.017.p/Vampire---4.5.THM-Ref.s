%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 100 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  260 ( 306 expanded)
%              Number of equality atoms :   99 ( 137 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(resolution,[],[f101,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] : sP1(X7,X1,X2,X3,X4,X5,X6,X7) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 != X7 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    ~ sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(resolution,[],[f96,f74])).

fof(f74,plain,(
    ~ r2_hidden(sK3,k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f36,f73])).

fof(f73,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f38,f71,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f36,plain,(
    ~ r2_hidden(sK3,k1_ordinal1(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ~ r2_hidden(sK3,k1_ordinal1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,
    ( ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0))
   => ~ r2_hidden(sK3,k1_ordinal1(sK3)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X8))))
      | ~ sP1(X0,X8,X7,X6,X5,X4,X3,X2) ) ),
    inference(resolution,[],[f91,f77])).

fof(f77,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f91,plain,(
    ! [X30,X28,X26,X33,X31,X29,X27,X25,X34,X32] :
      ( ~ sP0(k5_enumset1(X32,X31,X30,X29,X28,X27,X26),X34,X33)
      | r2_hidden(X25,X33)
      | ~ sP1(X25,X26,X27,X28,X29,X30,X31,X32) ) ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X0,k5_enumset1(X7,X6,X5,X4,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(resolution,[],[f54,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP2(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7) )
      & ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP2(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> sP1(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7)
      | ~ sP1(X9,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X9,X7) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ~ sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP1(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X8,X7) )
          & ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X8,X7) ) )
     => ( ( ~ sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP1(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ~ sP1(X8,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(nnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (26909)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (26902)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (26894)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (26894)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (26881)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(resolution,[],[f101,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X7,X5,X3,X1] : (sP1(X7,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.20/0.53    inference(equality_resolution,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | X0 != X7) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.53    inference(rectify,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP1(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~sP1(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP1(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~sP1(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X8,X6,X5,X4,X3,X2,X1,X0] : (sP1(X8,X6,X5,X4,X3,X2,X1,X0) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ~sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.53    inference(resolution,[],[f96,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~r2_hidden(sK3,k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 0.20/0.53    inference(definition_unfolding,[],[f36,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f38,f71,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f37,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f40,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f41,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f50,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f51,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f39,f70])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ~r2_hidden(sK3,k1_ordinal1(sK3))),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ~r2_hidden(sK3,k1_ordinal1(sK3))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0)) => ~r2_hidden(sK3,k1_ordinal1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (r2_hidden(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) | ~sP1(X0,X8,X7,X6,X5,X4,X3,X2)) )),
% 0.20/0.53    inference(resolution,[],[f91,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.53    inference(definition_unfolding,[],[f48,f71])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.53    inference(definition_folding,[],[f1,f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X30,X28,X26,X33,X31,X29,X27,X25,X34,X32] : (~sP0(k5_enumset1(X32,X31,X30,X29,X28,X27,X26),X34,X33) | r2_hidden(X25,X33) | ~sP1(X25,X26,X27,X28,X29,X30,X31,X32)) )),
% 0.20/0.53    inference(resolution,[],[f88,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f15])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X0,k5_enumset1(X7,X6,X5,X4,X3,X2,X1)) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.20/0.53    inference(resolution,[],[f54,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.53    inference(equality_resolution,[],[f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7)) & (sP2(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP2(X0,X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.53    inference(definition_folding,[],[f14,f18,f17])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> sP1(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (~sP2(X0,X1,X2,X3,X4,X5,X6,X7) | ~sP1(X9,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X7)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7) | ((~sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP1(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : ((~sP1(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP1(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7))) => ((~sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP1(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP1(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP1(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP1(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.53    inference(rectify,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP1(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP1(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | ~sP1(X8,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 0.20/0.53    inference(nnf_transformation,[],[f18])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (26894)------------------------------
% 0.20/0.53  % (26894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26894)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (26894)Memory used [KB]: 6268
% 0.20/0.53  % (26894)Time elapsed: 0.101 s
% 0.20/0.53  % (26894)------------------------------
% 0.20/0.53  % (26894)------------------------------
% 0.20/0.53  % (26879)Success in time 0.168 s
%------------------------------------------------------------------------------
