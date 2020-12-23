%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:20 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 140 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  299 ( 686 expanded)
%              Number of equality atoms :  125 ( 265 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f34])).

fof(f34,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f265,plain,(
    sK2 = sK5 ),
    inference(subsumption_resolution,[],[f264,f33])).

fof(f33,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f16])).

fof(f264,plain,
    ( sK2 = sK4
    | sK2 = sK5 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( sK2 = sK4
    | sK2 = sK4
    | sK2 = sK5 ),
    inference(resolution,[],[f200,f141])).

fof(f141,plain,(
    r2_hidden(sK2,k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(resolution,[],[f140,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(resolution,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f70,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f10,f13])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f140,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_enumset1(sK2,sK2,sK2,sK3))
      | r2_hidden(X5,k2_enumset1(sK4,sK4,sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f139,f126])).

fof(f126,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f125,f122])).

fof(f122,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f42,f76])).

fof(f76,plain,(
    ! [X1] : sP0(X1,X1,k1_xboole_0) ),
    inference(superposition,[],[f66,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f125,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f43,f76])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f139,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_enumset1(sK4,sK4,sK4,sK5))
      | ~ r2_hidden(X5,k2_enumset1(sK2,sK2,sK2,sK3))
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(resolution,[],[f44,f131])).

fof(f131,plain,(
    sP0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f66,f78])).

fof(f78,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f32,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f200,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X2,X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f50,f70])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n002.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 20:50:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.51  % (10464)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.52  % (10464)Refutation found. Thanks to Tanya!
% 1.13/0.52  % SZS status Theorem for theBenchmark
% 1.13/0.52  % (10480)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.13/0.52  % (10462)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.13/0.52  % (10463)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.13/0.53  % (10472)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.13/0.53  % (10468)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.13/0.53  % (10467)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.13/0.53  % SZS output start Proof for theBenchmark
% 1.13/0.53  fof(f266,plain,(
% 1.13/0.53    $false),
% 1.13/0.53    inference(subsumption_resolution,[],[f265,f34])).
% 1.13/0.53  fof(f34,plain,(
% 1.13/0.53    sK2 != sK5),
% 1.13/0.53    inference(cnf_transformation,[],[f16])).
% 1.13/0.53  fof(f16,plain,(
% 1.13/0.53    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 1.13/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f9,f15])).
% 1.13/0.53  fof(f15,plain,(
% 1.13/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 1.13/0.53    introduced(choice_axiom,[])).
% 1.13/0.53  fof(f9,plain,(
% 1.13/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.13/0.53    inference(ennf_transformation,[],[f8])).
% 1.13/0.53  fof(f8,negated_conjecture,(
% 1.13/0.53    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.13/0.53    inference(negated_conjecture,[],[f7])).
% 1.13/0.53  fof(f7,conjecture,(
% 1.13/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.13/0.53  fof(f265,plain,(
% 1.13/0.53    sK2 = sK5),
% 1.13/0.53    inference(subsumption_resolution,[],[f264,f33])).
% 1.13/0.53  fof(f33,plain,(
% 1.13/0.53    sK2 != sK4),
% 1.13/0.53    inference(cnf_transformation,[],[f16])).
% 1.13/0.53  fof(f264,plain,(
% 1.13/0.53    sK2 = sK4 | sK2 = sK5),
% 1.13/0.53    inference(duplicate_literal_removal,[],[f255])).
% 1.13/0.53  fof(f255,plain,(
% 1.13/0.53    sK2 = sK4 | sK2 = sK4 | sK2 = sK5),
% 1.13/0.53    inference(resolution,[],[f200,f141])).
% 1.13/0.53  fof(f141,plain,(
% 1.13/0.53    r2_hidden(sK2,k2_enumset1(sK4,sK4,sK4,sK5))),
% 1.13/0.53    inference(resolution,[],[f140,f118])).
% 1.13/0.53  fof(f118,plain,(
% 1.13/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.13/0.53    inference(resolution,[],[f70,f69])).
% 1.13/0.53  fof(f69,plain,(
% 1.13/0.53    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.13/0.53    inference(equality_resolution,[],[f51])).
% 1.13/0.53  fof(f51,plain,(
% 1.13/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f30])).
% 1.13/0.53  fof(f30,plain,(
% 1.13/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.13/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 1.13/0.53  fof(f29,plain,(
% 1.13/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.13/0.53    introduced(choice_axiom,[])).
% 1.13/0.53  fof(f28,plain,(
% 1.13/0.53    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.13/0.53    inference(rectify,[],[f27])).
% 1.13/0.53  fof(f27,plain,(
% 1.13/0.53    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.13/0.53    inference(flattening,[],[f26])).
% 1.13/0.53  fof(f26,plain,(
% 1.13/0.53    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.13/0.53    inference(nnf_transformation,[],[f13])).
% 1.13/0.53  fof(f13,plain,(
% 1.13/0.53    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.13/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.13/0.53  fof(f70,plain,(
% 1.13/0.53    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.13/0.53    inference(equality_resolution,[],[f63])).
% 1.13/0.53  fof(f63,plain,(
% 1.13/0.53    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.13/0.53    inference(definition_unfolding,[],[f58,f41])).
% 1.13/0.53  fof(f41,plain,(
% 1.13/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f6])).
% 1.13/0.53  fof(f6,axiom,(
% 1.13/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.13/0.53  fof(f58,plain,(
% 1.13/0.53    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.13/0.53    inference(cnf_transformation,[],[f31])).
% 1.13/0.53  fof(f31,plain,(
% 1.13/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.13/0.53    inference(nnf_transformation,[],[f14])).
% 1.13/0.53  fof(f14,plain,(
% 1.13/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 1.13/0.53    inference(definition_folding,[],[f10,f13])).
% 1.13/0.53  fof(f10,plain,(
% 1.13/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.13/0.53    inference(ennf_transformation,[],[f4])).
% 1.13/0.53  fof(f4,axiom,(
% 1.13/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.13/0.53  fof(f140,plain,(
% 1.13/0.53    ( ! [X5] : (~r2_hidden(X5,k2_enumset1(sK2,sK2,sK2,sK3)) | r2_hidden(X5,k2_enumset1(sK4,sK4,sK4,sK5))) )),
% 1.13/0.53    inference(subsumption_resolution,[],[f139,f126])).
% 1.13/0.53  fof(f126,plain,(
% 1.13/0.53    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 1.13/0.53    inference(subsumption_resolution,[],[f125,f122])).
% 1.13/0.53  fof(f122,plain,(
% 1.13/0.53    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,X4)) )),
% 1.13/0.53    inference(resolution,[],[f42,f76])).
% 1.13/0.53  fof(f76,plain,(
% 1.13/0.53    ( ! [X1] : (sP0(X1,X1,k1_xboole_0)) )),
% 1.13/0.53    inference(superposition,[],[f66,f74])).
% 1.13/0.53  fof(f74,plain,(
% 1.13/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.13/0.53    inference(resolution,[],[f40,f64])).
% 1.13/0.53  fof(f64,plain,(
% 1.13/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.13/0.53    inference(equality_resolution,[],[f37])).
% 1.13/0.53  fof(f37,plain,(
% 1.13/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.13/0.53    inference(cnf_transformation,[],[f18])).
% 1.13/0.53  fof(f18,plain,(
% 1.13/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.13/0.53    inference(flattening,[],[f17])).
% 1.13/0.53  fof(f17,plain,(
% 1.13/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.13/0.53    inference(nnf_transformation,[],[f2])).
% 1.13/0.53  fof(f2,axiom,(
% 1.13/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.13/0.53  fof(f40,plain,(
% 1.13/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.13/0.53    inference(cnf_transformation,[],[f19])).
% 1.13/0.53  fof(f19,plain,(
% 1.13/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.13/0.53    inference(nnf_transformation,[],[f3])).
% 1.13/0.53  fof(f3,axiom,(
% 1.13/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.13/0.53  fof(f66,plain,(
% 1.13/0.53    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.13/0.53    inference(equality_resolution,[],[f48])).
% 1.13/0.53  fof(f48,plain,(
% 1.13/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.13/0.53    inference(cnf_transformation,[],[f25])).
% 1.13/0.53  fof(f25,plain,(
% 1.13/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.13/0.53    inference(nnf_transformation,[],[f12])).
% 1.13/0.53  fof(f12,plain,(
% 1.13/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.13/0.53    inference(definition_folding,[],[f1,f11])).
% 1.13/0.53  fof(f11,plain,(
% 1.13/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.13/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.13/0.53  fof(f1,axiom,(
% 1.13/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.13/0.53  fof(f42,plain,(
% 1.13/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f24])).
% 1.13/0.53  fof(f24,plain,(
% 1.13/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.13/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 1.13/0.53  fof(f23,plain,(
% 1.13/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.13/0.53    introduced(choice_axiom,[])).
% 1.13/0.53  fof(f22,plain,(
% 1.13/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.13/0.53    inference(rectify,[],[f21])).
% 1.13/0.53  fof(f21,plain,(
% 1.13/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.13/0.53    inference(flattening,[],[f20])).
% 1.13/0.53  fof(f20,plain,(
% 1.13/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.13/0.53    inference(nnf_transformation,[],[f11])).
% 1.13/0.53  fof(f125,plain,(
% 1.13/0.53    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.13/0.53    inference(resolution,[],[f43,f76])).
% 1.13/0.53  fof(f43,plain,(
% 1.13/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f24])).
% 1.13/0.53  fof(f139,plain,(
% 1.13/0.53    ( ! [X5] : (r2_hidden(X5,k2_enumset1(sK4,sK4,sK4,sK5)) | ~r2_hidden(X5,k2_enumset1(sK2,sK2,sK2,sK3)) | r2_hidden(X5,k1_xboole_0)) )),
% 1.13/0.53    inference(resolution,[],[f44,f131])).
% 1.13/0.53  fof(f131,plain,(
% 1.13/0.53    sP0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0)),
% 1.13/0.53    inference(superposition,[],[f66,f78])).
% 1.13/0.53  fof(f78,plain,(
% 1.13/0.53    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5))),
% 1.13/0.53    inference(resolution,[],[f61,f40])).
% 1.13/0.53  fof(f61,plain,(
% 1.13/0.53    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5))),
% 1.13/0.53    inference(definition_unfolding,[],[f32,f60,f60])).
% 1.13/0.53  fof(f60,plain,(
% 1.13/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.13/0.53    inference(definition_unfolding,[],[f35,f41])).
% 1.13/0.53  fof(f35,plain,(
% 1.13/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f5])).
% 1.13/0.53  fof(f5,axiom,(
% 1.13/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.13/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.13/0.53  fof(f32,plain,(
% 1.13/0.53    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 1.13/0.53    inference(cnf_transformation,[],[f16])).
% 1.13/0.53  fof(f44,plain,(
% 1.13/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.13/0.53    inference(cnf_transformation,[],[f24])).
% 1.13/0.53  fof(f200,plain,(
% 1.13/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k2_enumset1(X2,X2,X0,X3)) | X1 = X2 | X0 = X1 | X1 = X3) )),
% 1.13/0.53    inference(resolution,[],[f50,f70])).
% 1.13/0.53  fof(f50,plain,(
% 1.13/0.53    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.13/0.53    inference(cnf_transformation,[],[f30])).
% 1.13/0.53  % SZS output end Proof for theBenchmark
% 1.13/0.53  % (10464)------------------------------
% 1.13/0.53  % (10464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (10464)Termination reason: Refutation
% 1.13/0.53  
% 1.13/0.53  % (10464)Memory used [KB]: 10874
% 1.13/0.53  % (10464)Time elapsed: 0.098 s
% 1.13/0.53  % (10464)------------------------------
% 1.13/0.53  % (10464)------------------------------
% 1.13/0.53  % (10460)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.13/0.54  % (10457)Success in time 0.163 s
%------------------------------------------------------------------------------
