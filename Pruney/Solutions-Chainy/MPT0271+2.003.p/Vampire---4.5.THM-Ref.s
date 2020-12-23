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
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 715 expanded)
%              Number of leaves         :   30 ( 237 expanded)
%              Depth                    :   25
%              Number of atoms          :  367 (1046 expanded)
%              Number of equality atoms :  127 ( 732 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4480,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f147,f1229,f4479])).

fof(f4479,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f4478])).

fof(f4478,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f4472,f145])).

fof(f145,plain,
    ( ~ r2_hidden(sK5,sK6)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_2
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f4472,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f4466,f136])).

fof(f136,plain,(
    ! [X2,X3,X1] : sP3(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f4466,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK5,sK5,sK5)
        | r2_hidden(X0,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f479,f1455])).

fof(f1455,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
        | r2_hidden(X0,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f1448,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1448,plain,
    ( ! [X0] :
        ( ~ sP0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),X0,sK6)
        | r2_hidden(X0,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f1374,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1374,plain,
    ( sP1(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f1366,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f105,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f96,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f107,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f108,f109])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f30,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1366,plain,
    ( ! [X5] :
        ( ~ sP4(sK5,sK5,sK5,X5)
        | sP1(sK6,X5,sK6) )
    | ~ spl9_1 ),
    inference(superposition,[],[f133,f1311])).

fof(f1311,plain,
    ( ! [X12] :
        ( sK6 = k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12))
        | ~ sP4(sK5,sK5,sK5,X12) )
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f1310,f818])).

fof(f818,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f817,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f817,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f123,f121])).

fof(f121,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f118])).

fof(f118,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f114])).

fof(f114,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f113])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f123,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f68,f116])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f75,f115])).

fof(f115,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f114])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f68,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1310,plain,
    ( ! [X12] :
        ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12)) = k5_xboole_0(k1_xboole_0,sK6)
        | ~ sP4(sK5,sK5,sK5,X12) )
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f1294,f70])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1294,plain,
    ( ! [X12] :
        ( k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12)) = k5_xboole_0(sK6,k1_xboole_0)
        | ~ sP4(sK5,sK5,sK5,X12) )
    | ~ spl9_1 ),
    inference(superposition,[],[f819,f1264])).

fof(f1264,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)))
        | ~ sP4(sK5,sK5,sK5,X0) )
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f1241,f819])).

fof(f1241,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)))))
        | ~ sP4(sK5,sK5,sK5,X0) )
    | ~ spl9_1 ),
    inference(superposition,[],[f1231,f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f106,f113])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1231,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f1230,f124])).

fof(f124,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f69,f114,f114])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1230,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f140,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f140,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_1
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f819,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f198,f818])).

fof(f198,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f80,f64])).

fof(f133,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f88,f115])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f32,f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f479,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f137,f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK8(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP3(sK8(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).

fof(f56,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK8(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP3(sK8(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP3(X4,X2,X1,X0) )
            & ( sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1229,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f1228])).

fof(f1228,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f1226,f144])).

fof(f144,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1226,plain,
    ( ~ r2_hidden(sK5,sK6)
    | spl9_1 ),
    inference(resolution,[],[f1225,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f118])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1225,plain,
    ( ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)
    | spl9_1 ),
    inference(resolution,[],[f1224,f137])).

fof(f1224,plain,
    ( ! [X2] :
        ( ~ sP4(sK5,sK5,sK5,X2)
        | ~ r1_tarski(X2,sK6) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f1223,f64])).

fof(f1223,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k5_xboole_0(sK6,sK6)
        | ~ sP4(sK5,sK5,sK5,X2)
        | ~ r1_tarski(X2,sK6) )
    | spl9_1 ),
    inference(superposition,[],[f1202,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f115])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1202,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k5_xboole_0(sK6,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,sK6)))
        | ~ sP4(sK5,sK5,sK5,X2) )
    | spl9_1 ),
    inference(superposition,[],[f1182,f124])).

fof(f1182,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)))
        | ~ sP4(sK5,sK5,sK5,X0) )
    | spl9_1 ),
    inference(forward_demodulation,[],[f1177,f819])).

fof(f1177,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)))))
        | ~ sP4(sK5,sK5,sK5,X0) )
    | spl9_1 ),
    inference(superposition,[],[f1167,f131])).

fof(f1167,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | spl9_1 ),
    inference(forward_demodulation,[],[f1166,f124])).

fof(f1166,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))))
    | spl9_1 ),
    inference(forward_demodulation,[],[f141,f80])).

fof(f141,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f147,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f120,f143,f139])).

fof(f120,plain,
    ( r2_hidden(sK5,sK6)
    | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))) ),
    inference(definition_unfolding,[],[f62,f117,f118])).

fof(f117,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f73,f116])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,
    ( r2_hidden(sK5,sK6)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r2_hidden(sK5,sK6)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) )
    & ( r2_hidden(sK5,sK6)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK5,sK6)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) )
      & ( r2_hidden(sK5,sK6)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f146,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f119,f143,f139])).

fof(f119,plain,
    ( ~ r2_hidden(sK5,sK6)
    | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))) ),
    inference(definition_unfolding,[],[f63,f117,f118])).

fof(f63,plain,
    ( ~ r2_hidden(sK5,sK6)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (28247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (28263)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (28237)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (28234)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (28255)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (28252)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (28244)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (28249)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (28235)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (28258)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (28260)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (28246)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28245)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (28239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (28238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (28250)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (28259)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (28241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (28248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (28236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (28251)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (28257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (28253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (28251)Refutation not found, incomplete strategy% (28251)------------------------------
% 0.22/0.54  % (28251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28251)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28251)Memory used [KB]: 10618
% 0.22/0.54  % (28251)Time elapsed: 0.128 s
% 0.22/0.54  % (28251)------------------------------
% 0.22/0.54  % (28251)------------------------------
% 0.22/0.54  % (28240)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (28243)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (28242)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (28262)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (28254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (28256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (28261)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.06/0.63  % (28242)Refutation not found, incomplete strategy% (28242)------------------------------
% 2.06/0.63  % (28242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.65  % (28242)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.65  
% 2.06/0.65  % (28242)Memory used [KB]: 11769
% 2.06/0.65  % (28242)Time elapsed: 0.200 s
% 2.06/0.65  % (28242)------------------------------
% 2.06/0.65  % (28242)------------------------------
% 2.31/0.68  % (28264)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.11/0.82  % (28265)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.60/0.86  % (28239)Time limit reached!
% 3.60/0.86  % (28239)------------------------------
% 3.60/0.86  % (28239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.86  % (28239)Termination reason: Time limit
% 3.60/0.86  
% 3.60/0.86  % (28239)Memory used [KB]: 10746
% 3.60/0.86  % (28239)Time elapsed: 0.431 s
% 3.60/0.86  % (28239)------------------------------
% 3.60/0.86  % (28239)------------------------------
% 3.77/0.90  % (28261)Refutation found. Thanks to Tanya!
% 3.77/0.90  % SZS status Theorem for theBenchmark
% 3.77/0.90  % SZS output start Proof for theBenchmark
% 3.77/0.90  fof(f4480,plain,(
% 3.77/0.90    $false),
% 3.77/0.90    inference(avatar_sat_refutation,[],[f146,f147,f1229,f4479])).
% 3.77/0.90  fof(f4479,plain,(
% 3.77/0.90    ~spl9_1 | spl9_2),
% 3.77/0.90    inference(avatar_contradiction_clause,[],[f4478])).
% 3.77/0.90  fof(f4478,plain,(
% 3.77/0.90    $false | (~spl9_1 | spl9_2)),
% 3.77/0.90    inference(subsumption_resolution,[],[f4472,f145])).
% 3.77/0.90  fof(f145,plain,(
% 3.77/0.90    ~r2_hidden(sK5,sK6) | spl9_2),
% 3.77/0.90    inference(avatar_component_clause,[],[f143])).
% 3.77/0.90  fof(f143,plain,(
% 3.77/0.90    spl9_2 <=> r2_hidden(sK5,sK6)),
% 3.77/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.77/0.90  fof(f4472,plain,(
% 3.77/0.90    r2_hidden(sK5,sK6) | ~spl9_1),
% 3.77/0.90    inference(resolution,[],[f4466,f136])).
% 3.77/0.90  fof(f136,plain,(
% 3.77/0.90    ( ! [X2,X3,X1] : (sP3(X3,X1,X2,X3)) )),
% 3.77/0.90    inference(equality_resolution,[],[f102])).
% 3.77/0.90  fof(f102,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X3) )),
% 3.77/0.90    inference(cnf_transformation,[],[f60])).
% 3.77/0.90  fof(f60,plain,(
% 3.77/0.90    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 3.77/0.90    inference(rectify,[],[f59])).
% 3.77/0.90  fof(f59,plain,(
% 3.77/0.90    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 3.77/0.90    inference(flattening,[],[f58])).
% 3.77/0.90  fof(f58,plain,(
% 3.77/0.90    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 3.77/0.90    inference(nnf_transformation,[],[f36])).
% 3.77/0.90  fof(f36,plain,(
% 3.77/0.90    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 3.77/0.90    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.77/0.90  fof(f4466,plain,(
% 3.77/0.90    ( ! [X0] : (~sP3(X0,sK5,sK5,sK5) | r2_hidden(X0,sK6)) ) | ~spl9_1),
% 3.77/0.90    inference(resolution,[],[f479,f1455])).
% 3.77/0.90  fof(f1455,plain,(
% 3.77/0.90    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) | r2_hidden(X0,sK6)) ) | ~spl9_1),
% 3.77/0.90    inference(resolution,[],[f1448,f87])).
% 3.77/0.90  fof(f87,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f49])).
% 3.77/0.90  fof(f49,plain,(
% 3.77/0.90    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 3.77/0.90    inference(rectify,[],[f48])).
% 3.77/0.90  fof(f48,plain,(
% 3.77/0.90    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 3.77/0.90    inference(flattening,[],[f47])).
% 3.77/0.90  fof(f47,plain,(
% 3.77/0.90    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 3.77/0.90    inference(nnf_transformation,[],[f31])).
% 3.77/0.90  fof(f31,plain,(
% 3.77/0.90    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 3.77/0.90    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.77/0.90  fof(f1448,plain,(
% 3.77/0.90    ( ! [X0] : (~sP0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),X0,sK6) | r2_hidden(X0,sK6)) ) | ~spl9_1),
% 3.77/0.90    inference(resolution,[],[f1374,f82])).
% 3.77/0.90  fof(f82,plain,(
% 3.77/0.90    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f46])).
% 3.77/0.90  fof(f46,plain,(
% 3.77/0.90    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.77/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 3.77/0.90  fof(f45,plain,(
% 3.77/0.90    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 3.77/0.90    introduced(choice_axiom,[])).
% 3.77/0.90  fof(f44,plain,(
% 3.77/0.90    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.77/0.90    inference(rectify,[],[f43])).
% 3.77/0.90  fof(f43,plain,(
% 3.77/0.90    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 3.77/0.90    inference(nnf_transformation,[],[f32])).
% 3.77/0.90  fof(f32,plain,(
% 3.77/0.90    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 3.77/0.90    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.77/0.90  fof(f1374,plain,(
% 3.77/0.90    sP1(sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6) | ~spl9_1),
% 3.77/0.90    inference(resolution,[],[f1366,f137])).
% 3.77/0.90  fof(f137,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.77/0.90    inference(equality_resolution,[],[f132])).
% 3.77/0.90  fof(f132,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.77/0.90    inference(definition_unfolding,[],[f105,f113])).
% 3.77/0.90  fof(f113,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f79,f112])).
% 3.77/0.90  fof(f112,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f96,f111])).
% 3.77/0.90  fof(f111,plain,(
% 3.77/0.90    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f107,f110])).
% 3.77/0.90  fof(f110,plain,(
% 3.77/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f108,f109])).
% 3.77/0.90  fof(f109,plain,(
% 3.77/0.90    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f20])).
% 3.77/0.90  fof(f20,axiom,(
% 3.77/0.90    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.77/0.90  fof(f108,plain,(
% 3.77/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f19])).
% 3.77/0.90  fof(f19,axiom,(
% 3.77/0.90    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.77/0.90  fof(f107,plain,(
% 3.77/0.90    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f18])).
% 3.77/0.90  fof(f18,axiom,(
% 3.77/0.90    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.77/0.90  fof(f96,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f17])).
% 3.77/0.90  fof(f17,axiom,(
% 3.77/0.90    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.77/0.90  fof(f79,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f16])).
% 3.77/0.90  fof(f16,axiom,(
% 3.77/0.90    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.77/0.90  fof(f105,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.77/0.90    inference(cnf_transformation,[],[f61])).
% 3.77/0.90  fof(f61,plain,(
% 3.77/0.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 3.77/0.90    inference(nnf_transformation,[],[f38])).
% 3.77/0.90  fof(f38,plain,(
% 3.77/0.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 3.77/0.90    inference(definition_folding,[],[f30,f37,f36])).
% 3.77/0.90  fof(f37,plain,(
% 3.77/0.90    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 3.77/0.90    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.77/0.90  fof(f30,plain,(
% 3.77/0.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.77/0.90    inference(ennf_transformation,[],[f13])).
% 3.77/0.90  fof(f13,axiom,(
% 3.77/0.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 3.77/0.90  fof(f1366,plain,(
% 3.77/0.90    ( ! [X5] : (~sP4(sK5,sK5,sK5,X5) | sP1(sK6,X5,sK6)) ) | ~spl9_1),
% 3.77/0.90    inference(superposition,[],[f133,f1311])).
% 3.77/0.90  fof(f1311,plain,(
% 3.77/0.90    ( ! [X12] : (sK6 = k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12)) | ~sP4(sK5,sK5,sK5,X12)) ) | ~spl9_1),
% 3.77/0.90    inference(forward_demodulation,[],[f1310,f818])).
% 3.77/0.90  fof(f818,plain,(
% 3.77/0.90    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.77/0.90    inference(forward_demodulation,[],[f817,f64])).
% 3.77/0.90  fof(f64,plain,(
% 3.77/0.90    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f10])).
% 3.77/0.90  fof(f10,axiom,(
% 3.77/0.90    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.77/0.90  fof(f817,plain,(
% 3.77/0.90    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 3.77/0.90    inference(forward_demodulation,[],[f123,f121])).
% 3.77/0.90  fof(f121,plain,(
% 3.77/0.90    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.77/0.90    inference(definition_unfolding,[],[f65,f118])).
% 3.77/0.90  fof(f118,plain,(
% 3.77/0.90    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f67,f114])).
% 3.77/0.90  fof(f114,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f71,f113])).
% 3.77/0.90  fof(f71,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f15])).
% 3.77/0.90  fof(f15,axiom,(
% 3.77/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.77/0.90  fof(f67,plain,(
% 3.77/0.90    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f14])).
% 3.77/0.90  fof(f14,axiom,(
% 3.77/0.90    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.77/0.90  fof(f65,plain,(
% 3.77/0.90    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.77/0.90    inference(cnf_transformation,[],[f23])).
% 3.77/0.90  fof(f23,axiom,(
% 3.77/0.90    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 3.77/0.90  fof(f123,plain,(
% 3.77/0.90    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.77/0.90    inference(definition_unfolding,[],[f68,f116])).
% 3.77/0.90  fof(f116,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.77/0.90    inference(definition_unfolding,[],[f75,f115])).
% 3.77/0.90  fof(f115,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.77/0.90    inference(definition_unfolding,[],[f72,f114])).
% 3.77/0.90  fof(f72,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.77/0.90    inference(cnf_transformation,[],[f22])).
% 3.77/0.90  fof(f22,axiom,(
% 3.77/0.90    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.77/0.90  fof(f75,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.77/0.90    inference(cnf_transformation,[],[f11])).
% 3.77/0.90  fof(f11,axiom,(
% 3.77/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.77/0.90  fof(f68,plain,(
% 3.77/0.90    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.77/0.90    inference(cnf_transformation,[],[f26])).
% 3.77/0.90  fof(f26,plain,(
% 3.77/0.90    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.77/0.90    inference(rectify,[],[f3])).
% 3.77/0.90  fof(f3,axiom,(
% 3.77/0.90    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.77/0.90  fof(f1310,plain,(
% 3.77/0.90    ( ! [X12] : (k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12)) = k5_xboole_0(k1_xboole_0,sK6) | ~sP4(sK5,sK5,sK5,X12)) ) | ~spl9_1),
% 3.77/0.90    inference(forward_demodulation,[],[f1294,f70])).
% 3.77/0.90  fof(f70,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f1])).
% 3.77/0.90  fof(f1,axiom,(
% 3.77/0.90    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.77/0.90  fof(f1294,plain,(
% 3.77/0.90    ( ! [X12] : (k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X12)) = k5_xboole_0(sK6,k1_xboole_0) | ~sP4(sK5,sK5,sK5,X12)) ) | ~spl9_1),
% 3.77/0.90    inference(superposition,[],[f819,f1264])).
% 3.77/0.90  fof(f1264,plain,(
% 3.77/0.90    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))) | ~sP4(sK5,sK5,sK5,X0)) ) | ~spl9_1),
% 3.77/0.90    inference(forward_demodulation,[],[f1241,f819])).
% 3.77/0.90  fof(f1241,plain,(
% 3.77/0.90    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))))) | ~sP4(sK5,sK5,sK5,X0)) ) | ~spl9_1),
% 3.77/0.90    inference(superposition,[],[f1231,f131])).
% 3.77/0.90  fof(f131,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f106,f113])).
% 3.77/0.90  fof(f106,plain,(
% 3.77/0.90    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f61])).
% 3.77/0.90  fof(f1231,plain,(
% 3.77/0.90    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) | ~spl9_1),
% 3.77/0.90    inference(forward_demodulation,[],[f1230,f124])).
% 3.77/0.90  fof(f124,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.77/0.90    inference(definition_unfolding,[],[f69,f114,f114])).
% 3.77/0.90  fof(f69,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.77/0.90    inference(cnf_transformation,[],[f12])).
% 3.77/0.90  fof(f12,axiom,(
% 3.77/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.77/0.90  fof(f1230,plain,(
% 3.77/0.90    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))) | ~spl9_1),
% 3.77/0.90    inference(forward_demodulation,[],[f140,f80])).
% 3.77/0.90  fof(f80,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.77/0.90    inference(cnf_transformation,[],[f9])).
% 3.77/0.90  fof(f9,axiom,(
% 3.77/0.90    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.77/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.77/0.90  fof(f140,plain,(
% 3.77/0.90    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))) | ~spl9_1),
% 3.77/0.90    inference(avatar_component_clause,[],[f139])).
% 3.77/0.90  fof(f139,plain,(
% 3.77/0.90    spl9_1 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))),
% 3.77/0.90    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.77/0.90  fof(f819,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.77/0.90    inference(backward_demodulation,[],[f198,f818])).
% 3.77/0.90  fof(f198,plain,(
% 3.77/0.90    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 3.77/0.90    inference(superposition,[],[f80,f64])).
% 3.77/0.90  fof(f133,plain,(
% 3.77/0.90    ( ! [X0,X1] : (sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.77/0.90    inference(equality_resolution,[],[f130])).
% 3.77/0.90  fof(f130,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.77/0.90    inference(definition_unfolding,[],[f88,f115])).
% 3.77/0.90  fof(f88,plain,(
% 3.77/0.90    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.77/0.90    inference(cnf_transformation,[],[f50])).
% 3.77/0.92  fof(f50,plain,(
% 3.77/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 3.77/0.92    inference(nnf_transformation,[],[f33])).
% 3.77/0.92  fof(f33,plain,(
% 3.77/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 3.77/0.92    inference(definition_folding,[],[f2,f32,f31])).
% 3.77/0.92  fof(f2,axiom,(
% 3.77/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.77/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.77/0.92  fof(f479,plain,(
% 3.77/0.92    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP3(X0,X1,X2,X3)) )),
% 3.77/0.92    inference(resolution,[],[f137,f98])).
% 3.77/0.92  fof(f98,plain,(
% 3.77/0.92    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 3.77/0.92    inference(cnf_transformation,[],[f57])).
% 3.77/0.92  fof(f57,plain,(
% 3.77/0.92    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP3(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.77/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).
% 3.77/0.92  fof(f56,plain,(
% 3.77/0.92    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP3(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 3.77/0.92    introduced(choice_axiom,[])).
% 3.77/0.92  fof(f55,plain,(
% 3.77/0.92    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.77/0.92    inference(rectify,[],[f54])).
% 3.77/0.92  fof(f54,plain,(
% 3.77/0.92    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.77/0.92    inference(nnf_transformation,[],[f37])).
% 3.77/0.92  fof(f1229,plain,(
% 3.77/0.92    spl9_1 | ~spl9_2),
% 3.77/0.92    inference(avatar_contradiction_clause,[],[f1228])).
% 3.77/0.92  fof(f1228,plain,(
% 3.77/0.92    $false | (spl9_1 | ~spl9_2)),
% 3.77/0.92    inference(subsumption_resolution,[],[f1226,f144])).
% 3.77/0.92  fof(f144,plain,(
% 3.77/0.92    r2_hidden(sK5,sK6) | ~spl9_2),
% 3.77/0.92    inference(avatar_component_clause,[],[f143])).
% 3.77/0.92  fof(f1226,plain,(
% 3.77/0.92    ~r2_hidden(sK5,sK6) | spl9_1),
% 3.77/0.92    inference(resolution,[],[f1225,f127])).
% 3.77/0.92  fof(f127,plain,(
% 3.77/0.92    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.77/0.92    inference(definition_unfolding,[],[f78,f118])).
% 3.77/0.92  fof(f78,plain,(
% 3.77/0.92    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.77/0.92    inference(cnf_transformation,[],[f42])).
% 3.77/0.92  fof(f42,plain,(
% 3.77/0.92    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.77/0.92    inference(nnf_transformation,[],[f21])).
% 3.77/0.92  fof(f21,axiom,(
% 3.77/0.92    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.77/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 3.77/0.92  fof(f1225,plain,(
% 3.77/0.92    ~r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6) | spl9_1),
% 3.77/0.92    inference(resolution,[],[f1224,f137])).
% 3.77/0.92  fof(f1224,plain,(
% 3.77/0.92    ( ! [X2] : (~sP4(sK5,sK5,sK5,X2) | ~r1_tarski(X2,sK6)) ) | spl9_1),
% 3.77/0.92    inference(subsumption_resolution,[],[f1223,f64])).
% 3.77/0.92  fof(f1223,plain,(
% 3.77/0.92    ( ! [X2] : (k1_xboole_0 != k5_xboole_0(sK6,sK6) | ~sP4(sK5,sK5,sK5,X2) | ~r1_tarski(X2,sK6)) ) | spl9_1),
% 3.77/0.92    inference(superposition,[],[f1202,f126])).
% 3.77/0.92  fof(f126,plain,(
% 3.77/0.92    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.77/0.92    inference(definition_unfolding,[],[f76,f115])).
% 3.77/0.92  fof(f76,plain,(
% 3.77/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.77/0.92    inference(cnf_transformation,[],[f28])).
% 3.77/0.92  fof(f28,plain,(
% 3.77/0.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.77/0.92    inference(ennf_transformation,[],[f6])).
% 3.77/0.92  fof(f6,axiom,(
% 3.77/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.77/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.77/0.92  fof(f1202,plain,(
% 3.77/0.92    ( ! [X2] : (k1_xboole_0 != k5_xboole_0(sK6,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,sK6))) | ~sP4(sK5,sK5,sK5,X2)) ) | spl9_1),
% 3.77/0.92    inference(superposition,[],[f1182,f124])).
% 3.77/0.92  fof(f1182,plain,(
% 3.77/0.92    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))) | ~sP4(sK5,sK5,sK5,X0)) ) | spl9_1),
% 3.77/0.92    inference(forward_demodulation,[],[f1177,f819])).
% 3.77/0.92  fof(f1177,plain,(
% 3.77/0.92    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))))) | ~sP4(sK5,sK5,sK5,X0)) ) | spl9_1),
% 3.77/0.92    inference(superposition,[],[f1167,f131])).
% 3.77/0.92  fof(f1167,plain,(
% 3.77/0.92    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) | spl9_1),
% 3.77/0.92    inference(forward_demodulation,[],[f1166,f124])).
% 3.77/0.92  fof(f1166,plain,(
% 3.77/0.92    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(sK6,k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))) | spl9_1),
% 3.77/0.92    inference(forward_demodulation,[],[f141,f80])).
% 3.77/0.92  fof(f141,plain,(
% 3.77/0.92    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6)))) | spl9_1),
% 3.77/0.92    inference(avatar_component_clause,[],[f139])).
% 3.77/0.92  fof(f147,plain,(
% 3.77/0.92    spl9_1 | spl9_2),
% 3.77/0.92    inference(avatar_split_clause,[],[f120,f143,f139])).
% 3.77/0.92  fof(f120,plain,(
% 3.77/0.92    r2_hidden(sK5,sK6) | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))),
% 3.77/0.92    inference(definition_unfolding,[],[f62,f117,f118])).
% 3.77/0.92  fof(f117,plain,(
% 3.77/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.77/0.92    inference(definition_unfolding,[],[f73,f116])).
% 3.77/0.92  fof(f73,plain,(
% 3.77/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.77/0.92    inference(cnf_transformation,[],[f5])).
% 3.77/0.92  fof(f5,axiom,(
% 3.77/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.77/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.77/0.92  fof(f62,plain,(
% 3.77/0.92    r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6)),
% 3.77/0.92    inference(cnf_transformation,[],[f41])).
% 3.77/0.92  fof(f41,plain,(
% 3.77/0.92    (~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)) & (r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6))),
% 3.77/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).
% 3.77/0.92  fof(f40,plain,(
% 3.77/0.92    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)) & (r2_hidden(sK5,sK6) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK5),sK6)))),
% 3.77/0.92    introduced(choice_axiom,[])).
% 3.77/0.92  fof(f39,plain,(
% 3.77/0.92    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 3.77/0.92    inference(nnf_transformation,[],[f27])).
% 3.77/0.92  fof(f27,plain,(
% 3.77/0.92    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 3.77/0.92    inference(ennf_transformation,[],[f25])).
% 3.77/0.92  fof(f25,negated_conjecture,(
% 3.77/0.92    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.77/0.92    inference(negated_conjecture,[],[f24])).
% 3.77/0.92  fof(f24,conjecture,(
% 3.77/0.92    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.77/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 3.77/0.92  fof(f146,plain,(
% 3.77/0.92    ~spl9_1 | ~spl9_2),
% 3.77/0.92    inference(avatar_split_clause,[],[f119,f143,f139])).
% 3.77/0.92  fof(f119,plain,(
% 3.77/0.92    ~r2_hidden(sK5,sK6) | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6),k3_tarski(k6_enumset1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK6))))),
% 3.77/0.92    inference(definition_unfolding,[],[f63,f117,f118])).
% 3.77/0.92  fof(f63,plain,(
% 3.77/0.92    ~r2_hidden(sK5,sK6) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK5),sK6)),
% 3.77/0.92    inference(cnf_transformation,[],[f41])).
% 3.77/0.92  % SZS output end Proof for theBenchmark
% 3.77/0.92  % (28261)------------------------------
% 3.77/0.92  % (28261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.92  % (28261)Termination reason: Refutation
% 3.77/0.92  
% 3.77/0.92  % (28261)Memory used [KB]: 8699
% 3.77/0.92  % (28261)Time elapsed: 0.442 s
% 3.77/0.92  % (28261)------------------------------
% 3.77/0.92  % (28261)------------------------------
% 3.77/0.92  % (28244)Time limit reached!
% 3.77/0.92  % (28244)------------------------------
% 3.77/0.92  % (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.92  % (28244)Termination reason: Time limit
% 3.77/0.92  % (28244)Termination phase: Saturation
% 3.77/0.92  
% 3.77/0.92  % (28244)Memory used [KB]: 17654
% 3.77/0.92  % (28244)Time elapsed: 0.512 s
% 3.77/0.92  % (28244)------------------------------
% 3.77/0.92  % (28244)------------------------------
% 3.77/0.92  % (28233)Success in time 0.562 s
%------------------------------------------------------------------------------
