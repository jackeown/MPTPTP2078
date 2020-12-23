%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 211 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  398 ( 594 expanded)
%              Number of equality atoms :  211 ( 299 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f161,f164,f167,f176,f178,f190,f363])).

fof(f363,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f216,f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) )
      & ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f216,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : ~ sP0(sK2,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_7 ),
    inference(resolution,[],[f213,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X0 != X9
              & X1 != X9
              & X2 != X9
              & X3 != X9
              & X4 != X9
              & X5 != X9
              & X6 != X9
              & X7 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X0 = X9
            | X1 = X9
            | X2 = X9
            | X3 = X9
            | X4 = X9
            | X5 = X9
            | X6 = X9
            | X7 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9
                & X7 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | X7 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f213,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_7 ),
    inference(resolution,[],[f175,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f175,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl5_7
  <=> r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f190,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f160,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f160,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_5
  <=> r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f178,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f171,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f176,plain,
    ( ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_2 ),
    inference(avatar_split_clause,[],[f162,f119,f173,f169,f150])).

fof(f150,plain,
    ( spl5_3
  <=> v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f119,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f162,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl5_2 ),
    inference(resolution,[],[f121,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f121,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f167,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f152,f103])).

fof(f103,plain,(
    ! [X0] : v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
    inference(resolution,[],[f35,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f76])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f152,plain,
    ( ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f164,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f156,f35])).

fof(f156,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f161,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f148,f115,f158,f154,f150])).

fof(f115,plain,
    ( spl5_1
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f148,plain,
    ( ~ r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl5_1 ),
    inference(resolution,[],[f117,f39])).

fof(f117,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f113,f119,f115])).

fof(f113,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1)) ),
    inference(resolution,[],[f77,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f77,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK2)))) ),
    inference(definition_unfolding,[],[f37,f76,f76])).

fof(f37,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (27045)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.44  % (27037)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.45  % (27029)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.47  % (27037)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f364,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f122,f161,f164,f167,f176,f178,f190,f363])).
% 0.21/0.47  fof(f363,plain,(
% 0.21/0.47    spl5_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.47  fof(f354,plain,(
% 0.21/0.47    $false | spl5_7),
% 0.21/0.47    inference(resolution,[],[f216,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.47    inference(equality_resolution,[],[f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)) & (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.21/0.47    inference(nnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8))),
% 0.21/0.47    inference(definition_folding,[],[f23,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP0(sK2,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ) | spl5_7),
% 0.21/0.47    inference(resolution,[],[f213,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 0.21/0.47    inference(equality_resolution,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.21/0.47    inference(rectify,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 0.21/0.47    inference(nnf_transformation,[],[f24])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | spl5_7),
% 0.21/0.47    inference(resolution,[],[f175,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl5_7 <=> r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl5_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    $false | spl5_5),
% 0.21/0.47    inference(resolution,[],[f160,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f40,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f41,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f45,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f47,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f48,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f49,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl5_5 <=> r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl5_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    $false | spl5_6),
% 0.21/0.47    inference(resolution,[],[f171,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f27,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f14])).
% 0.21/0.47  fof(f14,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f169])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    spl5_6 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~spl5_3 | ~spl5_6 | ~spl5_7 | spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f162,f119,f173,f169,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    spl5_3 <=> v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl5_2 <=> r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | spl5_2),
% 0.21/0.47    inference(resolution,[],[f121,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2)) | spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl5_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f165])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    $false | spl5_3),
% 0.21/0.47    inference(resolution,[],[f152,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) )),
% 0.21/0.47    inference(resolution,[],[f35,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f43,f76])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f150])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    $false | spl5_4),
% 0.21/0.47    inference(resolution,[],[f156,f35])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl5_4 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f148,f115,f158,f154,f150])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl5_1 <=> r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~r1_tarski(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | spl5_1),
% 0.21/0.47    inference(resolution,[],[f117,f39])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1)) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f113,f119,f115])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k2_relat_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f77,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f46,f76])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),k1_setfam_1(k6_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK2))))),
% 0.21/0.47    inference(definition_unfolding,[],[f37,f76,f76])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27037)------------------------------
% 0.21/0.47  % (27037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27037)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27037)Memory used [KB]: 6652
% 0.21/0.47  % (27037)Time elapsed: 0.060 s
% 0.21/0.47  % (27037)------------------------------
% 0.21/0.47  % (27037)------------------------------
% 0.21/0.48  % (27021)Success in time 0.125 s
%------------------------------------------------------------------------------
