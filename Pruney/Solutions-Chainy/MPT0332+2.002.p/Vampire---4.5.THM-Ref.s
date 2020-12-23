%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:08 EST 2020

% Result     : Theorem 9.66s
% Output     : Refutation 9.66s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 566 expanded)
%              Number of leaves         :   32 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  371 ( 980 expanded)
%              Number of equality atoms :  121 ( 538 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    9 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3854,f3983,f4045,f9579,f9649])).

fof(f9649,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f9648])).

fof(f9648,plain,
    ( $false
    | spl9_13 ),
    inference(subsumption_resolution,[],[f9644,f119])).

fof(f119,plain,(
    ! [X2,X3,X1] : sP2(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f9644,plain,
    ( ~ sP2(sK5,sK5,sK4,sK4)
    | spl9_13 ),
    inference(resolution,[],[f9634,f793])).

fof(f793,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f122,f85])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sP2(sK8(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X4,X2,X1,X0) )
            & ( sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f122,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f92,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f83,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f94,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f95,f96])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f28,f33,f32])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f9634,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | spl9_13 ),
    inference(resolution,[],[f9617,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9617,plain,
    ( ~ sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),sK5,sK6)
    | spl9_13 ),
    inference(resolution,[],[f4044,f499])).

fof(f499,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f118,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f118,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f77,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f100])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f30,f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f4044,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f4042])).

fof(f4042,plain,
    ( spl9_13
  <=> r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f9579,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f9578])).

fof(f9578,plain,
    ( $false
    | spl9_12 ),
    inference(subsumption_resolution,[],[f9575,f120])).

fof(f120,plain,(
    ! [X2,X3,X1] : sP2(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9575,plain,
    ( ~ sP2(sK4,sK5,sK4,sK4)
    | spl9_12 ),
    inference(resolution,[],[f9565,f793])).

fof(f9565,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))
    | spl9_12 ),
    inference(resolution,[],[f9548,f76])).

fof(f9548,plain,
    ( ~ sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),sK4,sK6)
    | spl9_12 ),
    inference(resolution,[],[f4040,f499])).

fof(f4040,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f4038])).

fof(f4038,plain,
    ( spl9_12
  <=> r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f4045,plain,
    ( ~ spl9_12
    | ~ spl9_13
    | spl9_3 ),
    inference(avatar_split_clause,[],[f4032,f3847,f4042,f4038])).

fof(f3847,plain,
    ( spl9_3
  <=> r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f4032,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | spl9_3 ),
    inference(resolution,[],[f3849,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f81,f101])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3849,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f3847])).

fof(f3983,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f3982])).

fof(f3982,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f3981,f55])).

fof(f55,plain,(
    ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5))
    & ~ r2_hidden(sK5,sK6)
    & ~ r2_hidden(sK4,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5))
      & ~ r2_hidden(sK5,sK6)
      & ~ r2_hidden(sK4,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f3981,plain,
    ( r2_hidden(sK4,sK6)
    | spl9_4 ),
    inference(subsumption_resolution,[],[f3980,f56])).

fof(f56,plain,(
    ~ r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f3980,plain,
    ( r2_hidden(sK5,sK6)
    | r2_hidden(sK4,sK6)
    | spl9_4 ),
    inference(trivial_inequality_removal,[],[f3979])).

fof(f3979,plain,
    ( sK6 != sK6
    | r2_hidden(sK5,sK6)
    | r2_hidden(sK4,sK6)
    | spl9_4 ),
    inference(superposition,[],[f3853,f2908])).

fof(f2908,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(forward_demodulation,[],[f2907,f1717])).

fof(f1717,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f125,f1716])).

fof(f1716,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f1715,f58])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1715,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f106,f107])).

fof(f107,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f102])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f59,f103])).

fof(f103,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f102])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f125,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f69,f58])).

fof(f69,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2907,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(forward_demodulation,[],[f115,f69])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f104,f101])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f65,f103])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f3853,plain,
    ( sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f3851])).

fof(f3851,plain,
    ( spl9_4
  <=> sK6 = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f3854,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f3845,f3851,f3847])).

fof(f3845,plain,
    ( sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))
    | ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f3844,f1718])).

fof(f1718,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(backward_demodulation,[],[f138,f1716])).

fof(f138,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f125,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3844,plain,
    ( sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))
    | ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f3843,f62])).

fof(f3843,plain,
    ( sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))
    | ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    inference(forward_demodulation,[],[f3811,f130])).

fof(f130,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f69,f62])).

fof(f3811,plain,
    ( sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))
    | ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) ),
    inference(superposition,[],[f3798,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f102])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3798,plain,(
    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))))) ),
    inference(forward_demodulation,[],[f3797,f108])).

fof(f108,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f61,f101,f101])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f3797,plain,(
    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))) ),
    inference(forward_demodulation,[],[f3796,f62])).

fof(f3796,plain,(
    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))) ),
    inference(forward_demodulation,[],[f3795,f130])).

fof(f3795,plain,(
    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))) ),
    inference(forward_demodulation,[],[f105,f69])).

fof(f105,plain,(
    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) ),
    inference(definition_unfolding,[],[f57,f104,f102,f101,f101])).

fof(f57,plain,(
    sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:20:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (14000)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (13992)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (13992)Refutation not found, incomplete strategy% (13992)------------------------------
% 0.22/0.51  % (13992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13984)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (13992)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13992)Memory used [KB]: 6268
% 0.22/0.52  % (13992)Time elapsed: 0.063 s
% 0.22/0.52  % (13992)------------------------------
% 0.22/0.52  % (13992)------------------------------
% 0.22/0.52  % (13979)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13985)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13981)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (13997)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (13999)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (13980)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (13994)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (13983)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (14004)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (14003)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (13977)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (13991)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13987)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (13996)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (13995)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (14006)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (14001)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (13986)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (14005)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (13978)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (13989)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (13988)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (13994)Refutation not found, incomplete strategy% (13994)------------------------------
% 0.22/0.56  % (13994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13994)Memory used [KB]: 10618
% 0.22/0.56  % (13994)Time elapsed: 0.147 s
% 0.22/0.56  % (13994)------------------------------
% 0.22/0.56  % (13994)------------------------------
% 0.22/0.56  % (14002)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (13993)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (13998)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (13982)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.70/0.60  % (13990)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.25/0.69  % (14010)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.24/0.80  % (14011)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.72/0.85  % (13982)Time limit reached!
% 3.72/0.85  % (13982)------------------------------
% 3.72/0.85  % (13982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.86  % (13982)Termination reason: Time limit
% 3.72/0.86  % (13982)Termination phase: Saturation
% 3.72/0.86  
% 3.72/0.86  % (13982)Memory used [KB]: 10106
% 3.72/0.86  % (13982)Time elapsed: 0.400 s
% 3.72/0.86  % (13982)------------------------------
% 3.72/0.86  % (13982)------------------------------
% 4.35/0.92  % (13987)Time limit reached!
% 4.35/0.92  % (13987)------------------------------
% 4.35/0.92  % (13987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.92  % (13987)Termination reason: Time limit
% 4.35/0.92  
% 4.35/0.92  % (13987)Memory used [KB]: 12665
% 4.35/0.92  % (13987)Time elapsed: 0.517 s
% 4.35/0.92  % (13987)------------------------------
% 4.35/0.92  % (13987)------------------------------
% 4.35/0.92  % (13989)Time limit reached!
% 4.35/0.92  % (13989)------------------------------
% 4.35/0.92  % (13989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.92  % (13989)Termination reason: Time limit
% 4.35/0.92  
% 4.35/0.92  % (13989)Memory used [KB]: 10234
% 4.35/0.92  % (13989)Time elapsed: 0.519 s
% 4.35/0.92  % (13989)------------------------------
% 4.35/0.92  % (13989)------------------------------
% 4.35/0.93  % (13977)Time limit reached!
% 4.35/0.93  % (13977)------------------------------
% 4.35/0.93  % (13977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (13977)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (13977)Memory used [KB]: 2558
% 4.35/0.93  % (13977)Time elapsed: 0.525 s
% 4.35/0.93  % (13977)------------------------------
% 4.35/0.93  % (13977)------------------------------
% 4.35/0.93  % (13978)Time limit reached!
% 4.35/0.93  % (13978)------------------------------
% 4.35/0.93  % (13978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (13978)Termination reason: Time limit
% 4.35/0.93  % (13978)Termination phase: Saturation
% 4.35/0.93  
% 4.35/0.93  % (13978)Memory used [KB]: 9083
% 4.35/0.93  % (13978)Time elapsed: 0.500 s
% 4.35/0.93  % (13978)------------------------------
% 4.35/0.93  % (13978)------------------------------
% 4.61/0.95  % (14043)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.61/1.02  % (14005)Time limit reached!
% 4.61/1.02  % (14005)------------------------------
% 4.61/1.02  % (14005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.03  % (13993)Time limit reached!
% 4.61/1.03  % (13993)------------------------------
% 4.61/1.03  % (13993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.03  % (13993)Termination reason: Time limit
% 4.61/1.03  
% 4.61/1.03  % (13993)Memory used [KB]: 14328
% 4.61/1.03  % (13993)Time elapsed: 0.619 s
% 4.61/1.03  % (13993)------------------------------
% 4.61/1.03  % (13993)------------------------------
% 4.61/1.03  % (14005)Termination reason: Time limit
% 4.61/1.03  
% 4.61/1.03  % (14005)Memory used [KB]: 8955
% 4.61/1.03  % (14005)Time elapsed: 0.622 s
% 4.61/1.03  % (14005)------------------------------
% 4.61/1.03  % (14005)------------------------------
% 5.14/1.04  % (14045)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.14/1.04  % (14048)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.14/1.05  % (14046)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.14/1.06  % (14047)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.45/1.11  % (13984)Time limit reached!
% 5.45/1.11  % (13984)------------------------------
% 5.45/1.11  % (13984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.45/1.11  % (13984)Termination reason: Time limit
% 5.45/1.11  
% 5.45/1.11  % (13984)Memory used [KB]: 12920
% 5.45/1.11  % (13984)Time elapsed: 0.636 s
% 5.45/1.11  % (13984)------------------------------
% 5.45/1.11  % (13984)------------------------------
% 6.22/1.16  % (14050)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.38/1.17  % (14049)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.38/1.21  % (13998)Time limit reached!
% 6.38/1.21  % (13998)------------------------------
% 6.38/1.21  % (13998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.38/1.22  % (13998)Termination reason: Time limit
% 6.38/1.22  
% 6.38/1.22  % (13998)Memory used [KB]: 7164
% 6.38/1.22  % (13998)Time elapsed: 0.812 s
% 6.38/1.22  % (13998)------------------------------
% 6.38/1.22  % (13998)------------------------------
% 6.82/1.24  % (14051)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.50/1.33  % (14100)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.50/1.36  % (14045)Time limit reached!
% 7.50/1.36  % (14045)------------------------------
% 7.50/1.36  % (14045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.37  % (14046)Time limit reached!
% 7.86/1.37  % (14046)------------------------------
% 7.86/1.37  % (14046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.37  % (14046)Termination reason: Time limit
% 7.86/1.37  
% 7.86/1.37  % (14046)Memory used [KB]: 13816
% 7.86/1.37  % (14046)Time elapsed: 0.426 s
% 7.86/1.37  % (14046)------------------------------
% 7.86/1.37  % (14046)------------------------------
% 7.86/1.38  % (14045)Termination reason: Time limit
% 7.86/1.38  
% 7.86/1.38  % (14045)Memory used [KB]: 10490
% 7.86/1.38  % (14045)Time elapsed: 0.424 s
% 7.86/1.38  % (14045)------------------------------
% 7.86/1.38  % (14045)------------------------------
% 7.86/1.43  % (13979)Time limit reached!
% 7.86/1.43  % (13979)------------------------------
% 7.86/1.43  % (13979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.43  % (13979)Termination reason: Time limit
% 7.86/1.43  % (13979)Termination phase: Saturation
% 7.86/1.43  
% 7.86/1.43  % (13979)Memory used [KB]: 16886
% 7.86/1.43  % (13979)Time elapsed: 1.0000 s
% 7.86/1.43  % (13979)------------------------------
% 7.86/1.43  % (13979)------------------------------
% 8.64/1.48  % (14192)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.64/1.50  % (14185)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.17/1.57  % (14207)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.17/1.61  % (13999)Time limit reached!
% 9.17/1.61  % (13999)------------------------------
% 9.17/1.61  % (13999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.17/1.61  % (13999)Termination reason: Time limit
% 9.17/1.61  
% 9.17/1.61  % (13999)Memory used [KB]: 15991
% 9.17/1.61  % (13999)Time elapsed: 1.208 s
% 9.17/1.61  % (13999)------------------------------
% 9.17/1.61  % (13999)------------------------------
% 9.66/1.62  % (14003)Time limit reached!
% 9.66/1.62  % (14003)------------------------------
% 9.66/1.62  % (14003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.66/1.64  % (14003)Termination reason: Time limit
% 9.66/1.64  
% 9.66/1.64  % (14003)Memory used [KB]: 17398
% 9.66/1.64  % (14003)Time elapsed: 1.220 s
% 9.66/1.64  % (14003)------------------------------
% 9.66/1.64  % (14003)------------------------------
% 9.66/1.65  % (14004)Refutation found. Thanks to Tanya!
% 9.66/1.65  % SZS status Theorem for theBenchmark
% 9.66/1.65  % SZS output start Proof for theBenchmark
% 9.66/1.65  fof(f9650,plain,(
% 9.66/1.65    $false),
% 9.66/1.65    inference(avatar_sat_refutation,[],[f3854,f3983,f4045,f9579,f9649])).
% 9.66/1.65  fof(f9649,plain,(
% 9.66/1.65    spl9_13),
% 9.66/1.65    inference(avatar_contradiction_clause,[],[f9648])).
% 9.66/1.65  fof(f9648,plain,(
% 9.66/1.65    $false | spl9_13),
% 9.66/1.65    inference(subsumption_resolution,[],[f9644,f119])).
% 9.66/1.65  fof(f119,plain,(
% 9.66/1.65    ( ! [X2,X3,X1] : (sP2(X1,X1,X2,X3)) )),
% 9.66/1.65    inference(equality_resolution,[],[f91])).
% 9.66/1.65  fof(f91,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X1) )),
% 9.66/1.65    inference(cnf_transformation,[],[f53])).
% 9.66/1.65  fof(f53,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 9.66/1.65    inference(rectify,[],[f52])).
% 9.66/1.65  fof(f52,plain,(
% 9.66/1.65    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 9.66/1.65    inference(flattening,[],[f51])).
% 9.66/1.65  fof(f51,plain,(
% 9.66/1.65    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 9.66/1.65    inference(nnf_transformation,[],[f32])).
% 9.66/1.65  fof(f32,plain,(
% 9.66/1.65    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 9.66/1.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 9.66/1.65  fof(f9644,plain,(
% 9.66/1.65    ~sP2(sK5,sK5,sK4,sK4) | spl9_13),
% 9.66/1.65    inference(resolution,[],[f9634,f793])).
% 9.66/1.65  fof(f793,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP2(X0,X1,X2,X3)) )),
% 9.66/1.65    inference(resolution,[],[f122,f85])).
% 9.66/1.65  fof(f85,plain,(
% 9.66/1.65    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f50])).
% 9.66/1.65  fof(f50,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 9.66/1.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).
% 9.66/1.65  fof(f49,plain,(
% 9.66/1.65    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 9.66/1.65    introduced(choice_axiom,[])).
% 9.66/1.65  fof(f48,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 9.66/1.65    inference(rectify,[],[f47])).
% 9.66/1.65  fof(f47,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 9.66/1.65    inference(nnf_transformation,[],[f33])).
% 9.66/1.65  fof(f33,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 9.66/1.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 9.66/1.65  fof(f122,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 9.66/1.65    inference(equality_resolution,[],[f117])).
% 9.66/1.65  fof(f117,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 9.66/1.65    inference(definition_unfolding,[],[f92,f100])).
% 9.66/1.65  fof(f100,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f68,f99])).
% 9.66/1.65  fof(f99,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f83,f98])).
% 9.66/1.65  fof(f98,plain,(
% 9.66/1.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f94,f97])).
% 9.66/1.65  fof(f97,plain,(
% 9.66/1.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f95,f96])).
% 9.66/1.65  fof(f96,plain,(
% 9.66/1.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f17])).
% 9.66/1.65  fof(f17,axiom,(
% 9.66/1.65    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 9.66/1.65  fof(f95,plain,(
% 9.66/1.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f16])).
% 9.66/1.65  fof(f16,axiom,(
% 9.66/1.65    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 9.66/1.65  fof(f94,plain,(
% 9.66/1.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f15])).
% 9.66/1.65  fof(f15,axiom,(
% 9.66/1.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 9.66/1.65  fof(f83,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f14])).
% 9.66/1.65  fof(f14,axiom,(
% 9.66/1.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 9.66/1.65  fof(f68,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f13])).
% 9.66/1.65  fof(f13,axiom,(
% 9.66/1.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 9.66/1.65  fof(f92,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 9.66/1.65    inference(cnf_transformation,[],[f54])).
% 9.66/1.65  fof(f54,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 9.66/1.65    inference(nnf_transformation,[],[f34])).
% 9.66/1.65  fof(f34,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 9.66/1.65    inference(definition_folding,[],[f28,f33,f32])).
% 9.66/1.65  fof(f28,plain,(
% 9.66/1.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 9.66/1.65    inference(ennf_transformation,[],[f11])).
% 9.66/1.65  fof(f11,axiom,(
% 9.66/1.65    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 9.66/1.65  fof(f9634,plain,(
% 9.66/1.65    ~r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) | spl9_13),
% 9.66/1.65    inference(resolution,[],[f9617,f76])).
% 9.66/1.65  fof(f76,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f43])).
% 9.66/1.65  fof(f43,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 9.66/1.65    inference(rectify,[],[f42])).
% 9.66/1.65  fof(f42,plain,(
% 9.66/1.65    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 9.66/1.65    inference(flattening,[],[f41])).
% 9.66/1.65  fof(f41,plain,(
% 9.66/1.65    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 9.66/1.65    inference(nnf_transformation,[],[f29])).
% 9.66/1.65  fof(f29,plain,(
% 9.66/1.65    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 9.66/1.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 9.66/1.65  fof(f9617,plain,(
% 9.66/1.65    ~sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),sK5,sK6) | spl9_13),
% 9.66/1.65    inference(resolution,[],[f4044,f499])).
% 9.66/1.65  fof(f499,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))) | ~sP0(X0,X1,X2)) )),
% 9.66/1.65    inference(resolution,[],[f118,f71])).
% 9.66/1.65  fof(f71,plain,(
% 9.66/1.65    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f40])).
% 9.66/1.65  fof(f40,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 9.66/1.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 9.66/1.65  fof(f39,plain,(
% 9.66/1.65    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 9.66/1.65    introduced(choice_axiom,[])).
% 9.66/1.65  fof(f38,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 9.66/1.65    inference(rectify,[],[f37])).
% 9.66/1.65  fof(f37,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 9.66/1.65    inference(nnf_transformation,[],[f30])).
% 9.66/1.65  fof(f30,plain,(
% 9.66/1.65    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 9.66/1.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 9.66/1.65  fof(f118,plain,(
% 9.66/1.65    ( ! [X0,X1] : (sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 9.66/1.65    inference(equality_resolution,[],[f111])).
% 9.66/1.65  fof(f111,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 9.66/1.65    inference(definition_unfolding,[],[f77,f102])).
% 9.66/1.65  fof(f102,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 9.66/1.65    inference(definition_unfolding,[],[f63,f101])).
% 9.66/1.65  fof(f101,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f64,f100])).
% 9.66/1.65  fof(f64,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f12])).
% 9.66/1.65  fof(f12,axiom,(
% 9.66/1.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 9.66/1.65  fof(f63,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 9.66/1.65    inference(cnf_transformation,[],[f18])).
% 9.66/1.65  fof(f18,axiom,(
% 9.66/1.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 9.66/1.65  fof(f77,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 9.66/1.65    inference(cnf_transformation,[],[f44])).
% 9.66/1.65  fof(f44,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 9.66/1.65    inference(nnf_transformation,[],[f31])).
% 9.66/1.65  fof(f31,plain,(
% 9.66/1.65    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 9.66/1.65    inference(definition_folding,[],[f2,f30,f29])).
% 9.66/1.65  fof(f2,axiom,(
% 9.66/1.65    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 9.66/1.65  fof(f4044,plain,(
% 9.66/1.65    ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | spl9_13),
% 9.66/1.65    inference(avatar_component_clause,[],[f4042])).
% 9.66/1.65  fof(f4042,plain,(
% 9.66/1.65    spl9_13 <=> r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 9.66/1.65  fof(f9579,plain,(
% 9.66/1.65    spl9_12),
% 9.66/1.65    inference(avatar_contradiction_clause,[],[f9578])).
% 9.66/1.65  fof(f9578,plain,(
% 9.66/1.65    $false | spl9_12),
% 9.66/1.65    inference(subsumption_resolution,[],[f9575,f120])).
% 9.66/1.65  fof(f120,plain,(
% 9.66/1.65    ( ! [X2,X3,X1] : (sP2(X2,X1,X2,X3)) )),
% 9.66/1.65    inference(equality_resolution,[],[f90])).
% 9.66/1.65  fof(f90,plain,(
% 9.66/1.65    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X2) )),
% 9.66/1.65    inference(cnf_transformation,[],[f53])).
% 9.66/1.65  fof(f9575,plain,(
% 9.66/1.65    ~sP2(sK4,sK5,sK4,sK4) | spl9_12),
% 9.66/1.65    inference(resolution,[],[f9565,f793])).
% 9.66/1.65  fof(f9565,plain,(
% 9.66/1.65    ~r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) | spl9_12),
% 9.66/1.65    inference(resolution,[],[f9548,f76])).
% 9.66/1.65  fof(f9548,plain,(
% 9.66/1.65    ~sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),sK4,sK6) | spl9_12),
% 9.66/1.65    inference(resolution,[],[f4040,f499])).
% 9.66/1.65  fof(f4040,plain,(
% 9.66/1.65    ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | spl9_12),
% 9.66/1.65    inference(avatar_component_clause,[],[f4038])).
% 9.66/1.65  fof(f4038,plain,(
% 9.66/1.65    spl9_12 <=> r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 9.66/1.65  fof(f4045,plain,(
% 9.66/1.65    ~spl9_12 | ~spl9_13 | spl9_3),
% 9.66/1.65    inference(avatar_split_clause,[],[f4032,f3847,f4042,f4038])).
% 9.66/1.65  fof(f3847,plain,(
% 9.66/1.65    spl9_3 <=> r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 9.66/1.65  fof(f4032,plain,(
% 9.66/1.65    ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | spl9_3),
% 9.66/1.65    inference(resolution,[],[f3849,f112])).
% 9.66/1.65  fof(f112,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f81,f101])).
% 9.66/1.65  fof(f81,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f46])).
% 9.66/1.65  fof(f46,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 9.66/1.65    inference(flattening,[],[f45])).
% 9.66/1.65  fof(f45,plain,(
% 9.66/1.65    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 9.66/1.65    inference(nnf_transformation,[],[f20])).
% 9.66/1.65  fof(f20,axiom,(
% 9.66/1.65    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 9.66/1.65  fof(f3849,plain,(
% 9.66/1.65    ~r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | spl9_3),
% 9.66/1.65    inference(avatar_component_clause,[],[f3847])).
% 9.66/1.65  fof(f3983,plain,(
% 9.66/1.65    spl9_4),
% 9.66/1.65    inference(avatar_contradiction_clause,[],[f3982])).
% 9.66/1.65  fof(f3982,plain,(
% 9.66/1.65    $false | spl9_4),
% 9.66/1.65    inference(subsumption_resolution,[],[f3981,f55])).
% 9.66/1.65  fof(f55,plain,(
% 9.66/1.65    ~r2_hidden(sK4,sK6)),
% 9.66/1.65    inference(cnf_transformation,[],[f36])).
% 9.66/1.65  fof(f36,plain,(
% 9.66/1.65    sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5)) & ~r2_hidden(sK5,sK6) & ~r2_hidden(sK4,sK6)),
% 9.66/1.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f35])).
% 9.66/1.65  fof(f35,plain,(
% 9.66/1.65    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5)) & ~r2_hidden(sK5,sK6) & ~r2_hidden(sK4,sK6))),
% 9.66/1.65    introduced(choice_axiom,[])).
% 9.66/1.65  fof(f25,plain,(
% 9.66/1.65    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 9.66/1.65    inference(ennf_transformation,[],[f22])).
% 9.66/1.65  fof(f22,negated_conjecture,(
% 9.66/1.65    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 9.66/1.65    inference(negated_conjecture,[],[f21])).
% 9.66/1.65  fof(f21,conjecture,(
% 9.66/1.65    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 9.66/1.65  fof(f3981,plain,(
% 9.66/1.65    r2_hidden(sK4,sK6) | spl9_4),
% 9.66/1.65    inference(subsumption_resolution,[],[f3980,f56])).
% 9.66/1.65  fof(f56,plain,(
% 9.66/1.65    ~r2_hidden(sK5,sK6)),
% 9.66/1.65    inference(cnf_transformation,[],[f36])).
% 9.66/1.65  fof(f3980,plain,(
% 9.66/1.65    r2_hidden(sK5,sK6) | r2_hidden(sK4,sK6) | spl9_4),
% 9.66/1.65    inference(trivial_inequality_removal,[],[f3979])).
% 9.66/1.65  fof(f3979,plain,(
% 9.66/1.65    sK6 != sK6 | r2_hidden(sK5,sK6) | r2_hidden(sK4,sK6) | spl9_4),
% 9.66/1.65    inference(superposition,[],[f3853,f2908])).
% 9.66/1.65  fof(f2908,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(forward_demodulation,[],[f2907,f1717])).
% 9.66/1.65  fof(f1717,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 9.66/1.65    inference(backward_demodulation,[],[f125,f1716])).
% 9.66/1.65  fof(f1716,plain,(
% 9.66/1.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 9.66/1.65    inference(forward_demodulation,[],[f1715,f58])).
% 9.66/1.65  fof(f58,plain,(
% 9.66/1.65    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 9.66/1.65    inference(cnf_transformation,[],[f8])).
% 9.66/1.65  fof(f8,axiom,(
% 9.66/1.65    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 9.66/1.65  fof(f1715,plain,(
% 9.66/1.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 9.66/1.65    inference(forward_demodulation,[],[f106,f107])).
% 9.66/1.65  fof(f107,plain,(
% 9.66/1.65    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 9.66/1.65    inference(definition_unfolding,[],[f60,f102])).
% 9.66/1.65  fof(f60,plain,(
% 9.66/1.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 9.66/1.65    inference(cnf_transformation,[],[f24])).
% 9.66/1.65  fof(f24,plain,(
% 9.66/1.65    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 9.66/1.65    inference(rectify,[],[f3])).
% 9.66/1.65  fof(f3,axiom,(
% 9.66/1.65    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 9.66/1.65  fof(f106,plain,(
% 9.66/1.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 9.66/1.65    inference(definition_unfolding,[],[f59,f103])).
% 9.66/1.65  fof(f103,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 9.66/1.65    inference(definition_unfolding,[],[f66,f102])).
% 9.66/1.65  fof(f66,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 9.66/1.65    inference(cnf_transformation,[],[f9])).
% 9.66/1.65  fof(f9,axiom,(
% 9.66/1.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 9.66/1.65  fof(f59,plain,(
% 9.66/1.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 9.66/1.65    inference(cnf_transformation,[],[f23])).
% 9.66/1.65  fof(f23,plain,(
% 9.66/1.65    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 9.66/1.65    inference(rectify,[],[f4])).
% 9.66/1.65  fof(f4,axiom,(
% 9.66/1.65    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 9.66/1.65  fof(f125,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 9.66/1.65    inference(superposition,[],[f69,f58])).
% 9.66/1.65  fof(f69,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 9.66/1.65    inference(cnf_transformation,[],[f7])).
% 9.66/1.65  fof(f7,axiom,(
% 9.66/1.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 9.66/1.65  fof(f2907,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(forward_demodulation,[],[f115,f69])).
% 9.66/1.65  fof(f115,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f82,f104,f101])).
% 9.66/1.65  fof(f104,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 9.66/1.65    inference(definition_unfolding,[],[f65,f103])).
% 9.66/1.65  fof(f65,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.66/1.65    inference(cnf_transformation,[],[f5])).
% 9.66/1.65  fof(f5,axiom,(
% 9.66/1.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.66/1.65  fof(f82,plain,(
% 9.66/1.65    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f27])).
% 9.66/1.65  fof(f27,plain,(
% 9.66/1.65    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 9.66/1.65    inference(ennf_transformation,[],[f19])).
% 9.66/1.65  fof(f19,axiom,(
% 9.66/1.65    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 9.66/1.65  fof(f3853,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | spl9_4),
% 9.66/1.65    inference(avatar_component_clause,[],[f3851])).
% 9.66/1.65  fof(f3851,plain,(
% 9.66/1.65    spl9_4 <=> sK6 = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 9.66/1.65  fof(f3854,plain,(
% 9.66/1.65    ~spl9_3 | ~spl9_4),
% 9.66/1.65    inference(avatar_split_clause,[],[f3845,f3851,f3847])).
% 9.66/1.65  fof(f3845,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))) | ~r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3844,f1718])).
% 9.66/1.65  fof(f1718,plain,(
% 9.66/1.65    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 9.66/1.65    inference(backward_demodulation,[],[f138,f1716])).
% 9.66/1.65  fof(f138,plain,(
% 9.66/1.65    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1))) )),
% 9.66/1.65    inference(superposition,[],[f125,f62])).
% 9.66/1.65  fof(f62,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f1])).
% 9.66/1.65  fof(f1,axiom,(
% 9.66/1.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 9.66/1.65  fof(f3844,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))) | ~r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3843,f62])).
% 9.66/1.65  fof(f3843,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) | ~r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3811,f130])).
% 9.66/1.65  fof(f130,plain,(
% 9.66/1.65    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 9.66/1.65    inference(superposition,[],[f69,f62])).
% 9.66/1.65  fof(f3811,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))) | ~r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))),
% 9.66/1.65    inference(superposition,[],[f3798,f109])).
% 9.66/1.65  fof(f109,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f67,f102])).
% 9.66/1.65  fof(f67,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f26])).
% 9.66/1.65  fof(f26,plain,(
% 9.66/1.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 9.66/1.65    inference(ennf_transformation,[],[f6])).
% 9.66/1.65  fof(f6,axiom,(
% 9.66/1.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 9.66/1.65  fof(f3798,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3797,f108])).
% 9.66/1.65  fof(f108,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 9.66/1.65    inference(definition_unfolding,[],[f61,f101,f101])).
% 9.66/1.65  fof(f61,plain,(
% 9.66/1.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 9.66/1.65    inference(cnf_transformation,[],[f10])).
% 9.66/1.65  fof(f10,axiom,(
% 9.66/1.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 9.66/1.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 9.66/1.65  fof(f3797,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3796,f62])).
% 9.66/1.65  fof(f3796,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))),
% 9.66/1.65    inference(forward_demodulation,[],[f3795,f130])).
% 9.66/1.65  fof(f3795,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))))),
% 9.66/1.65    inference(forward_demodulation,[],[f105,f69])).
% 9.66/1.65  fof(f105,plain,(
% 9.66/1.65    sK6 != k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k5_xboole_0(k5_xboole_0(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)))))),
% 9.66/1.65    inference(definition_unfolding,[],[f57,f104,f102,f101,f101])).
% 9.66/1.65  fof(f57,plain,(
% 9.66/1.65    sK6 != k4_xboole_0(k2_xboole_0(sK6,k2_tarski(sK4,sK5)),k2_tarski(sK4,sK5))),
% 9.66/1.65    inference(cnf_transformation,[],[f36])).
% 9.66/1.65  % SZS output end Proof for theBenchmark
% 9.66/1.65  % (14004)------------------------------
% 9.66/1.65  % (14004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.66/1.65  % (14004)Termination reason: Refutation
% 9.66/1.65  
% 9.66/1.65  % (14004)Memory used [KB]: 13560
% 9.66/1.65  % (14004)Time elapsed: 1.252 s
% 9.66/1.65  % (14004)------------------------------
% 9.66/1.65  % (14004)------------------------------
% 9.66/1.65  % (13976)Success in time 1.286 s
%------------------------------------------------------------------------------
