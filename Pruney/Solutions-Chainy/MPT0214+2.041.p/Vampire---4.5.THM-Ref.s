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
% DateTime   : Thu Dec  3 12:35:03 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 253 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  271 ( 600 expanded)
%              Number of equality atoms :  103 ( 291 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f204,f216,f347])).

fof(f347,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f340,f42])).

fof(f42,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK3 != sK4
    & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK3 != sK4
      & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f340,plain,
    ( sK3 = sK4
    | ~ spl6_3 ),
    inference(resolution,[],[f323,f90])).

fof(f90,plain,(
    ! [X2,X3,X1] : sP1(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X1,X0] :
      ( sP1(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ sP1(X0,sK3,sK3,sK3)
        | sK4 = X0 )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ sP1(X0,sK3,sK3,sK3)
        | sK4 = X0
        | sK4 = X0
        | sK4 = X0 )
    | ~ spl6_3 ),
    inference(resolution,[],[f317,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f317,plain,
    ( ! [X0] :
        ( sP1(X0,sK4,sK4,sK4)
        | ~ sP1(X0,sK3,sK3,sK3) )
    | ~ spl6_3 ),
    inference(resolution,[],[f246,f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ~ sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP1(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP1(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP1(X4,X2,X1,X0) )
            & ( sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( sP2(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP1(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f91,plain,(
    ! [X2,X0,X1] : sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X0,X1,X2,X3) )
      & ( sP2(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f20,f24,f23])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f246,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
        | sP1(X1,sK4,sK4,sK4) )
    | ~ spl6_3 ),
    inference(superposition,[],[f132,f174])).

fof(f174,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_3
  <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f132,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))
      | sP1(X4,X7,X6,X5) ) ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP1(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f216,plain,
    ( spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f215,f146,f172])).

fof(f146,plain,
    ( spl6_1
  <=> k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f215,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f212,f147])).

fof(f147,plain,
    ( k1_xboole_0 != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f212,plain,
    ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[],[f79,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f78,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f79,plain,(
    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f41,f78,f78])).

fof(f41,plain,(
    r1_tarski(k1_tarski(sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f204,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl6_1 ),
    inference(resolution,[],[f191,f88])).

fof(f88,plain,(
    ! [X2,X3,X1] : sP1(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f191,plain,
    ( ! [X2] : ~ sP1(X2,sK3,sK3,sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f187,f111])).

fof(f111,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f54,f97])).

fof(f97,plain,(
    ! [X2] :
      ( sP0(k1_xboole_0,X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f57,f95])).

fof(f95,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f80,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f19,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f187,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ sP1(X2,sK3,sK3,sK3) )
    | ~ spl6_1 ),
    inference(superposition,[],[f131,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (736690176)
% 0.14/0.38  ipcrm: permission denied for id (736821262)
% 0.14/0.39  ipcrm: permission denied for id (736886802)
% 0.14/0.39  ipcrm: permission denied for id (736985109)
% 0.22/0.40  ipcrm: permission denied for id (737116189)
% 0.22/0.42  ipcrm: permission denied for id (737148967)
% 0.22/0.42  ipcrm: permission denied for id (737247275)
% 0.22/0.42  ipcrm: permission denied for id (737280045)
% 0.22/0.43  ipcrm: permission denied for id (737411121)
% 0.22/0.46  ipcrm: permission denied for id (737542219)
% 0.22/0.48  ipcrm: permission denied for id (737673306)
% 0.22/0.49  ipcrm: permission denied for id (737706079)
% 0.22/0.49  ipcrm: permission denied for id (737738851)
% 0.22/0.50  ipcrm: permission denied for id (737804392)
% 0.22/0.50  ipcrm: permission denied for id (737837162)
% 0.22/0.50  ipcrm: permission denied for id (737869932)
% 0.22/0.51  ipcrm: permission denied for id (737902706)
% 0.22/0.51  ipcrm: permission denied for id (737935475)
% 1.10/0.66  % (19467)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.10/0.67  % (19450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.10/0.67  % (19450)Refutation not found, incomplete strategy% (19450)------------------------------
% 1.10/0.67  % (19450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.67  % (19459)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.10/0.68  % (19443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.10/0.68  % (19450)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.68  
% 1.10/0.68  % (19450)Memory used [KB]: 10618
% 1.10/0.68  % (19450)Time elapsed: 0.100 s
% 1.10/0.68  % (19450)------------------------------
% 1.10/0.68  % (19450)------------------------------
% 1.10/0.69  % (19444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.10/0.69  % (19441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.10/0.69  % (19454)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.10/0.70  % (19455)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.10/0.70  % (19461)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.70  % (19470)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.70  % (19461)Refutation not found, incomplete strategy% (19461)------------------------------
% 1.51/0.70  % (19461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.70  % (19440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.71  % (19461)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.71  
% 1.51/0.71  % (19461)Memory used [KB]: 10746
% 1.51/0.71  % (19461)Time elapsed: 0.112 s
% 1.51/0.71  % (19461)------------------------------
% 1.51/0.71  % (19461)------------------------------
% 1.51/0.71  % (19446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.71  % (19445)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.71  % (19468)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.71  % (19465)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.71  % (19466)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.71  % (19462)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.71  % (19451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.71  % (19456)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.71  % (19457)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.71  % (19448)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.72  % (19447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.72  % (19458)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.72  % (19458)Refutation not found, incomplete strategy% (19458)------------------------------
% 1.51/0.72  % (19458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.72  % (19458)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.72  
% 1.51/0.72  % (19458)Memory used [KB]: 10618
% 1.51/0.72  % (19458)Time elapsed: 0.138 s
% 1.51/0.72  % (19458)------------------------------
% 1.51/0.72  % (19458)------------------------------
% 1.51/0.72  % (19453)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.72  % (19449)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.72  % (19464)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.73  % (19460)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.73  % (19468)Refutation found. Thanks to Tanya!
% 1.51/0.73  % SZS status Theorem for theBenchmark
% 1.51/0.73  % SZS output start Proof for theBenchmark
% 1.51/0.73  fof(f348,plain,(
% 1.51/0.73    $false),
% 1.51/0.73    inference(avatar_sat_refutation,[],[f204,f216,f347])).
% 1.51/0.73  fof(f347,plain,(
% 1.51/0.73    ~spl6_3),
% 1.51/0.73    inference(avatar_contradiction_clause,[],[f346])).
% 1.51/0.73  fof(f346,plain,(
% 1.51/0.73    $false | ~spl6_3),
% 1.51/0.73    inference(subsumption_resolution,[],[f340,f42])).
% 1.51/0.73  fof(f42,plain,(
% 1.51/0.73    sK3 != sK4),
% 1.51/0.73    inference(cnf_transformation,[],[f27])).
% 1.51/0.73  fof(f27,plain,(
% 1.51/0.73    sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 1.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f26])).
% 1.51/0.73  fof(f26,plain,(
% 1.51/0.73    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK3 != sK4 & r1_tarski(k1_tarski(sK3),k1_tarski(sK4)))),
% 1.51/0.73    introduced(choice_axiom,[])).
% 1.51/0.73  fof(f17,plain,(
% 1.51/0.73    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.51/0.73    inference(ennf_transformation,[],[f16])).
% 1.51/0.73  fof(f16,negated_conjecture,(
% 1.51/0.73    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.51/0.73    inference(negated_conjecture,[],[f15])).
% 1.51/0.73  fof(f15,conjecture,(
% 1.51/0.73    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.51/0.73  fof(f340,plain,(
% 1.51/0.73    sK3 = sK4 | ~spl6_3),
% 1.51/0.73    inference(resolution,[],[f323,f90])).
% 1.51/0.73  fof(f90,plain,(
% 1.51/0.73    ( ! [X2,X3,X1] : (sP1(X3,X1,X2,X3)) )),
% 1.51/0.73    inference(equality_resolution,[],[f65])).
% 1.51/0.73  fof(f65,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X3) )),
% 1.51/0.73    inference(cnf_transformation,[],[f39])).
% 1.51/0.73  fof(f39,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP1(X0,X1,X2,X3)))),
% 1.51/0.73    inference(rectify,[],[f38])).
% 1.51/0.73  fof(f38,plain,(
% 1.51/0.73    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP1(X4,X2,X1,X0)))),
% 1.51/0.73    inference(flattening,[],[f37])).
% 1.51/0.73  fof(f37,plain,(
% 1.51/0.73    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP1(X4,X2,X1,X0)))),
% 1.51/0.73    inference(nnf_transformation,[],[f23])).
% 1.51/0.73  fof(f23,plain,(
% 1.51/0.73    ! [X4,X2,X1,X0] : (sP1(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.51/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.51/0.73  fof(f323,plain,(
% 1.51/0.73    ( ! [X0] : (~sP1(X0,sK3,sK3,sK3) | sK4 = X0) ) | ~spl6_3),
% 1.51/0.73    inference(duplicate_literal_removal,[],[f321])).
% 1.51/0.73  fof(f321,plain,(
% 1.51/0.73    ( ! [X0] : (~sP1(X0,sK3,sK3,sK3) | sK4 = X0 | sK4 = X0 | sK4 = X0) ) | ~spl6_3),
% 1.51/0.73    inference(resolution,[],[f317,f64])).
% 1.51/0.73  fof(f64,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 1.51/0.73    inference(cnf_transformation,[],[f39])).
% 1.51/0.73  fof(f317,plain,(
% 1.51/0.73    ( ! [X0] : (sP1(X0,sK4,sK4,sK4) | ~sP1(X0,sK3,sK3,sK3)) ) | ~spl6_3),
% 1.51/0.73    inference(resolution,[],[f246,f131])).
% 1.51/0.73  fof(f131,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP1(X0,X1,X2,X3)) )),
% 1.51/0.73    inference(resolution,[],[f91,f61])).
% 1.51/0.73  fof(f61,plain,(
% 1.51/0.73    ( ! [X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3) | ~sP1(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f36])).
% 1.51/0.73  fof(f36,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ((~sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 1.51/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.51/0.73  fof(f35,plain,(
% 1.51/0.73    ! [X3,X2,X1,X0] : (? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 1.51/0.73    introduced(choice_axiom,[])).
% 1.51/0.73  fof(f34,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 1.51/0.73    inference(rectify,[],[f33])).
% 1.51/0.73  fof(f33,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP1(X4,X2,X1,X0)) & (sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP2(X0,X1,X2,X3)))),
% 1.51/0.73    inference(nnf_transformation,[],[f24])).
% 1.51/0.73  fof(f24,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : (sP2(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP1(X4,X2,X1,X0)))),
% 1.51/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.51/0.73  fof(f91,plain,(
% 1.51/0.73    ( ! [X2,X0,X1] : (sP2(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.51/0.73    inference(equality_resolution,[],[f85])).
% 1.51/0.73  fof(f85,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.51/0.73    inference(definition_unfolding,[],[f68,f76])).
% 1.51/0.73  fof(f76,plain,(
% 1.51/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f52,f75])).
% 1.51/0.73  fof(f75,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f59,f74])).
% 1.51/0.73  fof(f74,plain,(
% 1.51/0.73    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f70,f73])).
% 1.51/0.73  fof(f73,plain,(
% 1.51/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f71,f72])).
% 1.51/0.73  fof(f72,plain,(
% 1.51/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f13])).
% 1.51/0.73  fof(f13,axiom,(
% 1.51/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.51/0.73  fof(f71,plain,(
% 1.51/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f12])).
% 1.51/0.73  fof(f12,axiom,(
% 1.51/0.73    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.51/0.73  fof(f70,plain,(
% 1.51/0.73    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f11])).
% 1.51/0.73  fof(f11,axiom,(
% 1.51/0.73    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.51/0.73  fof(f59,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f10])).
% 1.51/0.73  fof(f10,axiom,(
% 1.51/0.73    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.51/0.73  fof(f52,plain,(
% 1.51/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f9])).
% 1.51/0.73  fof(f9,axiom,(
% 1.51/0.73    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.51/0.73  fof(f68,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.51/0.73    inference(cnf_transformation,[],[f40])).
% 1.51/0.73  fof(f40,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) & (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.51/0.73    inference(nnf_transformation,[],[f25])).
% 1.51/0.73  fof(f25,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X0,X1,X2,X3))),
% 1.51/0.73    inference(definition_folding,[],[f20,f24,f23])).
% 1.51/0.73  fof(f20,plain,(
% 1.51/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.51/0.73    inference(ennf_transformation,[],[f6])).
% 1.51/0.73  fof(f6,axiom,(
% 1.51/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.51/0.73  fof(f246,plain,(
% 1.51/0.73    ( ! [X1] : (~r2_hidden(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | sP1(X1,sK4,sK4,sK4)) ) | ~spl6_3),
% 1.51/0.73    inference(superposition,[],[f132,f174])).
% 1.51/0.73  fof(f174,plain,(
% 1.51/0.73    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl6_3),
% 1.51/0.73    inference(avatar_component_clause,[],[f172])).
% 1.51/0.73  fof(f172,plain,(
% 1.51/0.73    spl6_3 <=> k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.51/0.73  fof(f132,plain,(
% 1.51/0.73    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)) | sP1(X4,X7,X6,X5)) )),
% 1.51/0.73    inference(resolution,[],[f91,f60])).
% 1.51/0.73  fof(f60,plain,(
% 1.51/0.73    ( ! [X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP1(X5,X2,X1,X0)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f36])).
% 1.51/0.73  fof(f216,plain,(
% 1.51/0.73    spl6_3 | spl6_1),
% 1.51/0.73    inference(avatar_split_clause,[],[f215,f146,f172])).
% 1.51/0.73  fof(f146,plain,(
% 1.51/0.73    spl6_1 <=> k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.51/0.73  fof(f215,plain,(
% 1.51/0.73    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | spl6_1),
% 1.51/0.73    inference(subsumption_resolution,[],[f212,f147])).
% 1.51/0.73  fof(f147,plain,(
% 1.51/0.73    k1_xboole_0 != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | spl6_1),
% 1.51/0.73    inference(avatar_component_clause,[],[f146])).
% 1.51/0.73  fof(f212,plain,(
% 1.51/0.73    k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.51/0.73    inference(resolution,[],[f79,f83])).
% 1.51/0.73  fof(f83,plain,(
% 1.51/0.73    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.51/0.73    inference(definition_unfolding,[],[f49,f78,f78])).
% 1.51/0.73  fof(f78,plain,(
% 1.51/0.73    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f44,f77])).
% 1.51/0.73  fof(f77,plain,(
% 1.51/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.51/0.73    inference(definition_unfolding,[],[f47,f76])).
% 1.51/0.73  fof(f47,plain,(
% 1.51/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f8])).
% 1.51/0.73  fof(f8,axiom,(
% 1.51/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.73  fof(f44,plain,(
% 1.51/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f7])).
% 1.51/0.73  fof(f7,axiom,(
% 1.51/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.51/0.73  fof(f49,plain,(
% 1.51/0.73    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.51/0.73    inference(cnf_transformation,[],[f29])).
% 1.51/0.73  fof(f29,plain,(
% 1.51/0.73    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.51/0.73    inference(flattening,[],[f28])).
% 1.51/0.73  fof(f28,plain,(
% 1.51/0.73    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.51/0.73    inference(nnf_transformation,[],[f14])).
% 1.51/0.73  fof(f14,axiom,(
% 1.51/0.73    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.51/0.73  fof(f79,plain,(
% 1.51/0.73    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.51/0.73    inference(definition_unfolding,[],[f41,f78,f78])).
% 1.51/0.73  fof(f41,plain,(
% 1.51/0.73    r1_tarski(k1_tarski(sK3),k1_tarski(sK4))),
% 1.51/0.73    inference(cnf_transformation,[],[f27])).
% 1.51/0.73  fof(f204,plain,(
% 1.51/0.73    ~spl6_1),
% 1.51/0.73    inference(avatar_contradiction_clause,[],[f198])).
% 1.51/0.73  fof(f198,plain,(
% 1.51/0.73    $false | ~spl6_1),
% 1.51/0.73    inference(resolution,[],[f191,f88])).
% 1.51/0.73  fof(f88,plain,(
% 1.51/0.73    ( ! [X2,X3,X1] : (sP1(X1,X1,X2,X3)) )),
% 1.51/0.73    inference(equality_resolution,[],[f67])).
% 1.51/0.73  fof(f67,plain,(
% 1.51/0.73    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X1) )),
% 1.51/0.73    inference(cnf_transformation,[],[f39])).
% 1.51/0.73  fof(f191,plain,(
% 1.51/0.73    ( ! [X2] : (~sP1(X2,sK3,sK3,sK3)) ) | ~spl6_1),
% 1.51/0.73    inference(subsumption_resolution,[],[f187,f111])).
% 1.51/0.73  fof(f111,plain,(
% 1.51/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.51/0.73    inference(duplicate_literal_removal,[],[f108])).
% 1.51/0.73  fof(f108,plain,(
% 1.51/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.51/0.73    inference(resolution,[],[f54,f97])).
% 1.51/0.73  fof(f97,plain,(
% 1.51/0.73    ( ! [X2] : (sP0(k1_xboole_0,X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.51/0.73    inference(superposition,[],[f57,f95])).
% 1.51/0.73  fof(f95,plain,(
% 1.51/0.73    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.51/0.73    inference(superposition,[],[f80,f92])).
% 1.51/0.73  fof(f92,plain,(
% 1.51/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.73    inference(resolution,[],[f45,f46])).
% 1.51/0.73  fof(f46,plain,(
% 1.51/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f3])).
% 1.51/0.73  fof(f3,axiom,(
% 1.51/0.73    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.51/0.73  fof(f45,plain,(
% 1.51/0.73    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.51/0.73    inference(cnf_transformation,[],[f18])).
% 1.51/0.73  fof(f18,plain,(
% 1.51/0.73    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.51/0.73    inference(ennf_transformation,[],[f5])).
% 1.51/0.73  fof(f5,axiom,(
% 1.51/0.73    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.51/0.73  fof(f80,plain,(
% 1.51/0.73    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.51/0.73    inference(definition_unfolding,[],[f43,f48])).
% 1.51/0.73  fof(f48,plain,(
% 1.51/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.73    inference(cnf_transformation,[],[f2])).
% 1.51/0.73  fof(f2,axiom,(
% 1.51/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.73  fof(f43,plain,(
% 1.51/0.73    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.73    inference(cnf_transformation,[],[f4])).
% 1.51/0.73  fof(f4,axiom,(
% 1.51/0.73    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.51/0.73  fof(f57,plain,(
% 1.51/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f32])).
% 1.51/0.73  fof(f32,plain,(
% 1.51/0.73    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.51/0.73    inference(nnf_transformation,[],[f22])).
% 1.51/0.73  fof(f22,plain,(
% 1.51/0.73    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.51/0.73    inference(definition_folding,[],[f19,f21])).
% 1.51/0.73  fof(f21,plain,(
% 1.51/0.73    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.51/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.51/0.73  fof(f19,plain,(
% 1.51/0.73    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.51/0.73    inference(ennf_transformation,[],[f1])).
% 1.51/0.73  fof(f1,axiom,(
% 1.51/0.73    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.51/0.73  fof(f54,plain,(
% 1.51/0.73    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.51/0.73    inference(cnf_transformation,[],[f31])).
% 1.51/0.73  fof(f31,plain,(
% 1.51/0.73    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 1.51/0.73    inference(rectify,[],[f30])).
% 1.51/0.73  fof(f30,plain,(
% 1.51/0.73    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.51/0.73    inference(nnf_transformation,[],[f21])).
% 1.51/0.73  fof(f187,plain,(
% 1.51/0.73    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~sP1(X2,sK3,sK3,sK3)) ) | ~spl6_1),
% 1.51/0.73    inference(superposition,[],[f131,f148])).
% 1.51/0.73  fof(f148,plain,(
% 1.51/0.73    k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl6_1),
% 1.51/0.73    inference(avatar_component_clause,[],[f146])).
% 1.51/0.73  % SZS output end Proof for theBenchmark
% 1.51/0.73  % (19468)------------------------------
% 1.51/0.73  % (19468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.73  % (19468)Termination reason: Refutation
% 1.51/0.73  
% 1.51/0.73  % (19468)Memory used [KB]: 6396
% 1.51/0.73  % (19468)Time elapsed: 0.140 s
% 1.51/0.73  % (19468)------------------------------
% 1.51/0.73  % (19468)------------------------------
% 1.51/0.73  % (19469)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.73  % (19449)Refutation not found, incomplete strategy% (19449)------------------------------
% 1.51/0.73  % (19449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.73  % (19442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.73  % (19449)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.73  % (19451)Refutation not found, incomplete strategy% (19451)------------------------------
% 1.51/0.73  % (19451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.73  % (19451)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.73  
% 1.51/0.73  % (19451)Memory used [KB]: 10618
% 1.51/0.73  % (19451)Time elapsed: 0.146 s
% 1.51/0.73  % (19451)------------------------------
% 1.51/0.73  % (19451)------------------------------
% 1.51/0.73  % (19255)Success in time 0.37 s
%------------------------------------------------------------------------------
