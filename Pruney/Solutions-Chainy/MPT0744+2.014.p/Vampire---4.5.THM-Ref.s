%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:31 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 434 expanded)
%              Number of leaves         :   26 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  427 (1392 expanded)
%              Number of equality atoms :   77 ( 279 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f147,f219,f294,f332,f371])).

fof(f371,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f367,f126])).

fof(f126,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f75,f113])).

fof(f113,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f111])).

fof(f111,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f88,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f89,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f90,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

% (27501)Refutation not found, incomplete strategy% (27501)------------------------------
% (27501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f367,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f357,f182])).

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f128,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & ~ r2_hidden(sK6(X0,X1,X2),X1) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & ~ r2_hidden(sK6(X0,X1,X2),X1) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f128,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f86,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f111])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f357,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | spl8_1
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f141,f165])).

fof(f165,plain,
    ( sK3 = sK4
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_4
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f141,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_1
  <=> r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f332,plain,
    ( ~ spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f327,f143,f163,f159])).

fof(f159,plain,
    ( spl8_3
  <=> r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f143,plain,
    ( spl8_2
  <=> r1_ordinal1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f327,plain,
    ( sK3 = sK4
    | ~ r1_tarski(sK4,sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f155,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f155,plain,
    ( r1_tarski(sK3,sK4)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f59,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_ordinal1(sK3,sK4)
      | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
    & ( r1_ordinal1(sK3,sK4)
      | r2_hidden(sK3,k1_ordinal1(sK4)) )
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK3,X1)
            | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK3,X1)
            | r2_hidden(sK3,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK3,X1)
          | ~ r2_hidden(sK3,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK3,X1)
          | r2_hidden(sK3,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK3,sK4)
        | ~ r2_hidden(sK3,k1_ordinal1(sK4)) )
      & ( r1_ordinal1(sK3,sK4)
        | r2_hidden(sK3,k1_ordinal1(sK4)) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f154,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK3)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f151,f60])).

fof(f60,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f151,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f69,f144])).

fof(f144,plain,
    ( r1_ordinal1(sK3,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f294,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f287,f149])).

fof(f149,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f78,f123])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f287,plain,
    ( r2_hidden(sK3,sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(backward_demodulation,[],[f222,f281])).

fof(f281,plain,
    ( sK3 = sK4
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f272,f127])).

fof(f127,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f74,f113])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f272,plain,
    ( r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f267,f224])).

fof(f224,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl8_2 ),
    inference(resolution,[],[f222,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f267,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_1 ),
    inference(resolution,[],[f181,f140])).

fof(f140,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f128,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f222,plain,
    ( r2_hidden(sK4,sK3)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f221,f59])).

fof(f221,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK3)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f220,f60])).

fof(f220,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK3)
    | spl8_2 ),
    inference(resolution,[],[f145,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f145,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f219,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f217,f178])).

fof(f178,plain,
    ( r2_hidden(sK3,sK4)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f177,f60])).

fof(f177,plain,
    ( ~ v3_ordinal1(sK4)
    | r2_hidden(sK3,sK4)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f175,plain,
    ( ~ v3_ordinal1(sK3)
    | ~ v3_ordinal1(sK4)
    | r2_hidden(sK3,sK4)
    | spl8_3 ),
    inference(resolution,[],[f153,f161])).

fof(f161,plain,
    ( ~ r1_tarski(sK4,sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f159])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f69,f65])).

fof(f217,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl8_1 ),
    inference(resolution,[],[f183,f141])).

fof(f183,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f128,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f147,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f116,f143,f139])).

fof(f116,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f61,f114])).

fof(f114,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f64,f112,f113])).

fof(f64,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f61,plain,
    ( r1_ordinal1(sK3,sK4)
    | r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f146,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f115,f143,f139])).

fof(f115,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f62,f114])).

fof(f62,plain,
    ( ~ r1_ordinal1(sK3,sK4)
    | ~ r2_hidden(sK3,k1_ordinal1(sK4)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.36  ipcrm: permission denied for id (801013760)
% 0.22/0.37  ipcrm: permission denied for id (801046539)
% 0.22/0.39  ipcrm: permission denied for id (801177630)
% 0.22/0.40  ipcrm: permission denied for id (801243186)
% 0.22/0.40  ipcrm: permission denied for id (801275956)
% 0.22/0.41  ipcrm: permission denied for id (801374273)
% 0.22/0.42  ipcrm: permission denied for id (801407042)
% 0.22/0.42  ipcrm: permission denied for id (801439812)
% 0.22/0.42  ipcrm: permission denied for id (801472582)
% 0.22/0.43  ipcrm: permission denied for id (801570892)
% 0.22/0.44  ipcrm: permission denied for id (801636437)
% 0.22/0.45  ipcrm: permission denied for id (801669207)
% 0.22/0.45  ipcrm: permission denied for id (801734748)
% 0.22/0.46  ipcrm: permission denied for id (801767518)
% 0.22/0.47  ipcrm: permission denied for id (801800293)
% 0.22/0.47  ipcrm: permission denied for id (801833064)
% 0.22/0.48  ipcrm: permission denied for id (801931377)
% 0.22/0.48  ipcrm: permission denied for id (801964148)
% 0.22/0.48  ipcrm: permission denied for id (801996918)
% 0.78/0.59  % (27499)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.78/0.62  % (27491)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.78/0.63  % (27515)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.78/0.63  % (27493)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.78/0.63  % (27507)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.78/0.64  % (27488)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.78/0.64  % (27509)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.78/0.64  % (27501)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.64  % (27493)Refutation found. Thanks to Tanya!
% 1.31/0.64  % SZS status Theorem for theBenchmark
% 1.31/0.64  % SZS output start Proof for theBenchmark
% 1.31/0.64  fof(f372,plain,(
% 1.31/0.64    $false),
% 1.31/0.64    inference(avatar_sat_refutation,[],[f146,f147,f219,f294,f332,f371])).
% 1.31/0.64  fof(f371,plain,(
% 1.31/0.64    spl8_1 | ~spl8_4),
% 1.31/0.64    inference(avatar_contradiction_clause,[],[f370])).
% 1.31/0.64  fof(f370,plain,(
% 1.31/0.64    $false | (spl8_1 | ~spl8_4)),
% 1.31/0.64    inference(subsumption_resolution,[],[f367,f126])).
% 1.31/0.64  fof(f126,plain,(
% 1.31/0.64    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 1.31/0.64    inference(equality_resolution,[],[f125])).
% 1.31/0.64  fof(f125,plain,(
% 1.31/0.64    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 1.31/0.64    inference(equality_resolution,[],[f119])).
% 1.31/0.64  fof(f119,plain,(
% 1.31/0.64    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.31/0.64    inference(definition_unfolding,[],[f75,f113])).
% 1.31/0.64  fof(f113,plain,(
% 1.31/0.64    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f63,f111])).
% 1.31/0.64  fof(f111,plain,(
% 1.31/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f67,f110])).
% 1.31/0.64  fof(f110,plain,(
% 1.31/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f79,f109])).
% 1.31/0.64  fof(f109,plain,(
% 1.31/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f88,f108])).
% 1.31/0.64  fof(f108,plain,(
% 1.31/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f89,f107])).
% 1.31/0.64  fof(f107,plain,(
% 1.31/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.64    inference(definition_unfolding,[],[f90,f91])).
% 1.31/0.64  fof(f91,plain,(
% 1.31/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f11])).
% 1.31/0.64  fof(f11,axiom,(
% 1.31/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.31/0.64  fof(f90,plain,(
% 1.31/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f10])).
% 1.31/0.64  fof(f10,axiom,(
% 1.31/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.64  fof(f89,plain,(
% 1.31/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f9])).
% 1.31/0.64  fof(f9,axiom,(
% 1.31/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.64  fof(f88,plain,(
% 1.31/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f8])).
% 1.31/0.64  fof(f8,axiom,(
% 1.31/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.64  fof(f79,plain,(
% 1.31/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f7])).
% 1.31/0.64  fof(f7,axiom,(
% 1.31/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.64  fof(f67,plain,(
% 1.31/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f6])).
% 1.31/0.64  fof(f6,axiom,(
% 1.31/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.64  fof(f63,plain,(
% 1.31/0.64    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.31/0.64    inference(cnf_transformation,[],[f5])).
% 1.31/0.64  fof(f5,axiom,(
% 1.31/0.64    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.64  fof(f75,plain,(
% 1.31/0.64    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.31/0.64    inference(cnf_transformation,[],[f44])).
% 1.31/0.64  fof(f44,plain,(
% 1.31/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.31/0.64  fof(f43,plain,(
% 1.31/0.64    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.31/0.64    introduced(choice_axiom,[])).
% 1.31/0.64  fof(f42,plain,(
% 1.31/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.64    inference(rectify,[],[f41])).
% 1.31/0.64  fof(f41,plain,(
% 1.31/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.64    inference(nnf_transformation,[],[f4])).
% 1.31/0.64  fof(f4,axiom,(
% 1.31/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.31/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.31/0.64  % (27501)Refutation not found, incomplete strategy% (27501)------------------------------
% 1.31/0.64  % (27501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.64  fof(f367,plain,(
% 1.31/0.64    ~r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | (spl8_1 | ~spl8_4)),
% 1.31/0.64    inference(resolution,[],[f357,f182])).
% 1.31/0.65  fof(f182,plain,(
% 1.31/0.65    ( ! [X4,X5,X3] : (r2_hidden(X3,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) | ~r2_hidden(X3,X4)) )),
% 1.31/0.65    inference(resolution,[],[f128,f82])).
% 1.31/0.65  fof(f82,plain,(
% 1.31/0.65    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f49])).
% 1.31/0.65  fof(f49,plain,(
% 1.31/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.31/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 1.31/0.65  fof(f48,plain,(
% 1.31/0.65    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.31/0.65    introduced(choice_axiom,[])).
% 1.31/0.65  fof(f47,plain,(
% 1.31/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.31/0.65    inference(rectify,[],[f46])).
% 1.31/0.65  fof(f46,plain,(
% 1.31/0.65    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.31/0.65    inference(flattening,[],[f45])).
% 1.31/0.65  fof(f45,plain,(
% 1.31/0.65    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.31/0.65    inference(nnf_transformation,[],[f28])).
% 1.31/0.65  fof(f28,plain,(
% 1.31/0.65    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.31/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.65  fof(f128,plain,(
% 1.31/0.65    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.31/0.65    inference(equality_resolution,[],[f122])).
% 1.31/0.65  fof(f122,plain,(
% 1.31/0.65    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.31/0.65    inference(definition_unfolding,[],[f86,f112])).
% 1.31/0.65  fof(f112,plain,(
% 1.31/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.31/0.65    inference(definition_unfolding,[],[f66,f111])).
% 1.31/0.65  fof(f66,plain,(
% 1.31/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.31/0.65    inference(cnf_transformation,[],[f12])).
% 1.31/0.65  fof(f12,axiom,(
% 1.31/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 1.31/0.65  fof(f86,plain,(
% 1.31/0.65    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.31/0.65    inference(cnf_transformation,[],[f50])).
% 1.31/0.65  fof(f50,plain,(
% 1.31/0.65    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.65    inference(nnf_transformation,[],[f29])).
% 1.31/0.65  fof(f29,plain,(
% 1.31/0.65    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.31/0.65    inference(definition_folding,[],[f2,f28])).
% 1.31/0.65  fof(f2,axiom,(
% 1.31/0.65    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.31/0.65  fof(f357,plain,(
% 1.31/0.65    ~r2_hidden(sK3,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (spl8_1 | ~spl8_4)),
% 1.31/0.65    inference(backward_demodulation,[],[f141,f165])).
% 1.31/0.65  fof(f165,plain,(
% 1.31/0.65    sK3 = sK4 | ~spl8_4),
% 1.31/0.65    inference(avatar_component_clause,[],[f163])).
% 1.31/0.65  fof(f163,plain,(
% 1.31/0.65    spl8_4 <=> sK3 = sK4),
% 1.31/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.31/0.65  fof(f141,plain,(
% 1.31/0.65    ~r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_1),
% 1.31/0.65    inference(avatar_component_clause,[],[f139])).
% 1.31/0.65  fof(f139,plain,(
% 1.31/0.65    spl8_1 <=> r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.31/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.31/0.65  fof(f332,plain,(
% 1.31/0.65    ~spl8_3 | spl8_4 | ~spl8_2),
% 1.31/0.65    inference(avatar_split_clause,[],[f327,f143,f163,f159])).
% 1.31/0.65  fof(f159,plain,(
% 1.31/0.65    spl8_3 <=> r1_tarski(sK4,sK3)),
% 1.31/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.31/0.65  fof(f143,plain,(
% 1.31/0.65    spl8_2 <=> r1_ordinal1(sK3,sK4)),
% 1.31/0.65    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.31/0.65  fof(f327,plain,(
% 1.31/0.65    sK3 = sK4 | ~r1_tarski(sK4,sK3) | ~spl8_2),
% 1.31/0.65    inference(resolution,[],[f155,f73])).
% 1.31/0.65  fof(f73,plain,(
% 1.31/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f40])).
% 1.31/0.65  fof(f40,plain,(
% 1.31/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.65    inference(flattening,[],[f39])).
% 1.31/0.65  fof(f39,plain,(
% 1.31/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.65    inference(nnf_transformation,[],[f3])).
% 1.31/0.65  fof(f3,axiom,(
% 1.31/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.65  fof(f155,plain,(
% 1.31/0.65    r1_tarski(sK3,sK4) | ~spl8_2),
% 1.31/0.65    inference(subsumption_resolution,[],[f154,f59])).
% 1.31/0.65  fof(f59,plain,(
% 1.31/0.65    v3_ordinal1(sK3)),
% 1.31/0.65    inference(cnf_transformation,[],[f37])).
% 1.31/0.65  fof(f37,plain,(
% 1.31/0.65    ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4)) & v3_ordinal1(sK3)),
% 1.31/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f36,f35])).
% 1.31/0.65  fof(f35,plain,(
% 1.31/0.65    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK3))),
% 1.31/0.65    introduced(choice_axiom,[])).
% 1.31/0.65  fof(f36,plain,(
% 1.31/0.65    ? [X1] : ((~r1_ordinal1(sK3,X1) | ~r2_hidden(sK3,k1_ordinal1(X1))) & (r1_ordinal1(sK3,X1) | r2_hidden(sK3,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))) & (r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))) & v3_ordinal1(sK4))),
% 1.31/0.65    introduced(choice_axiom,[])).
% 1.31/0.65  fof(f34,plain,(
% 1.31/0.65    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.65    inference(flattening,[],[f33])).
% 1.31/0.65  fof(f33,plain,(
% 1.31/0.65    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.65    inference(nnf_transformation,[],[f20])).
% 1.31/0.65  fof(f20,plain,(
% 1.31/0.65    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.31/0.65    inference(ennf_transformation,[],[f19])).
% 1.31/0.65  fof(f19,negated_conjecture,(
% 1.31/0.65    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.65    inference(negated_conjecture,[],[f18])).
% 1.31/0.65  fof(f18,conjecture,(
% 1.31/0.65    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.31/0.65  fof(f154,plain,(
% 1.31/0.65    r1_tarski(sK3,sK4) | ~v3_ordinal1(sK3) | ~spl8_2),
% 1.31/0.65    inference(subsumption_resolution,[],[f151,f60])).
% 1.31/0.65  fof(f60,plain,(
% 1.31/0.65    v3_ordinal1(sK4)),
% 1.31/0.65    inference(cnf_transformation,[],[f37])).
% 1.31/0.65  fof(f151,plain,(
% 1.31/0.65    r1_tarski(sK3,sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK3) | ~spl8_2),
% 1.31/0.65    inference(resolution,[],[f69,f144])).
% 1.31/0.65  fof(f144,plain,(
% 1.31/0.65    r1_ordinal1(sK3,sK4) | ~spl8_2),
% 1.31/0.65    inference(avatar_component_clause,[],[f143])).
% 1.31/0.65  fof(f69,plain,(
% 1.31/0.65    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f38])).
% 1.31/0.65  fof(f38,plain,(
% 1.31/0.65    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.65    inference(nnf_transformation,[],[f25])).
% 1.31/0.65  fof(f25,plain,(
% 1.31/0.65    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.31/0.65    inference(flattening,[],[f24])).
% 1.31/0.65  fof(f24,plain,(
% 1.31/0.65    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.31/0.65    inference(ennf_transformation,[],[f15])).
% 1.31/0.65  fof(f15,axiom,(
% 1.31/0.65    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.31/0.65  fof(f294,plain,(
% 1.31/0.65    ~spl8_1 | spl8_2),
% 1.31/0.65    inference(avatar_contradiction_clause,[],[f293])).
% 1.31/0.65  fof(f293,plain,(
% 1.31/0.65    $false | (~spl8_1 | spl8_2)),
% 1.31/0.65    inference(subsumption_resolution,[],[f287,f149])).
% 1.31/0.65  fof(f149,plain,(
% 1.31/0.65    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 1.31/0.65    inference(resolution,[],[f78,f123])).
% 1.31/0.65  fof(f123,plain,(
% 1.31/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.65    inference(equality_resolution,[],[f72])).
% 1.31/0.65  fof(f72,plain,(
% 1.31/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.65    inference(cnf_transformation,[],[f40])).
% 1.31/0.65  fof(f78,plain,(
% 1.31/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f26])).
% 1.31/0.65  fof(f26,plain,(
% 1.31/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.31/0.65    inference(ennf_transformation,[],[f17])).
% 1.31/0.65  fof(f17,axiom,(
% 1.31/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.31/0.65  fof(f287,plain,(
% 1.31/0.65    r2_hidden(sK3,sK3) | (~spl8_1 | spl8_2)),
% 1.31/0.65    inference(backward_demodulation,[],[f222,f281])).
% 1.31/0.65  fof(f281,plain,(
% 1.31/0.65    sK3 = sK4 | (~spl8_1 | spl8_2)),
% 1.31/0.65    inference(resolution,[],[f272,f127])).
% 1.31/0.65  fof(f127,plain,(
% 1.31/0.65    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.31/0.65    inference(equality_resolution,[],[f120])).
% 1.31/0.65  fof(f120,plain,(
% 1.31/0.65    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.31/0.65    inference(definition_unfolding,[],[f74,f113])).
% 1.31/0.65  fof(f74,plain,(
% 1.31/0.65    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.65    inference(cnf_transformation,[],[f44])).
% 1.31/0.65  fof(f272,plain,(
% 1.31/0.65    r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | (~spl8_1 | spl8_2)),
% 1.31/0.65    inference(subsumption_resolution,[],[f267,f224])).
% 1.31/0.65  fof(f224,plain,(
% 1.31/0.65    ~r2_hidden(sK3,sK4) | spl8_2),
% 1.31/0.65    inference(resolution,[],[f222,f68])).
% 1.31/0.65  fof(f68,plain,(
% 1.31/0.65    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f23])).
% 1.31/0.65  fof(f23,plain,(
% 1.31/0.65    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.31/0.65    inference(ennf_transformation,[],[f1])).
% 1.31/0.65  fof(f1,axiom,(
% 1.31/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.31/0.65  fof(f267,plain,(
% 1.31/0.65    r2_hidden(sK3,sK4) | r2_hidden(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl8_1),
% 1.31/0.65    inference(resolution,[],[f181,f140])).
% 1.31/0.65  fof(f140,plain,(
% 1.31/0.65    r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_1),
% 1.31/0.65    inference(avatar_component_clause,[],[f139])).
% 1.31/0.65  fof(f181,plain,(
% 1.31/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.31/0.65    inference(resolution,[],[f128,f80])).
% 1.31/0.65  fof(f80,plain,(
% 1.31/0.65    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f49])).
% 1.31/0.65  fof(f222,plain,(
% 1.31/0.65    r2_hidden(sK4,sK3) | spl8_2),
% 1.31/0.65    inference(subsumption_resolution,[],[f221,f59])).
% 1.31/0.65  fof(f221,plain,(
% 1.31/0.65    r2_hidden(sK4,sK3) | ~v3_ordinal1(sK3) | spl8_2),
% 1.31/0.65    inference(subsumption_resolution,[],[f220,f60])).
% 1.31/0.65  fof(f220,plain,(
% 1.31/0.65    r2_hidden(sK4,sK3) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK3) | spl8_2),
% 1.31/0.65    inference(resolution,[],[f145,f65])).
% 1.31/0.65  fof(f65,plain,(
% 1.31/0.65    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f22])).
% 1.31/0.65  fof(f22,plain,(
% 1.31/0.65    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.65    inference(flattening,[],[f21])).
% 1.31/0.65  fof(f21,plain,(
% 1.31/0.65    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.31/0.65    inference(ennf_transformation,[],[f16])).
% 1.31/0.65  fof(f16,axiom,(
% 1.31/0.65    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.31/0.65  fof(f145,plain,(
% 1.31/0.65    ~r1_ordinal1(sK3,sK4) | spl8_2),
% 1.31/0.65    inference(avatar_component_clause,[],[f143])).
% 1.31/0.65  fof(f219,plain,(
% 1.31/0.65    spl8_1 | spl8_3),
% 1.31/0.65    inference(avatar_contradiction_clause,[],[f218])).
% 1.31/0.65  fof(f218,plain,(
% 1.31/0.65    $false | (spl8_1 | spl8_3)),
% 1.31/0.65    inference(subsumption_resolution,[],[f217,f178])).
% 1.31/0.65  fof(f178,plain,(
% 1.31/0.65    r2_hidden(sK3,sK4) | spl8_3),
% 1.31/0.65    inference(subsumption_resolution,[],[f177,f60])).
% 1.31/0.65  fof(f177,plain,(
% 1.31/0.65    ~v3_ordinal1(sK4) | r2_hidden(sK3,sK4) | spl8_3),
% 1.31/0.65    inference(subsumption_resolution,[],[f175,f59])).
% 1.31/0.65  fof(f175,plain,(
% 1.31/0.65    ~v3_ordinal1(sK3) | ~v3_ordinal1(sK4) | r2_hidden(sK3,sK4) | spl8_3),
% 1.31/0.65    inference(resolution,[],[f153,f161])).
% 1.31/0.65  fof(f161,plain,(
% 1.31/0.65    ~r1_tarski(sK4,sK3) | spl8_3),
% 1.31/0.65    inference(avatar_component_clause,[],[f159])).
% 1.31/0.65  fof(f153,plain,(
% 1.31/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.31/0.65    inference(duplicate_literal_removal,[],[f152])).
% 1.31/0.65  fof(f152,plain,(
% 1.31/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.31/0.65    inference(resolution,[],[f69,f65])).
% 1.31/0.65  fof(f217,plain,(
% 1.31/0.65    ~r2_hidden(sK3,sK4) | spl8_1),
% 1.31/0.65    inference(resolution,[],[f183,f141])).
% 1.31/0.65  fof(f183,plain,(
% 1.31/0.65    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) | ~r2_hidden(X6,X7)) )),
% 1.31/0.65    inference(resolution,[],[f128,f81])).
% 1.31/0.65  fof(f81,plain,(
% 1.31/0.65    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.31/0.65    inference(cnf_transformation,[],[f49])).
% 1.31/0.65  fof(f147,plain,(
% 1.31/0.65    spl8_1 | spl8_2),
% 1.31/0.65    inference(avatar_split_clause,[],[f116,f143,f139])).
% 1.31/0.65  fof(f116,plain,(
% 1.31/0.65    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.31/0.65    inference(definition_unfolding,[],[f61,f114])).
% 1.31/0.65  fof(f114,plain,(
% 1.31/0.65    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.31/0.65    inference(definition_unfolding,[],[f64,f112,f113])).
% 1.31/0.65  fof(f64,plain,(
% 1.31/0.65    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.31/0.65    inference(cnf_transformation,[],[f14])).
% 1.31/0.65  fof(f14,axiom,(
% 1.31/0.65    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.31/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.31/0.65  fof(f61,plain,(
% 1.31/0.65    r1_ordinal1(sK3,sK4) | r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.31/0.65    inference(cnf_transformation,[],[f37])).
% 1.31/0.65  fof(f146,plain,(
% 1.31/0.65    ~spl8_1 | ~spl8_2),
% 1.31/0.65    inference(avatar_split_clause,[],[f115,f143,f139])).
% 1.31/0.65  fof(f115,plain,(
% 1.31/0.65    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.31/0.65    inference(definition_unfolding,[],[f62,f114])).
% 1.31/0.65  fof(f62,plain,(
% 1.31/0.65    ~r1_ordinal1(sK3,sK4) | ~r2_hidden(sK3,k1_ordinal1(sK4))),
% 1.31/0.65    inference(cnf_transformation,[],[f37])).
% 1.31/0.65  % SZS output end Proof for theBenchmark
% 1.31/0.65  % (27493)------------------------------
% 1.31/0.65  % (27493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.65  % (27493)Termination reason: Refutation
% 1.31/0.65  
% 1.31/0.65  % (27493)Memory used [KB]: 10874
% 1.31/0.65  % (27493)Time elapsed: 0.101 s
% 1.31/0.65  % (27493)------------------------------
% 1.31/0.65  % (27493)------------------------------
% 1.31/0.65  % (27497)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.65  % (27498)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.65  % (27501)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.65  
% 1.31/0.65  % (27501)Memory used [KB]: 1791
% 1.31/0.65  % (27501)Time elapsed: 0.106 s
% 1.31/0.65  % (27501)------------------------------
% 1.31/0.65  % (27501)------------------------------
% 1.31/0.65  % (27333)Success in time 0.292 s
%------------------------------------------------------------------------------
