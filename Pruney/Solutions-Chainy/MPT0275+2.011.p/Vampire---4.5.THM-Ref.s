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
% DateTime   : Thu Dec  3 12:41:27 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 332 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  433 ( 964 expanded)
%              Number of equality atoms :   94 ( 294 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f124,f125,f155,f481,f607,f608])).

fof(f608,plain,
    ( spl11_3
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f600,f152,f112,f120])).

fof(f120,plain,
    ( spl11_3
  <=> r2_hidden(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f112,plain,
    ( spl11_1
  <=> k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f152,plain,
    ( spl11_5
  <=> ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f600,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f595,f107])).

fof(f107,plain,(
    ! [X2,X3,X1] : sP3(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f595,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK6,sK5,sK5)
        | r2_hidden(X0,sK7) )
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f591,f348])).

fof(f348,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k4_enumset1(X3,X3,X3,X3,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f87,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f94,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f85,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f23,f30,f29])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
          & ( sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
        & ( sP3(sK10(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f591,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))
        | r2_hidden(X2,sK7) )
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f560,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f560,plain,
    ( ! [X1] :
        ( sP0(sK7,X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))
        | ~ r2_hidden(X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) )
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f507,f252])).

fof(f252,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,X5))
      | sP0(X4,X3,X5) ) ),
    inference(resolution,[],[f70,f130])).

fof(f130,plain,(
    ! [X2,X1] : sP1(X1,X2,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f106,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f106,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f25,f24])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP0(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP0(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f507,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)))
        | ~ r2_hidden(X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) )
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f488,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f488,plain,
    ( ! [X0] : ~ sP2(k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f486,f153])).

fof(f153,plain,
    ( ! [X9] : ~ r2_hidden(X9,k1_xboole_0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f486,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ sP2(k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) )
    | ~ spl11_1 ),
    inference(superposition,[],[f84,f482])).

fof(f482,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f113,f63])).

fof(f113,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f607,plain,
    ( spl11_2
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f601,f152,f112,f116])).

fof(f116,plain,
    ( spl11_2
  <=> r2_hidden(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f601,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(resolution,[],[f595,f108])).

fof(f108,plain,(
    ! [X2,X3,X1] : sP3(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f481,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f479,f117])).

fof(f117,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f479,plain,
    ( ~ r2_hidden(sK5,sK7)
    | spl11_1
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f477,f121])).

fof(f121,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f477,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ r2_hidden(sK5,sK7)
    | spl11_1 ),
    inference(resolution,[],[f476,f110])).

fof(f476,plain,
    ( ! [X68,X69] :
        ( ~ sP4(sK5,sK5,sK6,k4_enumset1(X68,X68,X68,X68,X68,X69))
        | ~ r2_hidden(X69,sK7)
        | ~ r2_hidden(X68,sK7) )
    | spl11_1 ),
    inference(subsumption_resolution,[],[f475,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f475,plain,
    ( ! [X68,X69] :
        ( k1_xboole_0 != k5_xboole_0(k4_enumset1(X68,X68,X68,X68,X68,X69),k4_enumset1(X68,X68,X68,X68,X68,X69))
        | ~ sP4(sK5,sK5,sK6,k4_enumset1(X68,X68,X68,X68,X68,X69))
        | ~ r2_hidden(X69,sK7)
        | ~ r2_hidden(X68,sK7) )
    | spl11_1 ),
    inference(superposition,[],[f397,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X2) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f99,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f98])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f397,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k5_xboole_0(X4,k3_xboole_0(X4,sK7))
        | ~ sP4(sK5,sK5,sK6,X4) )
    | spl11_1 ),
    inference(superposition,[],[f390,f63])).

fof(f390,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k5_xboole_0(X6,k3_xboole_0(sK7,X6))
        | ~ sP4(sK5,sK5,sK6,X6) )
    | spl11_1 ),
    inference(superposition,[],[f142,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f95,f98])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f142,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)))
    | spl11_1 ),
    inference(forward_demodulation,[],[f114,f63])).

fof(f114,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f155,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f147,f152])).

fof(f147,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f143,f60])).

fof(f60,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f67,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f125,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f102,f116,f112])).

fof(f102,plain,
    ( r2_hidden(sK5,sK7)
    | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f57,f65,f99])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,
    ( r2_hidden(sK5,sK7)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_hidden(sK6,sK7)
      | ~ r2_hidden(sK5,sK7)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
    & ( ( r2_hidden(sK6,sK7)
        & r2_hidden(sK5,sK7) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK6,sK7)
        | ~ r2_hidden(sK5,sK7)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
      & ( ( r2_hidden(sK6,sK7)
          & r2_hidden(sK5,sK7) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f124,plain,
    ( spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f101,f120,f112])).

fof(f101,plain,
    ( r2_hidden(sK6,sK7)
    | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f58,f65,f99])).

fof(f58,plain,
    ( r2_hidden(sK6,sK7)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f100,f120,f116,f112])).

fof(f100,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ r2_hidden(sK5,sK7)
    | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f59,f65,f99])).

fof(f59,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ r2_hidden(sK5,sK7)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:19:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (24289)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.48  % (24297)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (24287)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (24285)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (24292)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (24284)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (24296)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (24304)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (24295)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (24315)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (24283)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (24305)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (24306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (24302)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (24286)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24298)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (24311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (24314)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (24313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (24308)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (24303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (24290)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (24299)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (24312)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (24301)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (24301)Refutation not found, incomplete strategy% (24301)------------------------------
% 1.50/0.55  % (24301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (24301)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (24301)Memory used [KB]: 10746
% 1.50/0.55  % (24301)Time elapsed: 0.150 s
% 1.50/0.55  % (24301)------------------------------
% 1.50/0.55  % (24301)------------------------------
% 1.50/0.56  % (24293)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (24300)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.56  % (24294)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (24291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.57  % (24309)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.57  % (24313)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f609,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f123,f124,f125,f155,f481,f607,f608])).
% 1.60/0.57  fof(f608,plain,(
% 1.60/0.57    spl11_3 | ~spl11_1 | ~spl11_5),
% 1.60/0.57    inference(avatar_split_clause,[],[f600,f152,f112,f120])).
% 1.60/0.57  fof(f120,plain,(
% 1.60/0.57    spl11_3 <=> r2_hidden(sK6,sK7)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.60/0.57  fof(f112,plain,(
% 1.60/0.57    spl11_1 <=> k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.60/0.57  fof(f152,plain,(
% 1.60/0.57    spl11_5 <=> ! [X9] : ~r2_hidden(X9,k1_xboole_0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.60/0.57  fof(f600,plain,(
% 1.60/0.57    r2_hidden(sK6,sK7) | (~spl11_1 | ~spl11_5)),
% 1.60/0.57    inference(resolution,[],[f595,f107])).
% 1.60/0.57  fof(f107,plain,(
% 1.60/0.57    ( ! [X2,X3,X1] : (sP3(X1,X1,X2,X3)) )),
% 1.60/0.57    inference(equality_resolution,[],[f93])).
% 1.60/0.57  fof(f93,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f55])).
% 1.60/0.57  fof(f55,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 1.60/0.57    inference(rectify,[],[f54])).
% 1.60/0.57  fof(f54,plain,(
% 1.60/0.57    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 1.60/0.57    inference(flattening,[],[f53])).
% 1.60/0.57  fof(f53,plain,(
% 1.60/0.57    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 1.60/0.57    inference(nnf_transformation,[],[f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.60/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.60/0.57  fof(f595,plain,(
% 1.60/0.57    ( ! [X0] : (~sP3(X0,sK6,sK5,sK5) | r2_hidden(X0,sK7)) ) | (~spl11_1 | ~spl11_5)),
% 1.60/0.57    inference(resolution,[],[f591,f348])).
% 1.60/0.57  fof(f348,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k4_enumset1(X3,X3,X3,X3,X2,X1)) | ~sP3(X0,X1,X2,X3)) )),
% 1.60/0.57    inference(resolution,[],[f87,f110])).
% 1.60/0.57  fof(f110,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))) )),
% 1.60/0.57    inference(equality_resolution,[],[f105])).
% 1.60/0.57  fof(f105,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 1.60/0.57    inference(definition_unfolding,[],[f94,f98])).
% 1.60/0.57  fof(f98,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f68,f97])).
% 1.60/0.57  fof(f97,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f85,f96])).
% 1.60/0.57  fof(f96,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.60/0.57  fof(f85,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.57  fof(f94,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.57    inference(cnf_transformation,[],[f56])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.57    inference(nnf_transformation,[],[f31])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 1.60/0.57    inference(definition_folding,[],[f23,f30,f29])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 1.60/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.60/0.57    inference(ennf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.60/0.57  fof(f87,plain,(
% 1.60/0.57    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f52])).
% 1.60/0.57  fof(f52,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f50,f51])).
% 1.60/0.57  fof(f51,plain,(
% 1.60/0.57    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP3(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3))))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 1.60/0.57    inference(rectify,[],[f49])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 1.60/0.57    inference(nnf_transformation,[],[f30])).
% 1.60/0.57  fof(f591,plain,(
% 1.60/0.57    ( ! [X2] : (~r2_hidden(X2,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) | r2_hidden(X2,sK7)) ) | (~spl11_1 | ~spl11_5)),
% 1.60/0.57    inference(resolution,[],[f560,f75])).
% 1.60/0.57  fof(f75,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f44])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.60/0.57    inference(rectify,[],[f43])).
% 1.60/0.57  fof(f43,plain,(
% 1.60/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.60/0.57    inference(flattening,[],[f42])).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.60/0.57    inference(nnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.60/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.60/0.57  fof(f560,plain,(
% 1.60/0.57    ( ! [X1] : (sP0(sK7,X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)) | ~r2_hidden(X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) ) | (~spl11_1 | ~spl11_5)),
% 1.60/0.57    inference(resolution,[],[f507,f252])).
% 1.60/0.57  fof(f252,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,X5)) | sP0(X4,X3,X5)) )),
% 1.60/0.57    inference(resolution,[],[f70,f130])).
% 1.60/0.57  fof(f130,plain,(
% 1.60/0.57    ( ! [X2,X1] : (sP1(X1,X2,k3_xboole_0(X2,X1))) )),
% 1.60/0.57    inference(superposition,[],[f106,f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.58  fof(f106,plain,(
% 1.60/0.58    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(equality_resolution,[],[f77])).
% 1.60/0.58  fof(f77,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.60/0.58    inference(cnf_transformation,[],[f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.60/0.58    inference(nnf_transformation,[],[f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.60/0.58    inference(definition_folding,[],[f2,f25,f24])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.60/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.60/0.58  fof(f2,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.60/0.58  fof(f70,plain,(
% 1.60/0.58    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f41])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP0(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.58    inference(rectify,[],[f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.58    inference(nnf_transformation,[],[f25])).
% 1.60/0.58  fof(f507,plain,(
% 1.60/0.58    ( ! [X1] : (r2_hidden(X1,k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) | ~r2_hidden(X1,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) ) | (~spl11_1 | ~spl11_5)),
% 1.60/0.58    inference(resolution,[],[f488,f81])).
% 1.60/0.58  fof(f81,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f47])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 1.60/0.58    inference(rectify,[],[f46])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 1.60/0.58    inference(nnf_transformation,[],[f27])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.60/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.60/0.58  fof(f488,plain,(
% 1.60/0.58    ( ! [X0] : (~sP2(k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) ) | (~spl11_1 | ~spl11_5)),
% 1.60/0.58    inference(subsumption_resolution,[],[f486,f153])).
% 1.60/0.58  fof(f153,plain,(
% 1.60/0.58    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0)) ) | ~spl11_5),
% 1.60/0.58    inference(avatar_component_clause,[],[f152])).
% 1.60/0.58  fof(f486,plain,(
% 1.60/0.58    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP2(k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6)),X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) ) | ~spl11_1),
% 1.60/0.58    inference(superposition,[],[f84,f482])).
% 1.60/0.58  fof(f482,plain,(
% 1.60/0.58    k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) | ~spl11_1),
% 1.60/0.58    inference(forward_demodulation,[],[f113,f63])).
% 1.60/0.58  fof(f113,plain,(
% 1.60/0.58    k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) | ~spl11_1),
% 1.60/0.58    inference(avatar_component_clause,[],[f112])).
% 1.60/0.58  fof(f84,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f48])).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.60/0.58    inference(nnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 1.60/0.58    inference(definition_folding,[],[f22,f27])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.60/0.58    inference(ennf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.60/0.58  fof(f607,plain,(
% 1.60/0.58    spl11_2 | ~spl11_1 | ~spl11_5),
% 1.60/0.58    inference(avatar_split_clause,[],[f601,f152,f112,f116])).
% 1.60/0.58  fof(f116,plain,(
% 1.60/0.58    spl11_2 <=> r2_hidden(sK5,sK7)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.60/0.58  fof(f601,plain,(
% 1.60/0.58    r2_hidden(sK5,sK7) | (~spl11_1 | ~spl11_5)),
% 1.60/0.58    inference(resolution,[],[f595,f108])).
% 1.60/0.58  fof(f108,plain,(
% 1.60/0.58    ( ! [X2,X3,X1] : (sP3(X2,X1,X2,X3)) )),
% 1.60/0.58    inference(equality_resolution,[],[f92])).
% 1.60/0.58  fof(f92,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X2) )),
% 1.60/0.58    inference(cnf_transformation,[],[f55])).
% 1.60/0.58  fof(f481,plain,(
% 1.60/0.58    spl11_1 | ~spl11_2 | ~spl11_3),
% 1.60/0.58    inference(avatar_contradiction_clause,[],[f480])).
% 1.60/0.58  fof(f480,plain,(
% 1.60/0.58    $false | (spl11_1 | ~spl11_2 | ~spl11_3)),
% 1.60/0.58    inference(subsumption_resolution,[],[f479,f117])).
% 1.60/0.58  fof(f117,plain,(
% 1.60/0.58    r2_hidden(sK5,sK7) | ~spl11_2),
% 1.60/0.58    inference(avatar_component_clause,[],[f116])).
% 1.60/0.58  fof(f479,plain,(
% 1.60/0.58    ~r2_hidden(sK5,sK7) | (spl11_1 | ~spl11_3)),
% 1.60/0.58    inference(subsumption_resolution,[],[f477,f121])).
% 1.60/0.58  fof(f121,plain,(
% 1.60/0.58    r2_hidden(sK6,sK7) | ~spl11_3),
% 1.60/0.58    inference(avatar_component_clause,[],[f120])).
% 1.60/0.58  fof(f477,plain,(
% 1.60/0.58    ~r2_hidden(sK6,sK7) | ~r2_hidden(sK5,sK7) | spl11_1),
% 1.60/0.58    inference(resolution,[],[f476,f110])).
% 1.60/0.58  fof(f476,plain,(
% 1.60/0.58    ( ! [X68,X69] : (~sP4(sK5,sK5,sK6,k4_enumset1(X68,X68,X68,X68,X68,X69)) | ~r2_hidden(X69,sK7) | ~r2_hidden(X68,sK7)) ) | spl11_1),
% 1.60/0.58    inference(subsumption_resolution,[],[f475,f62])).
% 1.60/0.58  fof(f62,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.60/0.58  fof(f475,plain,(
% 1.60/0.58    ( ! [X68,X69] : (k1_xboole_0 != k5_xboole_0(k4_enumset1(X68,X68,X68,X68,X68,X69),k4_enumset1(X68,X68,X68,X68,X68,X69)) | ~sP4(sK5,sK5,sK6,k4_enumset1(X68,X68,X68,X68,X68,X69)) | ~r2_hidden(X69,sK7) | ~r2_hidden(X68,sK7)) ) | spl11_1),
% 1.60/0.58    inference(superposition,[],[f397,f103])).
% 1.60/0.58  fof(f103,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X2) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f69,f99,f99])).
% 1.60/0.58  fof(f99,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f64,f98])).
% 1.60/0.58  fof(f64,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.58  fof(f69,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f21])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.60/0.58    inference(flattening,[],[f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.60/0.58  fof(f397,plain,(
% 1.60/0.58    ( ! [X4] : (k1_xboole_0 != k5_xboole_0(X4,k3_xboole_0(X4,sK7)) | ~sP4(sK5,sK5,sK6,X4)) ) | spl11_1),
% 1.60/0.58    inference(superposition,[],[f390,f63])).
% 1.60/0.58  fof(f390,plain,(
% 1.60/0.58    ( ! [X6] : (k1_xboole_0 != k5_xboole_0(X6,k3_xboole_0(sK7,X6)) | ~sP4(sK5,sK5,sK6,X6)) ) | spl11_1),
% 1.60/0.58    inference(superposition,[],[f142,f104])).
% 1.60/0.58  fof(f104,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f95,f98])).
% 1.60/0.58  fof(f95,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f56])).
% 1.60/0.58  fof(f142,plain,(
% 1.60/0.58    k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(sK7,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6))) | spl11_1),
% 1.60/0.58    inference(forward_demodulation,[],[f114,f63])).
% 1.60/0.58  fof(f114,plain,(
% 1.60/0.58    k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7)) | spl11_1),
% 1.60/0.58    inference(avatar_component_clause,[],[f112])).
% 1.60/0.58  fof(f155,plain,(
% 1.60/0.58    spl11_5),
% 1.60/0.58    inference(avatar_split_clause,[],[f147,f152])).
% 1.60/0.58  fof(f147,plain,(
% 1.60/0.58    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f143,f60])).
% 1.60/0.58  fof(f60,plain,(
% 1.60/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.60/0.58  fof(f143,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.60/0.58    inference(superposition,[],[f67,f61])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.60/0.58  fof(f67,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f37])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f19,f36])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK8(X0,X1),k3_xboole_0(X0,X1)))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f19,plain,(
% 1.60/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,plain,(
% 1.60/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(rectify,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.60/0.58  fof(f125,plain,(
% 1.60/0.58    spl11_1 | spl11_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f102,f116,f112])).
% 1.60/0.58  fof(f102,plain,(
% 1.60/0.58    r2_hidden(sK5,sK7) | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 1.60/0.58    inference(definition_unfolding,[],[f57,f65,f99])).
% 1.60/0.58  fof(f65,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.58  fof(f57,plain,(
% 1.60/0.58    r2_hidden(sK5,sK7) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 1.60/0.58    inference(cnf_transformation,[],[f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    (~r2_hidden(sK6,sK7) | ~r2_hidden(sK5,sK7) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & ((r2_hidden(sK6,sK7) & r2_hidden(sK5,sK7)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK6,sK7) | ~r2_hidden(sK5,sK7) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & ((r2_hidden(sK6,sK7) & r2_hidden(sK5,sK7)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.60/0.58    inference(flattening,[],[f32])).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.60/0.58    inference(nnf_transformation,[],[f18])).
% 1.60/0.58  fof(f18,plain,(
% 1.60/0.58    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.60/0.58    inference(ennf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,negated_conjecture,(
% 1.60/0.58    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.60/0.58    inference(negated_conjecture,[],[f15])).
% 1.60/0.58  fof(f15,conjecture,(
% 1.60/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.60/0.58  fof(f124,plain,(
% 1.60/0.58    spl11_1 | spl11_3),
% 1.60/0.58    inference(avatar_split_clause,[],[f101,f120,f112])).
% 1.60/0.58  fof(f101,plain,(
% 1.60/0.58    r2_hidden(sK6,sK7) | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 1.60/0.58    inference(definition_unfolding,[],[f58,f65,f99])).
% 1.60/0.58  fof(f58,plain,(
% 1.60/0.58    r2_hidden(sK6,sK7) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 1.60/0.58    inference(cnf_transformation,[],[f35])).
% 1.60/0.58  fof(f123,plain,(
% 1.60/0.58    ~spl11_1 | ~spl11_2 | ~spl11_3),
% 1.60/0.58    inference(avatar_split_clause,[],[f100,f120,f116,f112])).
% 1.60/0.58  fof(f100,plain,(
% 1.60/0.58    ~r2_hidden(sK6,sK7) | ~r2_hidden(sK5,sK7) | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),k3_xboole_0(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK6),sK7))),
% 1.60/0.58    inference(definition_unfolding,[],[f59,f65,f99])).
% 1.60/0.58  fof(f59,plain,(
% 1.60/0.58    ~r2_hidden(sK6,sK7) | ~r2_hidden(sK5,sK7) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 1.60/0.58    inference(cnf_transformation,[],[f35])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (24313)------------------------------
% 1.60/0.58  % (24313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (24313)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (24313)Memory used [KB]: 6524
% 1.60/0.58  % (24313)Time elapsed: 0.175 s
% 1.60/0.58  % (24313)------------------------------
% 1.60/0.58  % (24313)------------------------------
% 1.60/0.58  % (24279)Success in time 0.214 s
%------------------------------------------------------------------------------
