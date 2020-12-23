%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 204 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  338 ( 700 expanded)
%              Number of equality atoms :   52 ( 119 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f98,f175,f178,f184,f198,f200])).

fof(f200,plain,
    ( spl9_3
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f192,f85,f93])).

fof(f93,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f85,plain,
    ( spl9_1
  <=> r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f192,plain,
    ( r2_hidden(sK5,sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f190,f80])).

fof(f80,plain,(
    ! [X2,X3,X1] : sP2(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK5,sK4,sK4)
        | r2_hidden(X0,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f145])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_enumset1(X3,X3,X2,X1))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f63,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f70,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f15,f20,f19])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
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

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ sP2(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK5))
        | r2_hidden(X0,sK6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f86,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f111,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

% (13801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f32,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( sP0(X5,X3,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f53,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f79,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f17,f16])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f86,plain,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f198,plain,
    ( spl9_2
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f193,f85,f89])).

fof(f89,plain,
    ( spl9_2
  <=> r2_hidden(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f193,plain,
    ( r2_hidden(sK4,sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f190,f81])).

fof(f81,plain,(
    ! [X2,X3,X1] : sP2(X2,X1,X2,X3) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f184,plain,
    ( ~ spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f181,f172,f93])).

fof(f172,plain,
    ( spl9_5
  <=> r1_tarski(k1_tarski(sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f181,plain,
    ( ~ r2_hidden(sK5,sK6)
    | spl9_5 ),
    inference(resolution,[],[f174,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f174,plain,
    ( ~ r1_tarski(k1_tarski(sK5),sK6)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f178,plain,
    ( ~ spl9_2
    | spl9_4 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl9_2
    | spl9_4 ),
    inference(subsumption_resolution,[],[f176,f90])).

fof(f90,plain,
    ( r2_hidden(sK4,sK6)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f176,plain,
    ( ~ r2_hidden(sK4,sK6)
    | spl9_4 ),
    inference(resolution,[],[f170,f50])).

fof(f170,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK6)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl9_4
  <=> r1_tarski(k1_tarski(sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f175,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f163,f85,f172,f168])).

fof(f163,plain,
    ( ~ r1_tarski(k1_tarski(sK5),sK6)
    | ~ r1_tarski(k1_tarski(sK4),sK6)
    | spl9_1 ),
    inference(resolution,[],[f123,f87])).

fof(f87,plain,
    ( ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r1_tarski(k1_tarski(X1),X2)
      | ~ r1_tarski(k1_tarski(X0),X2) ) ),
    inference(superposition,[],[f52,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f98,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f75,f89,f85])).

fof(f75,plain,
    ( r2_hidden(sK4,sK6)
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f43,plain,
    ( r2_hidden(sK4,sK6)
    | r1_tarski(k2_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(sK5,sK6)
      | ~ r2_hidden(sK4,sK6)
      | ~ r1_tarski(k2_tarski(sK4,sK5),sK6) )
    & ( ( r2_hidden(sK5,sK6)
        & r2_hidden(sK4,sK6) )
      | r1_tarski(k2_tarski(sK4,sK5),sK6) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK5,sK6)
        | ~ r2_hidden(sK4,sK6)
        | ~ r1_tarski(k2_tarski(sK4,sK5),sK6) )
      & ( ( r2_hidden(sK5,sK6)
          & r2_hidden(sK4,sK6) )
        | r1_tarski(k2_tarski(sK4,sK5),sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f97,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f74,f93,f85])).

fof(f74,plain,
    ( r2_hidden(sK5,sK6)
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f44,plain,
    ( r2_hidden(sK5,sK6)
    | r1_tarski(k2_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f73,f93,f89,f85])).

fof(f73,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ r2_hidden(sK4,sK6)
    | ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f45,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ r2_hidden(sK4,sK6)
    | ~ r1_tarski(k2_tarski(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (13795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (13792)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13814)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (13807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (13797)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13794)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13807)Refutation not found, incomplete strategy% (13807)------------------------------
% 0.22/0.53  % (13807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13807)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13808)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (13807)Memory used [KB]: 6140
% 0.22/0.53  % (13807)Time elapsed: 0.006 s
% 0.22/0.53  % (13807)------------------------------
% 0.22/0.53  % (13807)------------------------------
% 0.22/0.53  % (13796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (13819)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (13800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13800)Refutation not found, incomplete strategy% (13800)------------------------------
% 0.22/0.53  % (13800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13800)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13800)Memory used [KB]: 10618
% 0.22/0.53  % (13800)Time elapsed: 0.078 s
% 0.22/0.53  % (13800)------------------------------
% 0.22/0.53  % (13800)------------------------------
% 0.22/0.53  % (13806)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13819)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f96,f97,f98,f175,f178,f184,f198,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl9_3 | ~spl9_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f192,f85,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl9_3 <=> r2_hidden(sK5,sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl9_1 <=> r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    r2_hidden(sK5,sK6) | ~spl9_1),
% 0.22/0.54    inference(resolution,[],[f190,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X2,X3,X1] : (sP2(X1,X1,X2,X3)) )),
% 0.22/0.54    inference(equality_resolution,[],[f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 0.22/0.54    inference(flattening,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    ( ! [X0] : (~sP2(X0,sK5,sK4,sK4) | r2_hidden(X0,sK6)) ) | ~spl9_1),
% 0.22/0.54    inference(resolution,[],[f185,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X3,X3,X2,X1)) | ~sP2(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(resolution,[],[f63,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k2_enumset1(X0,X0,X1,X2))) )),
% 0.22/0.54    inference(equality_resolution,[],[f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f70,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 0.22/0.54    inference(definition_folding,[],[f15,f20,f19])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~sP2(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sP2(sK8(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK5)) | r2_hidden(X0,sK6)) ) | ~spl9_1),
% 0.22/0.54    inference(resolution,[],[f86,f114])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(resolution,[],[f111,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  % (13801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (sP0(X5,X3,X4) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,X5)) )),
% 0.22/0.54    inference(resolution,[],[f53,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP1(X0,X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(superposition,[],[f79,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.22/0.54    inference(definition_folding,[],[f1,f17,f16])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f17])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) | ~spl9_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f85])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    spl9_2 | ~spl9_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f193,f85,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl9_2 <=> r2_hidden(sK4,sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    r2_hidden(sK4,sK6) | ~spl9_1),
% 0.22/0.54    inference(resolution,[],[f190,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X2,X3,X1] : (sP2(X2,X1,X2,X3)) )),
% 0.22/0.54    inference(equality_resolution,[],[f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | X0 != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ~spl9_3 | spl9_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f181,f172,f93])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl9_5 <=> r1_tarski(k1_tarski(sK5),sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK6) | spl9_5),
% 0.22/0.54    inference(resolution,[],[f174,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK5),sK6) | spl9_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f172])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ~spl9_2 | spl9_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    $false | (~spl9_2 | spl9_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f176,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    r2_hidden(sK4,sK6) | ~spl9_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f89])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    ~r2_hidden(sK4,sK6) | spl9_4),
% 0.22/0.54    inference(resolution,[],[f170,f50])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK4),sK6) | spl9_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f168])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    spl9_4 <=> r1_tarski(k1_tarski(sK4),sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~spl9_4 | ~spl9_5 | spl9_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f163,f85,f172,f168])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK5),sK6) | ~r1_tarski(k1_tarski(sK4),sK6) | spl9_1),
% 0.22/0.54    inference(resolution,[],[f123,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6) | spl9_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f85])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r1_tarski(k1_tarski(X1),X2) | ~r1_tarski(k1_tarski(X0),X2)) )),
% 0.22/0.54    inference(superposition,[],[f52,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f47,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f51])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl9_1 | spl9_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f75,f89,f85])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    r2_hidden(sK4,sK6) | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f72])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    r2_hidden(sK4,sK6) | r1_tarski(k2_tarski(sK4,sK5),sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    (~r2_hidden(sK5,sK6) | ~r2_hidden(sK4,sK6) | ~r1_tarski(k2_tarski(sK4,sK5),sK6)) & ((r2_hidden(sK5,sK6) & r2_hidden(sK4,sK6)) | r1_tarski(k2_tarski(sK4,sK5),sK6))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK5,sK6) | ~r2_hidden(sK4,sK6) | ~r1_tarski(k2_tarski(sK4,sK5),sK6)) & ((r2_hidden(sK5,sK6) & r2_hidden(sK4,sK6)) | r1_tarski(k2_tarski(sK4,sK5),sK6)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    spl9_1 | spl9_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f74,f93,f85])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    r2_hidden(sK5,sK6) | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f72])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    r2_hidden(sK5,sK6) | r1_tarski(k2_tarski(sK4,sK5),sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f73,f93,f89,f85])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK6) | ~r2_hidden(sK4,sK6) | ~r1_tarski(k2_enumset1(sK4,sK4,sK4,sK5),sK6)),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f72])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~r2_hidden(sK5,sK6) | ~r2_hidden(sK4,sK6) | ~r1_tarski(k2_tarski(sK4,sK5),sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (13819)------------------------------
% 0.22/0.54  % (13819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13819)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (13819)Memory used [KB]: 6268
% 0.22/0.54  % (13819)Time elapsed: 0.084 s
% 0.22/0.54  % (13819)------------------------------
% 0.22/0.54  % (13819)------------------------------
% 0.22/0.54  % (13793)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (13784)Success in time 0.173 s
%------------------------------------------------------------------------------
