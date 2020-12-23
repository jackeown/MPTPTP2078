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
% DateTime   : Thu Dec  3 12:41:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 187 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 625 expanded)
%              Number of equality atoms :   86 ( 208 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f73,f78,f155,f157,f174,f181,f187])).

fof(f187,plain,
    ( spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f183,f72])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | spl8_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f183,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(resolution,[],[f170,f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f79])).

fof(f79,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f170,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_6
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f181,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f177,f62])).

fof(f62,plain,
    ( k1_xboole_0 != sK3
    | spl8_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f177,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_7 ),
    inference(resolution,[],[f173,f106])).

fof(f173,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_7
  <=> ! [X6] : ~ r2_hidden(X6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f174,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f167,f75,f172,f169])).

fof(f75,plain,
    ( spl8_5
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f167,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f162,f79])).

fof(f162,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k4_tarski(X5,X6),k1_xboole_0)
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2) )
    | ~ spl8_5 ),
    inference(superposition,[],[f51,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f157,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f68,f130])).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f110,f83])).

fof(f83,plain,(
    ! [X0,X1] : ~ sP0(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f43,f79])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
          & r2_hidden(sK7(X0,X1,X2),X1)
          & r2_hidden(sK6(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

% (23036)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP0(sK4(k2_zfmisc_1(X0,X1),k1_xboole_0),X1,X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f106,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f12,f11])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl8_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f155,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f58,f131])).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0) ),
    inference(resolution,[],[f110,f85])).

fof(f85,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f44,f79])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f78,plain,
    ( spl8_5
    | spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f32,f60,f70,f75])).

fof(f32,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2 )
      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2 )
        | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(inner_rewriting,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f54,f60,f56])).

fof(f54,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:16:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (23034)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (23042)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (23023)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (23023)Refutation not found, incomplete strategy% (23023)------------------------------
% 0.22/0.52  % (23023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23023)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23023)Memory used [KB]: 6268
% 0.22/0.52  % (23023)Time elapsed: 0.108 s
% 0.22/0.52  % (23023)------------------------------
% 0.22/0.52  % (23023)------------------------------
% 0.22/0.52  % (23026)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (23021)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23022)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (23021)Refutation not found, incomplete strategy% (23021)------------------------------
% 0.22/0.54  % (23021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23021)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23021)Memory used [KB]: 10618
% 0.22/0.54  % (23021)Time elapsed: 0.116 s
% 0.22/0.54  % (23021)------------------------------
% 0.22/0.54  % (23021)------------------------------
% 0.22/0.54  % (23037)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (23044)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (23044)Refutation not found, incomplete strategy% (23044)------------------------------
% 0.22/0.54  % (23044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23044)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23044)Memory used [KB]: 6268
% 0.22/0.54  % (23044)Time elapsed: 0.129 s
% 0.22/0.54  % (23044)------------------------------
% 0.22/0.54  % (23044)------------------------------
% 0.22/0.54  % (23019)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (23019)Refutation not found, incomplete strategy% (23019)------------------------------
% 0.22/0.54  % (23019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23019)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23019)Memory used [KB]: 1663
% 0.22/0.54  % (23019)Time elapsed: 0.122 s
% 0.22/0.54  % (23019)------------------------------
% 0.22/0.54  % (23019)------------------------------
% 0.22/0.54  % (23020)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23041)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (23046)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (23045)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (23035)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (23046)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f63,f73,f78,f155,f157,f174,f181,f187])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    spl8_4 | ~spl8_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    $false | (spl8_4 | ~spl8_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f183,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    k1_xboole_0 != sK2 | spl8_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    spl8_4 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl8_6),
% 0.22/0.55    inference(resolution,[],[f170,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(resolution,[],[f36,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f38,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.22/0.55    inference(nnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    ( ! [X5] : (~r2_hidden(X5,sK2)) ) | ~spl8_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f169])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    spl8_6 <=> ! [X5] : ~r2_hidden(X5,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    spl8_2 | ~spl8_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    $false | (spl8_2 | ~spl8_7)),
% 0.22/0.55    inference(subsumption_resolution,[],[f177,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    k1_xboole_0 != sK3 | spl8_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    spl8_2 <=> k1_xboole_0 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~spl8_7),
% 0.22/0.55    inference(resolution,[],[f173,f106])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ( ! [X6] : (~r2_hidden(X6,sK3)) ) | ~spl8_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f172])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    spl8_7 <=> ! [X6] : ~r2_hidden(X6,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    spl8_6 | spl8_7 | ~spl8_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f167,f75,f172,f169])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    spl8_5 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ( ! [X6,X5] : (~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2)) ) | ~spl8_5),
% 0.22/0.55    inference(subsumption_resolution,[],[f162,f79])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ( ! [X6,X5] : (r2_hidden(k4_tarski(X5,X6),k1_xboole_0) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2)) ) | ~spl8_5),
% 0.22/0.55    inference(superposition,[],[f51,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    k1_xboole_0 = k2_zfmisc_1(sK2,sK3) | ~spl8_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f75])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.55    inference(nnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    spl8_3),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    $false | spl8_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f68,f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f110,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~sP0(X0,X1,k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f43,f79])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f26,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  % (23036)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 0.22/0.55    inference(rectify,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 0.22/0.55    inference(nnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sP0(sK4(k2_zfmisc_1(X0,X1),k1_xboole_0),X1,X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f106,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP0(X0,X2,X1)) )),
% 0.22/0.55    inference(resolution,[],[f39,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.22/0.55    inference(definition_folding,[],[f3,f12,f11])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.55    inference(rectify,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.22/0.55    inference(nnf_transformation,[],[f12])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | spl8_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    spl8_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    spl8_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    $false | spl8_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f58,f131])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(X1,k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f110,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f44,f79])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | spl8_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    spl8_1 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl8_5 | spl8_4 | spl8_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f32,f60,f70,f75])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK3 & k1_xboole_0 != sK2) | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)) & (k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ~spl8_3 | ~spl8_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f64,f70,f66])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.22/0.55    inference(inner_rewriting,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    k1_xboole_0 != sK2 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~spl8_1 | ~spl8_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f60,f56])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)),
% 0.22/0.55    inference(inner_rewriting,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    k1_xboole_0 != sK3 | k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (23046)------------------------------
% 0.22/0.55  % (23046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23046)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (23046)Memory used [KB]: 6268
% 0.22/0.55  % (23046)Time elapsed: 0.129 s
% 0.22/0.55  % (23046)------------------------------
% 0.22/0.55  % (23046)------------------------------
% 0.22/0.55  % (23025)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (23038)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (23029)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (23040)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (23027)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (23029)Refutation not found, incomplete strategy% (23029)------------------------------
% 0.22/0.55  % (23029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23029)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23029)Memory used [KB]: 10618
% 0.22/0.55  % (23029)Time elapsed: 0.139 s
% 0.22/0.55  % (23029)------------------------------
% 0.22/0.55  % (23029)------------------------------
% 0.22/0.55  % (23040)Refutation not found, incomplete strategy% (23040)------------------------------
% 0.22/0.55  % (23040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23040)Memory used [KB]: 1663
% 0.22/0.55  % (23040)Time elapsed: 0.137 s
% 0.22/0.55  % (23040)------------------------------
% 0.22/0.55  % (23040)------------------------------
% 0.22/0.55  % (23028)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (23027)Refutation not found, incomplete strategy% (23027)------------------------------
% 0.22/0.55  % (23027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23043)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (23047)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (23033)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (23032)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (23031)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (23018)Success in time 0.19 s
%------------------------------------------------------------------------------
