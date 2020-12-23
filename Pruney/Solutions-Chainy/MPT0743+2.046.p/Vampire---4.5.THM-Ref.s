%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 568 expanded)
%              Number of leaves         :   36 ( 190 expanded)
%              Depth                    :   17
%              Number of atoms          :  646 (1704 expanded)
%              Number of equality atoms :  121 ( 385 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f618,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f142,f195,f270,f280,f314,f333,f441,f554,f563,f567,f575,f593,f617])).

fof(f617,plain,
    ( ~ spl8_5
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl8_5
    | spl8_7 ),
    inference(subsumption_resolution,[],[f614,f186])).

fof(f186,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_5
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f614,plain,
    ( ~ r2_hidden(sK5,sK4)
    | spl8_7 ),
    inference(resolution,[],[f597,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f597,plain,
    ( ~ sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK4)
    | spl8_7 ),
    inference(resolution,[],[f278,f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f123,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f123,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f87,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f111])).

% (27091)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (27084)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (27086)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (27078)Refutation not found, incomplete strategy% (27078)------------------------------
% (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27078)Termination reason: Refutation not found, incomplete strategy

% (27078)Memory used [KB]: 11257
% (27078)Time elapsed: 0.178 s
% (27078)------------------------------
% (27078)------------------------------
fof(f111,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f89,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f90,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f91,f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f34,f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f278,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl8_7
  <=> r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f593,plain,
    ( ~ spl8_7
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f589,f158,f277])).

fof(f158,plain,
    ( spl8_4
  <=> r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f589,plain,
    ( ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_4 ),
    inference(resolution,[],[f160,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f160,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f575,plain,
    ( spl8_4
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f574,f557,f154,f138,f158])).

fof(f138,plain,
    ( spl8_2
  <=> r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f154,plain,
    ( spl8_3
  <=> v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f557,plain,
    ( spl8_16
  <=> v3_ordinal1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f574,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f573,f155])).

fof(f155,plain,
    ( v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f573,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f569,f558])).

fof(f558,plain,
    ( v3_ordinal1(sK5)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f557])).

fof(f569,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_2 ),
    inference(resolution,[],[f139,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f139,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f567,plain,
    ( spl8_5
    | spl8_6
    | spl8_1
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f566,f557,f134,f188,f184])).

fof(f188,plain,
    ( spl8_6
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f134,plain,
    ( spl8_1
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f566,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4)
    | spl8_1
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f565,f558])).

fof(f565,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f564,f62])).

fof(f62,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK4),sK5)
      | ~ r2_hidden(sK4,sK5) )
    & ( r1_ordinal1(k1_ordinal1(sK4),sK5)
      | r2_hidden(sK4,sK5) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK4),X1)
            | ~ r2_hidden(sK4,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK4),X1)
            | r2_hidden(sK4,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK4),X1)
          | ~ r2_hidden(sK4,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK4),X1)
          | r2_hidden(sK4,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK4),sK5)
        | ~ r2_hidden(sK4,sK5) )
      & ( r1_ordinal1(k1_ordinal1(sK4),sK5)
        | r2_hidden(sK4,sK5) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f564,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(sK5)
    | spl8_1 ),
    inference(resolution,[],[f136,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f136,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f563,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f63,f557])).

fof(f63,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f554,plain,(
    spl8_12 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | spl8_12 ),
    inference(subsumption_resolution,[],[f549,f124])).

fof(f124,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP2(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f549,plain,
    ( ~ sP2(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | spl8_12 ),
    inference(resolution,[],[f390,f364])).

fof(f364,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl8_12
  <=> r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f390,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(resolution,[],[f94,f132])).

fof(f132,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP3(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f32,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | ~ sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X8) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f55,f56])).

fof(f56,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f441,plain,
    ( ~ spl8_12
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f438,f188,f158,f363])).

fof(f438,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f422,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f422,plain,
    ( ~ sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4,sK4)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f386,f201])).

fof(f386,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f383,f78])).

fof(f383,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK4)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f160,f190])).

fof(f190,plain,
    ( sK4 = sK5
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f333,plain,
    ( ~ spl8_1
    | spl8_5
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl8_1
    | spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f329,f135])).

fof(f135,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f329,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl8_5
    | ~ spl8_7 ),
    inference(resolution,[],[f328,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f119,f78])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f114])).

fof(f114,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f112])).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f328,plain,
    ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f326,f185])).

fof(f185,plain,
    ( ~ r2_hidden(sK5,sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f326,plain,
    ( r2_hidden(sK5,sK4)
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f319,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f319,plain,
    ( sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK4)
    | ~ spl8_7 ),
    inference(resolution,[],[f279,f202])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))
      | sP0(X5,X3,X4) ) ),
    inference(resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f279,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f277])).

fof(f314,plain,
    ( spl8_7
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f313,f158,f154,f277])).

fof(f313,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_3
    | spl8_4 ),
    inference(subsumption_resolution,[],[f312,f155])).

fof(f312,plain,
    ( ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_4 ),
    inference(subsumption_resolution,[],[f303,f63])).

fof(f303,plain,
    ( ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_4 ),
    inference(resolution,[],[f159,f150])).

fof(f150,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X3,X2)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f74,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f159,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f280,plain,
    ( ~ spl8_3
    | spl8_7
    | spl8_2 ),
    inference(avatar_split_clause,[],[f275,f138,f277,f154])).

fof(f275,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f200,f63])).

fof(f200,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_2 ),
    inference(resolution,[],[f140,f69])).

fof(f140,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f270,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f268,f132])).

fof(f268,plain,
    ( ~ sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl8_3 ),
    inference(subsumption_resolution,[],[f262,f62])).

fof(f262,plain,
    ( ~ v3_ordinal1(sK4)
    | ~ sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl8_3 ),
    inference(resolution,[],[f118,f236])).

fof(f236,plain,
    ( ! [X5] :
        ( ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X5)))
        | ~ sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,X5) )
    | spl8_3 ),
    inference(superposition,[],[f156,f107])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
      | ~ sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f156,plain,
    ( ~ v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f118,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f68,f115])).

fof(f115,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f67,f113,f114])).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f68,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f195,plain,
    ( ~ spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f194,f134,f184])).

fof(f194,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f193,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f192,plain,
    ( ~ v3_ordinal1(sK4)
    | ~ r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f135,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f170,f78])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f169,f78])).

fof(f169,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f151,f74])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f74,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f142,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f117,f138,f134])).

fof(f117,plain,
    ( r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(definition_unfolding,[],[f64,f115])).

fof(f64,plain,
    ( r1_ordinal1(k1_ordinal1(sK4),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f116,f138,f134])).

fof(f116,plain,
    ( ~ r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(definition_unfolding,[],[f65,f115])).

fof(f65,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK4),sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (27068)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (27092)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (27075)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (27072)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27078)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.52  % (27080)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (27071)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.53  % (27077)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.53  % (27079)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.54  % (27096)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.26/0.54  % (27069)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (27090)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.54  % (27082)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.54  % (27089)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.54  % (27097)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (27090)Refutation not found, incomplete strategy% (27090)------------------------------
% 1.41/0.54  % (27090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (27090)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (27090)Memory used [KB]: 1791
% 1.41/0.54  % (27090)Time elapsed: 0.092 s
% 1.41/0.54  % (27090)------------------------------
% 1.41/0.54  % (27090)------------------------------
% 1.41/0.55  % (27073)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.55  % (27087)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (27088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (27083)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.55  % (27074)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (27070)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (27085)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (27095)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  % (27070)Refutation not found, incomplete strategy% (27070)------------------------------
% 1.41/0.55  % (27070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (27070)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (27070)Memory used [KB]: 10746
% 1.41/0.55  % (27070)Time elapsed: 0.148 s
% 1.41/0.55  % (27070)------------------------------
% 1.41/0.55  % (27070)------------------------------
% 1.41/0.56  % (27076)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (27094)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.57  % (27098)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.57  % (27093)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.57  % (27096)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.57  % SZS output start Proof for theBenchmark
% 1.41/0.57  fof(f618,plain,(
% 1.41/0.57    $false),
% 1.41/0.57    inference(avatar_sat_refutation,[],[f141,f142,f195,f270,f280,f314,f333,f441,f554,f563,f567,f575,f593,f617])).
% 1.41/0.57  fof(f617,plain,(
% 1.41/0.57    ~spl8_5 | spl8_7),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f616])).
% 1.41/0.57  fof(f616,plain,(
% 1.41/0.57    $false | (~spl8_5 | spl8_7)),
% 1.41/0.57    inference(subsumption_resolution,[],[f614,f186])).
% 1.41/0.57  fof(f186,plain,(
% 1.41/0.57    r2_hidden(sK5,sK4) | ~spl8_5),
% 1.41/0.57    inference(avatar_component_clause,[],[f184])).
% 1.41/0.57  fof(f184,plain,(
% 1.41/0.57    spl8_5 <=> r2_hidden(sK5,sK4)),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.41/0.57  fof(f614,plain,(
% 1.41/0.57    ~r2_hidden(sK5,sK4) | spl8_7),
% 1.41/0.57    inference(resolution,[],[f597,f85])).
% 1.41/0.57  fof(f85,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f52])).
% 1.41/0.57  fof(f52,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 1.41/0.57    inference(rectify,[],[f51])).
% 1.41/0.57  fof(f51,plain,(
% 1.41/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 1.41/0.57    inference(flattening,[],[f50])).
% 1.41/0.57  fof(f50,plain,(
% 1.41/0.57    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.41/0.57    inference(nnf_transformation,[],[f33])).
% 1.41/0.57  fof(f33,plain,(
% 1.41/0.57    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 1.41/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.57  fof(f597,plain,(
% 1.41/0.57    ~sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK4) | spl8_7),
% 1.41/0.57    inference(resolution,[],[f278,f201])).
% 1.41/0.57  fof(f201,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))) | ~sP0(X0,X1,X2)) )),
% 1.41/0.57    inference(resolution,[],[f123,f81])).
% 1.41/0.57  fof(f81,plain,(
% 1.41/0.57    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f49])).
% 1.41/0.57  fof(f49,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.41/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 1.41/0.57  fof(f48,plain,(
% 1.41/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.41/0.57    introduced(choice_axiom,[])).
% 1.41/0.57  fof(f47,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.41/0.57    inference(rectify,[],[f46])).
% 1.41/0.57  fof(f46,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.41/0.57    inference(nnf_transformation,[],[f34])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.41/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.41/0.57  fof(f123,plain,(
% 1.41/0.57    ( ! [X0,X1] : (sP1(X0,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.41/0.57    inference(equality_resolution,[],[f122])).
% 1.41/0.57  fof(f122,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.57    inference(definition_unfolding,[],[f87,f113])).
% 1.41/0.57  fof(f113,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.41/0.57    inference(definition_unfolding,[],[f71,f112])).
% 1.41/0.57  fof(f112,plain,(
% 1.41/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.57    inference(definition_unfolding,[],[f72,f111])).
% 1.41/0.57  % (27091)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.57  % (27084)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.57  % (27086)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.59  % (27078)Refutation not found, incomplete strategy% (27078)------------------------------
% 1.41/0.59  % (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.59  % (27078)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.59  
% 1.41/0.59  % (27078)Memory used [KB]: 11257
% 1.41/0.59  % (27078)Time elapsed: 0.178 s
% 1.41/0.59  % (27078)------------------------------
% 1.41/0.59  % (27078)------------------------------
% 1.41/0.60  fof(f111,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f79,f110])).
% 1.41/0.60  fof(f110,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f89,f109])).
% 1.41/0.60  fof(f109,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f90,f108])).
% 1.41/0.60  fof(f108,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f91,f92])).
% 1.41/0.60  fof(f92,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f8])).
% 1.41/0.60  fof(f8,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.41/0.60  fof(f91,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f7])).
% 1.41/0.60  fof(f7,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.41/0.60  fof(f90,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f6])).
% 1.41/0.60  fof(f6,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.41/0.60  fof(f89,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f5])).
% 1.41/0.60  fof(f5,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.60  fof(f79,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f4])).
% 1.41/0.60  fof(f4,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.60  fof(f72,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f3])).
% 1.41/0.60  fof(f3,axiom,(
% 1.41/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.60  fof(f71,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f10])).
% 1.41/0.60  fof(f10,axiom,(
% 1.41/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.41/0.60  fof(f87,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.60    inference(cnf_transformation,[],[f53])).
% 1.41/0.60  fof(f53,plain,(
% 1.41/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.41/0.60    inference(nnf_transformation,[],[f35])).
% 1.41/0.60  fof(f35,plain,(
% 1.41/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.41/0.60    inference(definition_folding,[],[f1,f34,f33])).
% 1.41/0.60  fof(f1,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.41/0.60  fof(f278,plain,(
% 1.41/0.60    ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_7),
% 1.41/0.60    inference(avatar_component_clause,[],[f277])).
% 1.41/0.60  fof(f277,plain,(
% 1.41/0.60    spl8_7 <=> r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.41/0.60  fof(f593,plain,(
% 1.41/0.60    ~spl8_7 | ~spl8_4),
% 1.41/0.60    inference(avatar_split_clause,[],[f589,f158,f277])).
% 1.41/0.60  fof(f158,plain,(
% 1.41/0.60    spl8_4 <=> r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.41/0.60  fof(f589,plain,(
% 1.41/0.60    ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_4),
% 1.41/0.60    inference(resolution,[],[f160,f78])).
% 1.41/0.60  fof(f78,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f31])).
% 1.41/0.60  fof(f31,plain,(
% 1.41/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.41/0.60    inference(ennf_transformation,[],[f18])).
% 1.41/0.60  fof(f18,axiom,(
% 1.41/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.41/0.60  fof(f160,plain,(
% 1.41/0.60    r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~spl8_4),
% 1.41/0.60    inference(avatar_component_clause,[],[f158])).
% 1.41/0.60  fof(f575,plain,(
% 1.41/0.60    spl8_4 | ~spl8_2 | ~spl8_3 | ~spl8_16),
% 1.41/0.60    inference(avatar_split_clause,[],[f574,f557,f154,f138,f158])).
% 1.41/0.60  fof(f138,plain,(
% 1.41/0.60    spl8_2 <=> r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5)),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.41/0.60  fof(f154,plain,(
% 1.41/0.60    spl8_3 <=> v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.41/0.60  fof(f557,plain,(
% 1.41/0.60    spl8_16 <=> v3_ordinal1(sK5)),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.41/0.60  fof(f574,plain,(
% 1.41/0.60    r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | (~spl8_2 | ~spl8_3 | ~spl8_16)),
% 1.41/0.60    inference(subsumption_resolution,[],[f573,f155])).
% 1.41/0.60  fof(f155,plain,(
% 1.41/0.60    v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_3),
% 1.41/0.60    inference(avatar_component_clause,[],[f154])).
% 1.41/0.60  fof(f573,plain,(
% 1.41/0.60    r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | (~spl8_2 | ~spl8_16)),
% 1.41/0.60    inference(subsumption_resolution,[],[f569,f558])).
% 1.41/0.60  fof(f558,plain,(
% 1.41/0.60    v3_ordinal1(sK5) | ~spl8_16),
% 1.41/0.60    inference(avatar_component_clause,[],[f557])).
% 1.41/0.60  fof(f569,plain,(
% 1.41/0.60    r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~v3_ordinal1(sK5) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_2),
% 1.41/0.60    inference(resolution,[],[f139,f74])).
% 1.41/0.60  fof(f74,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f44])).
% 1.41/0.60  fof(f44,plain,(
% 1.41/0.60    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(nnf_transformation,[],[f30])).
% 1.41/0.60  fof(f30,plain,(
% 1.41/0.60    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(flattening,[],[f29])).
% 1.41/0.60  fof(f29,plain,(
% 1.41/0.60    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.41/0.60    inference(ennf_transformation,[],[f14])).
% 1.41/0.60  fof(f14,axiom,(
% 1.41/0.60    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.41/0.60  fof(f139,plain,(
% 1.41/0.60    r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~spl8_2),
% 1.41/0.60    inference(avatar_component_clause,[],[f138])).
% 1.41/0.60  fof(f567,plain,(
% 1.41/0.60    spl8_5 | spl8_6 | spl8_1 | ~spl8_16),
% 1.41/0.60    inference(avatar_split_clause,[],[f566,f557,f134,f188,f184])).
% 1.41/0.60  fof(f188,plain,(
% 1.41/0.60    spl8_6 <=> sK4 = sK5),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.41/0.60  fof(f134,plain,(
% 1.41/0.60    spl8_1 <=> r2_hidden(sK4,sK5)),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.41/0.60  fof(f566,plain,(
% 1.41/0.60    sK4 = sK5 | r2_hidden(sK5,sK4) | (spl8_1 | ~spl8_16)),
% 1.41/0.60    inference(subsumption_resolution,[],[f565,f558])).
% 1.41/0.60  fof(f565,plain,(
% 1.41/0.60    sK4 = sK5 | r2_hidden(sK5,sK4) | ~v3_ordinal1(sK5) | spl8_1),
% 1.41/0.60    inference(subsumption_resolution,[],[f564,f62])).
% 1.41/0.60  fof(f62,plain,(
% 1.41/0.60    v3_ordinal1(sK4)),
% 1.41/0.60    inference(cnf_transformation,[],[f43])).
% 1.41/0.60  fof(f43,plain,(
% 1.41/0.60    ((~r1_ordinal1(k1_ordinal1(sK4),sK5) | ~r2_hidden(sK4,sK5)) & (r1_ordinal1(k1_ordinal1(sK4),sK5) | r2_hidden(sK4,sK5)) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 1.41/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 1.41/0.60  fof(f41,plain,(
% 1.41/0.60    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK4),X1) | ~r2_hidden(sK4,X1)) & (r1_ordinal1(k1_ordinal1(sK4),X1) | r2_hidden(sK4,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 1.41/0.60    introduced(choice_axiom,[])).
% 1.41/0.60  fof(f42,plain,(
% 1.41/0.60    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK4),X1) | ~r2_hidden(sK4,X1)) & (r1_ordinal1(k1_ordinal1(sK4),X1) | r2_hidden(sK4,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK4),sK5) | ~r2_hidden(sK4,sK5)) & (r1_ordinal1(k1_ordinal1(sK4),sK5) | r2_hidden(sK4,sK5)) & v3_ordinal1(sK5))),
% 1.41/0.60    introduced(choice_axiom,[])).
% 1.41/0.60  fof(f40,plain,(
% 1.41/0.60    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.41/0.60    inference(flattening,[],[f39])).
% 1.41/0.60  fof(f39,plain,(
% 1.41/0.60    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.41/0.60    inference(nnf_transformation,[],[f21])).
% 1.41/0.60  fof(f21,plain,(
% 1.41/0.60    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f20])).
% 1.41/0.60  fof(f20,negated_conjecture,(
% 1.41/0.60    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.41/0.60    inference(negated_conjecture,[],[f19])).
% 1.41/0.60  fof(f19,conjecture,(
% 1.41/0.60    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.41/0.60  fof(f564,plain,(
% 1.41/0.60    sK4 = sK5 | r2_hidden(sK5,sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(sK5) | spl8_1),
% 1.41/0.60    inference(resolution,[],[f136,f70])).
% 1.41/0.60  fof(f70,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f26])).
% 1.41/0.60  fof(f26,plain,(
% 1.41/0.60    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(flattening,[],[f25])).
% 1.41/0.60  fof(f25,plain,(
% 1.41/0.60    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f15])).
% 1.41/0.60  fof(f15,axiom,(
% 1.41/0.60    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.41/0.60  fof(f136,plain,(
% 1.41/0.60    ~r2_hidden(sK4,sK5) | spl8_1),
% 1.41/0.60    inference(avatar_component_clause,[],[f134])).
% 1.41/0.60  fof(f563,plain,(
% 1.41/0.60    spl8_16),
% 1.41/0.60    inference(avatar_split_clause,[],[f63,f557])).
% 1.41/0.60  fof(f63,plain,(
% 1.41/0.60    v3_ordinal1(sK5)),
% 1.41/0.60    inference(cnf_transformation,[],[f43])).
% 1.41/0.60  fof(f554,plain,(
% 1.41/0.60    spl8_12),
% 1.41/0.60    inference(avatar_contradiction_clause,[],[f553])).
% 1.41/0.60  fof(f553,plain,(
% 1.41/0.60    $false | spl8_12),
% 1.41/0.60    inference(subsumption_resolution,[],[f549,f124])).
% 1.41/0.60  fof(f124,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP2(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.41/0.60    inference(equality_resolution,[],[f105])).
% 1.41/0.60  fof(f105,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 1.41/0.60    inference(cnf_transformation,[],[f60])).
% 1.41/0.60  fof(f60,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.41/0.60    inference(rectify,[],[f59])).
% 1.41/0.60  fof(f59,plain,(
% 1.41/0.60    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.41/0.60    inference(flattening,[],[f58])).
% 1.41/0.60  fof(f58,plain,(
% 1.41/0.60    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.41/0.60    inference(nnf_transformation,[],[f36])).
% 1.41/0.60  fof(f36,plain,(
% 1.41/0.60    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.41/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.41/0.60  fof(f549,plain,(
% 1.41/0.60    ~sP2(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | spl8_12),
% 1.41/0.60    inference(resolution,[],[f390,f364])).
% 1.41/0.60  fof(f364,plain,(
% 1.41/0.60    ~r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | spl8_12),
% 1.41/0.60    inference(avatar_component_clause,[],[f363])).
% 1.41/0.60  fof(f363,plain,(
% 1.41/0.60    spl8_12 <=> r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.41/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.41/0.60  fof(f390,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.41/0.60    inference(resolution,[],[f94,f132])).
% 1.41/0.60  fof(f132,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP3(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.41/0.60    inference(equality_resolution,[],[f106])).
% 1.41/0.60  fof(f106,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.41/0.60    inference(cnf_transformation,[],[f61])).
% 1.41/0.60  fof(f61,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.41/0.60    inference(nnf_transformation,[],[f38])).
% 1.41/0.60  fof(f38,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.41/0.60    inference(definition_folding,[],[f32,f37,f36])).
% 1.41/0.60  fof(f37,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.41/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.41/0.60  fof(f32,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.41/0.60    inference(ennf_transformation,[],[f11])).
% 1.41/0.60  fof(f11,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 1.41/0.60  fof(f94,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ~sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X8)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f57])).
% 1.41/0.60  fof(f57,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.41/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f55,f56])).
% 1.41/0.60  fof(f56,plain,(
% 1.41/0.60    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP2(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.41/0.60    introduced(choice_axiom,[])).
% 1.41/0.60  fof(f55,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP2(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.41/0.60    inference(rectify,[],[f54])).
% 1.41/0.60  fof(f54,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP2(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.41/0.60    inference(nnf_transformation,[],[f37])).
% 1.41/0.60  fof(f441,plain,(
% 1.41/0.60    ~spl8_12 | ~spl8_4 | ~spl8_6),
% 1.41/0.60    inference(avatar_split_clause,[],[f438,f188,f158,f363])).
% 1.41/0.60  fof(f438,plain,(
% 1.41/0.60    ~r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | (~spl8_4 | ~spl8_6)),
% 1.41/0.60    inference(resolution,[],[f422,f86])).
% 1.41/0.60  fof(f86,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f52])).
% 1.41/0.60  fof(f422,plain,(
% 1.41/0.60    ~sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK4,sK4) | (~spl8_4 | ~spl8_6)),
% 1.41/0.60    inference(resolution,[],[f386,f201])).
% 1.41/0.60  fof(f386,plain,(
% 1.41/0.60    ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | (~spl8_4 | ~spl8_6)),
% 1.41/0.60    inference(resolution,[],[f383,f78])).
% 1.41/0.60  fof(f383,plain,(
% 1.41/0.60    r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK4) | (~spl8_4 | ~spl8_6)),
% 1.41/0.60    inference(forward_demodulation,[],[f160,f190])).
% 1.41/0.60  fof(f190,plain,(
% 1.41/0.60    sK4 = sK5 | ~spl8_6),
% 1.41/0.60    inference(avatar_component_clause,[],[f188])).
% 1.41/0.60  fof(f333,plain,(
% 1.41/0.60    ~spl8_1 | spl8_5 | ~spl8_7),
% 1.41/0.60    inference(avatar_contradiction_clause,[],[f332])).
% 1.41/0.60  fof(f332,plain,(
% 1.41/0.60    $false | (~spl8_1 | spl8_5 | ~spl8_7)),
% 1.41/0.60    inference(subsumption_resolution,[],[f329,f135])).
% 1.41/0.60  fof(f135,plain,(
% 1.41/0.60    r2_hidden(sK4,sK5) | ~spl8_1),
% 1.41/0.60    inference(avatar_component_clause,[],[f134])).
% 1.41/0.60  fof(f329,plain,(
% 1.41/0.60    ~r2_hidden(sK4,sK5) | (spl8_5 | ~spl8_7)),
% 1.41/0.60    inference(resolution,[],[f328,f203])).
% 1.41/0.60  fof(f203,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 1.41/0.60    inference(resolution,[],[f119,f78])).
% 1.41/0.60  fof(f119,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f77,f114])).
% 1.41/0.60  fof(f114,plain,(
% 1.41/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f66,f112])).
% 1.41/0.60  fof(f66,plain,(
% 1.41/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f2])).
% 1.41/0.60  fof(f2,axiom,(
% 1.41/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.60  fof(f77,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f45])).
% 1.41/0.60  fof(f45,plain,(
% 1.41/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.41/0.60    inference(nnf_transformation,[],[f9])).
% 1.41/0.60  fof(f9,axiom,(
% 1.41/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.60  fof(f328,plain,(
% 1.41/0.60    r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | (spl8_5 | ~spl8_7)),
% 1.41/0.60    inference(subsumption_resolution,[],[f326,f185])).
% 1.41/0.60  fof(f185,plain,(
% 1.41/0.60    ~r2_hidden(sK5,sK4) | spl8_5),
% 1.41/0.60    inference(avatar_component_clause,[],[f184])).
% 1.41/0.60  fof(f326,plain,(
% 1.41/0.60    r2_hidden(sK5,sK4) | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl8_7),
% 1.41/0.60    inference(resolution,[],[f319,f84])).
% 1.41/0.60  fof(f84,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f52])).
% 1.41/0.60  fof(f319,plain,(
% 1.41/0.60    sP0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5,sK4) | ~spl8_7),
% 1.41/0.60    inference(resolution,[],[f279,f202])).
% 1.41/0.60  fof(f202,plain,(
% 1.41/0.60    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) | sP0(X5,X3,X4)) )),
% 1.41/0.60    inference(resolution,[],[f123,f80])).
% 1.41/0.60  fof(f80,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f49])).
% 1.41/0.60  fof(f279,plain,(
% 1.41/0.60    r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_7),
% 1.41/0.60    inference(avatar_component_clause,[],[f277])).
% 1.41/0.60  fof(f314,plain,(
% 1.41/0.60    spl8_7 | ~spl8_3 | spl8_4),
% 1.41/0.60    inference(avatar_split_clause,[],[f313,f158,f154,f277])).
% 1.41/0.60  fof(f313,plain,(
% 1.41/0.60    r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | (~spl8_3 | spl8_4)),
% 1.41/0.60    inference(subsumption_resolution,[],[f312,f155])).
% 1.41/0.60  fof(f312,plain,(
% 1.41/0.60    ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_4),
% 1.41/0.60    inference(subsumption_resolution,[],[f303,f63])).
% 1.41/0.60  fof(f303,plain,(
% 1.41/0.60    ~v3_ordinal1(sK5) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_4),
% 1.41/0.60    inference(resolution,[],[f159,f150])).
% 1.41/0.60  fof(f150,plain,(
% 1.41/0.60    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2)) )),
% 1.41/0.60    inference(duplicate_literal_removal,[],[f147])).
% 1.41/0.60  fof(f147,plain,(
% 1.41/0.60    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X3,X2) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2)) )),
% 1.41/0.60    inference(resolution,[],[f74,f69])).
% 1.41/0.60  fof(f69,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f24])).
% 1.41/0.60  fof(f24,plain,(
% 1.41/0.60    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(flattening,[],[f23])).
% 1.41/0.60  fof(f23,plain,(
% 1.41/0.60    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f16])).
% 1.41/0.60  fof(f16,axiom,(
% 1.41/0.60    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.41/0.60  fof(f159,plain,(
% 1.41/0.60    ~r1_tarski(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | spl8_4),
% 1.41/0.60    inference(avatar_component_clause,[],[f158])).
% 1.41/0.60  fof(f280,plain,(
% 1.41/0.60    ~spl8_3 | spl8_7 | spl8_2),
% 1.41/0.60    inference(avatar_split_clause,[],[f275,f138,f277,f154])).
% 1.41/0.60  fof(f275,plain,(
% 1.41/0.60    r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_2),
% 1.41/0.60    inference(subsumption_resolution,[],[f200,f63])).
% 1.41/0.60  fof(f200,plain,(
% 1.41/0.60    r2_hidden(sK5,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~v3_ordinal1(sK5) | ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_2),
% 1.41/0.60    inference(resolution,[],[f140,f69])).
% 1.41/0.60  fof(f140,plain,(
% 1.41/0.60    ~r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | spl8_2),
% 1.41/0.60    inference(avatar_component_clause,[],[f138])).
% 1.41/0.60  fof(f270,plain,(
% 1.41/0.60    spl8_3),
% 1.41/0.60    inference(avatar_contradiction_clause,[],[f269])).
% 1.41/0.60  fof(f269,plain,(
% 1.41/0.60    $false | spl8_3),
% 1.41/0.60    inference(subsumption_resolution,[],[f268,f132])).
% 1.41/0.60  fof(f268,plain,(
% 1.41/0.60    ~sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | spl8_3),
% 1.41/0.60    inference(subsumption_resolution,[],[f262,f62])).
% 1.41/0.60  fof(f262,plain,(
% 1.41/0.60    ~v3_ordinal1(sK4) | ~sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | spl8_3),
% 1.41/0.60    inference(resolution,[],[f118,f236])).
% 1.41/0.60  fof(f236,plain,(
% 1.41/0.60    ( ! [X5] : (~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X5))) | ~sP3(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,X5)) ) | spl8_3),
% 1.41/0.60    inference(superposition,[],[f156,f107])).
% 1.41/0.60  fof(f107,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP3(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f61])).
% 1.41/0.60  fof(f156,plain,(
% 1.41/0.60    ~v3_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_3),
% 1.41/0.60    inference(avatar_component_clause,[],[f154])).
% 1.41/0.60  fof(f118,plain,(
% 1.41/0.60    ( ! [X0] : (v3_ordinal1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f68,f115])).
% 1.41/0.60  fof(f115,plain,(
% 1.41/0.60    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.41/0.60    inference(definition_unfolding,[],[f67,f113,f114])).
% 1.41/0.60  fof(f67,plain,(
% 1.41/0.60    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f13])).
% 1.41/0.60  fof(f13,axiom,(
% 1.41/0.60    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.41/0.60  fof(f68,plain,(
% 1.41/0.60    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f22])).
% 1.41/0.60  fof(f22,plain,(
% 1.41/0.60    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(ennf_transformation,[],[f17])).
% 1.41/0.60  fof(f17,axiom,(
% 1.41/0.60    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.41/0.60  fof(f195,plain,(
% 1.41/0.60    ~spl8_5 | ~spl8_1),
% 1.41/0.60    inference(avatar_split_clause,[],[f194,f134,f184])).
% 1.41/0.60  fof(f194,plain,(
% 1.41/0.60    ~r2_hidden(sK5,sK4) | ~spl8_1),
% 1.41/0.60    inference(subsumption_resolution,[],[f193,f63])).
% 1.41/0.60  fof(f193,plain,(
% 1.41/0.60    ~r2_hidden(sK5,sK4) | ~v3_ordinal1(sK5) | ~spl8_1),
% 1.41/0.60    inference(subsumption_resolution,[],[f192,f62])).
% 1.41/0.60  fof(f192,plain,(
% 1.41/0.60    ~v3_ordinal1(sK4) | ~r2_hidden(sK5,sK4) | ~v3_ordinal1(sK5) | ~spl8_1),
% 1.41/0.60    inference(resolution,[],[f135,f173])).
% 1.41/0.60  fof(f173,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(resolution,[],[f170,f78])).
% 1.41/0.60  fof(f170,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X1,X0)) )),
% 1.41/0.60    inference(resolution,[],[f169,f78])).
% 1.41/0.60  fof(f169,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 1.41/0.60    inference(duplicate_literal_removal,[],[f168])).
% 1.41/0.60  fof(f168,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(resolution,[],[f151,f74])).
% 1.41/0.60  fof(f151,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 1.41/0.60    inference(duplicate_literal_removal,[],[f146])).
% 1.41/0.60  fof(f146,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.41/0.60    inference(resolution,[],[f74,f73])).
% 1.41/0.60  fof(f73,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f28])).
% 1.41/0.60  fof(f28,plain,(
% 1.41/0.60    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.41/0.60    inference(flattening,[],[f27])).
% 1.41/0.60  fof(f27,plain,(
% 1.41/0.60    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.41/0.60    inference(ennf_transformation,[],[f12])).
% 1.41/0.60  fof(f12,axiom,(
% 1.41/0.60    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.41/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.41/0.60  fof(f142,plain,(
% 1.41/0.60    spl8_1 | spl8_2),
% 1.41/0.60    inference(avatar_split_clause,[],[f117,f138,f134])).
% 1.41/0.60  fof(f117,plain,(
% 1.41/0.60    r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | r2_hidden(sK4,sK5)),
% 1.41/0.60    inference(definition_unfolding,[],[f64,f115])).
% 1.41/0.60  fof(f64,plain,(
% 1.41/0.60    r1_ordinal1(k1_ordinal1(sK4),sK5) | r2_hidden(sK4,sK5)),
% 1.41/0.60    inference(cnf_transformation,[],[f43])).
% 1.41/0.60  fof(f141,plain,(
% 1.41/0.60    ~spl8_1 | ~spl8_2),
% 1.41/0.60    inference(avatar_split_clause,[],[f116,f138,f134])).
% 1.41/0.60  fof(f116,plain,(
% 1.41/0.60    ~r1_ordinal1(k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK5) | ~r2_hidden(sK4,sK5)),
% 1.41/0.60    inference(definition_unfolding,[],[f65,f115])).
% 1.41/0.60  fof(f65,plain,(
% 1.41/0.60    ~r1_ordinal1(k1_ordinal1(sK4),sK5) | ~r2_hidden(sK4,sK5)),
% 1.41/0.60    inference(cnf_transformation,[],[f43])).
% 1.41/0.60  % SZS output end Proof for theBenchmark
% 1.41/0.60  % (27096)------------------------------
% 1.41/0.60  % (27096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (27096)Termination reason: Refutation
% 1.41/0.60  
% 1.41/0.60  % (27096)Memory used [KB]: 6524
% 1.41/0.60  % (27096)Time elapsed: 0.169 s
% 1.41/0.60  % (27096)------------------------------
% 1.41/0.60  % (27096)------------------------------
% 1.41/0.60  % (27067)Success in time 0.237 s
%------------------------------------------------------------------------------
