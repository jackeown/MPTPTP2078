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
% DateTime   : Thu Dec  3 12:38:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 322 expanded)
%              Number of leaves         :   33 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 565 expanded)
%              Number of equality atoms :   89 ( 302 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f205,f210,f221,f230,f241,f250,f266,f283,f311,f333,f377,f394,f396])).

fof(f396,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f394,plain,
    ( spl6_2
    | spl6_17
    | ~ spl6_25
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f393,f374,f308,f227,f88])).

% (4189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f88,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f227,plain,
    ( spl6_17
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f308,plain,
    ( spl6_25
  <=> sK0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f374,plain,
    ( spl6_33
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f393,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_25
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f390,f310])).

fof(f310,plain,
    ( sK0 = sK3(sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f308])).

fof(f390,plain,
    ( r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_33 ),
    inference(resolution,[],[f376,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),X0),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f72,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f58])).

% (4191)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f376,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f374])).

fof(f377,plain,
    ( spl6_2
    | spl6_33
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f364,f308,f374,f88])).

fof(f364,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_25 ),
    inference(superposition,[],[f29,f310])).

fof(f333,plain,
    ( spl6_1
    | spl6_20
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f332,f280,f263,f247,f83])).

fof(f83,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f247,plain,
    ( spl6_20
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f263,plain,
    ( spl6_21
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f280,plain,
    ( spl6_24
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f332,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f321,f265])).

fof(f265,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f263])).

fof(f321,plain,
    ( r1_tarski(k6_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK0),sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_24 ),
    inference(resolution,[],[f167,f282])).

fof(f282,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f311,plain,
    ( spl6_25
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f306,f197,f308])).

fof(f197,plain,
    ( spl6_12
  <=> r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f306,plain,
    ( sK0 = sK3(sK1)
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,
    ( sK0 = sK3(sK1)
    | sK0 = sK3(sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f199,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f199,plain,
    ( r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f197])).

fof(f283,plain,
    ( spl6_1
    | spl6_24
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f270,f263,f280,f83])).

fof(f270,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_21 ),
    inference(superposition,[],[f29,f265])).

fof(f266,plain,
    ( spl6_21
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f261,f192,f263])).

fof(f192,plain,
    ( spl6_11
  <=> r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f261,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( sK0 = sK3(sK2)
    | sK0 = sK3(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f194,f81])).

fof(f194,plain,
    ( r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f192])).

fof(f250,plain,
    ( spl6_19
    | ~ spl6_20
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f235,f202,f247,f243])).

fof(f243,plain,
    ( spl6_19
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f202,plain,
    ( spl6_13
  <=> r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f235,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)
    | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_13 ),
    inference(resolution,[],[f204,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f204,plain,
    ( r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f241,plain,
    ( spl6_1
    | spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f234,f202,f192,f83])).

fof(f234,plain,
    ( r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = sK2
    | ~ spl6_13 ),
    inference(resolution,[],[f204,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (4179)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f230,plain,
    ( spl6_16
    | ~ spl6_17
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f215,f207,f227,f223])).

fof(f223,plain,
    ( spl6_16
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f207,plain,
    ( spl6_14
  <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f215,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f209,f36])).

fof(f209,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f221,plain,
    ( spl6_2
    | spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f214,f207,f197,f88])).

fof(f214,plain,
    ( r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = sK1
    | ~ spl6_14 ),
    inference(resolution,[],[f209,f141])).

fof(f210,plain,
    ( spl6_14
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f190,f98,f207])).

fof(f98,plain,
    ( spl6_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f190,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_4 ),
    inference(superposition,[],[f63,f100])).

fof(f100,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f205,plain,
    ( spl6_13
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f189,f98,f202])).

fof(f189,plain,
    ( r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl6_4 ),
    inference(superposition,[],[f157,f100])).

fof(f157,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) ),
    inference(resolution,[],[f65,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f101,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f62,f98])).

fof(f62,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f61,f60])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f59])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f96,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f25,f93])).

fof(f93,plain,
    ( spl6_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f25,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f26,f88])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f83])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (4162)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (4177)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (4170)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (4166)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (4167)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4164)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (4178)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (4169)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (4178)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (4185)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (4182)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (4184)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (4174)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (4176)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (4165)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (4187)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (4163)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.53  % (4188)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.53  % (4186)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.53  % (4190)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.53  % (4168)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f397,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f205,f210,f221,f230,f241,f250,f266,f283,f311,f333,f377,f394,f396])).
% 1.39/0.53  fof(f396,plain,(
% 1.39/0.53    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 1.39/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.53  fof(f394,plain,(
% 1.39/0.53    spl6_2 | spl6_17 | ~spl6_25 | ~spl6_33),
% 1.39/0.53    inference(avatar_split_clause,[],[f393,f374,f308,f227,f88])).
% 1.39/0.53  % (4189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.53  fof(f88,plain,(
% 1.39/0.53    spl6_2 <=> k1_xboole_0 = sK1),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.39/0.53  fof(f227,plain,(
% 1.39/0.53    spl6_17 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.39/0.53  fof(f308,plain,(
% 1.39/0.53    spl6_25 <=> sK0 = sK3(sK1)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.39/0.53  fof(f374,plain,(
% 1.39/0.53    spl6_33 <=> r2_hidden(sK0,sK1)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.39/0.53  fof(f393,plain,(
% 1.39/0.53    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | (~spl6_25 | ~spl6_33)),
% 1.39/0.53    inference(forward_demodulation,[],[f390,f310])).
% 1.39/0.53  fof(f310,plain,(
% 1.39/0.53    sK0 = sK3(sK1) | ~spl6_25),
% 1.39/0.53    inference(avatar_component_clause,[],[f308])).
% 1.39/0.53  fof(f390,plain,(
% 1.39/0.53    r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK0),sK1) | k1_xboole_0 = sK1 | ~spl6_33),
% 1.39/0.53    inference(resolution,[],[f376,f167])).
% 1.39/0.53  fof(f167,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),sK3(X1),X0),X1) | k1_xboole_0 = X1) )),
% 1.39/0.53    inference(resolution,[],[f72,f29])).
% 1.39/0.53  fof(f29,plain,(
% 1.39/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.39/0.53    inference(cnf_transformation,[],[f20])).
% 1.39/0.53  fof(f20,plain,(
% 1.39/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.39/0.53    inference(ennf_transformation,[],[f2])).
% 1.39/0.53  fof(f2,axiom,(
% 1.39/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.39/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.39/0.53  fof(f72,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f50,f59])).
% 1.39/0.53  fof(f59,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f32,f58])).
% 1.39/0.54  % (4191)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  fof(f58,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f40,f57])).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f51,f56])).
% 1.39/0.54  fof(f56,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f52,f55])).
% 1.39/0.54  fof(f55,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f53,f54])).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f12])).
% 1.39/0.54  fof(f12,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.39/0.54  fof(f376,plain,(
% 1.39/0.54    r2_hidden(sK0,sK1) | ~spl6_33),
% 1.39/0.54    inference(avatar_component_clause,[],[f374])).
% 1.39/0.54  fof(f377,plain,(
% 1.39/0.54    spl6_2 | spl6_33 | ~spl6_25),
% 1.39/0.54    inference(avatar_split_clause,[],[f364,f308,f374,f88])).
% 1.39/0.54  fof(f364,plain,(
% 1.39/0.54    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | ~spl6_25),
% 1.39/0.54    inference(superposition,[],[f29,f310])).
% 1.39/0.54  fof(f333,plain,(
% 1.39/0.54    spl6_1 | spl6_20 | ~spl6_21 | ~spl6_24),
% 1.39/0.54    inference(avatar_split_clause,[],[f332,f280,f263,f247,f83])).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    spl6_1 <=> k1_xboole_0 = sK2),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.39/0.54  fof(f247,plain,(
% 1.39/0.54    spl6_20 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.39/0.54  fof(f263,plain,(
% 1.39/0.54    spl6_21 <=> sK0 = sK3(sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.39/0.54  fof(f280,plain,(
% 1.39/0.54    spl6_24 <=> r2_hidden(sK0,sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.39/0.54  fof(f332,plain,(
% 1.39/0.54    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | k1_xboole_0 = sK2 | (~spl6_21 | ~spl6_24)),
% 1.39/0.54    inference(forward_demodulation,[],[f321,f265])).
% 1.39/0.54  fof(f265,plain,(
% 1.39/0.54    sK0 = sK3(sK2) | ~spl6_21),
% 1.39/0.54    inference(avatar_component_clause,[],[f263])).
% 1.39/0.54  fof(f321,plain,(
% 1.39/0.54    r1_tarski(k6_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2),sK0),sK2) | k1_xboole_0 = sK2 | ~spl6_24),
% 1.39/0.54    inference(resolution,[],[f167,f282])).
% 1.39/0.54  fof(f282,plain,(
% 1.39/0.54    r2_hidden(sK0,sK2) | ~spl6_24),
% 1.39/0.54    inference(avatar_component_clause,[],[f280])).
% 1.39/0.54  fof(f311,plain,(
% 1.39/0.54    spl6_25 | ~spl6_12),
% 1.39/0.54    inference(avatar_split_clause,[],[f306,f197,f308])).
% 1.39/0.54  fof(f197,plain,(
% 1.39/0.54    spl6_12 <=> r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.39/0.54  fof(f306,plain,(
% 1.39/0.54    sK0 = sK3(sK1) | ~spl6_12),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f303])).
% 1.39/0.54  fof(f303,plain,(
% 1.39/0.54    sK0 = sK3(sK1) | sK0 = sK3(sK1) | ~spl6_12),
% 1.39/0.54    inference(resolution,[],[f199,f81])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.39/0.54    inference(equality_resolution,[],[f68])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.39/0.54    inference(definition_unfolding,[],[f45,f59])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.39/0.54  fof(f199,plain,(
% 1.39/0.54    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_12),
% 1.39/0.54    inference(avatar_component_clause,[],[f197])).
% 1.39/0.54  fof(f283,plain,(
% 1.39/0.54    spl6_1 | spl6_24 | ~spl6_21),
% 1.39/0.54    inference(avatar_split_clause,[],[f270,f263,f280,f83])).
% 1.39/0.54  fof(f270,plain,(
% 1.39/0.54    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl6_21),
% 1.39/0.54    inference(superposition,[],[f29,f265])).
% 1.39/0.54  fof(f266,plain,(
% 1.39/0.54    spl6_21 | ~spl6_11),
% 1.39/0.54    inference(avatar_split_clause,[],[f261,f192,f263])).
% 1.39/0.54  fof(f192,plain,(
% 1.39/0.54    spl6_11 <=> r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.39/0.54  fof(f261,plain,(
% 1.39/0.54    sK0 = sK3(sK2) | ~spl6_11),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f258])).
% 1.39/0.54  fof(f258,plain,(
% 1.39/0.54    sK0 = sK3(sK2) | sK0 = sK3(sK2) | ~spl6_11),
% 1.39/0.54    inference(resolution,[],[f194,f81])).
% 1.39/0.54  fof(f194,plain,(
% 1.39/0.54    r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_11),
% 1.39/0.54    inference(avatar_component_clause,[],[f192])).
% 1.39/0.54  fof(f250,plain,(
% 1.39/0.54    spl6_19 | ~spl6_20 | ~spl6_13),
% 1.39/0.54    inference(avatar_split_clause,[],[f235,f202,f247,f243])).
% 1.39/0.54  fof(f243,plain,(
% 1.39/0.54    spl6_19 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.39/0.54  fof(f202,plain,(
% 1.39/0.54    spl6_13 <=> r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.39/0.54  fof(f235,plain,(
% 1.39/0.54    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_13),
% 1.39/0.54    inference(resolution,[],[f204,f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f204,plain,(
% 1.39/0.54    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_13),
% 1.39/0.54    inference(avatar_component_clause,[],[f202])).
% 1.39/0.54  fof(f241,plain,(
% 1.39/0.54    spl6_1 | spl6_11 | ~spl6_13),
% 1.39/0.54    inference(avatar_split_clause,[],[f234,f202,f192,f83])).
% 1.39/0.54  fof(f234,plain,(
% 1.39/0.54    r2_hidden(sK3(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK2 | ~spl6_13),
% 1.39/0.54    inference(resolution,[],[f204,f141])).
% 1.39/0.54  fof(f141,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 1.39/0.54    inference(resolution,[],[f37,f29])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f1])).
% 1.39/0.54  % (4179)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.54  fof(f230,plain,(
% 1.39/0.54    spl6_16 | ~spl6_17 | ~spl6_14),
% 1.39/0.54    inference(avatar_split_clause,[],[f215,f207,f227,f223])).
% 1.39/0.54  fof(f223,plain,(
% 1.39/0.54    spl6_16 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.39/0.54  fof(f207,plain,(
% 1.39/0.54    spl6_14 <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.39/0.54  fof(f215,plain,(
% 1.39/0.54    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl6_14),
% 1.39/0.54    inference(resolution,[],[f209,f36])).
% 1.39/0.54  fof(f209,plain,(
% 1.39/0.54    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_14),
% 1.39/0.54    inference(avatar_component_clause,[],[f207])).
% 1.39/0.54  fof(f221,plain,(
% 1.39/0.54    spl6_2 | spl6_12 | ~spl6_14),
% 1.39/0.54    inference(avatar_split_clause,[],[f214,f207,f197,f88])).
% 1.39/0.54  fof(f214,plain,(
% 1.39/0.54    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | ~spl6_14),
% 1.39/0.54    inference(resolution,[],[f209,f141])).
% 1.39/0.54  fof(f210,plain,(
% 1.39/0.54    spl6_14 | ~spl6_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f190,f98,f207])).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    spl6_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.39/0.54  fof(f190,plain,(
% 1.39/0.54    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_4),
% 1.39/0.54    inference(superposition,[],[f63,f100])).
% 1.39/0.54  fof(f100,plain,(
% 1.39/0.54    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl6_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f98])).
% 1.39/0.54  fof(f63,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f30,f60])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f31,f59])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,axiom,(
% 1.39/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.39/0.54  fof(f205,plain,(
% 1.39/0.54    spl6_13 | ~spl6_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f189,f98,f202])).
% 1.39/0.54  fof(f189,plain,(
% 1.39/0.54    r1_tarski(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl6_4),
% 1.39/0.54    inference(superposition,[],[f157,f100])).
% 1.39/0.54  fof(f157,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )),
% 1.39/0.54    inference(resolution,[],[f65,f75])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) )),
% 1.39/0.54    inference(definition_unfolding,[],[f41,f60])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.39/0.54  fof(f101,plain,(
% 1.39/0.54    spl6_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f62,f98])).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.39/0.54    inference(definition_unfolding,[],[f24,f61,f60])).
% 1.39/0.54  fof(f61,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f28,f59])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.54    inference(ennf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.54    inference(negated_conjecture,[],[f17])).
% 1.39/0.54  fof(f17,conjecture,(
% 1.39/0.54    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    ~spl6_3),
% 1.39/0.54    inference(avatar_split_clause,[],[f25,f93])).
% 1.39/0.54  fof(f93,plain,(
% 1.39/0.54    spl6_3 <=> sK1 = sK2),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    sK1 != sK2),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f91,plain,(
% 1.39/0.54    ~spl6_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f26,f88])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    k1_xboole_0 != sK1),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    ~spl6_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f27,f83])).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    k1_xboole_0 != sK2),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (4178)------------------------------
% 1.39/0.54  % (4178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (4178)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (4178)Memory used [KB]: 11001
% 1.39/0.54  % (4178)Time elapsed: 0.124 s
% 1.39/0.54  % (4178)------------------------------
% 1.39/0.54  % (4178)------------------------------
% 1.39/0.54  % (4182)Refutation not found, incomplete strategy% (4182)------------------------------
% 1.39/0.54  % (4182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (4182)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (4182)Memory used [KB]: 10746
% 1.39/0.54  % (4182)Time elapsed: 0.126 s
% 1.39/0.54  % (4182)------------------------------
% 1.39/0.54  % (4182)------------------------------
% 1.39/0.54  % (4161)Success in time 0.188 s
%------------------------------------------------------------------------------
