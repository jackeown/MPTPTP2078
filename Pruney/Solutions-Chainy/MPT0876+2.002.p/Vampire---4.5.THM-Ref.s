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
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 251 expanded)
%              Number of leaves         :   26 ( 101 expanded)
%              Depth                    :    8
%              Number of atoms          :  314 ( 874 expanded)
%              Number of equality atoms :  126 ( 442 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f77,f82,f117,f141,f166,f172,f178,f183,f189,f198,f204,f208,f214,f255,f259,f267,f289,f359])).

fof(f359,plain,
    ( spl6_16
    | spl6_12
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f288,f252,f248,f138,f186])).

fof(f186,plain,
    ( spl6_16
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f138,plain,
    ( spl6_12
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f248,plain,
    ( spl6_23
  <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f252,plain,
    ( spl6_24
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f288,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK3,sK0)
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f269,f254])).

fof(f254,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f269,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(sK3,sK0)
    | ~ spl6_23 ),
    inference(resolution,[],[f249,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f249,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f289,plain,
    ( spl6_14
    | spl6_12
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f287,f252,f248,f138,f175])).

fof(f175,plain,
    ( spl6_14
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f287,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK4,sK1)
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f268,f254])).

fof(f268,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | r1_tarski(sK4,sK1)
    | ~ spl6_23 ),
    inference(resolution,[],[f249,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f267,plain,
    ( spl6_23
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f261,f257,f248])).

fof(f257,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f261,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_25 ),
    inference(resolution,[],[f258,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl6_10
    | spl6_25
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f103,f79,f257,f98])).

fof(f98,plain,
    ( spl6_10
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f79,plain,
    ( spl6_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | r1_tarski(k2_zfmisc_1(sK3,sK4),X0) )
    | ~ spl6_7 ),
    inference(superposition,[],[f25,f81])).

fof(f81,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f255,plain,
    ( ~ spl6_23
    | spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f146,f114,f252,f248])).

fof(f114,plain,
    ( spl6_11
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f146,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(resolution,[],[f116,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f214,plain,
    ( spl6_18
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl6_18
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f203,f48,f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(sK5,X1) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | r1_tarski(sK5,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f203,plain,
    ( ~ r1_tarski(sK5,sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl6_18
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f208,plain,
    ( spl6_10
    | spl6_19
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f127,f79,f206,f98])).

% (7311)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1))
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | r1_tarski(sK5,X1) )
    | ~ spl6_7 ),
    inference(superposition,[],[f26,f81])).

fof(f204,plain,
    ( ~ spl6_18
    | spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f199,f195,f74,f201])).

fof(f74,plain,
    ( spl6_6
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f195,plain,
    ( spl6_17
  <=> r1_tarski(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f199,plain,
    ( sK2 = sK5
    | ~ r1_tarski(sK5,sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f197,f37])).

fof(f197,plain,
    ( r1_tarski(sK2,sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( spl6_17
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f190,f79,f98,f195])).

fof(f190,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | r1_tarski(sK2,sK5)
    | ~ spl6_7 ),
    inference(resolution,[],[f131,f48])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0
        | r1_tarski(X1,sK5) )
    | ~ spl6_7 ),
    inference(superposition,[],[f26,f81])).

fof(f189,plain,
    ( ~ spl6_16
    | spl6_4
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f184,f180,f66,f186])).

fof(f66,plain,
    ( spl6_4
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f180,plain,
    ( spl6_15
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f184,plain,
    ( sK0 = sK3
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f182,f37])).

fof(f182,plain,
    ( r1_tarski(sK0,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f183,plain,
    ( spl6_15
    | spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f145,f114,f138,f180])).

fof(f145,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK0,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f116,f25])).

fof(f178,plain,
    ( ~ spl6_14
    | spl6_5
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f173,f169,f70,f175])).

fof(f70,plain,
    ( spl6_5
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f169,plain,
    ( spl6_13
  <=> r1_tarski(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f173,plain,
    ( sK1 = sK4
    | ~ r1_tarski(sK4,sK1)
    | ~ spl6_13 ),
    inference(resolution,[],[f171,f37])).

fof(f171,plain,
    ( r1_tarski(sK1,sK4)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f172,plain,
    ( spl6_13
    | spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f144,f114,f138,f169])).

fof(f144,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK1,sK4)
    | ~ spl6_11 ),
    inference(resolution,[],[f116,f26])).

fof(f166,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f58,f53,f140,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f140,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f53,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f141,plain,
    ( spl6_3
    | spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f125,f98,f138,f61])).

fof(f61,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f125,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK2
    | ~ spl6_10 ),
    inference(superposition,[],[f31,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f117,plain,
    ( spl6_11
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f109,f79,f98,f114])).

fof(f109,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl6_7 ),
    inference(resolution,[],[f106,f48])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0
        | r1_tarski(X0,k2_zfmisc_1(sK3,sK4)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f25,f81])).

fof(f82,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f20,f34,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f77,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f24,f74,f70,f66])).

fof(f24,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (7313)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (7309)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.54  % (7317)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.54  % (7331)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.55  % (7328)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.55  % (7323)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.55  % (7330)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.55  % (7309)Refutation not found, incomplete strategy% (7309)------------------------------
% 0.19/0.55  % (7309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (7309)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (7309)Memory used [KB]: 1663
% 0.19/0.55  % (7309)Time elapsed: 0.133 s
% 0.19/0.55  % (7309)------------------------------
% 0.19/0.55  % (7309)------------------------------
% 0.19/0.55  % (7336)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.56  % (7331)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % (7318)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.57  % (7315)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.57  % (7314)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.57  % (7312)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.58  % SZS output start Proof for theBenchmark
% 0.19/0.58  fof(f360,plain,(
% 0.19/0.58    $false),
% 0.19/0.58    inference(avatar_sat_refutation,[],[f54,f59,f64,f77,f82,f117,f141,f166,f172,f178,f183,f189,f198,f204,f208,f214,f255,f259,f267,f289,f359])).
% 0.19/0.58  fof(f359,plain,(
% 0.19/0.58    spl6_16 | spl6_12 | ~spl6_23 | ~spl6_24),
% 0.19/0.58    inference(avatar_split_clause,[],[f288,f252,f248,f138,f186])).
% 0.19/0.58  fof(f186,plain,(
% 0.19/0.58    spl6_16 <=> r1_tarski(sK3,sK0)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.58  fof(f138,plain,(
% 0.19/0.58    spl6_12 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.19/0.58  fof(f248,plain,(
% 0.19/0.58    spl6_23 <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.19/0.58  fof(f252,plain,(
% 0.19/0.58    spl6_24 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.19/0.58  fof(f288,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK3,sK0) | (~spl6_23 | ~spl6_24)),
% 0.19/0.58    inference(forward_demodulation,[],[f269,f254])).
% 0.19/0.58  fof(f254,plain,(
% 0.19/0.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~spl6_24),
% 0.19/0.58    inference(avatar_component_clause,[],[f252])).
% 0.19/0.58  fof(f269,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | r1_tarski(sK3,sK0) | ~spl6_23),
% 0.19/0.58    inference(resolution,[],[f249,f25])).
% 0.19/0.58  fof(f25,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X2)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f11])).
% 0.19/0.58  fof(f11,plain,(
% 0.19/0.58    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.19/0.58    inference(flattening,[],[f10])).
% 0.19/0.58  fof(f10,plain,(
% 0.19/0.58    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.19/0.58    inference(ennf_transformation,[],[f3])).
% 0.19/0.58  fof(f3,axiom,(
% 0.19/0.58    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.19/0.58  fof(f249,plain,(
% 0.19/0.58    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_23),
% 0.19/0.58    inference(avatar_component_clause,[],[f248])).
% 0.19/0.58  fof(f289,plain,(
% 0.19/0.58    spl6_14 | spl6_12 | ~spl6_23 | ~spl6_24),
% 0.19/0.58    inference(avatar_split_clause,[],[f287,f252,f248,f138,f175])).
% 0.19/0.58  fof(f175,plain,(
% 0.19/0.58    spl6_14 <=> r1_tarski(sK4,sK1)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.19/0.58  fof(f287,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK4,sK1) | (~spl6_23 | ~spl6_24)),
% 0.19/0.58    inference(forward_demodulation,[],[f268,f254])).
% 0.19/0.58  fof(f268,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | r1_tarski(sK4,sK1) | ~spl6_23),
% 0.19/0.58    inference(resolution,[],[f249,f26])).
% 0.19/0.58  fof(f26,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,X3)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f11])).
% 0.19/0.58  fof(f267,plain,(
% 0.19/0.58    spl6_23 | ~spl6_25),
% 0.19/0.58    inference(avatar_split_clause,[],[f261,f257,f248])).
% 0.19/0.58  fof(f257,plain,(
% 0.19/0.58    spl6_25 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.19/0.58  fof(f261,plain,(
% 0.19/0.58    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_25),
% 0.19/0.58    inference(resolution,[],[f258,f48])).
% 0.19/0.58  fof(f48,plain,(
% 0.19/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.58    inference(equality_resolution,[],[f36])).
% 0.19/0.58  fof(f36,plain,(
% 0.19/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.58    inference(cnf_transformation,[],[f19])).
% 0.19/0.58  fof(f19,plain,(
% 0.19/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.58    inference(flattening,[],[f18])).
% 0.19/0.58  fof(f18,plain,(
% 0.19/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.58    inference(nnf_transformation,[],[f1])).
% 0.19/0.58  fof(f1,axiom,(
% 0.19/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.58  fof(f258,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)) ) | ~spl6_25),
% 0.19/0.58    inference(avatar_component_clause,[],[f257])).
% 0.19/0.58  fof(f259,plain,(
% 0.19/0.58    spl6_10 | spl6_25 | ~spl6_7),
% 0.19/0.58    inference(avatar_split_clause,[],[f103,f79,f257,f98])).
% 0.19/0.58  fof(f98,plain,(
% 0.19/0.58    spl6_10 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.58  fof(f79,plain,(
% 0.19/0.58    spl6_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.58  fof(f103,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(k2_zfmisc_1(sK3,sK4),X0)) ) | ~spl6_7),
% 0.19/0.58    inference(superposition,[],[f25,f81])).
% 0.19/0.58  fof(f81,plain,(
% 0.19/0.58    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) | ~spl6_7),
% 0.19/0.58    inference(avatar_component_clause,[],[f79])).
% 0.19/0.58  fof(f255,plain,(
% 0.19/0.58    ~spl6_23 | spl6_24 | ~spl6_11),
% 0.19/0.58    inference(avatar_split_clause,[],[f146,f114,f252,f248])).
% 0.19/0.58  fof(f114,plain,(
% 0.19/0.58    spl6_11 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.58  fof(f146,plain,(
% 0.19/0.58    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK0,sK1)) | ~spl6_11),
% 0.19/0.58    inference(resolution,[],[f116,f37])).
% 0.19/0.58  fof(f37,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f19])).
% 0.19/0.58  fof(f116,plain,(
% 0.19/0.58    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_11),
% 0.19/0.58    inference(avatar_component_clause,[],[f114])).
% 0.19/0.58  fof(f214,plain,(
% 0.19/0.58    spl6_18 | ~spl6_19),
% 0.19/0.58    inference(avatar_contradiction_clause,[],[f209])).
% 0.19/0.58  fof(f209,plain,(
% 0.19/0.58    $false | (spl6_18 | ~spl6_19)),
% 0.19/0.58    inference(unit_resulting_resolution,[],[f203,f48,f207])).
% 0.19/0.58  fof(f207,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(sK5,X1)) ) | ~spl6_19),
% 0.19/0.58    inference(avatar_component_clause,[],[f206])).
% 0.19/0.58  fof(f206,plain,(
% 0.19/0.58    spl6_19 <=> ! [X1,X0] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | r1_tarski(sK5,X1))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.19/0.58  fof(f203,plain,(
% 0.19/0.58    ~r1_tarski(sK5,sK2) | spl6_18),
% 0.19/0.58    inference(avatar_component_clause,[],[f201])).
% 0.19/0.58  fof(f201,plain,(
% 0.19/0.58    spl6_18 <=> r1_tarski(sK5,sK2)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.19/0.58  fof(f208,plain,(
% 0.19/0.58    spl6_10 | spl6_19 | ~spl6_7),
% 0.19/0.58    inference(avatar_split_clause,[],[f127,f79,f206,f98])).
% 0.19/0.58  % (7311)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.58  fof(f127,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(sK5,X1)) ) | ~spl6_7),
% 0.19/0.58    inference(superposition,[],[f26,f81])).
% 0.19/0.58  fof(f204,plain,(
% 0.19/0.58    ~spl6_18 | spl6_6 | ~spl6_17),
% 0.19/0.58    inference(avatar_split_clause,[],[f199,f195,f74,f201])).
% 0.19/0.58  fof(f74,plain,(
% 0.19/0.58    spl6_6 <=> sK2 = sK5),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.58  fof(f195,plain,(
% 0.19/0.58    spl6_17 <=> r1_tarski(sK2,sK5)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.19/0.58  fof(f199,plain,(
% 0.19/0.58    sK2 = sK5 | ~r1_tarski(sK5,sK2) | ~spl6_17),
% 0.19/0.58    inference(resolution,[],[f197,f37])).
% 0.19/0.58  fof(f197,plain,(
% 0.19/0.58    r1_tarski(sK2,sK5) | ~spl6_17),
% 0.19/0.58    inference(avatar_component_clause,[],[f195])).
% 0.19/0.58  fof(f198,plain,(
% 0.19/0.58    spl6_17 | spl6_10 | ~spl6_7),
% 0.19/0.58    inference(avatar_split_clause,[],[f190,f79,f98,f195])).
% 0.19/0.58  fof(f190,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(sK2,sK5) | ~spl6_7),
% 0.19/0.58    inference(resolution,[],[f131,f48])).
% 0.19/0.58  fof(f131,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,sK5)) ) | ~spl6_7),
% 0.19/0.58    inference(superposition,[],[f26,f81])).
% 0.19/0.58  fof(f189,plain,(
% 0.19/0.58    ~spl6_16 | spl6_4 | ~spl6_15),
% 0.19/0.58    inference(avatar_split_clause,[],[f184,f180,f66,f186])).
% 0.19/0.58  fof(f66,plain,(
% 0.19/0.58    spl6_4 <=> sK0 = sK3),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.58  fof(f180,plain,(
% 0.19/0.58    spl6_15 <=> r1_tarski(sK0,sK3)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.58  fof(f184,plain,(
% 0.19/0.58    sK0 = sK3 | ~r1_tarski(sK3,sK0) | ~spl6_15),
% 0.19/0.58    inference(resolution,[],[f182,f37])).
% 0.19/0.58  fof(f182,plain,(
% 0.19/0.58    r1_tarski(sK0,sK3) | ~spl6_15),
% 0.19/0.58    inference(avatar_component_clause,[],[f180])).
% 0.19/0.58  fof(f183,plain,(
% 0.19/0.58    spl6_15 | spl6_12 | ~spl6_11),
% 0.19/0.58    inference(avatar_split_clause,[],[f145,f114,f138,f180])).
% 0.19/0.58  fof(f145,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK0,sK3) | ~spl6_11),
% 0.19/0.58    inference(resolution,[],[f116,f25])).
% 0.19/0.58  fof(f178,plain,(
% 0.19/0.58    ~spl6_14 | spl6_5 | ~spl6_13),
% 0.19/0.58    inference(avatar_split_clause,[],[f173,f169,f70,f175])).
% 0.19/0.58  fof(f70,plain,(
% 0.19/0.58    spl6_5 <=> sK1 = sK4),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.58  fof(f169,plain,(
% 0.19/0.58    spl6_13 <=> r1_tarski(sK1,sK4)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.19/0.58  fof(f173,plain,(
% 0.19/0.58    sK1 = sK4 | ~r1_tarski(sK4,sK1) | ~spl6_13),
% 0.19/0.58    inference(resolution,[],[f171,f37])).
% 0.19/0.58  fof(f171,plain,(
% 0.19/0.58    r1_tarski(sK1,sK4) | ~spl6_13),
% 0.19/0.58    inference(avatar_component_clause,[],[f169])).
% 0.19/0.58  fof(f172,plain,(
% 0.19/0.58    spl6_13 | spl6_12 | ~spl6_11),
% 0.19/0.58    inference(avatar_split_clause,[],[f144,f114,f138,f169])).
% 0.19/0.58  fof(f144,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(sK1,sK4) | ~spl6_11),
% 0.19/0.58    inference(resolution,[],[f116,f26])).
% 0.19/0.58  fof(f166,plain,(
% 0.19/0.58    spl6_1 | spl6_2 | ~spl6_12),
% 0.19/0.58    inference(avatar_contradiction_clause,[],[f155])).
% 0.19/0.58  fof(f155,plain,(
% 0.19/0.58    $false | (spl6_1 | spl6_2 | ~spl6_12)),
% 0.19/0.58    inference(unit_resulting_resolution,[],[f58,f53,f140,f31])).
% 0.19/0.58  fof(f31,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.19/0.58    inference(cnf_transformation,[],[f17])).
% 0.19/0.58  fof(f17,plain,(
% 0.19/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.58    inference(flattening,[],[f16])).
% 0.19/0.58  fof(f16,plain,(
% 0.19/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.58    inference(nnf_transformation,[],[f2])).
% 0.19/0.58  fof(f2,axiom,(
% 0.19/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.58  fof(f140,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_12),
% 0.19/0.58    inference(avatar_component_clause,[],[f138])).
% 0.19/0.58  fof(f53,plain,(
% 0.19/0.58    k1_xboole_0 != sK0 | spl6_1),
% 0.19/0.58    inference(avatar_component_clause,[],[f51])).
% 0.19/0.58  fof(f51,plain,(
% 0.19/0.58    spl6_1 <=> k1_xboole_0 = sK0),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.58  fof(f58,plain,(
% 0.19/0.58    k1_xboole_0 != sK1 | spl6_2),
% 0.19/0.58    inference(avatar_component_clause,[],[f56])).
% 0.19/0.58  fof(f56,plain,(
% 0.19/0.58    spl6_2 <=> k1_xboole_0 = sK1),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.58  fof(f141,plain,(
% 0.19/0.58    spl6_3 | spl6_12 | ~spl6_10),
% 0.19/0.58    inference(avatar_split_clause,[],[f125,f98,f138,f61])).
% 0.19/0.58  fof(f61,plain,(
% 0.19/0.58    spl6_3 <=> k1_xboole_0 = sK2),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.58  fof(f125,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_10),
% 0.19/0.58    inference(trivial_inequality_removal,[],[f124])).
% 0.19/0.58  fof(f124,plain,(
% 0.19/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK2 | ~spl6_10),
% 0.19/0.58    inference(superposition,[],[f31,f99])).
% 0.19/0.58  fof(f99,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_10),
% 0.19/0.58    inference(avatar_component_clause,[],[f98])).
% 0.19/0.58  fof(f117,plain,(
% 0.19/0.58    spl6_11 | spl6_10 | ~spl6_7),
% 0.19/0.58    inference(avatar_split_clause,[],[f109,f79,f98,f114])).
% 0.19/0.58  fof(f109,plain,(
% 0.19/0.58    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl6_7),
% 0.19/0.58    inference(resolution,[],[f106,f48])).
% 0.19/0.58  fof(f106,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,k2_zfmisc_1(sK3,sK4))) ) | ~spl6_7),
% 0.19/0.58    inference(superposition,[],[f25,f81])).
% 0.19/0.58  fof(f82,plain,(
% 0.19/0.58    spl6_7),
% 0.19/0.58    inference(avatar_split_clause,[],[f38,f79])).
% 0.19/0.58  fof(f38,plain,(
% 0.19/0.58    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.19/0.58    inference(definition_unfolding,[],[f20,f34,f34])).
% 0.19/0.58  fof(f34,plain,(
% 0.19/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f4])).
% 0.19/0.58  fof(f4,axiom,(
% 0.19/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.58  fof(f20,plain,(
% 0.19/0.58    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.19/0.58    inference(cnf_transformation,[],[f13])).
% 0.19/0.58  fof(f13,plain,(
% 0.19/0.58    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.19/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f12])).
% 0.19/0.58  fof(f12,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 0.19/0.58    introduced(choice_axiom,[])).
% 0.19/0.58  fof(f9,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.58    inference(flattening,[],[f8])).
% 0.19/0.58  fof(f8,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.19/0.58    inference(ennf_transformation,[],[f7])).
% 0.19/0.58  fof(f7,negated_conjecture,(
% 0.19/0.58    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.58    inference(negated_conjecture,[],[f6])).
% 0.19/0.58  fof(f6,conjecture,(
% 0.19/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.19/0.58  fof(f77,plain,(
% 0.19/0.58    ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.19/0.58    inference(avatar_split_clause,[],[f24,f74,f70,f66])).
% 0.19/0.58  fof(f24,plain,(
% 0.19/0.58    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.19/0.58    inference(cnf_transformation,[],[f13])).
% 0.19/0.58  fof(f64,plain,(
% 0.19/0.58    ~spl6_3),
% 0.19/0.58    inference(avatar_split_clause,[],[f23,f61])).
% 0.19/0.58  fof(f23,plain,(
% 0.19/0.58    k1_xboole_0 != sK2),
% 0.19/0.58    inference(cnf_transformation,[],[f13])).
% 0.19/0.58  fof(f59,plain,(
% 0.19/0.58    ~spl6_2),
% 0.19/0.58    inference(avatar_split_clause,[],[f22,f56])).
% 0.19/0.58  fof(f22,plain,(
% 0.19/0.58    k1_xboole_0 != sK1),
% 0.19/0.58    inference(cnf_transformation,[],[f13])).
% 0.19/0.58  fof(f54,plain,(
% 0.19/0.58    ~spl6_1),
% 0.19/0.58    inference(avatar_split_clause,[],[f21,f51])).
% 0.19/0.58  fof(f21,plain,(
% 0.19/0.58    k1_xboole_0 != sK0),
% 0.19/0.58    inference(cnf_transformation,[],[f13])).
% 0.19/0.58  % SZS output end Proof for theBenchmark
% 0.19/0.58  % (7331)------------------------------
% 0.19/0.58  % (7331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (7331)Termination reason: Refutation
% 0.19/0.58  
% 0.19/0.58  % (7331)Memory used [KB]: 10874
% 0.19/0.58  % (7331)Time elapsed: 0.088 s
% 0.19/0.58  % (7331)------------------------------
% 0.19/0.58  % (7331)------------------------------
% 0.19/0.58  % (7307)Success in time 0.238 s
%------------------------------------------------------------------------------
