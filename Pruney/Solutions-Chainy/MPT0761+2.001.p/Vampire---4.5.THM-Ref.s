%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 231 expanded)
%              Number of leaves         :   26 ( 109 expanded)
%              Depth                    :    7
%              Number of atoms          :  482 ( 848 expanded)
%              Number of equality atoms :   56 (  97 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f31,f34,f38,f42,f46,f50,f54,f58,f62,f66,f70,f74,f79,f84,f99,f105,f111,f126,f138,f143,f151,f159,f171,f191])).

fof(f191,plain,
    ( ~ spl5_17
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f190,f109,f29,f94])).

fof(f94,plain,
    ( spl5_17
  <=> r1_tarski(sK1(sK0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f29,plain,
    ( spl5_3
  <=> r1_wellord1(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f109,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ r1_tarski(sK1(sK0),X0)
        | ~ r1_wellord1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f190,plain,
    ( ~ r1_tarski(sK1(sK0),k3_relat_1(sK0))
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(resolution,[],[f110,f30])).

fof(f30,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_wellord1(sK0,X0)
        | ~ r1_tarski(sK1(sK0),X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f109])).

% (17025)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f171,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f169,f33])).

fof(f33,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f169,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f165,f23])).

fof(f23,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f165,plain,
    ( ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl5_7
    | ~ spl5_24 ),
    inference(superposition,[],[f49,f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_24
  <=> k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != sK3(X0,X1)
        | ~ v1_relat_1(X0)
        | r1_wellord1(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != sK3(X0,X1)
        | r1_wellord1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f159,plain,
    ( spl5_24
    | ~ spl5_1
    | spl5_3
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f155,f149,f44,f29,f22,f157])).

fof(f44,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(sK3(X0,X1),X1)
        | r1_wellord1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f149,plain,
    ( spl5_23
  <=> ! [X0] :
        ( k1_xboole_0 = sK3(sK0,X0)
        | ~ r1_tarski(sK3(sK0,X0),k3_relat_1(sK0))
        | r1_wellord1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f155,plain,
    ( k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f154,f23])).

fof(f154,plain,
    ( k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f153,f33])).

fof(f153,plain,
    ( k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(resolution,[],[f150,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK3(X0,X1),X1)
        | ~ v1_relat_1(X0)
        | r1_wellord1(X0,X1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3(sK0,X0),k3_relat_1(sK0))
        | k1_xboole_0 = sK3(sK0,X0)
        | r1_wellord1(sK0,X0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f147,f141,f136,f64,f22,f149])).

fof(f64,plain,
    ( spl5_11
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,sK3(X0,X1))
        | ~ r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1))
        | r1_wellord1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f136,plain,
    ( spl5_21
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(sK0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f141,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f147,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3(sK0,X0)
        | ~ r1_tarski(sK3(sK0,X0),k3_relat_1(sK0))
        | r1_wellord1(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f146,f137])).

fof(f137,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(sK0,X1),X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK0)) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f146,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3(sK0,X0)
        | ~ r1_tarski(sK3(sK0,X0),k3_relat_1(sK0))
        | ~ r2_hidden(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0))
        | r1_wellord1(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f145,f23])).

fof(f145,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3(sK0,X0)
        | ~ r1_tarski(sK3(sK0,X0),k3_relat_1(sK0))
        | ~ r2_hidden(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0))
        | ~ v1_relat_1(sK0)
        | r1_wellord1(sK0,X0) )
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(resolution,[],[f142,f65])).

fof(f65,plain,
    ( ! [X0,X3,X1] :
        ( ~ r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1))
        | ~ r2_hidden(X3,sK3(X0,X1))
        | ~ v1_relat_1(X0)
        | r1_wellord1(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f64])).

fof(f142,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl5_22
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f129,f68,f26,f22,f141])).

fof(f26,plain,
    ( spl5_2
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f68,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1)
        | ~ v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f127,f23])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f27,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_wellord1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f68])).

fof(f27,plain,
    ( v1_wellord1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f138,plain,
    ( spl5_21
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f130,f56,f26,f22,f136])).

fof(f56,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1),X1)
        | ~ v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(sK0,X1),X1) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f128,f23])).

fof(f128,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(sK0,X1),X1)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f27,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_wellord1(X0)
        | ~ r1_tarski(X1,k3_relat_1(X0))
        | k1_xboole_0 = X1
        | r2_hidden(sK2(X0,X1),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f126,plain,
    ( spl5_2
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f123,f97,f36,f22,f26])).

fof(f36,plain,
    ( spl5_4
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != sK1(X0)
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f97,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f123,plain,
    ( v1_wellord1(sK0)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f117,f23])).

fof(f117,plain,
    ( ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(superposition,[],[f37,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f97])).

fof(f37,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK1(X0)
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f111,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_1
    | ~ spl5_10
    | spl5_16 ),
    inference(avatar_split_clause,[],[f107,f91,f60,f22,f109,f97])).

fof(f60,plain,
    ( spl5_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X2,X1)
        | k1_xboole_0 = X2
        | r2_hidden(sK4(X0,X2),X2)
        | ~ r1_wellord1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f91,plain,
    ( spl5_16
  <=> r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1(sK0),X0)
        | k1_xboole_0 = sK1(sK0)
        | ~ r1_wellord1(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_10
    | spl5_16 ),
    inference(subsumption_resolution,[],[f106,f23])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1(sK0),X0)
        | k1_xboole_0 = sK1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ r1_wellord1(sK0,X0) )
    | ~ spl5_10
    | spl5_16 ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X2),X2)
        | ~ r1_tarski(X2,X1)
        | k1_xboole_0 = X2
        | ~ v1_relat_1(X0)
        | ~ r1_wellord1(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f60])).

fof(f92,plain,
    ( ~ r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f91])).

fof(f105,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_5
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5
    | spl5_17 ),
    inference(subsumption_resolution,[],[f103,f32])).

fof(f32,plain,
    ( ~ v1_wellord1(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f103,plain,
    ( v1_wellord1(sK0)
    | ~ spl5_1
    | ~ spl5_5
    | spl5_17 ),
    inference(subsumption_resolution,[],[f101,f23])).

fof(f101,plain,
    ( ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl5_5
    | spl5_17 ),
    inference(resolution,[],[f95,f41])).

fof(f41,plain,
    ( ! [X0] :
        ( r1_tarski(sK1(X0),k3_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(sK1(X0),k3_relat_1(X0))
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f95,plain,
    ( ~ r1_tarski(sK1(sK0),k3_relat_1(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f94])).

fof(f99,plain,
    ( ~ spl5_16
    | ~ spl5_17
    | spl5_18
    | ~ spl5_1
    | spl5_2
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f88,f82,f52,f26,f22,f97,f94,f91])).

fof(f52,plain,
    ( spl5_8
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,sK1(X0))
        | ~ r1_xboole_0(k1_wellord1(X0,X2),sK1(X0))
        | v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f82,plain,
    ( spl5_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f88,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ r1_tarski(sK1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0))
    | ~ spl5_1
    | spl5_2
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ r1_tarski(sK1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0))
    | v1_wellord1(sK0)
    | ~ spl5_1
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f85,f23])).

fof(f85,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ r1_tarski(sK1(sK0),k3_relat_1(sK0))
    | ~ r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0))
    | ~ v1_relat_1(sK0)
    | v1_wellord1(sK0)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,
    ( ! [X2,X0] :
        ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK1(X0))
        | ~ r2_hidden(X2,sK1(X0))
        | ~ v1_relat_1(X0)
        | v1_wellord1(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f80,f77,f29,f82])).

fof(f77,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | ~ r1_wellord1(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f80,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(resolution,[],[f78,f30])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_wellord1(sK0,X1)
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl5_14
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f75,f72,f22,f77])).

fof(f72,plain,
    ( spl5_13
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X2,X1)
        | k1_xboole_0 = X2
        | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2)
        | ~ r1_wellord1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0)
        | ~ r1_wellord1(sK0,X1) )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(resolution,[],[f73,f23])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X2,X1)
        | k1_xboole_0 = X2
        | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2)
        | ~ r1_wellord1(X0,X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f18,f72])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X1)
      | k1_xboole_0 = X2
      | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2)
      | ~ r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                  & r2_hidden(X3,X2) )
              | k1_xboole_0 = X2
              | ~ r1_tarski(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_wellord1(X0,X1)
        <=> ! [X2] :
              ~ ( ! [X3] :
                    ~ ( r1_xboole_0(k1_wellord1(X0,X3),X2)
                      & r2_hidden(X3,X2) )
                & k1_xboole_0 != X2
                & r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_wellord1)).

fof(f70,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f13,f68])).

% (17018)Termination reason: Refutation not found, incomplete strategy
fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

% (17018)Memory used [KB]: 10490
fof(f6,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (17018)Time elapsed: 0.061 s
% (17018)------------------------------
% (17018)------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord1)).

fof(f66,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f16,f64])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK3(X0,X1))
      | ~ r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1))
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f17,f60])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X1)
      | k1_xboole_0 = X2
      | r2_hidden(sK4(X0,X2),X2)
      | ~ r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f12,f56])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f11,f52])).

fof(f11,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,sK1(X0))
      | ~ r1_xboole_0(k1_wellord1(X0,X2),sK1(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != sK3(X0,X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK3(X0,X1),X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f14,f40])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(sK1(X0),k3_relat_1(X0))
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != sK1(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f9,f29,f26])).

fof(f9,plain,
    ( ~ r1_wellord1(sK0,k3_relat_1(sK0))
    | ~ v1_wellord1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ( v1_wellord1(X0)
      <~> r1_wellord1(X0,k3_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v1_wellord1(X0)
        <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> r1_wellord1(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).

fof(f31,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f8,f29,f26])).

fof(f8,plain,
    ( r1_wellord1(sK0,k3_relat_1(sK0))
    | v1_wellord1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f10,f22])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17026)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (17026)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (17018)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (17018)Refutation not found, incomplete strategy% (17018)------------------------------
% 0.21/0.48  % (17018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f24,f31,f34,f38,f42,f46,f50,f54,f58,f62,f66,f70,f74,f79,f84,f99,f105,f111,f126,f138,f143,f151,f159,f171,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~spl5_17 | ~spl5_3 | ~spl5_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f190,f109,f29,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl5_17 <=> r1_tarski(sK1(sK0),k3_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl5_3 <=> r1_wellord1(sK0,k3_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl5_19 <=> ! [X0] : (~r1_tarski(sK1(sK0),X0) | ~r1_wellord1(sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~r1_tarski(sK1(sK0),k3_relat_1(sK0)) | (~spl5_3 | ~spl5_19)),
% 0.21/0.48    inference(resolution,[],[f110,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    r1_wellord1(sK0,k3_relat_1(sK0)) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_wellord1(sK0,X0) | ~r1_tarski(sK1(sK0),X0)) ) | ~spl5_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  % (17025)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ~spl5_1 | spl5_3 | ~spl5_7 | ~spl5_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    $false | (~spl5_1 | spl5_3 | ~spl5_7 | ~spl5_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~r1_wellord1(sK0,k3_relat_1(sK0)) | spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    r1_wellord1(sK0,k3_relat_1(sK0)) | (~spl5_1 | ~spl5_7 | ~spl5_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    spl5_1 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | r1_wellord1(sK0,k3_relat_1(sK0)) | (~spl5_7 | ~spl5_24)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | r1_wellord1(sK0,k3_relat_1(sK0)) | (~spl5_7 | ~spl5_24)),
% 0.21/0.48    inference(superposition,[],[f49,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) | ~spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl5_24 <=> k1_xboole_0 = sK3(sK0,k3_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != sK3(X0,X1) | ~v1_relat_1(X0) | r1_wellord1(X0,X1)) ) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl5_7 <=> ! [X1,X0] : (~v1_relat_1(X0) | k1_xboole_0 != sK3(X0,X1) | r1_wellord1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl5_24 | ~spl5_1 | spl5_3 | ~spl5_6 | ~spl5_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f149,f44,f29,f22,f157])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl5_6 <=> ! [X1,X0] : (~v1_relat_1(X0) | r1_tarski(sK3(X0,X1),X1) | r1_wellord1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl5_23 <=> ! [X0] : (k1_xboole_0 = sK3(sK0,X0) | ~r1_tarski(sK3(sK0,X0),k3_relat_1(sK0)) | r1_wellord1(sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) | (~spl5_1 | spl5_3 | ~spl5_6 | ~spl5_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f23])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (spl5_3 | ~spl5_6 | ~spl5_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f153,f33])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) | r1_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl5_6 | ~spl5_23)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    k1_xboole_0 = sK3(sK0,k3_relat_1(sK0)) | r1_wellord1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_wellord1(sK0,k3_relat_1(sK0)) | (~spl5_6 | ~spl5_23)),
% 0.21/0.48    inference(resolution,[],[f150,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(sK3(X0,X1),X1) | ~v1_relat_1(X0) | r1_wellord1(X0,X1)) ) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK3(sK0,X0),k3_relat_1(sK0)) | k1_xboole_0 = sK3(sK0,X0) | r1_wellord1(sK0,X0)) ) | ~spl5_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f149])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl5_23 | ~spl5_1 | ~spl5_11 | ~spl5_21 | ~spl5_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f147,f141,f136,f64,f22,f149])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_11 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~r2_hidden(X3,sK3(X0,X1)) | ~r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1)) | r1_wellord1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl5_21 <=> ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k1_xboole_0 = X1 | r2_hidden(sK2(sK0,X1),X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl5_22 <=> ! [X0] : (~r1_tarski(X0,k3_relat_1(sK0)) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK3(sK0,X0) | ~r1_tarski(sK3(sK0,X0),k3_relat_1(sK0)) | r1_wellord1(sK0,X0)) ) | (~spl5_1 | ~spl5_11 | ~spl5_21 | ~spl5_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X1] : (r2_hidden(sK2(sK0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK0))) ) | ~spl5_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK3(sK0,X0) | ~r1_tarski(sK3(sK0,X0),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0)) | r1_wellord1(sK0,X0)) ) | (~spl5_1 | ~spl5_11 | ~spl5_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f23])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK3(sK0,X0) | ~r1_tarski(sK3(sK0,X0),k3_relat_1(sK0)) | ~r2_hidden(sK2(sK0,sK3(sK0,X0)),sK3(sK0,X0)) | ~v1_relat_1(sK0) | r1_wellord1(sK0,X0)) ) | (~spl5_11 | ~spl5_22)),
% 0.21/0.48    inference(resolution,[],[f142,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1)) | ~r2_hidden(X3,sK3(X0,X1)) | ~v1_relat_1(X0) | r1_wellord1(X0,X1)) ) | ~spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0))) ) | ~spl5_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f141])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl5_22 | ~spl5_1 | ~spl5_2 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f68,f26,f22,f141])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    spl5_2 <=> v1_wellord1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl5_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1) | ~v1_wellord1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK0)) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f23])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK0)) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK2(sK0,X0)),X0) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_12)),
% 0.21/0.48    inference(resolution,[],[f27,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_wellord1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1) | ~v1_relat_1(X0)) ) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_wellord1(sK0) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f26])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl5_21 | ~spl5_1 | ~spl5_2 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f56,f26,f22,f136])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl5_9 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_wellord1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k1_xboole_0 = X1 | r2_hidden(sK2(sK0,X1),X1)) ) | (~spl5_1 | ~spl5_2 | ~spl5_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f23])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k1_xboole_0 = X1 | r2_hidden(sK2(sK0,X1),X1) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.48    inference(resolution,[],[f27,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_wellord1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_relat_1(X0)) ) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl5_2 | ~spl5_1 | ~spl5_4 | ~spl5_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f97,f36,f22,f26])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl5_4 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != sK1(X0) | v1_wellord1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_18 <=> k1_xboole_0 = sK1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    v1_wellord1(sK0) | (~spl5_1 | ~spl5_4 | ~spl5_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f23])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | v1_wellord1(sK0) | (~spl5_4 | ~spl5_18)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | v1_wellord1(sK0) | (~spl5_4 | ~spl5_18)),
% 0.21/0.48    inference(superposition,[],[f37,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = sK1(sK0) | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != sK1(X0) | ~v1_relat_1(X0) | v1_wellord1(X0)) ) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl5_18 | spl5_19 | ~spl5_1 | ~spl5_10 | spl5_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f91,f60,f22,f109,f97])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl5_10 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | r2_hidden(sK4(X0,X2),X2) | ~r1_wellord1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl5_16 <=> r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK1(sK0),X0) | k1_xboole_0 = sK1(sK0) | ~r1_wellord1(sK0,X0)) ) | (~spl5_1 | ~spl5_10 | spl5_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f23])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK1(sK0),X0) | k1_xboole_0 = sK1(sK0) | ~v1_relat_1(sK0) | ~r1_wellord1(sK0,X0)) ) | (~spl5_10 | spl5_16)),
% 0.21/0.48    inference(resolution,[],[f92,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X2),X2) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | ~v1_relat_1(X0) | ~r1_wellord1(X0,X1)) ) | ~spl5_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0)) | spl5_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~spl5_1 | spl5_2 | ~spl5_5 | spl5_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    $false | (~spl5_1 | spl5_2 | ~spl5_5 | spl5_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~v1_wellord1(sK0) | spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f26])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    v1_wellord1(sK0) | (~spl5_1 | ~spl5_5 | spl5_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f23])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | v1_wellord1(sK0) | (~spl5_5 | spl5_17)),
% 0.21/0.48    inference(resolution,[],[f95,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0) | v1_wellord1(X0)) ) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl5_5 <=> ! [X0] : (~v1_relat_1(X0) | r1_tarski(sK1(X0),k3_relat_1(X0)) | v1_wellord1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~r1_tarski(sK1(sK0),k3_relat_1(sK0)) | spl5_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~spl5_16 | ~spl5_17 | spl5_18 | ~spl5_1 | spl5_2 | ~spl5_8 | ~spl5_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f88,f82,f52,f26,f22,f97,f94,f91])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl5_8 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~r2_hidden(X2,sK1(X0)) | ~r1_xboole_0(k1_wellord1(X0,X2),sK1(X0)) | v1_wellord1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl5_15 <=> ! [X0] : (k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | ~r1_tarski(X0,k3_relat_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k1_xboole_0 = sK1(sK0) | ~r1_tarski(sK1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0)) | (~spl5_1 | spl5_2 | ~spl5_8 | ~spl5_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f32])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    k1_xboole_0 = sK1(sK0) | ~r1_tarski(sK1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0)) | v1_wellord1(sK0) | (~spl5_1 | ~spl5_8 | ~spl5_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f23])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    k1_xboole_0 = sK1(sK0) | ~r1_tarski(sK1(sK0),k3_relat_1(sK0)) | ~r2_hidden(sK4(sK0,sK1(sK0)),sK1(sK0)) | ~v1_relat_1(sK0) | v1_wellord1(sK0) | (~spl5_8 | ~spl5_15)),
% 0.21/0.48    inference(resolution,[],[f83,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r1_xboole_0(k1_wellord1(X0,X2),sK1(X0)) | ~r2_hidden(X2,sK1(X0)) | ~v1_relat_1(X0) | v1_wellord1(X0)) ) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK0))) ) | ~spl5_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl5_15 | ~spl5_3 | ~spl5_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f77,f29,f82])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl5_14 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | ~r1_wellord1(sK0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | ~r1_tarski(X0,k3_relat_1(sK0))) ) | (~spl5_3 | ~spl5_14)),
% 0.21/0.48    inference(resolution,[],[f78,f30])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_wellord1(sK0,X1) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | ~r1_tarski(X0,X1)) ) | ~spl5_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl5_14 | ~spl5_1 | ~spl5_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f75,f72,f22,f77])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl5_13 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2) | ~r1_wellord1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_xboole_0(k1_wellord1(sK0,sK4(sK0,X0)),X0) | ~r1_wellord1(sK0,X1)) ) | (~spl5_1 | ~spl5_13)),
% 0.21/0.48    inference(resolution,[],[f73,f23])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2) | ~r1_wellord1(X0,X1)) ) | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl5_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f72])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | r1_xboole_0(k1_wellord1(X0,sK4(X0,X2)),X2) | ~r1_wellord1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_wellord1(X0,X1) <=> ! [X2] : (? [X3] : (r1_xboole_0(k1_wellord1(X0,X3),X2) & r2_hidden(X3,X2)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_wellord1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_xboole_0(k1_wellord1(X0,X3),X2) & r2_hidden(X3,X2)) & k1_xboole_0 != X2 & r1_tarski(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_wellord1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f68])).
% 0.21/0.48  % (17018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r1_xboole_0(k1_wellord1(X0,sK2(X0,X1)),X1) | ~v1_wellord1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  
% 0.21/0.48  % (17018)Memory used [KB]: 10490
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0] : ((v1_wellord1(X0) <=> ! [X1] : (? [X2] : (r1_xboole_0(k1_wellord1(X0,X2),X1) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  % (17018)Time elapsed: 0.061 s
% 0.21/0.48  % (17018)------------------------------
% 0.21/0.48  % (17018)------------------------------
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> ! [X1] : ~(! [X2] : ~(r1_xboole_0(k1_wellord1(X0,X2),X1) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f64])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X3,sK3(X0,X1)) | ~r1_xboole_0(k1_wellord1(X0,X3),sK3(X0,X1)) | r1_wellord1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl5_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f60])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X2,X1) | k1_xboole_0 = X2 | r2_hidden(sK4(X0,X2),X2) | ~r1_wellord1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f56])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,k3_relat_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1) | ~v1_wellord1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f52])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~v1_relat_1(X0) | ~r2_hidden(X2,sK1(X0)) | ~r1_xboole_0(k1_wellord1(X0,X2),sK1(X0)) | v1_wellord1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f48])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 != sK3(X0,X1) | r1_wellord1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(sK3(X0,X1),X1) | r1_wellord1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f40])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(sK1(X0),k3_relat_1(X0)) | v1_wellord1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f36])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != sK1(X0) | v1_wellord1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl5_2 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f9,f29,f26])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ~r1_wellord1(sK0,k3_relat_1(sK0)) | ~v1_wellord1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0] : ((v1_wellord1(X0) <~> r1_wellord1(X0,k3_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (v1_wellord1(X0) <=> r1_wellord1(X0,k3_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl5_2 | spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f8,f29,f26])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    r1_wellord1(sK0,k3_relat_1(sK0)) | v1_wellord1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f10,f22])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17026)------------------------------
% 0.21/0.48  % (17026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17026)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17026)Memory used [KB]: 10618
% 0.21/0.48  % (17026)Time elapsed: 0.058 s
% 0.21/0.49  % (17026)------------------------------
% 0.21/0.49  % (17026)------------------------------
% 0.21/0.49  % (17013)Success in time 0.121 s
%------------------------------------------------------------------------------
