%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 180 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  311 ( 530 expanded)
%              Number of equality atoms :   58 ( 115 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f48,f53,f58,f67,f71,f75,f79,f83,f87,f93,f100,f109,f115,f125,f132,f143,f150,f155,f178])).

fof(f178,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f176,f47])).

fof(f47,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f176,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f174,f41])).

fof(f41,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f174,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(superposition,[],[f82,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_19
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k7_relat_1(X1,X0)
        | r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f155,plain,
    ( spl2_19
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f151,f147,f91,f122])).

fof(f91,plain,
    ( spl2_13
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f147,plain,
    ( spl2_22
  <=> v1_xboole_0(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f151,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(resolution,[],[f149,f92])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f149,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f150,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f145,f141,f50,f35,f147])).

fof(f35,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f50,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f141,plain,
    ( spl2_21
  <=> ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f145,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f144,f52])).

fof(f52,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f144,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(superposition,[],[f142,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f139,f107,f69,f45,f141])).

fof(f69,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f107,plain,
    ( spl2_16
  <=> ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | ~ v1_relat_1(k7_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) )
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(resolution,[],[f108,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X0))
        | ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f132,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f128,f122,f98,f55,f35])).

fof(f55,plain,
    ( spl2_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f98,plain,
    ( spl2_14
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f128,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f126,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f126,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(superposition,[],[f99,f124])).

fof(f99,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f125,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f120,f113,f39,f122])).

fof(f113,plain,
    ( spl2_17
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f120,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(resolution,[],[f114,f40])).

fof(f40,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f110,f77,f45,f113])).

fof(f77,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f78,f47])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f109,plain,
    ( spl2_16
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f105,f98,f65,f107])).

fof(f65,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
        | ~ v1_relat_1(k7_relat_1(sK1,X0))
        | v1_xboole_0(k7_relat_1(sK1,X0)) )
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(superposition,[],[f66,f99])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f100,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f95,f73,f45,f98])).

fof(f73,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f95,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f93,plain,
    ( spl2_13
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f89,f85,f50,f91])).

fof(f85,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f86,f52])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f83,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f79,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f71,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (27310)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

% (27305)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f67,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f58,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f48,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f43,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f23,f39,f35])).

fof(f23,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f39,f35])).

fof(f24,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (27309)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (27309)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f179,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f42,f43,f48,f53,f58,f67,f71,f75,f79,f83,f87,f93,f100,f109,f115,f125,f132,f143,f150,f155,f178])).
% 0.20/0.43  fof(f178,plain,(
% 0.20/0.43    spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_19),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    $false | (spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f176,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    v1_relat_1(sK1) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl2_3 <=> v1_relat_1(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    ~v1_relat_1(sK1) | (spl2_2 | ~spl2_11 | ~spl2_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f174,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | (~spl2_11 | ~spl2_19)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f172])).
% 0.20/0.43  fof(f172,plain,(
% 0.20/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | (~spl2_11 | ~spl2_19)),
% 0.20/0.43    inference(superposition,[],[f82,f124])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl2_19 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl2_11 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    spl2_19 | ~spl2_13 | ~spl2_22),
% 0.20/0.43    inference(avatar_split_clause,[],[f151,f147,f91,f122])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl2_13 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    spl2_22 <=> v1_xboole_0(k7_relat_1(sK1,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_13 | ~spl2_22)),
% 0.20/0.43    inference(resolution,[],[f149,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f91])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    v1_xboole_0(k7_relat_1(sK1,sK0)) | ~spl2_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f147])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    spl2_22 | ~spl2_1 | ~spl2_4 | ~spl2_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f145,f141,f50,f35,f147])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl2_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    spl2_21 <=> ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    v1_xboole_0(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_4 | ~spl2_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f144,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k7_relat_1(sK1,sK0)) | (~spl2_1 | ~spl2_21)),
% 0.20/0.43    inference(superposition,[],[f142,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) ) | ~spl2_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f141])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    spl2_21 | ~spl2_3 | ~spl2_8 | ~spl2_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f139,f107,f69,f45,f141])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl2_8 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl2_16 <=> ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | ~v1_relat_1(k7_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) ) | (~spl2_3 | ~spl2_8 | ~spl2_16)),
% 0.20/0.43    inference(subsumption_resolution,[],[f138,f47])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) ) | (~spl2_8 | ~spl2_16)),
% 0.20/0.43    inference(resolution,[],[f108,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f69])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) ) | ~spl2_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl2_1 | ~spl2_5 | ~spl2_14 | ~spl2_19),
% 0.20/0.43    inference(avatar_split_clause,[],[f128,f122,f98,f55,f35])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    spl2_14 <=> ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    k1_xboole_0 = k9_relat_1(sK1,sK0) | (~spl2_5 | ~spl2_14 | ~spl2_19)),
% 0.20/0.43    inference(forward_demodulation,[],[f126,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | (~spl2_14 | ~spl2_19)),
% 0.20/0.43    inference(superposition,[],[f99,f124])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f98])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    spl2_19 | ~spl2_2 | ~spl2_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f120,f113,f39,f122])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl2_17 <=> ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_2 | ~spl2_17)),
% 0.20/0.43    inference(resolution,[],[f114,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f113])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl2_17 | ~spl2_3 | ~spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f110,f77,f45,f113])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl2_10 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_10)),
% 0.20/0.43    inference(resolution,[],[f78,f47])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f77])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl2_16 | ~spl2_7 | ~spl2_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f105,f98,f65,f107])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl2_7 <=> ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | ~v1_relat_1(k7_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) ) | (~spl2_7 | ~spl2_14)),
% 0.20/0.43    inference(superposition,[],[f66,f99])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    spl2_14 | ~spl2_3 | ~spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f95,f73,f45,f98])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl2_9 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | (~spl2_3 | ~spl2_9)),
% 0.20/0.43    inference(resolution,[],[f74,f47])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f73])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl2_13 | ~spl2_4 | ~spl2_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f89,f85,f50,f91])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    spl2_12 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl2_4 | ~spl2_12)),
% 0.20/0.43    inference(resolution,[],[f86,f52])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl2_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f85])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl2_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f85])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f81])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f77])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f73])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f69])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  % (27310)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.43  % (27305)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f55])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f50])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f45])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    v1_relat_1(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f8])).
% 0.20/0.43  fof(f8,conjecture,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl2_1 | spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f39,f35])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ~spl2_1 | ~spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f39,f35])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (27309)------------------------------
% 0.20/0.43  % (27309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (27309)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (27309)Memory used [KB]: 10618
% 0.20/0.43  % (27309)Time elapsed: 0.010 s
% 0.20/0.43  % (27309)------------------------------
% 0.20/0.43  % (27309)------------------------------
% 0.20/0.44  % (27303)Success in time 0.079 s
%------------------------------------------------------------------------------
