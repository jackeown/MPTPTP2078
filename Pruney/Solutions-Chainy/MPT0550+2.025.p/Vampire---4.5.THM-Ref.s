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
% DateTime   : Thu Dec  3 12:49:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 133 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  248 ( 383 expanded)
%              Number of equality atoms :   48 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f54,f62,f66,f72,f77,f86,f92,f96,f101,f108,f117])).

fof(f117,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f37,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f114,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f113,f33])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ v1_relat_1(sK1)
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f110,f41])).

% (3180)Refutation not found, incomplete strategy% (3180)------------------------------
% (3180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f41,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f110,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f91,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_17
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f108,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f104,f99,f70,f44,f32,f106])).

fof(f44,plain,
    ( spl3_4
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f104,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f103,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f102,f71])).

fof(f71,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f102,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f100,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f97,f94,f60,f99])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f94,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k7_relat_1(X0,X1) )
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(resolution,[],[f95,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl3_15
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f88,f84,f75,f64,f94])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f75,plain,
    ( spl3_11
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f84,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f87,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(superposition,[],[f76,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f92,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f29,f90])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f86,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f28,f84])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f77,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f72,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f68,f60,f48,f70])).

fof(f48,plain,
    ( spl3_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f49,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (3189)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (3198)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (3180)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3192)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3183)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (3189)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f54,f62,f66,f72,f77,f86,f92,f96,f101,f108,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_14 | ~spl3_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_6 | ~spl3_14 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_2 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_14 | ~spl3_17)),
% 0.21/0.48    inference(forward_demodulation,[],[f114,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl3_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = sK0 | (~spl3_1 | ~spl3_3 | ~spl3_14 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl3_1 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = sK0 | ~v1_relat_1(sK1) | (~spl3_3 | ~spl3_14 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f41])).
% 0.21/0.48  % (3180)Refutation not found, incomplete strategy% (3180)------------------------------
% 0.21/0.48  % (3180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_3 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = sK0 | ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_14 | ~spl3_17)),
% 0.21/0.48    inference(superposition,[],[f91,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl3_17 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_14 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl3_17 | ~spl3_1 | ~spl3_4 | ~spl3_10 | ~spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f99,f70,f44,f32,f106])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_4 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl3_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl3_16 <=> ! [X1,X0] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl3_1 | ~spl3_4 | ~spl3_10 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f33])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl3_4 | ~spl3_10 | ~spl3_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl3_4 | ~spl3_16)),
% 0.21/0.48    inference(superposition,[],[f100,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) ) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_16 | ~spl3_8 | ~spl3_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f94,f60,f99])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_15 <=> ! [X1,X0] : (~v1_xboole_0(k9_relat_1(X0,X1)) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) ) | (~spl3_8 | ~spl3_15)),
% 0.21/0.49    inference(resolution,[],[f95,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_15 | ~spl3_9 | ~spl3_11 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f84,f75,f64,f94])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_11 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl3_9 | ~spl3_11 | ~spl3_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl3_11 | ~spl3_13)),
% 0.21/0.49    inference(superposition,[],[f76,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f90])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f84])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f75])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_10 | ~spl3_5 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f60,f48,f70])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl3_5 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | (~spl3_5 | ~spl3_8)),
% 0.21/0.49    inference(backward_demodulation,[],[f49,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | (~spl3_5 | ~spl3_8)),
% 0.21/0.49    inference(resolution,[],[f61,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    v1_xboole_0(sK2) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f48])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_xboole_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f36])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f32])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3189)------------------------------
% 0.21/0.49  % (3189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3189)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3189)Memory used [KB]: 10618
% 0.21/0.49  % (3189)Time elapsed: 0.075 s
% 0.21/0.49  % (3189)------------------------------
% 0.21/0.49  % (3189)------------------------------
% 0.21/0.49  % (3175)Success in time 0.131 s
%------------------------------------------------------------------------------
