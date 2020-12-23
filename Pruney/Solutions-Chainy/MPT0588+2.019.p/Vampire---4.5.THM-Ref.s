%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 324 expanded)
%              Number of leaves         :   28 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 ( 467 expanded)
%              Number of equality atoms :   72 ( 280 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f75,f79,f83,f89,f96,f105,f111,f116,f131,f141])).

% (14188)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (14184)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f141,plain,
    ( spl2_4
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl2_4
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f134,f110])).

fof(f110,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_11
  <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f134,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f74,f130])).

fof(f130,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_14
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f74,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_4
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f131,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f126,f114,f59,f129])).

fof(f59,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

% (14173)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f126,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f115,f61])).

fof(f61,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f111,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f107,f103,f64,f59,f109])).

fof(f64,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f103,plain,
    ( spl2_10
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f107,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f106,f61])).

fof(f106,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X0))
        | k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f97,f94,f77,f103])).

fof(f77,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f94,plain,
    ( spl2_8
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f97,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f95,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f95,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f91,f87,f68,f94])).

fof(f68,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f87,plain,
    ( spl2_7
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

% (14186)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f91,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(superposition,[],[f69,f88])).

fof(f88,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f69,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

% (14174)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f89,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f84,f81,f59,f87])).

fof(f81,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f82,f61])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f56,f81])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f75,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f55,f72])).

fof(f55,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f53,f50])).

fof(f53,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f28,f46,f46])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f26,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f70,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f54,f68])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f66,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f62,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (14187)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (14177)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (14179)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (14183)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (14175)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (14176)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (14179)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f62,f66,f70,f75,f79,f83,f89,f96,f105,f111,f116,f131,f141])).
% 0.21/0.48  % (14188)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (14184)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl2_4 | ~spl2_11 | ~spl2_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    $false | (spl2_4 | ~spl2_11 | ~spl2_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl2_11 <=> ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | (spl2_4 | ~spl2_14)),
% 0.21/0.48    inference(superposition,[],[f74,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl2_14 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) | spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl2_4 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl2_14 | ~spl2_1 | ~spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f114,f59,f129])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl2_12 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.48  % (14173)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl2_1 | ~spl2_12)),
% 0.21/0.48    inference(resolution,[],[f115,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl2_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f114])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f52,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f31,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f29,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f30,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f35,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f37,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f38,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f36,f46])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl2_11 | ~spl2_1 | ~spl2_2 | ~spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f103,f64,f59,f109])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl2_2 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl2_10 <=> ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f61])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_10)),
% 0.21/0.48    inference(resolution,[],[f104,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl2_10 | ~spl2_5 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f94,f77,f103])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl2_5 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl2_8 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.48    inference(resolution,[],[f95,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl2_8 | ~spl2_3 | ~spl2_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f87,f68,f94])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl2_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl2_7 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.48  % (14186)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.48    inference(superposition,[],[f69,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) ) | ~spl2_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  % (14174)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f81,f59,f87])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl2_6 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_6)),
% 0.21/0.48    inference(resolution,[],[f82,f61])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f81])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f51,f50])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f33,f46])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f77])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f55,f72])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))),
% 0.21/0.48    inference(backward_demodulation,[],[f53,f50])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))))),
% 0.21/0.48    inference(backward_demodulation,[],[f47,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f28,f46,f46])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f46])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f68])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f48,f50])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f27,f46])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f64])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14179)------------------------------
% 0.21/0.48  % (14179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14179)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14179)Memory used [KB]: 6140
% 0.21/0.48  % (14179)Time elapsed: 0.010 s
% 0.21/0.48  % (14179)------------------------------
% 0.21/0.48  % (14179)------------------------------
% 0.21/0.48  % (14189)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (14178)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (14171)Success in time 0.124 s
%------------------------------------------------------------------------------
