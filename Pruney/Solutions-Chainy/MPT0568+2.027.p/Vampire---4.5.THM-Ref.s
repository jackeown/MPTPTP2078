%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 204 expanded)
%              Number of leaves         :   33 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 ( 378 expanded)
%              Number of equality atoms :  105 ( 194 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f75,f83,f87,f104,f112,f117,f130,f140,f167,f173,f177,f187,f198])).

fof(f198,plain,
    ( ~ spl1_13
    | ~ spl1_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl1_13
    | ~ spl1_15 ),
    inference(subsumption_resolution,[],[f111,f125])).

fof(f125,plain,
    ( ! [X4] : k1_xboole_0 != X4
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl1_15
  <=> ! [X4] : k1_xboole_0 != X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl1_13
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f187,plain,
    ( ~ spl1_3
    | spl1_4
    | ~ spl1_16
    | ~ spl1_17
    | ~ spl1_23
    | ~ spl1_24 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl1_3
    | spl1_4
    | ~ spl1_16
    | ~ spl1_17
    | ~ spl1_23
    | ~ spl1_24 ),
    inference(subsumption_resolution,[],[f70,f185])).

fof(f185,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl1_3
    | ~ spl1_16
    | ~ spl1_17
    | ~ spl1_23
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f184,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl1_17
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f184,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2)
    | ~ spl1_3
    | ~ spl1_16
    | ~ spl1_23
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f183,f172])).

fof(f172,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl1_23
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f183,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)))
    | ~ spl1_3
    | ~ spl1_16
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f181,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f181,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k6_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X2)))
    | ~ spl1_16
    | ~ spl1_24 ),
    inference(resolution,[],[f176,f129])).

fof(f129,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl1_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl1_24
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f70,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl1_4
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f177,plain,(
    spl1_24 ),
    inference(avatar_split_clause,[],[f52,f175])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f173,plain,
    ( spl1_23
    | ~ spl1_13
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f168,f165,f110,f171])).

fof(f165,plain,
    ( spl1_22
  <=> ! [X1,X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f168,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))
    | ~ spl1_13
    | ~ spl1_22 ),
    inference(superposition,[],[f111,f166])).

fof(f166,plain,
    ( ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,(
    spl1_22 ),
    inference(avatar_split_clause,[],[f51,f165])).

fof(f51,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f48,f48])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f140,plain,
    ( spl1_17
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f135,f127,f81,f63,f58,f137])).

fof(f58,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f81,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f135,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f134,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f134,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f133,f65])).

fof(f133,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_16 ),
    inference(resolution,[],[f129,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f130,plain,
    ( spl1_15
    | spl1_16
    | ~ spl1_1
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f122,f115,f54,f127,f124])).

fof(f54,plain,
    ( spl1_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f115,plain,
    ( spl1_14
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = k6_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

% (6222)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f122,plain,
    ( ! [X4] :
        ( v1_relat_1(k1_xboole_0)
        | k1_xboole_0 != X4 )
    | ~ spl1_1
    | ~ spl1_14 ),
    inference(superposition,[],[f55,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k6_relat_1(X0)
        | k1_xboole_0 != X0 )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f55,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f54])).

% (6213)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f117,plain,
    ( spl1_14
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f113,f102,f73,f115])).

fof(f73,plain,
    ( spl1_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f102,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
        | k1_xboole_0 = k6_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | k1_xboole_0 = k6_relat_1(X0) )
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(superposition,[],[f103,f74])).

fof(f74,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f103,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
        | k1_xboole_0 = k6_relat_1(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f112,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f50,f110])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f104,plain,
    ( spl1_11
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f99,f85,f54,f102])).

fof(f85,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k6_relat_1(X0))
        | k1_xboole_0 = k6_relat_1(X0) )
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f83,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f75,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f71,plain,(
    ~ spl1_4 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).

fof(f23,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f66,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f61,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (6219)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (6215)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (6227)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (6219)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f75,f83,f87,f104,f112,f117,f130,f140,f167,f173,f177,f187,f198])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ~spl1_13 | ~spl1_15),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    $false | (~spl1_13 | ~spl1_15)),
% 0.21/0.46    inference(subsumption_resolution,[],[f111,f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X4] : (k1_xboole_0 != X4) ) | ~spl1_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f124])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    spl1_15 <=> ! [X4] : k1_xboole_0 != X4),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ) | ~spl1_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl1_13 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ~spl1_3 | spl1_4 | ~spl1_16 | ~spl1_17 | ~spl1_23 | ~spl1_24),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    $false | (~spl1_3 | spl1_4 | ~spl1_16 | ~spl1_17 | ~spl1_23 | ~spl1_24)),
% 0.21/0.46    inference(subsumption_resolution,[],[f70,f185])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | (~spl1_3 | ~spl1_16 | ~spl1_17 | ~spl1_23 | ~spl1_24)),
% 0.21/0.46    inference(forward_demodulation,[],[f184,f139])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f137])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    spl1_17 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ( ! [X2] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X2)) ) | (~spl1_3 | ~spl1_16 | ~spl1_23 | ~spl1_24)),
% 0.21/0.46    inference(forward_demodulation,[],[f183,f172])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ) | ~spl1_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f171])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl1_23 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)))) ) | (~spl1_3 | ~spl1_16 | ~spl1_24)),
% 0.21/0.46    inference(forward_demodulation,[],[f181,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,k1_setfam_1(k6_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X2)))) ) | (~spl1_16 | ~spl1_24)),
% 0.21/0.46    inference(resolution,[],[f176,f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    v1_relat_1(k1_xboole_0) | ~spl1_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f127])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    spl1_16 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)))) ) | ~spl1_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f175])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    spl1_24 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl1_4 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    spl1_24),
% 0.21/0.46    inference(avatar_split_clause,[],[f52,f175])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f38,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f37,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f36,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f39,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f40,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f41,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f42,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl1_23 | ~spl1_13 | ~spl1_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f168,f165,f110,f171])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    spl1_22 <=> ! [X1,X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ) | (~spl1_13 | ~spl1_22)),
% 0.21/0.46    inference(superposition,[],[f111,f166])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ) | ~spl1_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f165])).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    spl1_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f165])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f35,f48,f48])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    spl1_17 | ~spl1_2 | ~spl1_3 | ~spl1_7 | ~spl1_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f135,f127,f81,f63,f58,f137])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl1_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl1_7 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_3 | ~spl1_7 | ~spl1_16)),
% 0.21/0.46    inference(forward_demodulation,[],[f134,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_3 | ~spl1_7 | ~spl1_16)),
% 0.21/0.46    inference(forward_demodulation,[],[f133,f65])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl1_7 | ~spl1_16)),
% 0.21/0.46    inference(resolution,[],[f129,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) ) | ~spl1_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    spl1_15 | spl1_16 | ~spl1_1 | ~spl1_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f122,f115,f54,f127,f124])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl1_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl1_14 <=> ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.46  % (6222)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X4] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X4) ) | (~spl1_1 | ~spl1_14)),
% 0.21/0.46    inference(superposition,[],[f55,f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k6_relat_1(X0) | k1_xboole_0 != X0) ) | ~spl1_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  % (6213)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl1_14 | ~spl1_5 | ~spl1_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f113,f102,f73,f115])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl1_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    spl1_11 <=> ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) ) | (~spl1_5 | ~spl1_11)),
% 0.21/0.46    inference(superposition,[],[f103,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) ) | ~spl1_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f102])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    spl1_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f50,f110])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f29,f49])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl1_11 | ~spl1_1 | ~spl1_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f99,f85,f54,f102])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl1_8 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) ) | (~spl1_1 | ~spl1_8)),
% 0.21/0.46    inference(resolution,[],[f86,f55])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl1_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl1_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f85])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl1_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f32,f81])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl1_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f73])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ~spl1_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f68])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f16])).
% 0.21/0.46  fof(f16,conjecture,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl1_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (6219)------------------------------
% 0.21/0.46  % (6219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6219)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (6219)Memory used [KB]: 6268
% 0.21/0.46  % (6219)Time elapsed: 0.054 s
% 0.21/0.46  % (6219)------------------------------
% 0.21/0.46  % (6219)------------------------------
% 0.21/0.46  % (6218)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (6211)Success in time 0.111 s
%------------------------------------------------------------------------------
