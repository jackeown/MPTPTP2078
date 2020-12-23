%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :  217 ( 317 expanded)
%              Number of equality atoms :   57 (  81 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f62,f66,f78,f82,f93,f101,f116,f126,f147,f152,f161,f196,f278,f293])).

fof(f293,plain,
    ( ~ spl2_2
    | ~ spl2_7
    | spl2_17
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_7
    | spl2_17
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f115,f291])).

fof(f291,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f279,f195])).

fof(f195,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl2_26
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f279,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f65,f45,f277])).

fof(f277,plain,
    ( ! [X4,X5] :
        ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4)
        | ~ r1_tarski(X4,X5)
        | ~ v1_relat_1(k6_relat_1(X4)) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl2_30
  <=> ! [X5,X4] :
        ( ~ r1_tarski(X4,X5)
        | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4)
        | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f45,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f115,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_17
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f278,plain,
    ( spl2_30
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f156,f150,f91,f60,f276])).

fof(f60,plain,
    ( spl2_6
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f150,plain,
    ( spl2_22
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

% (10233)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f156,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,X5)
        | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4)
        | ~ v1_relat_1(k6_relat_1(X4)) )
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f153,f61])).

fof(f61,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f153,plain,
    ( ! [X4,X5] :
        ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4)
        | ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X5)
        | ~ v1_relat_1(k6_relat_1(X4)) )
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(superposition,[],[f151,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f151,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f196,plain,
    ( spl2_26
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f162,f159,f145,f194])).

fof(f145,plain,
    ( spl2_21
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f159,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f162,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(superposition,[],[f160,f146])).

fof(f146,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f160,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f117,f99,f44,f159])).

fof(f99,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f117,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f45,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f152,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f87,f76,f44,f150])).

fof(f76,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f87,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f45,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f147,plain,
    ( spl2_21
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f89,f80,f48,f44,f145])).

fof(f48,plain,
    ( spl2_3
  <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f80,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f89,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f45,f49,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f49,plain,
    ( ! [X0] : v4_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f126,plain,
    ( ~ spl2_2
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl2_2
    | spl2_16 ),
    inference(unit_resulting_resolution,[],[f45,f111])).

fof(f111,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_16
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f116,plain,
    ( ~ spl2_16
    | ~ spl2_17
    | spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f88,f76,f39,f113,f109])).

fof(f39,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f41,f77])).

fof(f41,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f101,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f36,f99])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f93,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f33,f91])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f82,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f78,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f66,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f62,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (10229)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (10229)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f306,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f42,f46,f50,f62,f66,f78,f82,f93,f101,f116,f126,f147,f152,f161,f196,f278,f293])).
% 0.22/0.47  fof(f293,plain,(
% 0.22/0.47    ~spl2_2 | ~spl2_7 | spl2_17 | ~spl2_26 | ~spl2_30),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f292])).
% 0.22/0.47  fof(f292,plain,(
% 0.22/0.47    $false | (~spl2_2 | ~spl2_7 | spl2_17 | ~spl2_26 | ~spl2_30)),
% 0.22/0.47    inference(subsumption_resolution,[],[f115,f291])).
% 0.22/0.47  fof(f291,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_2 | ~spl2_7 | ~spl2_26 | ~spl2_30)),
% 0.22/0.47    inference(forward_demodulation,[],[f279,f195])).
% 0.22/0.47  fof(f195,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | ~spl2_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f194])).
% 0.22/0.47  fof(f194,plain,(
% 0.22/0.47    spl2_26 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.47  fof(f279,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_7 | ~spl2_30)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f65,f45,f277])).
% 0.22/0.47  fof(f277,plain,(
% 0.22/0.47    ( ! [X4,X5] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4) | ~r1_tarski(X4,X5) | ~v1_relat_1(k6_relat_1(X4))) ) | ~spl2_30),
% 0.22/0.47    inference(avatar_component_clause,[],[f276])).
% 0.22/0.47  fof(f276,plain,(
% 0.22/0.47    spl2_30 <=> ! [X5,X4] : (~r1_tarski(X4,X5) | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4) | ~v1_relat_1(k6_relat_1(X4)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl2_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f113])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    spl2_17 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.47  fof(f278,plain,(
% 0.22/0.47    spl2_30 | ~spl2_6 | ~spl2_13 | ~spl2_22),
% 0.22/0.47    inference(avatar_split_clause,[],[f156,f150,f91,f60,f276])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_6 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl2_13 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    spl2_22 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.47  % (10233)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4) | ~v1_relat_1(k6_relat_1(X4))) ) | (~spl2_6 | ~spl2_13 | ~spl2_22)),
% 0.22/0.47    inference(forward_demodulation,[],[f153,f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f60])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    ( ! [X4,X5] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4) | ~r1_tarski(k2_relat_1(k6_relat_1(X4)),X5) | ~v1_relat_1(k6_relat_1(X4))) ) | (~spl2_13 | ~spl2_22)),
% 0.22/0.47    inference(superposition,[],[f151,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f91])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_22),
% 0.22/0.47    inference(avatar_component_clause,[],[f150])).
% 0.22/0.47  fof(f196,plain,(
% 0.22/0.47    spl2_26 | ~spl2_21 | ~spl2_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f162,f159,f145,f194])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    spl2_21 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    spl2_23 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_21 | ~spl2_23)),
% 0.22/0.47    inference(superposition,[],[f160,f146])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f145])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) ) | ~spl2_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f159])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    spl2_23 | ~spl2_2 | ~spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f117,f99,f44,f159])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl2_15 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) ) | (~spl2_2 | ~spl2_15)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f99])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    spl2_22 | ~spl2_2 | ~spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f87,f76,f44,f150])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl2_10 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_2 | ~spl2_10)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f76])).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    spl2_21 | ~spl2_2 | ~spl2_3 | ~spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f89,f80,f48,f44,f145])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl2_3 <=> ! [X0] : v4_relat_1(k6_relat_1(X0),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_11)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f49,f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    ~spl2_2 | spl2_16),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    $false | (~spl2_2 | spl2_16)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f45,f111])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ~v1_relat_1(k6_relat_1(sK0)) | spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl2_16 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ~spl2_16 | ~spl2_17 | spl2_1 | ~spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f88,f76,f39,f113,f109])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (spl2_1 | ~spl2_10)),
% 0.22/0.47    inference(superposition,[],[f41,f77])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f99])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f91])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f80])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f76])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f60])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f48])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f44])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f39])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10229)------------------------------
% 0.22/0.48  % (10229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10229)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10229)Memory used [KB]: 6268
% 0.22/0.48  % (10229)Time elapsed: 0.021 s
% 0.22/0.48  % (10229)------------------------------
% 0.22/0.48  % (10229)------------------------------
% 0.22/0.48  % (10216)Success in time 0.116 s
%------------------------------------------------------------------------------
