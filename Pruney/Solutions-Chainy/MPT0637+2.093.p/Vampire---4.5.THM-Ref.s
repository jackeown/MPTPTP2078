%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 139 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  237 ( 342 expanded)
%              Number of equality atoms :   67 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f53,f57,f61,f65,f80,f84,f92,f102,f130,f134,f143,f155,f163,f194,f305,f324])).

fof(f324,plain,
    ( ~ spl2_2
    | ~ spl2_6
    | spl2_18
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6
    | spl2_18
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(subsumption_resolution,[],[f129,f322])).

fof(f322,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f306,f193])).

fof(f193,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_26
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f306,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f60,f44,f304])).

fof(f304,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl2_32
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f44,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f129,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_18
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f305,plain,
    ( spl2_32
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f158,f153,f90,f55,f303])).

fof(f55,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f153,plain,
    ( spl2_22
  <=> ! [X1,X0] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f158,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f156,f56])).

fof(f56,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f156,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3)
        | ~ r1_tarski(k2_relat_1(k6_relat_1(X3)),X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(superposition,[],[f154,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f154,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f194,plain,
    ( spl2_26
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f170,f161,f51,f43,f192])).

fof(f51,plain,
    ( spl2_4
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f161,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f170,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f164,f52])).

fof(f52,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f164,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f44,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl2_23
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f108,f100,f63,f161])).

fof(f63,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f100,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(superposition,[],[f101,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f155,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f144,f141,f82,f43,f153])).

fof(f82,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f141,plain,
    ( spl2_20
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f144,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f142,f95])).

fof(f95,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f44,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f142,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f78,f43,f141])).

fof(f78,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f44,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f134,plain,
    ( ~ spl2_2
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl2_2
    | spl2_17 ),
    inference(unit_resulting_resolution,[],[f44,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_17
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f130,plain,
    ( ~ spl2_17
    | ~ spl2_18
    | spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f97,f82,f38,f127,f123])).

fof(f38,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f97,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_1
    | ~ spl2_11 ),
    inference(superposition,[],[f40,f83])).

fof(f40,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f102,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f36,f100])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f92,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f84,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f80,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f65,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f61,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f57,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (11142)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (11142)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f340,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f41,f45,f53,f57,f61,f65,f80,f84,f92,f102,f130,f134,f143,f155,f163,f194,f305,f324])).
% 0.21/0.45  fof(f324,plain,(
% 0.21/0.45    ~spl2_2 | ~spl2_6 | spl2_18 | ~spl2_26 | ~spl2_32),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.45  fof(f323,plain,(
% 0.21/0.45    $false | (~spl2_2 | ~spl2_6 | spl2_18 | ~spl2_26 | ~spl2_32)),
% 0.21/0.45    inference(subsumption_resolution,[],[f129,f322])).
% 0.21/0.45  fof(f322,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_2 | ~spl2_6 | ~spl2_26 | ~spl2_32)),
% 0.21/0.45    inference(forward_demodulation,[],[f306,f193])).
% 0.21/0.45  fof(f193,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | ~spl2_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f192])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    spl2_26 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_6 | ~spl2_32)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f60,f44,f304])).
% 0.21/0.45  fof(f304,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~r1_tarski(X3,X2) | ~v1_relat_1(k6_relat_1(X3))) ) | ~spl2_32),
% 0.21/0.45    inference(avatar_component_clause,[],[f303])).
% 0.21/0.45  fof(f303,plain,(
% 0.21/0.45    spl2_32 <=> ! [X3,X2] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~v1_relat_1(k6_relat_1(X3)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl2_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f127])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    spl2_18 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.45  fof(f305,plain,(
% 0.21/0.45    spl2_32 | ~spl2_5 | ~spl2_13 | ~spl2_22),
% 0.21/0.45    inference(avatar_split_clause,[],[f158,f153,f90,f55,f303])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl2_13 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    spl2_22 <=> ! [X1,X0] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.45  fof(f158,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_5 | ~spl2_13 | ~spl2_22)),
% 0.21/0.45    inference(forward_demodulation,[],[f156,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f55])).
% 0.21/0.45  fof(f156,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X2),X3) | ~r1_tarski(k2_relat_1(k6_relat_1(X3)),X2) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_13 | ~spl2_22)),
% 0.21/0.45    inference(superposition,[],[f154,f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f154,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f153])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    spl2_26 | ~spl2_2 | ~spl2_4 | ~spl2_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f170,f161,f51,f43,f192])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl2_4 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    spl2_23 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_23)),
% 0.21/0.45    inference(forward_demodulation,[],[f164,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f51])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ) | (~spl2_2 | ~spl2_23)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f44,f162])).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) ) | ~spl2_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f161])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    spl2_23 | ~spl2_7 | ~spl2_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f108,f100,f63,f161])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl2_7 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl2_14 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) ) | (~spl2_7 | ~spl2_14)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_7 | ~spl2_14)),
% 0.21/0.45    inference(superposition,[],[f101,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f63])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) ) | ~spl2_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    spl2_22 | ~spl2_2 | ~spl2_11 | ~spl2_20),
% 0.21/0.45    inference(avatar_split_clause,[],[f144,f141,f82,f43,f153])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    spl2_20 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_2 | ~spl2_11 | ~spl2_20)),
% 0.21/0.45    inference(forward_demodulation,[],[f142,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_2 | ~spl2_11)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f44,f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f82])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f141])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    spl2_20 | ~spl2_2 | ~spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f93,f78,f43,f141])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl2_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_10)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f44,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    ~spl2_2 | spl2_17),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    $false | (~spl2_2 | spl2_17)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f44,f125])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    ~v1_relat_1(k6_relat_1(sK0)) | spl2_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    spl2_17 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ~spl2_17 | ~spl2_18 | spl2_1 | ~spl2_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f97,f82,f38,f127,f123])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | (spl2_1 | ~spl2_11)),
% 0.21/0.45    inference(superposition,[],[f40,f83])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f38])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl2_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f100])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl2_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f34,f90])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl2_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f82])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl2_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl2_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f55])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f51])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f43])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f38])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f12])).
% 0.21/0.45  fof(f12,conjecture,(
% 0.21/0.45    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (11142)------------------------------
% 0.21/0.45  % (11142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (11142)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (11142)Memory used [KB]: 6396
% 0.21/0.45  % (11142)Time elapsed: 0.014 s
% 0.21/0.45  % (11142)------------------------------
% 0.21/0.45  % (11142)------------------------------
% 0.21/0.45  % (11134)Success in time 0.094 s
%------------------------------------------------------------------------------
