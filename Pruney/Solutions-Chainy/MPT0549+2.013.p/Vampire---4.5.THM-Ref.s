%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 171 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  310 ( 507 expanded)
%              Number of equality atoms :   82 ( 142 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f45,f50,f55,f64,f68,f76,f80,f84,f88,f92,f101,f116,f141,f147,f178,f191,f196,f237])).

fof(f237,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f235,f49])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f235,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_2
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f234,f43])).

fof(f43,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f234,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_12
    | ~ spl2_28 ),
    inference(superposition,[],[f87,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl2_28
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) != k1_xboole_0
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f196,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f195,f145,f37,f175])).

fof(f37,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f145,plain,
    ( spl2_23
  <=> ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f195,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(superposition,[],[f146,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f146,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f145])).

fof(f191,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f189,f39])).

fof(f39,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f189,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f187,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f187,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(superposition,[],[f140,f177])).

fof(f140,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_22
  <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f178,plain,
    ( spl2_28
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f173,f82,f47,f41,f175])).

fof(f82,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f173,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f171,f49])).

fof(f171,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f83,f42])).

fof(f42,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0
        | ~ v1_relat_1(X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f147,plain,
    ( spl2_23
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f143,f139,f114,f66,f145])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f114,plain,
    ( spl2_17
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f143,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0) )
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f142,f115])).

fof(f115,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f142,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | k1_xboole_0 = k7_relat_1(sK1,X0)
        | ~ v1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(superposition,[],[f67,f140])).

fof(f67,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f141,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f125,f78,f47,f139])).

fof(f78,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f125,plain,
    ( ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f79,f49])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f116,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f112,f99,f90,f62,f47,f114])).

fof(f62,plain,
    ( spl2_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f90,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( spl2_14
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f112,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f111,f63])).

fof(f63,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f111,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( ! [X0] :
        ( v1_relat_1(k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f91,f100])).

fof(f100,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f101,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f95,f74,f47,f99])).

fof(f74,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f95,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f92,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f88,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f33,f86])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f84,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f76,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f64,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) = k1_xboole_0 )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) != k1_xboole_0 )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) = k1_xboole_0 )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k9_relat_1(X1,X0) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f45,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f24,f41,f37])).

fof(f24,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f41,f37])).

fof(f25,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:51:34 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.42  % (17113)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.43  % (17114)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.44  % (17112)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.44  % (17112)Refutation found. Thanks to Tanya!
% 0.23/0.44  % SZS status Theorem for theBenchmark
% 0.23/0.44  % SZS output start Proof for theBenchmark
% 0.23/0.44  fof(f238,plain,(
% 0.23/0.44    $false),
% 0.23/0.44    inference(avatar_sat_refutation,[],[f44,f45,f50,f55,f64,f68,f76,f80,f84,f88,f92,f101,f116,f141,f147,f178,f191,f196,f237])).
% 0.23/0.44  fof(f237,plain,(
% 0.23/0.44    spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_28),
% 0.23/0.44    inference(avatar_contradiction_clause,[],[f236])).
% 0.23/0.44  fof(f236,plain,(
% 0.23/0.44    $false | (spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_28)),
% 0.23/0.44    inference(subsumption_resolution,[],[f235,f49])).
% 0.23/0.44  fof(f49,plain,(
% 0.23/0.44    v1_relat_1(sK1) | ~spl2_3),
% 0.23/0.44    inference(avatar_component_clause,[],[f47])).
% 0.23/0.44  fof(f47,plain,(
% 0.23/0.44    spl2_3 <=> v1_relat_1(sK1)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.44  fof(f235,plain,(
% 0.23/0.44    ~v1_relat_1(sK1) | (spl2_2 | ~spl2_12 | ~spl2_28)),
% 0.23/0.44    inference(subsumption_resolution,[],[f234,f43])).
% 0.23/0.44  fof(f43,plain,(
% 0.23/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl2_2),
% 0.23/0.44    inference(avatar_component_clause,[],[f41])).
% 0.23/0.44  fof(f41,plain,(
% 0.23/0.44    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.44  fof(f234,plain,(
% 0.23/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | (~spl2_12 | ~spl2_28)),
% 0.23/0.44    inference(trivial_inequality_removal,[],[f233])).
% 0.23/0.44  fof(f233,plain,(
% 0.23/0.44    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | (~spl2_12 | ~spl2_28)),
% 0.23/0.44    inference(superposition,[],[f87,f177])).
% 0.23/0.44  fof(f177,plain,(
% 0.23/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_28),
% 0.23/0.44    inference(avatar_component_clause,[],[f175])).
% 0.23/0.44  fof(f175,plain,(
% 0.23/0.44    spl2_28 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.23/0.44  fof(f87,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_12),
% 0.23/0.44    inference(avatar_component_clause,[],[f86])).
% 0.23/0.44  fof(f86,plain,(
% 0.23/0.44    spl2_12 <=> ! [X1,X0] : (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.44  fof(f196,plain,(
% 0.23/0.44    spl2_28 | ~spl2_1 | ~spl2_23),
% 0.23/0.44    inference(avatar_split_clause,[],[f195,f145,f37,f175])).
% 0.23/0.44  fof(f37,plain,(
% 0.23/0.44    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.44  fof(f145,plain,(
% 0.23/0.44    spl2_23 <=> ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.23/0.44  fof(f195,plain,(
% 0.23/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_23)),
% 0.23/0.44    inference(trivial_inequality_removal,[],[f194])).
% 0.23/0.44  fof(f194,plain,(
% 0.23/0.44    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_1 | ~spl2_23)),
% 0.23/0.44    inference(superposition,[],[f146,f38])).
% 0.23/0.44  fof(f38,plain,(
% 0.23/0.44    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.23/0.44    inference(avatar_component_clause,[],[f37])).
% 0.23/0.44  fof(f146,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | ~spl2_23),
% 0.23/0.44    inference(avatar_component_clause,[],[f145])).
% 0.23/0.44  fof(f191,plain,(
% 0.23/0.44    spl2_1 | ~spl2_4 | ~spl2_22 | ~spl2_28),
% 0.23/0.44    inference(avatar_contradiction_clause,[],[f190])).
% 0.23/0.44  fof(f190,plain,(
% 0.23/0.44    $false | (spl2_1 | ~spl2_4 | ~spl2_22 | ~spl2_28)),
% 0.23/0.44    inference(subsumption_resolution,[],[f189,f39])).
% 0.23/0.44  fof(f39,plain,(
% 0.23/0.44    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl2_1),
% 0.23/0.44    inference(avatar_component_clause,[],[f37])).
% 0.23/0.44  fof(f189,plain,(
% 0.23/0.44    k1_xboole_0 = k9_relat_1(sK1,sK0) | (~spl2_4 | ~spl2_22 | ~spl2_28)),
% 0.23/0.44    inference(forward_demodulation,[],[f187,f54])).
% 0.23/0.44  fof(f54,plain,(
% 0.23/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_4),
% 0.23/0.44    inference(avatar_component_clause,[],[f52])).
% 0.23/0.44  fof(f52,plain,(
% 0.23/0.44    spl2_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.44  fof(f187,plain,(
% 0.23/0.44    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | (~spl2_22 | ~spl2_28)),
% 0.23/0.44    inference(superposition,[],[f140,f177])).
% 0.23/0.44  fof(f140,plain,(
% 0.23/0.44    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | ~spl2_22),
% 0.23/0.44    inference(avatar_component_clause,[],[f139])).
% 0.23/0.44  fof(f139,plain,(
% 0.23/0.44    spl2_22 <=> ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.23/0.44  fof(f178,plain,(
% 0.23/0.44    spl2_28 | ~spl2_2 | ~spl2_3 | ~spl2_11),
% 0.23/0.44    inference(avatar_split_clause,[],[f173,f82,f47,f41,f175])).
% 0.23/0.44  fof(f82,plain,(
% 0.23/0.44    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.44  fof(f173,plain,(
% 0.23/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_11)),
% 0.23/0.44    inference(subsumption_resolution,[],[f171,f49])).
% 0.23/0.44  fof(f171,plain,(
% 0.23/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | (~spl2_2 | ~spl2_11)),
% 0.23/0.44    inference(resolution,[],[f83,f42])).
% 0.23/0.44  fof(f42,plain,(
% 0.23/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.23/0.44    inference(avatar_component_clause,[],[f41])).
% 0.23/0.44  fof(f83,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) ) | ~spl2_11),
% 0.23/0.44    inference(avatar_component_clause,[],[f82])).
% 0.23/0.44  fof(f147,plain,(
% 0.23/0.44    spl2_23 | ~spl2_7 | ~spl2_17 | ~spl2_22),
% 0.23/0.44    inference(avatar_split_clause,[],[f143,f139,f114,f66,f145])).
% 0.23/0.44  fof(f66,plain,(
% 0.23/0.44    spl2_7 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.44  fof(f114,plain,(
% 0.23/0.44    spl2_17 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.23/0.44  fof(f143,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0)) ) | (~spl2_7 | ~spl2_17 | ~spl2_22)),
% 0.23/0.44    inference(subsumption_resolution,[],[f142,f115])).
% 0.23/0.44  fof(f115,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_17),
% 0.23/0.44    inference(avatar_component_clause,[],[f114])).
% 0.23/0.44  fof(f142,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k7_relat_1(sK1,X0) | ~v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_7 | ~spl2_22)),
% 0.23/0.44    inference(superposition,[],[f67,f140])).
% 0.23/0.44  fof(f67,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.23/0.44    inference(avatar_component_clause,[],[f66])).
% 0.23/0.44  fof(f141,plain,(
% 0.23/0.44    spl2_22 | ~spl2_3 | ~spl2_10),
% 0.23/0.44    inference(avatar_split_clause,[],[f125,f78,f47,f139])).
% 0.23/0.44  fof(f78,plain,(
% 0.23/0.44    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.44  fof(f125,plain,(
% 0.23/0.44    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) ) | (~spl2_3 | ~spl2_10)),
% 0.23/0.44    inference(resolution,[],[f79,f49])).
% 0.23/0.44  fof(f79,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 0.23/0.44    inference(avatar_component_clause,[],[f78])).
% 0.23/0.44  fof(f116,plain,(
% 0.23/0.44    spl2_17 | ~spl2_3 | ~spl2_6 | ~spl2_13 | ~spl2_14),
% 0.23/0.44    inference(avatar_split_clause,[],[f112,f99,f90,f62,f47,f114])).
% 0.23/0.44  fof(f62,plain,(
% 0.23/0.44    spl2_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.44  fof(f90,plain,(
% 0.23/0.44    spl2_13 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.44  fof(f99,plain,(
% 0.23/0.44    spl2_14 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.44  fof(f112,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_3 | ~spl2_6 | ~spl2_13 | ~spl2_14)),
% 0.23/0.44    inference(subsumption_resolution,[],[f111,f63])).
% 0.23/0.44  fof(f63,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_6),
% 0.23/0.44    inference(avatar_component_clause,[],[f62])).
% 0.23/0.44  fof(f111,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_13 | ~spl2_14)),
% 0.23/0.44    inference(subsumption_resolution,[],[f110,f49])).
% 0.23/0.44  fof(f110,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_13 | ~spl2_14)),
% 0.23/0.44    inference(superposition,[],[f91,f100])).
% 0.23/0.44  fof(f100,plain,(
% 0.23/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_14),
% 0.23/0.44    inference(avatar_component_clause,[],[f99])).
% 0.23/0.44  fof(f91,plain,(
% 0.23/0.44    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.23/0.44    inference(avatar_component_clause,[],[f90])).
% 0.23/0.44  fof(f101,plain,(
% 0.23/0.44    spl2_14 | ~spl2_3 | ~spl2_9),
% 0.23/0.44    inference(avatar_split_clause,[],[f95,f74,f47,f99])).
% 0.23/0.44  fof(f74,plain,(
% 0.23/0.44    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.44  fof(f95,plain,(
% 0.23/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl2_3 | ~spl2_9)),
% 0.23/0.44    inference(resolution,[],[f75,f49])).
% 0.23/0.44  fof(f75,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.23/0.44    inference(avatar_component_clause,[],[f74])).
% 0.23/0.44  fof(f92,plain,(
% 0.23/0.44    spl2_13),
% 0.23/0.44    inference(avatar_split_clause,[],[f35,f90])).
% 0.23/0.44  fof(f35,plain,(
% 0.23/0.44    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f17])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.23/0.44    inference(flattening,[],[f16])).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f1])).
% 0.23/0.44  fof(f1,axiom,(
% 0.23/0.44    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.23/0.44  fof(f88,plain,(
% 0.23/0.44    spl2_12),
% 0.23/0.44    inference(avatar_split_clause,[],[f33,f86])).
% 0.23/0.44  fof(f33,plain,(
% 0.23/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f22])).
% 0.23/0.44  fof(f22,plain,(
% 0.23/0.44    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(nnf_transformation,[],[f15])).
% 0.23/0.44  fof(f15,plain,(
% 0.23/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f7])).
% 0.23/0.44  fof(f7,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.23/0.44  fof(f84,plain,(
% 0.23/0.44    spl2_11),
% 0.23/0.44    inference(avatar_split_clause,[],[f34,f82])).
% 0.23/0.44  fof(f34,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f22])).
% 0.23/0.44  fof(f80,plain,(
% 0.23/0.44    spl2_10),
% 0.23/0.44    inference(avatar_split_clause,[],[f32,f78])).
% 0.23/0.44  fof(f32,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f14])).
% 0.23/0.44  fof(f14,plain,(
% 0.23/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.44  fof(f76,plain,(
% 0.23/0.44    spl2_9),
% 0.23/0.44    inference(avatar_split_clause,[],[f31,f74])).
% 0.23/0.44  fof(f31,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f13])).
% 0.23/0.44  fof(f13,plain,(
% 0.23/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f6])).
% 0.23/0.44  fof(f6,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.44  fof(f68,plain,(
% 0.23/0.44    spl2_7),
% 0.23/0.44    inference(avatar_split_clause,[],[f30,f66])).
% 0.23/0.44  fof(f30,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f12])).
% 0.23/0.44  fof(f12,plain,(
% 0.23/0.44    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.44    inference(flattening,[],[f11])).
% 0.23/0.44  fof(f11,plain,(
% 0.23/0.44    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,axiom,(
% 0.23/0.44    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.23/0.44  fof(f64,plain,(
% 0.23/0.44    spl2_6),
% 0.23/0.44    inference(avatar_split_clause,[],[f28,f62])).
% 0.23/0.44  fof(f28,plain,(
% 0.23/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.23/0.44  fof(f55,plain,(
% 0.23/0.44    spl2_4),
% 0.23/0.44    inference(avatar_split_clause,[],[f27,f52])).
% 0.23/0.44  fof(f27,plain,(
% 0.23/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.44    inference(cnf_transformation,[],[f4])).
% 0.23/0.44  fof(f4,axiom,(
% 0.23/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.44  fof(f50,plain,(
% 0.23/0.44    spl2_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f23,f47])).
% 0.23/0.44  fof(f23,plain,(
% 0.23/0.44    v1_relat_1(sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 0.23/0.44  fof(f20,plain,(
% 0.23/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f19,plain,(
% 0.23/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0) & v1_relat_1(X1))),
% 0.23/0.44    inference(flattening,[],[f18])).
% 0.23/0.44  fof(f18,plain,(
% 0.23/0.44    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0)) & v1_relat_1(X1))),
% 0.23/0.44    inference(nnf_transformation,[],[f10])).
% 0.23/0.44  fof(f10,plain,(
% 0.23/0.44    ? [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f9])).
% 0.23/0.44  fof(f9,negated_conjecture,(
% 0.23/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.23/0.44    inference(negated_conjecture,[],[f8])).
% 0.23/0.44  fof(f8,conjecture,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.23/0.44  fof(f45,plain,(
% 0.23/0.44    spl2_1 | spl2_2),
% 0.23/0.44    inference(avatar_split_clause,[],[f24,f41,f37])).
% 0.23/0.44  fof(f24,plain,(
% 0.23/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f21])).
% 0.23/0.44  fof(f44,plain,(
% 0.23/0.44    ~spl2_1 | ~spl2_2),
% 0.23/0.44    inference(avatar_split_clause,[],[f25,f41,f37])).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f21])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (17112)------------------------------
% 0.23/0.44  % (17112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (17112)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (17112)Memory used [KB]: 10618
% 0.23/0.44  % (17112)Time elapsed: 0.009 s
% 0.23/0.44  % (17112)------------------------------
% 0.23/0.44  % (17112)------------------------------
% 0.23/0.45  % (17106)Success in time 0.078 s
%------------------------------------------------------------------------------
