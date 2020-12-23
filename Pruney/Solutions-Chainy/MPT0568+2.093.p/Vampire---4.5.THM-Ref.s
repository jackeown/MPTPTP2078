%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 180 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :    6
%              Number of atoms          :  276 ( 401 expanded)
%              Number of equality atoms :  101 ( 150 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f72,f77,f81,f85,f89,f93,f109,f113,f117,f125,f129,f155,f159,f184,f199,f216,f251,f274,f293,f301])).

fof(f301,plain,
    ( spl1_1
    | ~ spl1_31
    | ~ spl1_33
    | ~ spl1_38 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl1_1
    | ~ spl1_31
    | ~ spl1_33
    | ~ spl1_38 ),
    inference(subsumption_resolution,[],[f58,f299])).

fof(f299,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_31
    | ~ spl1_33
    | ~ spl1_38 ),
    inference(forward_demodulation,[],[f295,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_31 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl1_31
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f295,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_33
    | ~ spl1_38 ),
    inference(superposition,[],[f250,f292])).

fof(f292,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl1_38 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl1_38
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f250,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl1_33
  <=> ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f58,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f293,plain,
    ( spl1_38
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_36 ),
    inference(avatar_split_clause,[],[f282,f272,f127,f79,f291])).

fof(f79,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f127,plain,
    ( spl1_18
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f272,plain,
    ( spl1_36
  <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f282,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl1_6
    | ~ spl1_18
    | ~ spl1_36 ),
    inference(forward_demodulation,[],[f277,f80])).

fof(f80,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f277,plain,
    ( ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl1_18
    | ~ spl1_36 ),
    inference(superposition,[],[f273,f128])).

fof(f128,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f273,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_36 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl1_36
    | ~ spl1_17
    | ~ spl1_20
    | ~ spl1_28 ),
    inference(avatar_split_clause,[],[f206,f197,f153,f123,f272])).

fof(f123,plain,
    ( spl1_17
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f153,plain,
    ( spl1_20
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f197,plain,
    ( spl1_28
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f206,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_17
    | ~ spl1_20
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f205,f154])).

fof(f154,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f205,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl1_17
    | ~ spl1_28 ),
    inference(superposition,[],[f124,f198])).

fof(f198,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f124,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f251,plain,
    ( spl1_33
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_21
    | ~ spl1_26 ),
    inference(avatar_split_clause,[],[f188,f181,f157,f74,f61,f249])).

fof(f61,plain,
    ( spl1_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f74,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f157,plain,
    ( spl1_21
  <=> ! [X1,X0] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f181,plain,
    ( spl1_26
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f188,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | ~ spl1_2
    | ~ spl1_5
    | ~ spl1_21
    | ~ spl1_26 ),
    inference(subsumption_resolution,[],[f165,f187])).

fof(f187,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_26 ),
    inference(superposition,[],[f62,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f181])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f165,plain,
    ( ! [X0] :
        ( k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_21 ),
    inference(superposition,[],[f158,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
        | ~ v1_relat_1(X1) )
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f216,plain,
    ( spl1_31
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_14
    | ~ spl1_26 ),
    inference(avatar_split_clause,[],[f189,f181,f111,f74,f69,f61,f213])).

fof(f69,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f111,plain,
    ( spl1_14
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f189,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_14
    | ~ spl1_26 ),
    inference(subsumption_resolution,[],[f140,f187])).

fof(f140,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f136,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f136,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_14 ),
    inference(superposition,[],[f112,f76])).

fof(f112,plain,
    ( ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f199,plain,
    ( spl1_28
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f151,f127,f87,f83,f197])).

fof(f83,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f87,plain,
    ( spl1_8
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f151,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f150,f88])).

fof(f88,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f150,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_18 ),
    inference(superposition,[],[f128,f84])).

fof(f84,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f184,plain,
    ( spl1_26
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f142,f115,f91,f61,f181])).

fof(f91,plain,
    ( spl1_9
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f115,plain,
    ( spl1_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f142,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_9
    | ~ spl1_15 ),
    inference(unit_resulting_resolution,[],[f62,f92,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f92,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f159,plain,(
    spl1_21 ),
    inference(avatar_split_clause,[],[f48,f157])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f155,plain,
    ( spl1_20
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f130,f107,f65,f153])).

fof(f65,plain,
    ( spl1_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f107,plain,
    ( spl1_13
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f130,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl1_3
    | ~ spl1_13 ),
    inference(unit_resulting_resolution,[],[f66,f108])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f129,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f125,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f46,f123])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f117,plain,(
    spl1_15 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f113,plain,(
    spl1_14 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f109,plain,(
    spl1_13 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f93,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f39,f91])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f89,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f77,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f72,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f35,f65])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f59,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).

fof(f29,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

% (31134)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f23,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:11:39 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (31126)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (31125)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31126)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f59,f63,f67,f72,f77,f81,f85,f89,f93,f109,f113,f117,f125,f129,f155,f159,f184,f199,f216,f251,f274,f293,f301])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    spl1_1 | ~spl1_31 | ~spl1_33 | ~spl1_38),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    $false | (spl1_1 | ~spl1_31 | ~spl1_33 | ~spl1_38)),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f299])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_31 | ~spl1_33 | ~spl1_38)),
% 0.21/0.48    inference(forward_demodulation,[],[f295,f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl1_31 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_33 | ~spl1_38)),
% 0.21/0.48    inference(superposition,[],[f250,f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl1_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f291])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl1_38 <=> ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | ~spl1_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f249])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl1_33 <=> ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    spl1_38 | ~spl1_6 | ~spl1_18 | ~spl1_36),
% 0.21/0.48    inference(avatar_split_clause,[],[f282,f272,f127,f79,f291])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl1_6 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl1_18 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    spl1_36 <=> ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | (~spl1_6 | ~spl1_18 | ~spl1_36)),
% 0.21/0.48    inference(forward_demodulation,[],[f277,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)) ) | (~spl1_18 | ~spl1_36)),
% 0.21/0.48    inference(superposition,[],[f273,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl1_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f127])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl1_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f272])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    spl1_36 | ~spl1_17 | ~spl1_20 | ~spl1_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f206,f197,f153,f123,f272])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl1_17 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl1_20 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl1_28 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_17 | ~spl1_20 | ~spl1_28)),
% 0.21/0.48    inference(forward_demodulation,[],[f205,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl1_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f153])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl1_17 | ~spl1_28)),
% 0.21/0.48    inference(superposition,[],[f124,f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl1_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f123])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    spl1_33 | ~spl1_2 | ~spl1_5 | ~spl1_21 | ~spl1_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f181,f157,f74,f61,f249])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl1_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl1_21 <=> ! [X1,X0] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl1_26 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ) | (~spl1_2 | ~spl1_5 | ~spl1_21 | ~spl1_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_26)),
% 0.21/0.48    inference(superposition,[],[f62,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f181])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_21)),
% 0.21/0.48    inference(superposition,[],[f158,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) ) | ~spl1_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    spl1_31 | ~spl1_2 | ~spl1_4 | ~spl1_5 | ~spl1_14 | ~spl1_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f189,f181,f111,f74,f69,f61,f213])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl1_14 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_2 | ~spl1_4 | ~spl1_5 | ~spl1_14 | ~spl1_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f187])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_4 | ~spl1_5 | ~spl1_14)),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl1_5 | ~spl1_14)),
% 0.21/0.48    inference(superposition,[],[f112,f76])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl1_28 | ~spl1_7 | ~spl1_8 | ~spl1_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f151,f127,f87,f83,f197])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl1_7 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl1_8 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl1_7 | ~spl1_8 | ~spl1_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f150,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) ) | (~spl1_7 | ~spl1_18)),
% 0.21/0.48    inference(superposition,[],[f128,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl1_26 | ~spl1_2 | ~spl1_9 | ~spl1_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f115,f91,f61,f181])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl1_9 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl1_15 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_9 | ~spl1_15)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f92,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl1_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl1_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f157])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl1_20 | ~spl1_3 | ~spl1_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f130,f107,f65,f153])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl1_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl1_13 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl1_3 | ~spl1_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f66,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl1_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl1_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f127])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl1_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f123])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl1_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f115])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl1_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f111])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl1_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f107])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl1_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f91])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl1_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f87])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl1_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f83])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl1_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f79])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl1_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f74])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,axiom,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl1_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f69])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl1_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f65])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl1_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f61])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~spl1_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f56])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  % (31134)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,negated_conjecture,(
% 0.21/0.48    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f21])).
% 0.21/0.48  fof(f21,conjecture,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31126)------------------------------
% 0.21/0.48  % (31126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31126)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31126)Memory used [KB]: 6268
% 0.21/0.48  % (31126)Time elapsed: 0.069 s
% 0.21/0.48  % (31126)------------------------------
% 0.21/0.48  % (31126)------------------------------
% 0.21/0.49  % (31131)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (31123)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (31120)Success in time 0.125 s
%------------------------------------------------------------------------------
