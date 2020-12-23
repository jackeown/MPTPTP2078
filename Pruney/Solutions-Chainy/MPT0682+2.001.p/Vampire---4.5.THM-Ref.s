%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 159 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 416 expanded)
%              Number of equality atoms :   75 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f62,f66,f74,f78,f82,f96,f100,f104,f113,f140,f191,f207,f219,f241,f267,f272,f302,f306])).

fof(f306,plain,
    ( ~ spl3_4
    | spl3_45 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl3_4
    | spl3_45 ),
    inference(unit_resulting_resolution,[],[f65,f301])).

fof(f301,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl3_45
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f65,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f302,plain,
    ( ~ spl3_1
    | ~ spl3_45
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f280,f270,f189,f80,f59,f299,f49])).

fof(f49,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_3
  <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f189,plain,
    ( spl3_28
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f270,plain,
    ( spl3_42
  <=> ! [X5,X7,X6] :
        ( k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f280,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f276,f198])).

fof(f198,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(superposition,[],[f190,f81])).

fof(f81,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f190,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f189])).

fof(f276,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | spl3_3
    | ~ spl3_42 ),
    inference(superposition,[],[f61,f271])).

fof(f271,plain,
    ( ! [X6,X7,X5] :
        ( k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f270])).

fof(f61,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f272,plain,
    ( spl3_42
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f268,f265,f239,f270])).

fof(f239,plain,
    ( spl3_36
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f265,plain,
    ( spl3_41
  <=> ! [X5,X7,X6] :
        ( k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f268,plain,
    ( ! [X6,X7,X5] :
        ( k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) )
    | ~ spl3_36
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f266,f240])).

fof(f240,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f239])).

fof(f266,plain,
    ( ! [X6,X7,X5] :
        ( k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( spl3_41
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f152,f138,f98,f265])).

fof(f98,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f138,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f152,plain,
    ( ! [X6,X7,X5] :
        ( k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5) )
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X6,X7,X5] :
        ( k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7)
        | ~ v1_relat_1(k6_relat_1(X6))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X5) )
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(superposition,[],[f139,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f138])).

fof(f241,plain,
    ( spl3_36
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f221,f217,f205,f111,f98,f72,f64,f239])).

fof(f72,plain,
    ( spl3_6
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f205,plain,
    ( spl3_31
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f217,plain,
    ( spl3_33
  <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f221,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_15
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f220,f132])).

fof(f132,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f131,f73])).

fof(f73,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f131,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0)
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f65,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f220,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_31
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f218,f208])).

fof(f208,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f206,f117])).

fof(f117,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f65,f99])).

fof(f206,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f205])).

fof(f218,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f121,f102,f64,f217])).

fof(f102,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f121,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f65,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f207,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f115,f94,f64,f205])).

fof(f94,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f115,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f65,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f191,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f80,f76,f189])).

fof(f76,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f81,f77])).

fof(f77,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f140,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f42,f138])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

% (22375)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (22376)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f113,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f104,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f100,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f39,f98])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f96,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f82,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f78,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f74,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f62,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (22368)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (22368)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f307,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f52,f62,f66,f74,f78,f82,f96,f100,f104,f113,f140,f191,f207,f219,f241,f267,f272,f302,f306])).
% 0.21/0.45  fof(f306,plain,(
% 0.21/0.45    ~spl3_4 | spl3_45),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.45  fof(f303,plain,(
% 0.21/0.45    $false | (~spl3_4 | spl3_45)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f65,f301])).
% 0.21/0.45  fof(f301,plain,(
% 0.21/0.45    ~v1_relat_1(k6_relat_1(sK0)) | spl3_45),
% 0.21/0.45    inference(avatar_component_clause,[],[f299])).
% 0.21/0.45  fof(f299,plain,(
% 0.21/0.45    spl3_45 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f302,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_45 | spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_42),
% 0.21/0.45    inference(avatar_split_clause,[],[f280,f270,f189,f80,f59,f299,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl3_3 <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl3_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    spl3_28 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.45  fof(f270,plain,(
% 0.21/0.45    spl3_42 <=> ! [X5,X7,X6] : (k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.45  fof(f280,plain,(
% 0.21/0.45    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_42)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f279])).
% 0.21/0.45  fof(f279,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_42)),
% 0.21/0.45    inference(forward_demodulation,[],[f276,f198])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl3_8 | ~spl3_28)),
% 0.21/0.45    inference(superposition,[],[f190,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f80])).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl3_28),
% 0.21/0.45    inference(avatar_component_clause,[],[f189])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (spl3_3 | ~spl3_42)),
% 0.21/0.45    inference(superposition,[],[f61,f271])).
% 0.21/0.45  fof(f271,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5)) ) | ~spl3_42),
% 0.21/0.45    inference(avatar_component_clause,[],[f270])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f272,plain,(
% 0.21/0.45    spl3_42 | ~spl3_36 | ~spl3_41),
% 0.21/0.45    inference(avatar_split_clause,[],[f268,f265,f239,f270])).
% 0.21/0.45  fof(f239,plain,(
% 0.21/0.45    spl3_36 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.45  fof(f265,plain,(
% 0.21/0.45    spl3_41 <=> ! [X5,X7,X6] : (k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.45  fof(f268,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k9_relat_1(k8_relat_1(X6,X5),X7) = k3_xboole_0(k9_relat_1(X5,X7),X6) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5)) ) | (~spl3_36 | ~spl3_41)),
% 0.21/0.45    inference(forward_demodulation,[],[f266,f240])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_36),
% 0.21/0.45    inference(avatar_component_clause,[],[f239])).
% 0.21/0.45  fof(f266,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5)) ) | ~spl3_41),
% 0.21/0.45    inference(avatar_component_clause,[],[f265])).
% 0.21/0.45  fof(f267,plain,(
% 0.21/0.45    spl3_41 | ~spl3_12 | ~spl3_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f152,f138,f98,f265])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    spl3_19 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5)) ) | (~spl3_12 | ~spl3_19)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.45  fof(f151,plain,(
% 0.21/0.45    ( ! [X6,X7,X5] : (k9_relat_1(k6_relat_1(X6),k9_relat_1(X5,X7)) = k9_relat_1(k8_relat_1(X6,X5),X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X5) | ~v1_relat_1(X5)) ) | (~spl3_12 | ~spl3_19)),
% 0.21/0.45    inference(superposition,[],[f139,f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f98])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f138])).
% 0.21/0.45  fof(f241,plain,(
% 0.21/0.45    spl3_36 | ~spl3_4 | ~spl3_6 | ~spl3_12 | ~spl3_15 | ~spl3_31 | ~spl3_33),
% 0.21/0.45    inference(avatar_split_clause,[],[f221,f217,f205,f111,f98,f72,f64,f239])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl3_6 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    spl3_15 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    spl3_31 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    spl3_33 <=> ! [X1,X0] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_4 | ~spl3_6 | ~spl3_12 | ~spl3_15 | ~spl3_31 | ~spl3_33)),
% 0.21/0.45    inference(forward_demodulation,[],[f220,f132])).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ) | (~spl3_4 | ~spl3_6 | ~spl3_15)),
% 0.21/0.45    inference(forward_demodulation,[],[f131,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0)) ) | (~spl3_4 | ~spl3_15)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f65,f112])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f111])).
% 0.21/0.45  fof(f220,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ) | (~spl3_4 | ~spl3_12 | ~spl3_31 | ~spl3_33)),
% 0.21/0.45    inference(forward_demodulation,[],[f218,f208])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl3_4 | ~spl3_12 | ~spl3_31)),
% 0.21/0.45    inference(forward_demodulation,[],[f206,f117])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f65,f99])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | ~spl3_31),
% 0.21/0.45    inference(avatar_component_clause,[],[f205])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_33),
% 0.21/0.45    inference(avatar_component_clause,[],[f217])).
% 0.21/0.45  fof(f219,plain,(
% 0.21/0.45    spl3_33 | ~spl3_4 | ~spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f121,f102,f64,f217])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_13 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl3_4 | ~spl3_13)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f65,f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f102])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    spl3_31 | ~spl3_4 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f115,f94,f64,f205])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl3_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl3_4 | ~spl3_11)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f65,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f191,plain,(
% 0.21/0.45    spl3_28 | ~spl3_7 | ~spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f91,f80,f76,f189])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl3_7 | ~spl3_8)),
% 0.21/0.45    inference(superposition,[],[f81,f77])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f76])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    spl3_19),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f138])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  % (22375)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (22376)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f111])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl3_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f102])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f98])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f94])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f80])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f34,f76])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f72])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,axiom,(
% 0.21/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f64])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f59])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f17])).
% 0.21/0.46  fof(f17,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f49])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (22368)------------------------------
% 0.21/0.46  % (22368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (22368)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (22368)Memory used [KB]: 6268
% 0.21/0.46  % (22368)Time elapsed: 0.050 s
% 0.21/0.46  % (22368)------------------------------
% 0.21/0.46  % (22368)------------------------------
% 0.21/0.46  % (22377)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (22358)Success in time 0.103 s
%------------------------------------------------------------------------------
