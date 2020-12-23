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
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 175 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :    6
%              Number of atoms          :  261 ( 400 expanded)
%              Number of equality atoms :   80 ( 126 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f63,f67,f80,f90,f94,f110,f114,f135,f141,f149,f153,f162,f192,f211,f221,f246,f426])).

fof(f426,plain,
    ( spl2_15
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl2_15
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f109,f405])).

fof(f405,plain,
    ( ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X1,X0))
    | ~ spl2_21
    | ~ spl2_31 ),
    inference(superposition,[],[f245,f148])).

fof(f148,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_21
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f245,plain,
    ( ! [X6,X7] : k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_31
  <=> ! [X7,X6] : k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f109,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_15
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f246,plain,
    ( spl2_31
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f235,f219,f209,f133,f244])).

fof(f133,plain,
    ( spl2_19
  <=> ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f209,plain,
    ( spl2_29
  <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f219,plain,
    ( spl2_30
  <=> ! [X1,X0,X2] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f235,plain,
    ( ! [X6,X7] : k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6))
    | ~ spl2_19
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f225,f134])).

fof(f134,plain,
    ( ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f225,plain,
    ( ! [X6,X7] : k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k8_relat_1(X6,k6_relat_1(X6)))
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(superposition,[],[f220,f210])).

fof(f210,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f220,plain,
    ( ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( spl2_30
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f169,f160,f147,f219])).

fof(f160,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f169,plain,
    ( ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2))
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(superposition,[],[f161,f148])).

fof(f161,plain,
    ( ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f211,plain,
    ( spl2_29
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f193,f190,f53,f41,f209])).

fof(f41,plain,
    ( spl2_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f53,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f190,plain,
    ( spl2_27
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f193,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f54,f42,f191])).

% (32689)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f191,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2))
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f190])).

fof(f42,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f54,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f192,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f157,f151,f88,f45,f190])).

fof(f45,plain,
    ( spl2_3
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f88,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f151,plain,
    ( spl2_22
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f154,f46])).

fof(f46,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2))
        | ~ r1_tarski(k1_relat_1(k6_relat_1(X3)),X2)
        | ~ v1_relat_1(k6_relat_1(X3)) )
    | ~ spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f152,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f152,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f162,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f101,f92,f41,f160])).

fof(f92,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f101,plain,
    ( ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f42,f93])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f153,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f85,f78,f41,f151])).

fof(f78,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f85,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f42,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f149,plain,
    ( spl2_21
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f144,f139,f65,f147])).

fof(f65,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f139,plain,
    ( spl2_20
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f144,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(superposition,[],[f140,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f140,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl2_20
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f75,f65,f57,f139])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f75,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f66,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f135,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f74,f61,f49,f41,f133])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f74,plain,
    ( ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f72,f50])).

fof(f50,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f72,plain,
    ( ! [X0] : k6_relat_1(X0) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k6_relat_1(X0))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f42,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f114,plain,
    ( ~ spl2_2
    | spl2_14 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl2_2
    | spl2_14 ),
    inference(unit_resulting_resolution,[],[f42,f105])).

fof(f105,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_14
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f110,plain,
    ( ~ spl2_14
    | ~ spl2_15
    | spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f86,f78,f36,f107,f103])).

fof(f36,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f38,f79])).

fof(f38,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f94,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f90,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f32,f88])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f80,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f67,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f39,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (32693)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (32688)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (32687)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (32685)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (32692)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (32695)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (32683)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (32688)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f440,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f63,f67,f80,f90,f94,f110,f114,f135,f141,f149,f153,f162,f192,f211,f221,f246,f426])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    spl2_15 | ~spl2_21 | ~spl2_31),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f425])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    $false | (spl2_15 | ~spl2_21 | ~spl2_31)),
% 0.22/0.50    inference(subsumption_resolution,[],[f109,f405])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X1,X0))) ) | (~spl2_21 | ~spl2_31)),
% 0.22/0.50    inference(superposition,[],[f245,f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl2_21 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6))) ) | ~spl2_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f244])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    spl2_31 <=> ! [X7,X6] : k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl2_15 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    spl2_31 | ~spl2_19 | ~spl2_29 | ~spl2_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f235,f219,f209,f133,f244])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl2_19 <=> ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    spl2_29 <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl2_30 <=> ! [X1,X0,X2] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k6_relat_1(X6))) ) | (~spl2_19 | ~spl2_29 | ~spl2_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f225,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))) ) | ~spl2_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k6_relat_1(k3_xboole_0(X6,X7)) = k8_relat_1(X7,k8_relat_1(X6,k6_relat_1(X6)))) ) | (~spl2_29 | ~spl2_30)),
% 0.22/0.50    inference(superposition,[],[f220,f210])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0))) ) | ~spl2_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f209])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2))) ) | ~spl2_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f219])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    spl2_30 | ~spl2_21 | ~spl2_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f169,f160,f147,f219])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl2_23 <=> ! [X1,X0,X2] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X1,X0),k6_relat_1(X2))) ) | (~spl2_21 | ~spl2_23)),
% 0.22/0.50    inference(superposition,[],[f161,f148])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))) ) | ~spl2_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f160])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl2_29 | ~spl2_2 | ~spl2_5 | ~spl2_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f190,f53,f41,f209])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl2_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl2_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    spl2_27 <=> ! [X3,X2] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_5 | ~spl2_27)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f54,f42,f191])).
% 0.22/0.50  % (32689)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2)) | ~r1_tarski(X3,X2) | ~v1_relat_1(k6_relat_1(X3))) ) | ~spl2_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f190])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    spl2_27 | ~spl2_3 | ~spl2_12 | ~spl2_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f157,f151,f88,f45,f190])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl2_3 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl2_12 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl2_22 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_3 | ~spl2_12 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f154,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f45])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k6_relat_1(X3) = k8_relat_1(X3,k6_relat_1(X2)) | ~r1_tarski(k1_relat_1(k6_relat_1(X3)),X2) | ~v1_relat_1(k6_relat_1(X3))) ) | (~spl2_12 | ~spl2_22)),
% 0.22/0.50    inference(superposition,[],[f152,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f151])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl2_23 | ~spl2_2 | ~spl2_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f101,f92,f41,f160])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl2_13 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))) ) | (~spl2_2 | ~spl2_13)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f42,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) ) | ~spl2_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl2_22 | ~spl2_2 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f85,f78,f41,f151])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl2_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_10)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f42,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl2_21 | ~spl2_8 | ~spl2_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f144,f139,f65,f147])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl2_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl2_20 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_8 | ~spl2_20)),
% 0.22/0.50    inference(superposition,[],[f140,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f139])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl2_20 | ~spl2_6 | ~spl2_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f65,f57,f139])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.50    inference(superposition,[],[f66,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl2_19 | ~spl2_2 | ~spl2_4 | ~spl2_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f74,f61,f49,f41,f133])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl2_7 <=> ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_4 | ~spl2_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f72,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f49])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_7)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f42,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~spl2_2 | spl2_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    $false | (~spl2_2 | spl2_14)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f42,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ~v1_relat_1(k6_relat_1(sK1)) | spl2_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl2_14 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~spl2_14 | ~spl2_15 | spl2_1 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f78,f36,f107,f103])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | (spl2_1 | ~spl2_10)),
% 0.22/0.50    inference(superposition,[],[f38,f79])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f36])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl2_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f92])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl2_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f88])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f78])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl2_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f65])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl2_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f61])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl2_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl2_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f53])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f49])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f45])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f41])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f36])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (32688)------------------------------
% 0.22/0.50  % (32688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32688)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (32688)Memory used [KB]: 6396
% 0.22/0.50  % (32688)Time elapsed: 0.052 s
% 0.22/0.50  % (32688)------------------------------
% 0.22/0.50  % (32688)------------------------------
% 0.22/0.50  % (32682)Success in time 0.139 s
%------------------------------------------------------------------------------
