%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 182 expanded)
%              Number of leaves         :   28 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  290 ( 498 expanded)
%              Number of equality atoms :   63 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f75,f91,f95,f99,f107,f138,f163,f167,f195,f201,f254,f274,f283,f294])).

fof(f294,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_20
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_20
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f196,f292])).

fof(f292,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,X0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_23
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f287,f255])).

fof(f255,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1)))
    | ~ spl2_23
    | ~ spl2_30 ),
    inference(superposition,[],[f253,f200])).

fof(f200,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl2_23
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f253,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl2_30
  <=> ! [X1,X0] : k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f287,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_20
    | ~ spl2_34 ),
    inference(unit_resulting_resolution,[],[f52,f57,f282,f166])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f282,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl2_34
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f57,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f196,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | spl2_3
    | ~ spl2_22 ),
    inference(superposition,[],[f62,f194])).

fof(f194,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_22
  <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f62,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_3
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f283,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f275,f272,f136,f105,f73,f65,f281])).

fof(f65,plain,
    ( spl2_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f73,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f105,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f136,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f272,plain,
    ( spl2_32
  <=> ! [X1,X0] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f275,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f273,f154])).

fof(f154,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f153,f74])).

fof(f74,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f153,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f152,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f152,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f146,f74])).

fof(f146,plain,
    ( ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f66,f66,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f66,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f273,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( spl2_32
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f103,f89,f73,f65,f272])).

fof(f89,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f103,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f101,f74])).

fof(f101,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f66,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f254,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f184,f161,f136,f105,f73,f65,f50,f252])).

fof(f161,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f184,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f174,f154])).

fof(f174,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k10_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f52,f66,f162])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f201,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f119,f97,f50,f198])).

fof(f97,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f119,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f52,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f195,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f112,f93,f50,f192])).

fof(f93,plain,
    ( spl2_11
  <=> ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f112,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f52,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f167,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f44,f165])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f163,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f138,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f38,f136])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f107,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f41,f105])).

fof(f41,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f99,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f95,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f91,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f75,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f67,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f63,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:19:47 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (32187)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (32181)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (32186)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (32187)Refutation not found, incomplete strategy% (32187)------------------------------
% 0.22/0.48  % (32187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32181)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (32191)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (32176)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (32179)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (32189)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32182)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (32183)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (32178)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (32187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (32187)Memory used [KB]: 10618
% 0.22/0.49  % (32187)Time elapsed: 0.053 s
% 0.22/0.49  % (32187)------------------------------
% 0.22/0.49  % (32187)------------------------------
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f75,f91,f95,f99,f107,f138,f163,f167,f195,f201,f254,f274,f283,f294])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    ~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_20 | ~spl2_22 | ~spl2_23 | ~spl2_30 | ~spl2_34),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    $false | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_20 | ~spl2_22 | ~spl2_23 | ~spl2_30 | ~spl2_34)),
% 0.22/0.49    inference(subsumption_resolution,[],[f196,f292])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,k2_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_23 | ~spl2_30 | ~spl2_34)),
% 0.22/0.49    inference(forward_demodulation,[],[f287,f255])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1)))) ) | (~spl2_23 | ~spl2_30)),
% 0.22/0.49    inference(superposition,[],[f253,f200])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | ~spl2_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f198])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl2_23 <=> sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0))) ) | ~spl2_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl2_30 <=> ! [X1,X0] : k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,k2_relat_1(sK1)) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(X0,k2_relat_1(sK1))))) ) | (~spl2_1 | ~spl2_2 | ~spl2_20 | ~spl2_34)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f52,f57,f282,f166])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f165])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl2_20 <=> ! [X1,X0] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl2_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f281])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    spl2_34 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    v1_funct_1(sK1) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl2_2 <=> v1_funct_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1)) | (spl2_3 | ~spl2_22)),
% 0.22/0.49    inference(superposition,[],[f62,f194])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | ~spl2_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl2_22 <=> k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) | spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl2_3 <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    spl2_34 | ~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17 | ~spl2_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f275,f272,f136,f105,f73,f65,f281])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl2_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl2_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl2_17 <=> ! [X1,X0] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    spl2_32 <=> ! [X1,X0] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17 | ~spl2_32)),
% 0.22/0.49    inference(forward_demodulation,[],[f273,f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f153,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) ) | (~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f152,f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_4 | ~spl2_6 | ~spl2_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f146,f74])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) ) | (~spl2_4 | ~spl2_17)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f66,f66,f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f136])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f272])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    spl2_32 | ~spl2_4 | ~spl2_6 | ~spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f103,f89,f73,f65,f272])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl2_10 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_4 | ~spl2_6 | ~spl2_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f101,f74])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_4 | ~spl2_10)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f66,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    spl2_30 | ~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17 | ~spl2_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f184,f161,f136,f105,f73,f65,f50,f252])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl2_19 <=> ! [X1,X0,X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k3_xboole_0(X1,X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_13 | ~spl2_17 | ~spl2_19)),
% 0.22/0.49    inference(forward_demodulation,[],[f174,f154])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(sK1,k6_relat_1(X0)),X1) = k10_relat_1(sK1,k10_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_1 | ~spl2_4 | ~spl2_19)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f52,f66,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl2_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    spl2_23 | ~spl2_1 | ~spl2_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f119,f97,f50,f198])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl2_12 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) | (~spl2_1 | ~spl2_12)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f52,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) ) | ~spl2_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f97])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl2_22 | ~spl2_1 | ~spl2_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f93,f50,f192])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl2_11 <=> ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) | (~spl2_1 | ~spl2_11)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f52,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl2_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f165])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl2_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f161])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl2_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f136])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl2_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f105])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl2_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f97])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl2_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f93])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f89])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f65])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f16])).
% 0.22/0.49  fof(f16,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f55])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f50])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (32181)------------------------------
% 0.22/0.49  % (32181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (32181)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (32181)Memory used [KB]: 6268
% 0.22/0.49  % (32181)Time elapsed: 0.057 s
% 0.22/0.49  % (32181)------------------------------
% 0.22/0.49  % (32181)------------------------------
% 0.22/0.49  % (32175)Success in time 0.13 s
%------------------------------------------------------------------------------
