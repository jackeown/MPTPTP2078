%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 136 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 365 expanded)
%              Number of equality atoms :   56 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f59,f63,f71,f75,f93,f97,f101,f110,f129,f157,f247,f438,f446])).

fof(f446,plain,
    ( ~ spl3_7
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl3_7
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f74,f437])).

fof(f437,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl3_42
  <=> k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) = k3_xboole_0(k9_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f74,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f438,plain,
    ( ~ spl3_42
    | spl3_3
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f248,f245,f56,f435])).

fof(f56,plain,
    ( spl3_3
  <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f245,plain,
    ( spl3_30
  <=> ! [X1,X0] : k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f248,plain,
    ( k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)
    | spl3_3
    | ~ spl3_30 ),
    inference(superposition,[],[f58,f246])).

fof(f246,plain,
    ( ! [X0,X1] : k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f245])).

fof(f58,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f247,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f176,f155,f127,f108,f99,f95,f91,f61,f46,f245])).

fof(f46,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f91,plain,
    ( spl3_11
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f99,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f108,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f127,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f155,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f176,plain,
    ( ! [X0,X1] : k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f175,f148])).

fof(f148,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0)) = k3_xboole_0(k9_relat_1(sK2,X0),X1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f147,f125])).

fof(f125,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0)
    | ~ spl3_1
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f124,f113])).

fof(f113,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f48,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f124,plain,
    ( ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0)
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f92,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f92,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f147,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0)) = k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f146,f116])).

fof(f116,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k5_relat_1(k7_relat_1(sK2,X1),k6_relat_1(X0))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f92,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f146,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f139,f113])).

fof(f139,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(sK2,X0)))
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f92,f62,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f175,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f165,f111])).

fof(f111,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f48,f96])).

fof(f165,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f48,f62,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f41,f155])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f129,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f32,f127])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f110,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f101,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f39,f99])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f97,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f95])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f93,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f76,f69,f46,f91])).

fof(f69,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f76,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f48,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f75,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f59,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (29602)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (29613)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (29600)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (29610)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (29605)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (29611)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (29614)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (29615)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (29616)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (29603)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (29617)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (29605)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f447,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f49,f59,f63,f71,f75,f93,f97,f101,f110,f129,f157,f247,f438,f446])).
% 0.20/0.47  fof(f446,plain,(
% 0.20/0.47    ~spl3_7 | spl3_42),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f439])).
% 0.20/0.47  fof(f439,plain,(
% 0.20/0.47    $false | (~spl3_7 | spl3_42)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f74,f437])).
% 0.20/0.47  fof(f437,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) | spl3_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f435])).
% 0.20/0.47  fof(f435,plain,(
% 0.20/0.47    spl3_42 <=> k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) = k3_xboole_0(k9_relat_1(sK2,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f438,plain,(
% 0.20/0.47    ~spl3_42 | spl3_3 | ~spl3_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f248,f245,f56,f435])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl3_3 <=> k9_relat_1(k8_relat_1(sK0,sK2),sK1) = k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    spl3_30 <=> ! [X1,X0] : k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) | (spl3_3 | ~spl3_30)),
% 0.20/0.47    inference(superposition,[],[f58,f246])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1)) ) | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f245])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    spl3_30 | ~spl3_1 | ~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f176,f155,f127,f108,f99,f95,f91,f61,f46,f245])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_11 <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl3_12 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl3_13 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl3_15 <=> ! [X1,X0] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl3_17 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl3_19 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(k9_relat_1(sK2,X1),X0) = k9_relat_1(k8_relat_1(X0,sK2),X1)) ) | (~spl3_1 | ~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_15 | ~spl3_17 | ~spl3_19)),
% 0.20/0.47    inference(forward_demodulation,[],[f175,f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0)) = k3_xboole_0(k9_relat_1(sK2,X0),X1)) ) | (~spl3_1 | ~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_15 | ~spl3_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f147,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0)) ) | (~spl3_1 | ~spl3_11 | ~spl3_13 | ~spl3_15)),
% 0.20/0.47    inference(forward_demodulation,[],[f124,f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | (~spl3_1 | ~spl3_13)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f99])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0)) ) | (~spl3_11 | ~spl3_15)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f92,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f91])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0)) = k2_relat_1(k8_relat_1(X1,k7_relat_1(sK2,X0)))) ) | (~spl3_1 | ~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f146,f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k5_relat_1(k7_relat_1(sK2,X1),k6_relat_1(X0))) ) | (~spl3_11 | ~spl3_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f92,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f95])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k9_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_4 | ~spl3_11 | ~spl3_13 | ~spl3_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f139,f113])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k7_relat_1(sK2,X0)))) ) | (~spl3_4 | ~spl3_11 | ~spl3_17)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f92,f62,f128])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f127])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) ) | (~spl3_1 | ~spl3_4 | ~spl3_12 | ~spl3_19)),
% 0.20/0.47    inference(forward_demodulation,[],[f165,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) ) | (~spl3_1 | ~spl3_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f96])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k9_relat_1(sK2,X1)) = k9_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)) ) | (~spl3_1 | ~spl3_4 | ~spl3_19)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f62,f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f155])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f155])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl3_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f127])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f108])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f99])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f95])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_11 | ~spl3_1 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f69,f46,f91])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f48,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f73])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f69])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f61])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f29,f56])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f15])).
% 0.20/0.47  fof(f15,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f46])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (29605)------------------------------
% 0.20/0.47  % (29605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29605)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (29605)Memory used [KB]: 6524
% 0.20/0.47  % (29605)Time elapsed: 0.052 s
% 0.20/0.47  % (29605)------------------------------
% 0.20/0.47  % (29605)------------------------------
% 0.20/0.47  % (29608)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (29599)Success in time 0.103 s
%------------------------------------------------------------------------------
