%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 171 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :    6
%              Number of atoms          :  295 ( 520 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f78,f86,f90,f118,f129,f133,f137,f141,f165,f188,f201,f220,f228,f257,f273])).

fof(f273,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_23
    | spl3_26
    | ~ spl3_28
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_23
    | spl3_26
    | ~ spl3_28
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f262,f261])).

fof(f261,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(X0,sK2))
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f68,f256,f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f256,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_31
  <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f262,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_23
    | spl3_26
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f58,f68,f200,f256,f187])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f200,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_26
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f58,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f257,plain,
    ( spl3_31
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f175,f135,f131,f127,f116,f255])).

fof(f116,plain,
    ( spl3_14
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f127,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f131,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f135,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f175,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f174,f152])).

fof(f152,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f117,f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f117,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f174,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f171,f128])).

fof(f128,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f171,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0)
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(superposition,[],[f136,f117])).

fof(f136,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f228,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f119,f88,f84,f226])).

fof(f84,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f88,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f89,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f220,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_23
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_23
    | spl3_25 ),
    inference(subsumption_resolution,[],[f206,f212])).

fof(f212,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK1,X0))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f63,f164,f89])).

fof(f164,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_21
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f63,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f206,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_23
    | spl3_25 ),
    inference(unit_resulting_resolution,[],[f58,f63,f77,f196,f187])).

fof(f196,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_25
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f77,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f201,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f178,f139,f71,f198,f194])).

fof(f71,plain,
    ( spl3_4
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f139,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f178,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_4
    | ~ spl3_19 ),
    inference(resolution,[],[f140,f73])).

fof(f73,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f188,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f36,f186])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f165,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f104,f84,f76,f163])).

fof(f104,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f77,f85])).

fof(f141,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f50,f139])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f137,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f49,f135])).

fof(f49,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f133,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f48,f131])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f129,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f118,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f43,f116])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f90,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f74,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29,f28,f27])).

% (32193)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (32189)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (32188)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f69,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:13:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (32192)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (32192)Refutation not found, incomplete strategy% (32192)------------------------------
% 0.22/0.46  % (32192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (32192)Memory used [KB]: 10618
% 0.22/0.46  % (32192)Time elapsed: 0.004 s
% 0.22/0.46  % (32192)------------------------------
% 0.22/0.46  % (32192)------------------------------
% 0.22/0.47  % (32187)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (32190)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (32185)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (32195)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (32196)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (32186)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (32183)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (32194)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32186)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f274,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f59,f64,f69,f74,f78,f86,f90,f118,f129,f133,f137,f141,f165,f188,f201,f220,f228,f257,f273])).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_3 | ~spl3_23 | spl3_26 | ~spl3_28 | ~spl3_31),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f271])).
% 0.22/0.48  fof(f271,plain,(
% 0.22/0.48    $false | (~spl3_1 | ~spl3_3 | ~spl3_23 | spl3_26 | ~spl3_28 | ~spl3_31)),
% 0.22/0.48    inference(subsumption_resolution,[],[f262,f261])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK2))) ) | (~spl3_3 | ~spl3_28 | ~spl3_31)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f68,f256,f227])).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f226])).
% 0.22/0.48  fof(f226,plain,(
% 0.22/0.48    spl3_28 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f256,plain,(
% 0.22/0.48    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | ~spl3_31),
% 0.22/0.48    inference(avatar_component_clause,[],[f255])).
% 0.22/0.48  fof(f255,plain,(
% 0.22/0.48    spl3_31 <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f262,plain,(
% 0.22/0.48    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_23 | spl3_26 | ~spl3_31)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f58,f68,f200,f256,f187])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f186])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    spl3_23 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | spl3_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f198])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    spl3_26 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    v1_relat_1(sK0) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl3_1 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f257,plain,(
% 0.22/0.48    spl3_31 | ~spl3_14 | ~spl3_16 | ~spl3_17 | ~spl3_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f175,f135,f131,f127,f116,f255])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl3_14 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl3_16 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    spl3_18 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | (~spl3_14 | ~spl3_16 | ~spl3_17 | ~spl3_18)),
% 0.22/0.48    inference(forward_demodulation,[],[f174,f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(k3_xboole_0(X0,X1),X2))) ) | (~spl3_14 | ~spl3_17)),
% 0.22/0.48    inference(superposition,[],[f117,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0)) ) | (~spl3_14 | ~spl3_16 | ~spl3_18)),
% 0.22/0.48    inference(forward_demodulation,[],[f171,f128])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f127])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0)) ) | (~spl3_14 | ~spl3_18)),
% 0.22/0.48    inference(superposition,[],[f136,f117])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl3_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f135])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    spl3_28 | ~spl3_7 | ~spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f119,f88,f84,f226])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl3_7 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl3_8 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl3_7 | ~spl3_8)),
% 0.22/0.48    inference(resolution,[],[f89,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_21 | ~spl3_23 | spl3_25),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f219])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    $false | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_8 | ~spl3_21 | ~spl3_23 | spl3_25)),
% 0.22/0.48    inference(subsumption_resolution,[],[f206,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK1,X0))) ) | (~spl3_2 | ~spl3_8 | ~spl3_21)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f63,f164,f89])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl3_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    spl3_21 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl3_2 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_23 | spl3_25)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f58,f63,f77,f196,f187])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | spl3_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f194])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    spl3_25 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl3_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ~spl3_25 | ~spl3_26 | spl3_4 | ~spl3_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f178,f139,f71,f198,f194])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_4 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    spl3_19 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | (spl3_4 | ~spl3_19)),
% 0.22/0.48    inference(resolution,[],[f140,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f139])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    spl3_23),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f186])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl3_21 | ~spl3_5 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f104,f84,f76,f163])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f77,f85])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl3_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f50,f139])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    spl3_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f49,f135])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl3_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f48,f131])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl3_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f47,f127])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl3_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f43,f116])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f88])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f84])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f76])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f71])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29,f28,f27])).
% 0.22/0.49  % (32193)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (32189)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (32188)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f19])).
% 0.22/0.50  fof(f19,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f66])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f61])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f56])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (32186)------------------------------
% 0.22/0.50  % (32186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32186)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (32186)Memory used [KB]: 6268
% 0.22/0.50  % (32186)Time elapsed: 0.067 s
% 0.22/0.50  % (32186)------------------------------
% 0.22/0.50  % (32186)------------------------------
% 0.22/0.50  % (32191)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (32177)Success in time 0.135 s
%------------------------------------------------------------------------------
