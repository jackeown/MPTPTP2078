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
% DateTime   : Thu Dec  3 13:08:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 233 expanded)
%              Number of leaves         :   29 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  418 ( 796 expanded)
%              Number of equality atoms :   51 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f109,f114,f119,f128,f137,f156,f164,f187,f240,f262,f272,f291,f294,f301])).

fof(f301,plain,
    ( ~ spl3_2
    | ~ spl3_12
    | spl3_20
    | spl3_26
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_12
    | spl3_20
    | spl3_26
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f297,f279])).

fof(f279,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f297,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_12
    | spl3_20
    | spl3_26 ),
    inference(subsumption_resolution,[],[f296,f271])).

fof(f271,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK0)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_26
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f296,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_12
    | spl3_20 ),
    inference(forward_demodulation,[],[f295,f198])).

fof(f198,plain,
    ( ! [X0] : k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_12 ),
    inference(resolution,[],[f155,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f155,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f295,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0)
    | ~ spl3_2
    | ~ spl3_12
    | spl3_20 ),
    inference(subsumption_resolution,[],[f196,f211])).

fof(f211,plain,
    ( k1_xboole_0 != sK0
    | spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f196,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | k1_xboole_0 = sK0
    | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f155,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1
        | k8_relset_1(X0,X1,sK2,X1) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f70,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f294,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5
    | spl3_29 ),
    inference(subsumption_resolution,[],[f292,f85])).

fof(f85,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_5
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f292,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ spl3_1
    | spl3_29 ),
    inference(resolution,[],[f290,f89])).

fof(f89,plain,
    ( ! [X2] :
        ( r1_tarski(k2_relat_1(sK2),X2)
        | ~ v5_relat_1(sK2,X2) )
    | ~ spl3_1 ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f290,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_29
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f291,plain,
    ( ~ spl3_29
    | ~ spl3_1
    | ~ spl3_2
    | spl3_28 ),
    inference(avatar_split_clause,[],[f286,f278,f68,f63,f288])).

fof(f286,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_28 ),
    inference(resolution,[],[f280,f97])).

fof(f97,plain,
    ( ! [X3] :
        ( v1_funct_2(sK2,k1_relat_1(sK2),X3)
        | ~ r1_tarski(k2_relat_1(sK2),X3) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f93,f65])).

fof(f93,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),X3)
        | v1_funct_2(sK2,k1_relat_1(sK2),X3) )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f280,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f272,plain,
    ( ~ spl3_26
    | spl3_8
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f263,f259,f116,f269])).

fof(f116,plain,
    ( spl3_8
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f259,plain,
    ( spl3_25
  <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f263,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK0)
    | spl3_8
    | ~ spl3_25 ),
    inference(superposition,[],[f118,f261])).

fof(f261,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f259])).

fof(f118,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f262,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f194,f184,f125,f63,f259])).

fof(f125,plain,
    ( spl3_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f184,plain,
    ( spl3_18
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f194,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f190,f127])).

fof(f127,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f190,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(superposition,[],[f90,f186])).

fof(f186,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f90,plain,
    ( ! [X3] :
        ( k1_relat_1(k5_relat_1(sK2,X3)) = k10_relat_1(sK2,k1_relat_1(X3))
        | ~ v1_relat_1(X3) )
    | ~ spl3_1 ),
    inference(resolution,[],[f65,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f240,plain,
    ( spl3_4
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f230,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f230,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f80,f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f187,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f182,f161,f134,f125,f184])).

fof(f134,plain,
    ( spl3_10
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f161,plain,
    ( spl3_13
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f182,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f181,f136])).

fof(f136,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f181,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f129])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK1,X0)
        | k1_relat_1(sK1) = X0
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f127,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f163,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( spl3_13
    | ~ spl3_3
    | spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f159,f111,f106,f78,f73,f161])).

fof(f73,plain,
    ( spl3_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( spl3_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f159,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f158,f108])).

fof(f108,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f158,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f157,f80])).

% (32453)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f157,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_partfun1(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f104,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f104,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v1_xboole_0(X8)
        | ~ v1_funct_2(sK1,X7,X8)
        | v1_partfun1(sK1,X7) )
    | ~ spl3_3 ),
    inference(resolution,[],[f75,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f75,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f156,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f151,f83,f68,f63,f153])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f148,f85])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK2,X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f98,f89])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k2_relat_1(sK2),X4)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X4))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f94,f65])).

fof(f94,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(sK2),X4)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X4))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f121,f111,f134])).

fof(f121,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f113,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f128,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f123,f111,f125])).

fof(f123,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f37,f116])).

fof(f37,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f114,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f40,f111])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f106])).

fof(f39,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:34 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.22/0.47  % (32445)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (32443)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (32446)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (32442)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (32443)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (32451)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (32454)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (32451)Refutation not found, incomplete strategy% (32451)------------------------------
% 0.22/0.48  % (32451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f302,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f109,f114,f119,f128,f137,f156,f164,f187,f240,f262,f272,f291,f294,f301])).
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    ~spl3_2 | ~spl3_12 | spl3_20 | spl3_26 | ~spl3_28),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f300])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    $false | (~spl3_2 | ~spl3_12 | spl3_20 | spl3_26 | ~spl3_28)),
% 0.22/0.48    inference(subsumption_resolution,[],[f297,f279])).
% 0.22/0.48  fof(f279,plain,(
% 0.22/0.48    v1_funct_2(sK2,k1_relat_1(sK2),sK0) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f278])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    spl3_28 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f297,plain,(
% 0.22/0.48    ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | (~spl3_2 | ~spl3_12 | spl3_20 | spl3_26)),
% 0.22/0.48    inference(subsumption_resolution,[],[f296,f271])).
% 0.22/0.48  fof(f271,plain,(
% 0.22/0.48    k1_relat_1(sK2) != k10_relat_1(sK2,sK0) | spl3_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f269])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    spl3_26 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.48  fof(f296,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | (~spl3_2 | ~spl3_12 | spl3_20)),
% 0.22/0.48    inference(forward_demodulation,[],[f295,f198])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ( ! [X0] : (k8_relset_1(k1_relat_1(sK2),sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_12),
% 0.22/0.48    inference(resolution,[],[f155,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f153])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0) | (~spl3_2 | ~spl3_12 | spl3_20)),
% 0.22/0.48    inference(subsumption_resolution,[],[f196,f211])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    k1_xboole_0 != sK0 | spl3_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f210])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    spl3_20 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | k1_xboole_0 = sK0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK0,sK2,sK0) | (~spl3_2 | ~spl3_12)),
% 0.22/0.48    inference(resolution,[],[f155,f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,sK2,X1) = X0) ) | ~spl3_2),
% 0.22/0.48    inference(resolution,[],[f70,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f294,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_5 | spl3_29),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f293])).
% 0.22/0.48  fof(f293,plain,(
% 0.22/0.48    $false | (~spl3_1 | ~spl3_5 | spl3_29)),
% 0.22/0.48    inference(subsumption_resolution,[],[f292,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    v5_relat_1(sK2,sK0) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl3_5 <=> v5_relat_1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f292,plain,(
% 0.22/0.48    ~v5_relat_1(sK2,sK0) | (~spl3_1 | spl3_29)),
% 0.22/0.48    inference(resolution,[],[f290,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2] : (r1_tarski(k2_relat_1(sK2),X2) | ~v5_relat_1(sK2,X2)) ) | ~spl3_1),
% 0.22/0.48    inference(resolution,[],[f65,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f290,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f288])).
% 0.22/0.48  fof(f288,plain,(
% 0.22/0.48    spl3_29 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.48  fof(f291,plain,(
% 0.22/0.48    ~spl3_29 | ~spl3_1 | ~spl3_2 | spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f286,f278,f68,f63,f288])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(sK2),sK0) | (~spl3_1 | ~spl3_2 | spl3_28)),
% 0.22/0.48    inference(resolution,[],[f280,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X3] : (v1_funct_2(sK2,k1_relat_1(sK2),X3) | ~r1_tarski(k2_relat_1(sK2),X3)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f65])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X3] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X3) | v1_funct_2(sK2,k1_relat_1(sK2),X3)) ) | ~spl3_2),
% 0.22/0.48    inference(resolution,[],[f70,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    ~v1_funct_2(sK2,k1_relat_1(sK2),sK0) | spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f278])).
% 0.22/0.48  fof(f272,plain,(
% 0.22/0.48    ~spl3_26 | spl3_8 | ~spl3_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f263,f259,f116,f269])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl3_8 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f259,plain,(
% 0.22/0.48    spl3_25 <=> k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    k1_relat_1(sK2) != k10_relat_1(sK2,sK0) | (spl3_8 | ~spl3_25)),
% 0.22/0.48    inference(superposition,[],[f118,f261])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) | ~spl3_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f259])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2) | spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f262,plain,(
% 0.22/0.48    spl3_25 | ~spl3_1 | ~spl3_9 | ~spl3_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f194,f184,f125,f63,f259])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl3_9 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    spl3_18 <=> sK0 = k1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_9 | ~spl3_18)),
% 0.22/0.48    inference(subsumption_resolution,[],[f190,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f125])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) | ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_18)),
% 0.22/0.48    inference(superposition,[],[f90,f186])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    sK0 = k1_relat_1(sK1) | ~spl3_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f184])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X3] : (k1_relat_1(k5_relat_1(sK2,X3)) = k10_relat_1(sK2,k1_relat_1(X3)) | ~v1_relat_1(X3)) ) | ~spl3_1),
% 0.22/0.48    inference(resolution,[],[f65,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    spl3_4 | ~spl3_20),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f239])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    $false | (spl3_4 | ~spl3_20)),
% 0.22/0.48    inference(subsumption_resolution,[],[f230,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f230,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (spl3_4 | ~spl3_20)),
% 0.22/0.48    inference(superposition,[],[f80,f212])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl3_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f210])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_4 <=> v1_xboole_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    spl3_18 | ~spl3_9 | ~spl3_10 | ~spl3_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f182,f161,f134,f125,f184])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl3_10 <=> v4_relat_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    spl3_13 <=> v1_partfun1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    sK0 = k1_relat_1(sK1) | (~spl3_9 | ~spl3_10 | ~spl3_13)),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    v4_relat_1(sK1,sK0) | ~spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f134])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    sK0 = k1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | (~spl3_9 | ~spl3_13)),
% 0.22/0.48    inference(resolution,[],[f163,f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_partfun1(sK1,X0) | k1_relat_1(sK1) = X0 | ~v4_relat_1(sK1,X0)) ) | ~spl3_9),
% 0.22/0.48    inference(resolution,[],[f127,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    v1_partfun1(sK1,sK0) | ~spl3_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f161])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    spl3_13 | ~spl3_3 | spl3_4 | ~spl3_6 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f159,f111,f106,f78,f73,f161])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl3_3 <=> v1_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    spl3_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    v1_partfun1(sK1,sK0) | (~spl3_3 | spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f158,f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f106])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0) | (~spl3_3 | spl3_4 | ~spl3_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f157,f80])).
% 0.22/0.48  % (32453)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    v1_xboole_0(sK0) | ~v1_funct_2(sK1,sK0,sK0) | v1_partfun1(sK1,sK0) | (~spl3_3 | ~spl3_7)),
% 0.22/0.48    inference(resolution,[],[f104,f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f111])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X8,X7] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | v1_xboole_0(X8) | ~v1_funct_2(sK1,X7,X8) | v1_partfun1(sK1,X7)) ) | ~spl3_3),
% 0.22/0.48    inference(resolution,[],[f75,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl3_12 | ~spl3_1 | ~spl3_2 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f151,f83,f68,f63,f153])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_5)),
% 0.22/0.48    inference(resolution,[],[f148,f85])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    ( ! [X0] : (~v5_relat_1(sK2,X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.48    inference(resolution,[],[f98,f89])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ( ! [X4] : (~r1_tarski(k2_relat_1(sK2),X4) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X4)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f94,f65])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X4] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X4) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X4)))) ) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f70,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    spl3_10 | ~spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f121,f111,f134])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    v4_relat_1(sK1,sK0) | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f113,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl3_9 | ~spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f123,f111,f125])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl3_7),
% 0.22/0.49    inference(resolution,[],[f113,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f116])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f111])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f106])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f83])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v5_relat_1(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f78])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~v1_xboole_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f73])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f68])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f63])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (32443)------------------------------
% 0.22/0.49  % (32443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (32443)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (32443)Memory used [KB]: 10746
% 0.22/0.49  % (32443)Time elapsed: 0.065 s
% 0.22/0.49  % (32443)------------------------------
% 0.22/0.49  % (32443)------------------------------
% 0.22/0.49  % (32439)Success in time 0.128 s
%------------------------------------------------------------------------------
