%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:33 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 291 expanded)
%              Number of leaves         :   42 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  482 (1165 expanded)
%              Number of equality atoms :   42 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f129,f142,f151,f156,f160,f179,f303,f335,f338,f340,f350,f376,f383,f414,f432,f442,f478,f517,f519,f521,f525,f552])).

fof(f552,plain,
    ( spl4_6
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | spl4_6
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f54,f533])).

fof(f533,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_6
    | ~ spl4_38 ),
    inference(superposition,[],[f152,f504])).

fof(f504,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl4_38
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_6 ),
    inference(resolution,[],[f128,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f128,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f525,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f86,f516])).

fof(f516,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl4_41
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f521,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | spl4_40 ),
    inference(subsumption_resolution,[],[f52,f512])).

fof(f512,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl4_40
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f519,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl4_39 ),
    inference(subsumption_resolution,[],[f48,f508])).

fof(f508,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl4_39
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f517,plain,
    ( spl4_2
    | spl4_38
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_39
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_40
    | ~ spl4_41
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f499,f300,f514,f510,f321,f317,f506,f313,f309,f502,f101])).

fof(f101,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f309,plain,
    ( spl4_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f313,plain,
    ( spl4_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f317,plain,
    ( spl4_19
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f321,plain,
    ( spl4_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f300,plain,
    ( spl4_16
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f499,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f78,f302])).

fof(f302,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f300])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f478,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f454,f429,f97,f135])).

fof(f135,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f97,plain,
    ( spl4_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f429,plain,
    ( spl4_30
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f454,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f212,f431])).

fof(f431,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f429])).

fof(f212,plain,(
    ! [X0] :
      ( v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f90,f193])).

fof(f193,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f90,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f442,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f207,f427])).

fof(f427,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl4_29
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f207,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f432,plain,
    ( ~ spl4_29
    | ~ spl4_7
    | spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f421,f411,f429,f135,f425])).

fof(f411,plain,
    ( spl4_28
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f421,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_28 ),
    inference(resolution,[],[f413,f203])).

fof(f203,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X1) ) ),
    inference(resolution,[],[f75,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f413,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f411])).

fof(f414,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_28
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f409,f360,f411,f135,f144])).

fof(f144,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f360,plain,
    ( spl4_23
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f409,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f394,f88])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f394,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f64,f362])).

fof(f362,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f360])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f383,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | spl4_23
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f380,f300,f360,f321,f317,f313,f309])).

fof(f380,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f82,f302])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f376,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f51,f47,f49,f53,f298,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f298,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_15
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f350,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f53,f323])).

fof(f323,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f321])).

fof(f340,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f47,f319])).

fof(f319,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f317])).

fof(f338,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f49,f315])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f313])).

fof(f335,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f51,f311])).

fof(f311,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f309])).

fof(f303,plain,
    ( ~ spl4_15
    | spl4_16 ),
    inference(avatar_split_clause,[],[f293,f300,f296])).

fof(f293,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f260,f50])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f260,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f81,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f179,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f164,f144,f122,f101])).

fof(f122,plain,
    ( spl4_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f164,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f160,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f67,f150])).

fof(f150,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f156,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f67,f141])).

fof(f141,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_8
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f151,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f132,f148,f144])).

fof(f132,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f131,f139,f135])).

fof(f131,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f49])).

fof(f129,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f126,f122])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f104,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f101,f97])).

fof(f46,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (23700)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (23691)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (23707)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (23689)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (23690)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.52  % (23701)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.52  % (23708)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.52  % (23706)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.52  % (23696)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.52  % (23692)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.52  % (23688)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.53  % (23710)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (23716)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (23714)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (23702)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (23716)Refutation not found, incomplete strategy% (23716)------------------------------
% 1.27/0.53  % (23716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (23716)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (23716)Memory used [KB]: 10874
% 1.27/0.53  % (23716)Time elapsed: 0.125 s
% 1.27/0.53  % (23716)------------------------------
% 1.27/0.53  % (23716)------------------------------
% 1.27/0.53  % (23711)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.53  % (23693)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.53  % (23694)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (23699)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.54  % (23712)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.54  % (23705)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.54  % (23703)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.54  % (23701)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f553,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f104,f129,f142,f151,f156,f160,f179,f303,f335,f338,f340,f350,f376,f383,f414,f432,f442,f478,f517,f519,f521,f525,f552])).
% 1.37/0.54  fof(f552,plain,(
% 1.37/0.54    spl4_6 | ~spl4_38),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f551])).
% 1.37/0.54  fof(f551,plain,(
% 1.37/0.54    $false | (spl4_6 | ~spl4_38)),
% 1.37/0.54    inference(subsumption_resolution,[],[f54,f533])).
% 1.37/0.54  fof(f533,plain,(
% 1.37/0.54    ~v1_xboole_0(k1_xboole_0) | (spl4_6 | ~spl4_38)),
% 1.37/0.54    inference(superposition,[],[f152,f504])).
% 1.37/0.54  fof(f504,plain,(
% 1.37/0.54    k1_xboole_0 = sK0 | ~spl4_38),
% 1.37/0.54    inference(avatar_component_clause,[],[f502])).
% 1.37/0.54  fof(f502,plain,(
% 1.37/0.54    spl4_38 <=> k1_xboole_0 = sK0),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.37/0.54  fof(f152,plain,(
% 1.37/0.54    ~v1_xboole_0(sK0) | spl4_6),
% 1.37/0.54    inference(resolution,[],[f128,f68])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.37/0.54  fof(f128,plain,(
% 1.37/0.54    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_6),
% 1.37/0.54    inference(avatar_component_clause,[],[f126])).
% 1.37/0.54  fof(f126,plain,(
% 1.37/0.54    spl4_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    v1_xboole_0(k1_xboole_0)),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    v1_xboole_0(k1_xboole_0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.37/0.54  fof(f525,plain,(
% 1.37/0.54    spl4_41),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f522])).
% 1.37/0.54  fof(f522,plain,(
% 1.37/0.54    $false | spl4_41),
% 1.37/0.54    inference(unit_resulting_resolution,[],[f86,f516])).
% 1.37/0.54  fof(f516,plain,(
% 1.37/0.54    ~v2_funct_1(k6_partfun1(sK0)) | spl4_41),
% 1.37/0.54    inference(avatar_component_clause,[],[f514])).
% 1.37/0.54  fof(f514,plain,(
% 1.37/0.54    spl4_41 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.37/0.54  fof(f86,plain,(
% 1.37/0.54    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f58,f55])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f20])).
% 1.37/0.54  fof(f20,axiom,(
% 1.37/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,axiom,(
% 1.37/0.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.37/0.54  fof(f521,plain,(
% 1.37/0.54    spl4_40),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f520])).
% 1.37/0.54  fof(f520,plain,(
% 1.37/0.54    $false | spl4_40),
% 1.37/0.54    inference(subsumption_resolution,[],[f52,f512])).
% 1.37/0.54  fof(f512,plain,(
% 1.37/0.54    ~v1_funct_2(sK2,sK0,sK1) | spl4_40),
% 1.37/0.54    inference(avatar_component_clause,[],[f510])).
% 1.37/0.54  fof(f510,plain,(
% 1.37/0.54    spl4_40 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.37/0.54    inference(flattening,[],[f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.37/0.54    inference(ennf_transformation,[],[f23])).
% 1.37/0.54  fof(f23,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.37/0.54    inference(negated_conjecture,[],[f22])).
% 1.37/0.54  fof(f22,conjecture,(
% 1.37/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.37/0.54  fof(f519,plain,(
% 1.37/0.54    spl4_39),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f518])).
% 1.37/0.54  fof(f518,plain,(
% 1.37/0.54    $false | spl4_39),
% 1.37/0.54    inference(subsumption_resolution,[],[f48,f508])).
% 1.37/0.54  fof(f508,plain,(
% 1.37/0.54    ~v1_funct_2(sK3,sK1,sK0) | spl4_39),
% 1.37/0.54    inference(avatar_component_clause,[],[f506])).
% 1.37/0.54  fof(f506,plain,(
% 1.37/0.54    spl4_39 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    v1_funct_2(sK3,sK1,sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f517,plain,(
% 1.37/0.54    spl4_2 | spl4_38 | ~spl4_17 | ~spl4_18 | ~spl4_39 | ~spl4_19 | ~spl4_20 | ~spl4_40 | ~spl4_41 | ~spl4_16),
% 1.37/0.54    inference(avatar_split_clause,[],[f499,f300,f514,f510,f321,f317,f506,f313,f309,f502,f101])).
% 1.37/0.54  fof(f101,plain,(
% 1.37/0.54    spl4_2 <=> v2_funct_1(sK2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.54  fof(f309,plain,(
% 1.37/0.54    spl4_17 <=> v1_funct_1(sK2)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.37/0.54  fof(f313,plain,(
% 1.37/0.54    spl4_18 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.37/0.54  fof(f317,plain,(
% 1.37/0.54    spl4_19 <=> v1_funct_1(sK3)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.37/0.54  fof(f321,plain,(
% 1.37/0.54    spl4_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.37/0.54  fof(f300,plain,(
% 1.37/0.54    spl4_16 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.37/0.54  fof(f499,plain,(
% 1.37/0.54    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl4_16),
% 1.37/0.54    inference(superposition,[],[f78,f302])).
% 1.37/0.54  fof(f302,plain,(
% 1.37/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_16),
% 1.37/0.54    inference(avatar_component_clause,[],[f300])).
% 1.37/0.54  fof(f78,plain,(
% 1.37/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.37/0.54    inference(flattening,[],[f38])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.37/0.54    inference(ennf_transformation,[],[f21])).
% 1.37/0.54  fof(f21,axiom,(
% 1.37/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.37/0.54  fof(f478,plain,(
% 1.37/0.54    ~spl4_7 | spl4_1 | ~spl4_30),
% 1.37/0.54    inference(avatar_split_clause,[],[f454,f429,f97,f135])).
% 1.37/0.54  fof(f135,plain,(
% 1.37/0.54    spl4_7 <=> v1_relat_1(sK3)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.37/0.54  fof(f97,plain,(
% 1.37/0.54    spl4_1 <=> v2_funct_2(sK3,sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.54  fof(f429,plain,(
% 1.37/0.54    spl4_30 <=> sK0 = k2_relat_1(sK3)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.37/0.54  fof(f454,plain,(
% 1.37/0.54    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_30),
% 1.37/0.54    inference(superposition,[],[f212,f431])).
% 1.37/0.54  fof(f431,plain,(
% 1.37/0.54    sK0 = k2_relat_1(sK3) | ~spl4_30),
% 1.37/0.54    inference(avatar_component_clause,[],[f429])).
% 1.37/0.54  fof(f212,plain,(
% 1.37/0.54    ( ! [X0] : (v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f210])).
% 1.37/0.54  fof(f210,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_relat_1(X0) | v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(resolution,[],[f90,f193])).
% 1.37/0.54  fof(f193,plain,(
% 1.37/0.54    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.37/0.54    inference(resolution,[],[f69,f91])).
% 1.37/0.54  fof(f91,plain,(
% 1.37/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.37/0.54    inference(equality_resolution,[],[f74])).
% 1.37/0.54  fof(f74,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.37/0.54  fof(f69,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.37/0.54  fof(f90,plain,(
% 1.37/0.54    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.37/0.54    inference(equality_resolution,[],[f71])).
% 1.37/0.54  fof(f71,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f36])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.37/0.54    inference(flattening,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.37/0.54    inference(ennf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,axiom,(
% 1.37/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.37/0.54  fof(f442,plain,(
% 1.37/0.54    spl4_29),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f439])).
% 1.37/0.54  fof(f439,plain,(
% 1.37/0.54    $false | spl4_29),
% 1.37/0.54    inference(subsumption_resolution,[],[f207,f427])).
% 1.37/0.54  fof(f427,plain,(
% 1.37/0.54    ~v5_relat_1(sK3,sK0) | spl4_29),
% 1.37/0.54    inference(avatar_component_clause,[],[f425])).
% 1.37/0.54  fof(f425,plain,(
% 1.37/0.54    spl4_29 <=> v5_relat_1(sK3,sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.37/0.54  fof(f207,plain,(
% 1.37/0.54    v5_relat_1(sK3,sK0)),
% 1.37/0.54    inference(resolution,[],[f77,f49])).
% 1.37/0.54  fof(f49,plain,(
% 1.37/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f77,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.37/0.54  fof(f432,plain,(
% 1.37/0.54    ~spl4_29 | ~spl4_7 | spl4_30 | ~spl4_28),
% 1.37/0.54    inference(avatar_split_clause,[],[f421,f411,f429,f135,f425])).
% 1.37/0.54  fof(f411,plain,(
% 1.37/0.54    spl4_28 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.37/0.54  fof(f421,plain,(
% 1.37/0.54    sK0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | ~spl4_28),
% 1.37/0.54    inference(resolution,[],[f413,f203])).
% 1.37/0.54  fof(f203,plain,(
% 1.37/0.54    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v1_relat_1(X2) | ~v5_relat_1(X2,X1)) )),
% 1.37/0.54    inference(resolution,[],[f75,f70])).
% 1.37/0.54  fof(f70,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f34])).
% 1.37/0.54  fof(f75,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.37/0.55    inference(cnf_transformation,[],[f2])).
% 1.37/0.55  fof(f413,plain,(
% 1.37/0.55    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl4_28),
% 1.37/0.55    inference(avatar_component_clause,[],[f411])).
% 1.37/0.55  fof(f414,plain,(
% 1.37/0.55    ~spl4_9 | ~spl4_7 | spl4_28 | ~spl4_23),
% 1.37/0.55    inference(avatar_split_clause,[],[f409,f360,f411,f135,f144])).
% 1.37/0.55  fof(f144,plain,(
% 1.37/0.55    spl4_9 <=> v1_relat_1(sK2)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.37/0.55  fof(f360,plain,(
% 1.37/0.55    spl4_23 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.37/0.55  fof(f409,plain,(
% 1.37/0.55    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.37/0.55    inference(forward_demodulation,[],[f394,f88])).
% 1.37/0.55  fof(f88,plain,(
% 1.37/0.55    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.37/0.55    inference(definition_unfolding,[],[f60,f55])).
% 1.37/0.55  fof(f60,plain,(
% 1.37/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.37/0.55    inference(cnf_transformation,[],[f10])).
% 1.37/0.55  fof(f10,axiom,(
% 1.37/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.37/0.55  fof(f394,plain,(
% 1.37/0.55    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.37/0.55    inference(superposition,[],[f64,f362])).
% 1.37/0.55  fof(f362,plain,(
% 1.37/0.55    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_23),
% 1.37/0.55    inference(avatar_component_clause,[],[f360])).
% 1.37/0.55  fof(f64,plain,(
% 1.37/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f29])).
% 1.37/0.55  fof(f29,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f9])).
% 1.37/0.55  fof(f9,axiom,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.37/0.55  fof(f383,plain,(
% 1.37/0.55    ~spl4_17 | ~spl4_18 | ~spl4_19 | ~spl4_20 | spl4_23 | ~spl4_16),
% 1.37/0.55    inference(avatar_split_clause,[],[f380,f300,f360,f321,f317,f313,f309])).
% 1.37/0.55  fof(f380,plain,(
% 1.37/0.55    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_16),
% 1.37/0.55    inference(superposition,[],[f82,f302])).
% 1.37/0.55  fof(f82,plain,(
% 1.37/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f43])).
% 1.37/0.55  fof(f43,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.37/0.55    inference(flattening,[],[f42])).
% 1.37/0.55  fof(f42,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.37/0.55    inference(ennf_transformation,[],[f19])).
% 1.37/0.55  fof(f19,axiom,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.37/0.55  fof(f376,plain,(
% 1.37/0.55    spl4_15),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f364])).
% 1.37/0.55  fof(f364,plain,(
% 1.37/0.55    $false | spl4_15),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f51,f47,f49,f53,f298,f84])).
% 1.37/0.55  fof(f84,plain,(
% 1.37/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f45])).
% 1.37/0.55  fof(f45,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.37/0.55    inference(flattening,[],[f44])).
% 1.37/0.55  fof(f44,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.37/0.55    inference(ennf_transformation,[],[f18])).
% 1.37/0.55  fof(f18,axiom,(
% 1.37/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.37/0.55  fof(f298,plain,(
% 1.37/0.55    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_15),
% 1.37/0.55    inference(avatar_component_clause,[],[f296])).
% 1.37/0.55  fof(f296,plain,(
% 1.37/0.55    spl4_15 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.37/0.55  fof(f53,plain,(
% 1.37/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  fof(f47,plain,(
% 1.37/0.55    v1_funct_1(sK3)),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  fof(f51,plain,(
% 1.37/0.55    v1_funct_1(sK2)),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  fof(f350,plain,(
% 1.37/0.55    spl4_20),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f349])).
% 1.37/0.55  fof(f349,plain,(
% 1.37/0.55    $false | spl4_20),
% 1.37/0.55    inference(subsumption_resolution,[],[f53,f323])).
% 1.37/0.55  fof(f323,plain,(
% 1.37/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_20),
% 1.37/0.55    inference(avatar_component_clause,[],[f321])).
% 1.37/0.55  fof(f340,plain,(
% 1.37/0.55    spl4_19),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f339])).
% 1.37/0.55  fof(f339,plain,(
% 1.37/0.55    $false | spl4_19),
% 1.37/0.55    inference(subsumption_resolution,[],[f47,f319])).
% 1.37/0.55  fof(f319,plain,(
% 1.37/0.55    ~v1_funct_1(sK3) | spl4_19),
% 1.37/0.55    inference(avatar_component_clause,[],[f317])).
% 1.37/0.55  fof(f338,plain,(
% 1.37/0.55    spl4_18),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f337])).
% 1.37/0.55  fof(f337,plain,(
% 1.37/0.55    $false | spl4_18),
% 1.37/0.55    inference(subsumption_resolution,[],[f49,f315])).
% 1.37/0.55  fof(f315,plain,(
% 1.37/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_18),
% 1.37/0.55    inference(avatar_component_clause,[],[f313])).
% 1.37/0.55  fof(f335,plain,(
% 1.37/0.55    spl4_17),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f334])).
% 1.37/0.55  fof(f334,plain,(
% 1.37/0.55    $false | spl4_17),
% 1.37/0.55    inference(subsumption_resolution,[],[f51,f311])).
% 1.37/0.55  fof(f311,plain,(
% 1.37/0.55    ~v1_funct_1(sK2) | spl4_17),
% 1.37/0.55    inference(avatar_component_clause,[],[f309])).
% 1.37/0.55  fof(f303,plain,(
% 1.37/0.55    ~spl4_15 | spl4_16),
% 1.37/0.55    inference(avatar_split_clause,[],[f293,f300,f296])).
% 1.37/0.55  fof(f293,plain,(
% 1.37/0.55    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.37/0.55    inference(resolution,[],[f260,f50])).
% 1.37/0.55  fof(f50,plain,(
% 1.37/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  fof(f260,plain,(
% 1.37/0.55    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.37/0.55    inference(resolution,[],[f81,f85])).
% 1.37/0.55  fof(f85,plain,(
% 1.37/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.37/0.55    inference(definition_unfolding,[],[f56,f55])).
% 1.37/0.55  fof(f56,plain,(
% 1.37/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f16])).
% 1.37/0.55  fof(f16,axiom,(
% 1.37/0.55    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.37/0.55  fof(f81,plain,(
% 1.37/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f41])).
% 1.37/0.55  fof(f41,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.37/0.55    inference(flattening,[],[f40])).
% 1.37/0.55  fof(f40,plain,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.37/0.55    inference(ennf_transformation,[],[f15])).
% 1.37/0.55  fof(f15,axiom,(
% 1.37/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.37/0.55  fof(f179,plain,(
% 1.37/0.55    spl4_2 | ~spl4_5 | ~spl4_9),
% 1.37/0.55    inference(avatar_split_clause,[],[f164,f144,f122,f101])).
% 1.37/0.55  fof(f122,plain,(
% 1.37/0.55    spl4_5 <=> v1_xboole_0(sK2)),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.37/0.55  fof(f164,plain,(
% 1.37/0.55    ~v1_relat_1(sK2) | ~v1_xboole_0(sK2) | v2_funct_1(sK2)),
% 1.37/0.55    inference(resolution,[],[f66,f51])).
% 1.37/0.55  fof(f66,plain,(
% 1.37/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f32])).
% 1.37/0.55  fof(f32,plain,(
% 1.37/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.37/0.55    inference(flattening,[],[f31])).
% 1.37/0.55  fof(f31,plain,(
% 1.37/0.55    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.37/0.55    inference(ennf_transformation,[],[f12])).
% 1.37/0.55  fof(f12,axiom,(
% 1.37/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.37/0.55  fof(f160,plain,(
% 1.37/0.55    spl4_10),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f157])).
% 1.37/0.55  fof(f157,plain,(
% 1.37/0.55    $false | spl4_10),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f67,f150])).
% 1.37/0.55  fof(f150,plain,(
% 1.37/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_10),
% 1.37/0.55    inference(avatar_component_clause,[],[f148])).
% 1.37/0.55  fof(f148,plain,(
% 1.37/0.55    spl4_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.37/0.55  fof(f67,plain,(
% 1.37/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.37/0.55    inference(cnf_transformation,[],[f8])).
% 1.37/0.55  fof(f8,axiom,(
% 1.37/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.37/0.55  fof(f156,plain,(
% 1.37/0.55    spl4_8),
% 1.37/0.55    inference(avatar_contradiction_clause,[],[f153])).
% 1.37/0.55  fof(f153,plain,(
% 1.37/0.55    $false | spl4_8),
% 1.37/0.55    inference(unit_resulting_resolution,[],[f67,f141])).
% 1.37/0.55  fof(f141,plain,(
% 1.37/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_8),
% 1.37/0.55    inference(avatar_component_clause,[],[f139])).
% 1.37/0.55  fof(f139,plain,(
% 1.37/0.55    spl4_8 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.37/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.37/0.55  fof(f151,plain,(
% 1.37/0.55    spl4_9 | ~spl4_10),
% 1.37/0.55    inference(avatar_split_clause,[],[f132,f148,f144])).
% 1.37/0.55  fof(f132,plain,(
% 1.37/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.37/0.55    inference(resolution,[],[f65,f53])).
% 1.37/0.55  fof(f65,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f30])).
% 1.37/0.55  fof(f30,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f6])).
% 1.37/0.55  fof(f6,axiom,(
% 1.37/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.37/0.55  fof(f142,plain,(
% 1.37/0.55    spl4_7 | ~spl4_8),
% 1.37/0.55    inference(avatar_split_clause,[],[f131,f139,f135])).
% 1.37/0.55  fof(f131,plain,(
% 1.37/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.37/0.55    inference(resolution,[],[f65,f49])).
% 1.37/0.55  fof(f129,plain,(
% 1.37/0.55    spl4_5 | ~spl4_6),
% 1.37/0.55    inference(avatar_split_clause,[],[f110,f126,f122])).
% 1.37/0.55  fof(f110,plain,(
% 1.37/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 1.37/0.55    inference(resolution,[],[f63,f53])).
% 1.37/0.55  fof(f63,plain,(
% 1.37/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.37/0.55    inference(cnf_transformation,[],[f28])).
% 1.37/0.55  fof(f28,plain,(
% 1.37/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.37/0.55    inference(ennf_transformation,[],[f4])).
% 1.37/0.55  fof(f4,axiom,(
% 1.37/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.37/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.37/0.55  fof(f104,plain,(
% 1.37/0.55    ~spl4_1 | ~spl4_2),
% 1.37/0.55    inference(avatar_split_clause,[],[f46,f101,f97])).
% 1.37/0.55  fof(f46,plain,(
% 1.37/0.55    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 1.37/0.55    inference(cnf_transformation,[],[f25])).
% 1.37/0.55  % SZS output end Proof for theBenchmark
% 1.37/0.55  % (23701)------------------------------
% 1.37/0.55  % (23701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (23701)Termination reason: Refutation
% 1.37/0.55  
% 1.37/0.55  % (23701)Memory used [KB]: 6524
% 1.37/0.55  % (23701)Time elapsed: 0.147 s
% 1.37/0.55  % (23701)------------------------------
% 1.37/0.55  % (23701)------------------------------
% 1.37/0.55  % (23704)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.55  % (23717)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (23695)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.37/0.55  % (23704)Refutation not found, incomplete strategy% (23704)------------------------------
% 1.37/0.55  % (23704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (23704)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (23704)Memory used [KB]: 10746
% 1.37/0.55  % (23704)Time elapsed: 0.148 s
% 1.37/0.55  % (23704)------------------------------
% 1.37/0.55  % (23704)------------------------------
% 1.37/0.55  % (23697)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (23698)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.55  % (23713)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (23709)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (23715)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (23698)Refutation not found, incomplete strategy% (23698)------------------------------
% 1.37/0.55  % (23698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (23698)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (23698)Memory used [KB]: 10874
% 1.37/0.55  % (23698)Time elapsed: 0.153 s
% 1.37/0.55  % (23698)------------------------------
% 1.37/0.55  % (23698)------------------------------
% 1.37/0.56  % (23687)Success in time 0.206 s
%------------------------------------------------------------------------------
