%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 238 expanded)
%              Number of leaves         :   33 ( 107 expanded)
%              Depth                    :    8
%              Number of atoms          :  434 (1183 expanded)
%              Number of equality atoms :   75 ( 242 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f67,f71,f75,f79,f83,f87,f95,f103,f116,f131,f144,f150,f153,f159,f162,f167,f171,f193,f198,f230,f231])).

fof(f231,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | k1_xboole_0 != sK1
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f230,plain,
    ( spl5_30
    | ~ spl5_26
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f223,f191,f196,f227])).

fof(f227,plain,
    ( spl5_30
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f196,plain,
    ( spl5_26
  <=> v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f191,plain,
    ( spl5_25
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f223,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl5_25 ),
    inference(resolution,[],[f192,f56])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f192,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f191])).

fof(f198,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f194,f77,f65,f62,f196])).

fof(f62,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_6
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f194,plain,
    ( v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f181,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f181,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f78,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f78,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f193,plain,
    ( spl5_25
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f189,f73,f65,f62,f191])).

fof(f73,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f189,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f180,f101])).

fof(f180,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f74,f66])).

fof(f74,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f171,plain,
    ( ~ spl5_8
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl5_8
    | spl5_21 ),
    inference(subsumption_resolution,[],[f86,f168])).

fof(f168,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl5_21 ),
    inference(resolution,[],[f166,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f166,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_21
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f167,plain,
    ( ~ spl5_17
    | ~ spl5_21
    | spl5_18 ),
    inference(avatar_split_clause,[],[f163,f142,f165,f138])).

fof(f138,plain,
    ( spl5_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f142,plain,
    ( spl5_18
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f163,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | spl5_18 ),
    inference(resolution,[],[f143,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f143,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f162,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f158,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_20
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f159,plain,
    ( ~ spl5_20
    | ~ spl5_8
    | spl5_17 ),
    inference(avatar_split_clause,[],[f155,f138,f85,f157])).

fof(f155,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_8
    | spl5_17 ),
    inference(resolution,[],[f154,f86])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_17 ),
    inference(resolution,[],[f139,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f139,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f153,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f149,f40])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_19
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f150,plain,
    ( ~ spl5_19
    | ~ spl5_5
    | spl5_16 ),
    inference(avatar_split_clause,[],[f146,f135,f73,f148])).

fof(f135,plain,
    ( spl5_16
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f146,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl5_5
    | spl5_16 ),
    inference(resolution,[],[f145,f74])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_16 ),
    inference(resolution,[],[f136,f38])).

fof(f136,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f144,plain,
    ( ~ spl5_16
    | ~ spl5_7
    | ~ spl5_17
    | ~ spl5_10
    | spl5_1
    | ~ spl5_18
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f133,f129,f113,f142,f58,f93,f138,f81,f135])).

fof(f81,plain,
    ( spl5_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( spl5_10
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f58,plain,
    ( spl5_1
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( spl5_13
  <=> sK1 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f129,plain,
    ( spl5_15
  <=> v2_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f132,f114])).

fof(f114,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f132,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_15 ),
    inference(resolution,[],[f130,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f130,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( ~ spl5_10
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_5
    | spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f125,f69,f129,f73,f81,f85,f93])).

fof(f69,plain,
    ( spl5_4
  <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f125,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(superposition,[],[f70,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f70,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f116,plain,
    ( ~ spl5_5
    | spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f110,f99,f113,f73])).

fof(f99,plain,
    ( spl5_11
  <=> sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f110,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_11 ),
    inference(superposition,[],[f43,f100])).

fof(f100,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f103,plain,
    ( spl5_11
    | spl5_2
    | ~ spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f96,f73,f77,f62,f99])).

fof(f96,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f45,f74])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f29,f93])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_funct_1(sK3)
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_1(X3)
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_1(sK3)
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X4] :
        ( ~ v2_funct_1(sK3)
        & ( k1_xboole_0 = sK1
          | k1_xboole_0 != sK2 )
        & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( ~ v2_funct_1(sK3)
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f87,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f32,f81])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f36,f65,f62])).

fof(f36,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24126)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (24128)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (24127)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (24121)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24133)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (24136)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (24134)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (24126)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (24135)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f60,f67,f71,f75,f79,f83,f87,f95,f103,f116,f131,f144,f150,f153,f159,f162,f167,f171,f193,f198,f230,f231])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | k1_xboole_0 != sK1 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl5_30 | ~spl5_26 | ~spl5_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f223,f191,f196,f227])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    spl5_30 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl5_26 <=> v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    spl5_25 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | ~spl5_25),
% 0.21/0.52    inference(resolution,[],[f192,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f191])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl5_26 | ~spl5_2 | ~spl5_3 | ~spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f194,f77,f65,f62,f196])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl5_2 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl5_3 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_6 <=> v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f181,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    v1_funct_2(sK4,k1_xboole_0,sK2) | (~spl5_3 | ~spl5_6)),
% 0.21/0.52    inference(superposition,[],[f78,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK1,sK2) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    spl5_25 | ~spl5_2 | ~spl5_3 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f189,f73,f65,f62,f191])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f180,f101])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | (~spl5_3 | ~spl5_5)),
% 0.21/0.52    inference(superposition,[],[f74,f66])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~spl5_8 | spl5_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    $false | (~spl5_8 | spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl5_21),
% 0.21/0.52    inference(resolution,[],[f166,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~v5_relat_1(sK3,sK1) | spl5_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl5_21 <=> v5_relat_1(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl5_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~spl5_17 | ~spl5_21 | spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f163,f142,f165,f138])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl5_17 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl5_18 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~v5_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | spl5_18),
% 0.21/0.52    inference(resolution,[],[f143,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK3),sK1) | spl5_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl5_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    $false | spl5_20),
% 0.21/0.52    inference(resolution,[],[f158,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl5_20 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~spl5_20 | ~spl5_8 | spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f155,f138,f85,f157])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_8 | spl5_17)),
% 0.21/0.52    inference(resolution,[],[f154,f86])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_17),
% 0.21/0.52    inference(resolution,[],[f139,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl5_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    $false | spl5_19),
% 0.21/0.52    inference(resolution,[],[f149,f40])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl5_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl5_19 <=> v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~spl5_19 | ~spl5_5 | spl5_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f146,f135,f73,f148])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl5_16 <=> v1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | (~spl5_5 | spl5_16)),
% 0.21/0.52    inference(resolution,[],[f145,f74])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_16),
% 0.21/0.52    inference(resolution,[],[f136,f38])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~v1_relat_1(sK4) | spl5_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~spl5_16 | ~spl5_7 | ~spl5_17 | ~spl5_10 | spl5_1 | ~spl5_18 | ~spl5_13 | ~spl5_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f133,f129,f113,f142,f58,f93,f138,f81,f135])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_7 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl5_10 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl5_1 <=> v2_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl5_13 <=> sK1 = k1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl5_15 <=> v2_funct_1(k5_relat_1(sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK3),sK1) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_13 | ~spl5_15)),
% 0.21/0.52    inference(forward_demodulation,[],[f132,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK4) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl5_15),
% 0.21/0.52    inference(resolution,[],[f130,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ~spl5_10 | ~spl5_8 | ~spl5_7 | ~spl5_5 | spl5_15 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f125,f69,f129,f73,f81,f85,f93])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl5_4 <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    v2_funct_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl5_4),
% 0.21/0.52    inference(superposition,[],[f70,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~spl5_5 | spl5_13 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f110,f99,f113,f73])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl5_11 <=> sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_11),
% 0.21/0.52    inference(superposition,[],[f43,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    sK1 = k1_relset_1(sK1,sK2,sK4) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f99])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl5_11 | spl5_2 | ~spl5_6 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f96,f73,f77,f62,f99])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~spl5_5),
% 0.21/0.52    inference(resolution,[],[f45,f74])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl5_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f93])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f25,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X4] : (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (~v2_funct_1(sK3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (((~v2_funct_1(X3) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f85])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f81])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f73])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f69])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~spl5_2 | spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f65,f62])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ~spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f58])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~v2_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (24126)------------------------------
% 0.21/0.53  % (24126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24126)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (24126)Memory used [KB]: 10746
% 0.21/0.53  % (24126)Time elapsed: 0.086 s
% 0.21/0.53  % (24126)------------------------------
% 0.21/0.53  % (24126)------------------------------
% 0.21/0.53  % (24119)Success in time 0.159 s
%------------------------------------------------------------------------------
