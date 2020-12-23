%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:12 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 237 expanded)
%              Number of leaves         :   28 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  376 (1004 expanded)
%              Number of equality atoms :  102 ( 371 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f57,f61,f65,f69,f73,f77,f86,f91,f110,f129,f144,f157,f168,f190,f243,f275,f280])).

fof(f280,plain,
    ( ~ spl5_5
    | ~ spl5_9
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_9
    | spl5_41 ),
    inference(subsumption_resolution,[],[f64,f278])).

fof(f278,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl5_9
    | spl5_41 ),
    inference(trivial_inequality_removal,[],[f277])).

fof(f277,plain,
    ( ! [X0] :
        ( sK2 != sK2
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_9
    | spl5_41 ),
    inference(forward_demodulation,[],[f276,f85])).

fof(f85,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_9
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f276,plain,
    ( ! [X0] :
        ( sK2 != k2_relat_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl5_41 ),
    inference(superposition,[],[f274,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f40,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f38,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(global_subsumption,[],[f39,f40,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f274,plain,
    ( sK2 != k9_relat_1(sK4,sK1)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl5_41
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f64,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f275,plain,
    ( ~ spl5_41
    | spl5_20
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f271,f241,f155,f273])).

fof(f155,plain,
    ( spl5_20
  <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f241,plain,
    ( spl5_34
  <=> k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f271,plain,
    ( sK2 != k9_relat_1(sK4,sK1)
    | spl5_20
    | ~ spl5_34 ),
    inference(superposition,[],[f156,f242])).

fof(f242,plain,
    ( k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f241])).

fof(f156,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f243,plain,
    ( spl5_34
    | ~ spl5_12
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f239,f188,f108,f241])).

fof(f108,plain,
    ( spl5_12
  <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f188,plain,
    ( spl5_26
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f239,plain,
    ( k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_12
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f231,f109])).

fof(f109,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f231,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_26 ),
    inference(resolution,[],[f189,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f189,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( ~ spl5_8
    | spl5_26
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f186,f166,f142,f71,f188,f75])).

fof(f75,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f71,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f142,plain,
    ( spl5_18
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f166,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f186,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f180,f143])).

fof(f143,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f180,plain,
    ( ~ v1_funct_1(sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_7
    | ~ spl5_22 ),
    inference(resolution,[],[f167,f72])).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( ~ spl5_6
    | spl5_22
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f163,f63,f166,f67])).

fof(f67,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f45,f64])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f157,plain,
    ( ~ spl5_20
    | spl5_1
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f152,f142,f47,f155])).

fof(f47,plain,
    ( spl5_1
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f152,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | spl5_1
    | ~ spl5_18 ),
    inference(superposition,[],[f48,f143])).

fof(f48,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f144,plain,
    ( spl5_18
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f136,f127,f71,f75,f142])).

fof(f127,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f136,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(resolution,[],[f128,f72])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( ~ spl5_6
    | spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f123,f63,f127,f67])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f43,f64])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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

% (26033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f110,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f106,f89,f71,f63,f108])).

fof(f89,plain,
    ( spl5_10
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f106,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f100,f90])).

fof(f90,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f100,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f72])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f96,f64])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f79,f40])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f37,f40])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f91,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f87,f71,f59,f89])).

fof(f59,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f87,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f81,f60])).

fof(f60,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f41,f72])).

fof(f86,plain,
    ( spl5_9
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f82,f63,f55,f84])).

fof(f55,plain,
    ( spl5_3
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f80,f56])).

fof(f56,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f80,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f41,f64])).

fof(f77,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK2
    & sK2 = k2_relset_1(sK1,sK2,sK4)
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & k1_xboole_0 != sK2
          & sK2 = k2_relset_1(sK1,sK2,X4)
          & sK1 = k2_relset_1(sK0,sK1,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & k1_xboole_0 != sK2
        & sK2 = k2_relset_1(sK1,sK2,X4)
        & sK1 = k2_relset_1(sK0,sK1,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_1(X4) )
   => ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & k1_xboole_0 != sK2
      & sK2 = k2_relset_1(sK1,sK2,sK4)
      & sK1 = k2_relset_1(sK0,sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
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
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

fof(f73,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f47])).

fof(f36,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.49  % (26035)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.49  % (26034)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.49  % (26036)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.50  % (26043)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  % (26037)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.50  % (26044)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.10/0.51  % (26035)Refutation found. Thanks to Tanya!
% 1.10/0.51  % SZS status Theorem for theBenchmark
% 1.10/0.51  % (26038)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.10/0.51  % (26048)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.10/0.51  % (26030)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.10/0.52  % (26042)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.10/0.52  % (26046)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.10/0.52  % (26030)Refutation not found, incomplete strategy% (26030)------------------------------
% 1.10/0.52  % (26030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.52  % (26030)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.52  
% 1.10/0.52  % (26030)Memory used [KB]: 10618
% 1.10/0.52  % (26030)Time elapsed: 0.050 s
% 1.10/0.52  % (26030)------------------------------
% 1.10/0.52  % (26030)------------------------------
% 1.10/0.52  % (26029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.10/0.52  % (26031)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.10/0.52  % (26041)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.10/0.52  % (26045)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.10/0.52  % (26049)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.10/0.52  % SZS output start Proof for theBenchmark
% 1.10/0.52  fof(f281,plain,(
% 1.10/0.52    $false),
% 1.10/0.52    inference(avatar_sat_refutation,[],[f49,f57,f61,f65,f69,f73,f77,f86,f91,f110,f129,f144,f157,f168,f190,f243,f275,f280])).
% 1.10/0.52  fof(f280,plain,(
% 1.10/0.52    ~spl5_5 | ~spl5_9 | spl5_41),
% 1.10/0.52    inference(avatar_contradiction_clause,[],[f279])).
% 1.10/0.52  fof(f279,plain,(
% 1.10/0.52    $false | (~spl5_5 | ~spl5_9 | spl5_41)),
% 1.10/0.52    inference(subsumption_resolution,[],[f64,f278])).
% 1.10/0.52  fof(f278,plain,(
% 1.10/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_9 | spl5_41)),
% 1.10/0.52    inference(trivial_inequality_removal,[],[f277])).
% 1.10/0.52  fof(f277,plain,(
% 1.10/0.52    ( ! [X0] : (sK2 != sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_9 | spl5_41)),
% 1.10/0.52    inference(forward_demodulation,[],[f276,f85])).
% 1.10/0.52  fof(f85,plain,(
% 1.10/0.52    sK2 = k2_relat_1(sK4) | ~spl5_9),
% 1.10/0.52    inference(avatar_component_clause,[],[f84])).
% 1.10/0.52  fof(f84,plain,(
% 1.10/0.52    spl5_9 <=> sK2 = k2_relat_1(sK4)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.10/0.52  fof(f276,plain,(
% 1.10/0.52    ( ! [X0] : (sK2 != k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl5_41),
% 1.10/0.52    inference(superposition,[],[f274,f95])).
% 1.10/0.52  fof(f95,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.10/0.52    inference(global_subsumption,[],[f40,f94])).
% 1.10/0.52  fof(f94,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.10/0.52    inference(superposition,[],[f38,f93])).
% 1.28/0.52  fof(f93,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 1.28/0.52    inference(global_subsumption,[],[f39,f40,f42])).
% 1.28/0.52  fof(f42,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.52    inference(cnf_transformation,[],[f21])).
% 1.28/0.52  fof(f21,plain,(
% 1.28/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.52    inference(ennf_transformation,[],[f12])).
% 1.28/0.52  fof(f12,plain,(
% 1.28/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.28/0.52    inference(pure_predicate_removal,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(flattening,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.28/0.53    inference(ennf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.53  fof(f274,plain,(
% 1.28/0.53    sK2 != k9_relat_1(sK4,sK1) | spl5_41),
% 1.28/0.53    inference(avatar_component_clause,[],[f273])).
% 1.28/0.53  fof(f273,plain,(
% 1.28/0.53    spl5_41 <=> sK2 = k9_relat_1(sK4,sK1)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.28/0.53  fof(f64,plain,(
% 1.28/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 1.28/0.53    inference(avatar_component_clause,[],[f63])).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.28/0.53  fof(f275,plain,(
% 1.28/0.53    ~spl5_41 | spl5_20 | ~spl5_34),
% 1.28/0.53    inference(avatar_split_clause,[],[f271,f241,f155,f273])).
% 1.28/0.53  fof(f155,plain,(
% 1.28/0.53    spl5_20 <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.28/0.53  fof(f241,plain,(
% 1.28/0.53    spl5_34 <=> k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.28/0.53  fof(f271,plain,(
% 1.28/0.53    sK2 != k9_relat_1(sK4,sK1) | (spl5_20 | ~spl5_34)),
% 1.28/0.53    inference(superposition,[],[f156,f242])).
% 1.28/0.53  fof(f242,plain,(
% 1.28/0.53    k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~spl5_34),
% 1.28/0.53    inference(avatar_component_clause,[],[f241])).
% 1.28/0.53  fof(f156,plain,(
% 1.28/0.53    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | spl5_20),
% 1.28/0.53    inference(avatar_component_clause,[],[f155])).
% 1.28/0.53  fof(f243,plain,(
% 1.28/0.53    spl5_34 | ~spl5_12 | ~spl5_26),
% 1.28/0.53    inference(avatar_split_clause,[],[f239,f188,f108,f241])).
% 1.28/0.53  fof(f108,plain,(
% 1.28/0.53    spl5_12 <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.28/0.53  fof(f188,plain,(
% 1.28/0.53    spl5_26 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.28/0.53  fof(f239,plain,(
% 1.28/0.53    k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | (~spl5_12 | ~spl5_26)),
% 1.28/0.53    inference(forward_demodulation,[],[f231,f109])).
% 1.28/0.53  fof(f109,plain,(
% 1.28/0.53    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) | ~spl5_12),
% 1.28/0.53    inference(avatar_component_clause,[],[f108])).
% 1.28/0.53  fof(f231,plain,(
% 1.28/0.53    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~spl5_26),
% 1.28/0.53    inference(resolution,[],[f189,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.28/0.53  fof(f189,plain,(
% 1.28/0.53    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_26),
% 1.28/0.53    inference(avatar_component_clause,[],[f188])).
% 1.28/0.53  fof(f190,plain,(
% 1.28/0.53    ~spl5_8 | spl5_26 | ~spl5_7 | ~spl5_18 | ~spl5_22),
% 1.28/0.53    inference(avatar_split_clause,[],[f186,f166,f142,f71,f188,f75])).
% 1.28/0.53  fof(f75,plain,(
% 1.28/0.53    spl5_8 <=> v1_funct_1(sK3)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.28/0.53  fof(f71,plain,(
% 1.28/0.53    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.28/0.53  fof(f142,plain,(
% 1.28/0.53    spl5_18 <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.28/0.53  fof(f166,plain,(
% 1.28/0.53    spl5_22 <=> ! [X1,X0,X2] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.28/0.53  fof(f186,plain,(
% 1.28/0.53    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_18 | ~spl5_22)),
% 1.28/0.53    inference(forward_demodulation,[],[f180,f143])).
% 1.28/0.53  fof(f143,plain,(
% 1.28/0.53    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl5_18),
% 1.28/0.53    inference(avatar_component_clause,[],[f142])).
% 1.28/0.53  fof(f180,plain,(
% 1.28/0.53    ~v1_funct_1(sK3) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_7 | ~spl5_22)),
% 1.28/0.53    inference(resolution,[],[f167,f72])).
% 1.28/0.53  fof(f72,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 1.28/0.53    inference(avatar_component_clause,[],[f71])).
% 1.28/0.53  fof(f167,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_22),
% 1.28/0.53    inference(avatar_component_clause,[],[f166])).
% 1.28/0.53  fof(f168,plain,(
% 1.28/0.53    ~spl5_6 | spl5_22 | ~spl5_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f163,f63,f166,f67])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    spl5_6 <=> v1_funct_1(sK4)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.28/0.53  fof(f163,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 1.28/0.53    inference(resolution,[],[f45,f64])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.53    inference(flattening,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.28/0.53  fof(f157,plain,(
% 1.28/0.53    ~spl5_20 | spl5_1 | ~spl5_18),
% 1.28/0.53    inference(avatar_split_clause,[],[f152,f142,f47,f155])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    spl5_1 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.28/0.53  fof(f152,plain,(
% 1.28/0.53    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | (spl5_1 | ~spl5_18)),
% 1.28/0.53    inference(superposition,[],[f48,f143])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl5_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f47])).
% 1.28/0.53  fof(f144,plain,(
% 1.28/0.53    spl5_18 | ~spl5_8 | ~spl5_7 | ~spl5_15),
% 1.28/0.53    inference(avatar_split_clause,[],[f136,f127,f71,f75,f142])).
% 1.28/0.53  fof(f127,plain,(
% 1.28/0.53    spl5_15 <=> ! [X1,X0,X2] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.28/0.53  fof(f136,plain,(
% 1.28/0.53    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_7 | ~spl5_15)),
% 1.28/0.53    inference(resolution,[],[f128,f72])).
% 1.28/0.53  fof(f128,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)) ) | ~spl5_15),
% 1.28/0.53    inference(avatar_component_clause,[],[f127])).
% 1.28/0.53  fof(f129,plain,(
% 1.28/0.53    ~spl5_6 | spl5_15 | ~spl5_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f123,f63,f127,f67])).
% 1.28/0.53  fof(f123,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 1.28/0.53    inference(resolution,[],[f43,f64])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.28/0.53    inference(flattening,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.28/0.53    inference(ennf_transformation,[],[f8])).
% 1.28/0.53  % (26033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.28/0.53  fof(f110,plain,(
% 1.28/0.53    spl5_12 | ~spl5_5 | ~spl5_7 | ~spl5_10),
% 1.28/0.53    inference(avatar_split_clause,[],[f106,f89,f71,f63,f108])).
% 1.28/0.53  fof(f89,plain,(
% 1.28/0.53    spl5_10 <=> sK1 = k2_relat_1(sK3)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.28/0.53  fof(f106,plain,(
% 1.28/0.53    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) | (~spl5_5 | ~spl5_7 | ~spl5_10)),
% 1.28/0.53    inference(forward_demodulation,[],[f100,f90])).
% 1.28/0.53  fof(f90,plain,(
% 1.28/0.53    sK1 = k2_relat_1(sK3) | ~spl5_10),
% 1.28/0.53    inference(avatar_component_clause,[],[f89])).
% 1.28/0.53  fof(f100,plain,(
% 1.28/0.53    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_5 | ~spl5_7)),
% 1.28/0.53    inference(resolution,[],[f97,f72])).
% 1.28/0.53  fof(f97,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_5),
% 1.28/0.53    inference(resolution,[],[f96,f64])).
% 1.28/0.53  fof(f96,plain,(
% 1.28/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 1.28/0.53    inference(resolution,[],[f79,f40])).
% 1.28/0.53  fof(f79,plain,(
% 1.28/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.28/0.53    inference(resolution,[],[f37,f40])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.28/0.53  fof(f91,plain,(
% 1.28/0.53    spl5_10 | ~spl5_4 | ~spl5_7),
% 1.28/0.53    inference(avatar_split_clause,[],[f87,f71,f59,f89])).
% 1.28/0.53  fof(f59,plain,(
% 1.28/0.53    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    sK1 = k2_relat_1(sK3) | (~spl5_4 | ~spl5_7)),
% 1.28/0.53    inference(forward_demodulation,[],[f81,f60])).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    sK1 = k2_relset_1(sK0,sK1,sK3) | ~spl5_4),
% 1.28/0.53    inference(avatar_component_clause,[],[f59])).
% 1.28/0.53  fof(f81,plain,(
% 1.28/0.53    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl5_7),
% 1.28/0.53    inference(resolution,[],[f41,f72])).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    spl5_9 | ~spl5_3 | ~spl5_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f82,f63,f55,f84])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    spl5_3 <=> sK2 = k2_relset_1(sK1,sK2,sK4)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.28/0.53  fof(f82,plain,(
% 1.28/0.53    sK2 = k2_relat_1(sK4) | (~spl5_3 | ~spl5_5)),
% 1.28/0.53    inference(forward_demodulation,[],[f80,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    sK2 = k2_relset_1(sK1,sK2,sK4) | ~spl5_3),
% 1.28/0.53    inference(avatar_component_clause,[],[f55])).
% 1.28/0.53  fof(f80,plain,(
% 1.28/0.53    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) | ~spl5_5),
% 1.28/0.53    inference(resolution,[],[f41,f64])).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    spl5_8),
% 1.28/0.53    inference(avatar_split_clause,[],[f29,f75])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    v1_funct_1(sK3)),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f27,f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.28/0.53    inference(flattening,[],[f13])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.28/0.53    inference(ennf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 1.28/0.53    inference(pure_predicate_removal,[],[f10])).
% 1.28/0.53  fof(f10,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 1.28/0.53    inference(negated_conjecture,[],[f9])).
% 1.28/0.53  fof(f9,conjecture,(
% 1.28/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    spl5_7),
% 1.28/0.53    inference(avatar_split_clause,[],[f30,f71])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    spl5_6),
% 1.28/0.53    inference(avatar_split_clause,[],[f31,f67])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    v1_funct_1(sK4)),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    spl5_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f32,f63])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    spl5_4),
% 1.28/0.53    inference(avatar_split_clause,[],[f33,f59])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f57,plain,(
% 1.28/0.53    spl5_3),
% 1.28/0.53    inference(avatar_split_clause,[],[f34,f55])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    sK2 = k2_relset_1(sK1,sK2,sK4)),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ~spl5_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f36,f47])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (26035)------------------------------
% 1.28/0.53  % (26035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (26035)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (26035)Memory used [KB]: 10874
% 1.28/0.53  % (26035)Time elapsed: 0.076 s
% 1.28/0.53  % (26035)------------------------------
% 1.28/0.53  % (26035)------------------------------
% 1.28/0.53  % (26028)Success in time 0.158 s
%------------------------------------------------------------------------------
