%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 222 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  346 ( 944 expanded)
%              Number of equality atoms :  100 ( 362 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f60,f64,f68,f72,f76,f80,f89,f94,f113,f137,f219,f226,f251,f256,f261])).

fof(f261,plain,
    ( ~ spl5_5
    | ~ spl5_9
    | spl5_36 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_9
    | spl5_36 ),
    inference(subsumption_resolution,[],[f67,f259])).

fof(f259,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl5_9
    | spl5_36 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( ! [X0] :
        ( sK2 != sK2
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_9
    | spl5_36 ),
    inference(forward_demodulation,[],[f257,f88])).

fof(f88,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_9
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f257,plain,
    ( ! [X0] :
        ( sK2 != k2_relat_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl5_36 ),
    inference(superposition,[],[f255,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f43,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f41,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(global_subsumption,[],[f42,f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f255,plain,
    ( sK2 != k9_relat_1(sK4,sK1)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl5_36
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f67,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f256,plain,
    ( ~ spl5_36
    | spl5_31
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f252,f249,f224,f254])).

fof(f224,plain,
    ( spl5_31
  <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f249,plain,
    ( spl5_35
  <=> k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f252,plain,
    ( sK2 != k9_relat_1(sK4,sK1)
    | spl5_31
    | ~ spl5_35 ),
    inference(superposition,[],[f225,f250])).

fof(f250,plain,
    ( k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f249])).

fof(f225,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f224])).

% (9271)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f251,plain,
    ( spl5_35
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f247,f217,f111,f249])).

fof(f111,plain,
    ( spl5_12
  <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f217,plain,
    ( spl5_30
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f247,plain,
    ( k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_12
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f232,f112])).

fof(f112,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f232,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_30 ),
    inference(resolution,[],[f218,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f218,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f217])).

fof(f226,plain,
    ( ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_31
    | spl5_1 ),
    inference(avatar_split_clause,[],[f220,f50,f224,f66,f70,f74,f78])).

fof(f78,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f74,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f70,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f50,plain,
    ( spl5_1
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f220,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl5_1 ),
    inference(superposition,[],[f51,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f51,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f219,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | spl5_30
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f198,f135,f217,f66,f74])).

fof(f135,plain,
    ( spl5_16
  <=> m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f198,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_16 ),
    inference(superposition,[],[f136,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f136,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl5_16
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f129,f74,f66,f135])).

fof(f129,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f48,f67])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f113,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f109,f92,f74,f66,f111])).

fof(f92,plain,
    ( spl5_10
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f109,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f103,f93])).

fof(f93,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f103,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f100,f75])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f99,f67])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f82,f43])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f94,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f90,f74,f62,f92])).

fof(f62,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f90,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f84,f63])).

fof(f63,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f84,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f44,f75])).

fof(f89,plain,
    ( spl5_9
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f85,f66,f58,f87])).

fof(f58,plain,
    ( spl5_3
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f85,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f83,f59])).

fof(f59,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f44,f67])).

fof(f80,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK2
    & sK2 = k2_relset_1(sK1,sK2,sK4)
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

fof(f76,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f50])).

fof(f39,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:35:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.47  % (9262)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.47  % (9263)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.48  % (9272)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.49  % (9263)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f262,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f52,f60,f64,f68,f72,f76,f80,f89,f94,f113,f137,f219,f226,f251,f256,f261])).
% 0.23/0.49  fof(f261,plain,(
% 0.23/0.49    ~spl5_5 | ~spl5_9 | spl5_36),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f260])).
% 0.23/0.49  fof(f260,plain,(
% 0.23/0.49    $false | (~spl5_5 | ~spl5_9 | spl5_36)),
% 0.23/0.49    inference(subsumption_resolution,[],[f67,f259])).
% 0.23/0.49  fof(f259,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_9 | spl5_36)),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f258])).
% 0.23/0.49  fof(f258,plain,(
% 0.23/0.49    ( ! [X0] : (sK2 != sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_9 | spl5_36)),
% 0.23/0.49    inference(forward_demodulation,[],[f257,f88])).
% 0.23/0.49  fof(f88,plain,(
% 0.23/0.49    sK2 = k2_relat_1(sK4) | ~spl5_9),
% 0.23/0.49    inference(avatar_component_clause,[],[f87])).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    spl5_9 <=> sK2 = k2_relat_1(sK4)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.23/0.49  fof(f257,plain,(
% 0.23/0.49    ( ! [X0] : (sK2 != k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl5_36),
% 0.23/0.49    inference(superposition,[],[f255,f98])).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.23/0.49    inference(global_subsumption,[],[f43,f97])).
% 0.23/0.49  fof(f97,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.23/0.49    inference(superposition,[],[f41,f96])).
% 0.23/0.49  fof(f96,plain,(
% 0.23/0.49    ( ! [X4,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.23/0.49    inference(global_subsumption,[],[f42,f43,f45])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.23/0.49    inference(pure_predicate_removal,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(flattening,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.49  fof(f255,plain,(
% 0.23/0.49    sK2 != k9_relat_1(sK4,sK1) | spl5_36),
% 0.23/0.49    inference(avatar_component_clause,[],[f254])).
% 0.23/0.49  fof(f254,plain,(
% 0.23/0.49    spl5_36 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.23/0.49  fof(f67,plain,(
% 0.23/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.23/0.49    inference(avatar_component_clause,[],[f66])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.23/0.49  fof(f256,plain,(
% 0.23/0.49    ~spl5_36 | spl5_31 | ~spl5_35),
% 0.23/0.49    inference(avatar_split_clause,[],[f252,f249,f224,f254])).
% 0.23/0.49  fof(f224,plain,(
% 0.23/0.49    spl5_31 <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.23/0.49  fof(f249,plain,(
% 0.23/0.49    spl5_35 <=> k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.23/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.23/0.49  fof(f252,plain,(
% 0.23/0.49    sK2 != k9_relat_1(sK4,sK1) | (spl5_31 | ~spl5_35)),
% 0.23/0.49    inference(superposition,[],[f225,f250])).
% 0.23/0.49  fof(f250,plain,(
% 0.23/0.49    k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~spl5_35),
% 0.23/0.49    inference(avatar_component_clause,[],[f249])).
% 0.23/0.49  fof(f225,plain,(
% 0.23/0.49    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | spl5_31),
% 0.23/0.49    inference(avatar_component_clause,[],[f224])).
% 0.23/0.50  % (9271)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.50  fof(f251,plain,(
% 0.23/0.50    spl5_35 | ~spl5_12 | ~spl5_30),
% 0.23/0.50    inference(avatar_split_clause,[],[f247,f217,f111,f249])).
% 0.23/0.50  fof(f111,plain,(
% 0.23/0.50    spl5_12 <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.23/0.50  fof(f217,plain,(
% 0.23/0.50    spl5_30 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.23/0.50  fof(f247,plain,(
% 0.23/0.50    k9_relat_1(sK4,sK1) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | (~spl5_12 | ~spl5_30)),
% 0.23/0.50    inference(forward_demodulation,[],[f232,f112])).
% 0.23/0.50  fof(f112,plain,(
% 0.23/0.50    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) | ~spl5_12),
% 0.23/0.50    inference(avatar_component_clause,[],[f111])).
% 0.23/0.50  fof(f232,plain,(
% 0.23/0.50    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~spl5_30),
% 0.23/0.50    inference(resolution,[],[f218,f44])).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.50  fof(f218,plain,(
% 0.23/0.50    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_30),
% 0.23/0.50    inference(avatar_component_clause,[],[f217])).
% 0.23/0.50  fof(f226,plain,(
% 0.23/0.50    ~spl5_8 | ~spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_31 | spl5_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f220,f50,f224,f66,f70,f74,f78])).
% 0.23/0.50  fof(f78,plain,(
% 0.23/0.50    spl5_8 <=> v1_funct_1(sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    spl5_6 <=> v1_funct_1(sK4)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    spl5_1 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.50  fof(f220,plain,(
% 0.23/0.50    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl5_1),
% 0.23/0.50    inference(superposition,[],[f51,f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.23/0.50    inference(flattening,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.23/0.50    inference(ennf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,axiom,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.23/0.50  fof(f51,plain,(
% 0.23/0.50    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl5_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f50])).
% 0.23/0.50  fof(f219,plain,(
% 0.23/0.50    ~spl5_7 | ~spl5_5 | spl5_30 | ~spl5_16),
% 0.23/0.50    inference(avatar_split_clause,[],[f198,f135,f217,f66,f74])).
% 0.23/0.50  fof(f135,plain,(
% 0.23/0.50    spl5_16 <=> m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.23/0.50  fof(f198,plain,(
% 0.23/0.50    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_16),
% 0.23/0.50    inference(superposition,[],[f136,f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.50    inference(flattening,[],[f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.50    inference(ennf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,axiom,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.23/0.50  fof(f136,plain,(
% 0.23/0.50    m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_16),
% 0.23/0.50    inference(avatar_component_clause,[],[f135])).
% 0.23/0.50  fof(f137,plain,(
% 0.23/0.50    spl5_16 | ~spl5_5 | ~spl5_7),
% 0.23/0.50    inference(avatar_split_clause,[],[f129,f74,f66,f135])).
% 0.23/0.50  fof(f129,plain,(
% 0.23/0.50    m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_5 | ~spl5_7)),
% 0.23/0.50    inference(resolution,[],[f126,f75])).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.23/0.50    inference(avatar_component_clause,[],[f74])).
% 0.23/0.50  fof(f126,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k4_relset_1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_5),
% 0.23/0.50    inference(resolution,[],[f48,f67])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.50    inference(flattening,[],[f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.23/0.50  fof(f113,plain,(
% 0.23/0.50    spl5_12 | ~spl5_5 | ~spl5_7 | ~spl5_10),
% 0.23/0.50    inference(avatar_split_clause,[],[f109,f92,f74,f66,f111])).
% 0.23/0.50  fof(f92,plain,(
% 0.23/0.50    spl5_10 <=> sK1 = k2_relat_1(sK3)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.23/0.50  fof(f109,plain,(
% 0.23/0.50    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,sK1) | (~spl5_5 | ~spl5_7 | ~spl5_10)),
% 0.23/0.50    inference(forward_demodulation,[],[f103,f93])).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    sK1 = k2_relat_1(sK3) | ~spl5_10),
% 0.23/0.50    inference(avatar_component_clause,[],[f92])).
% 0.23/0.50  fof(f103,plain,(
% 0.23/0.50    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_5 | ~spl5_7)),
% 0.23/0.50    inference(resolution,[],[f100,f75])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_relat_1(k5_relat_1(X0,sK4)) = k9_relat_1(sK4,k2_relat_1(X0))) ) | ~spl5_5),
% 0.23/0.51    inference(resolution,[],[f99,f67])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.23/0.51    inference(resolution,[],[f82,f43])).
% 0.23/0.51  fof(f82,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.23/0.51    inference(resolution,[],[f40,f43])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.23/0.51  fof(f94,plain,(
% 0.23/0.51    spl5_10 | ~spl5_4 | ~spl5_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f90,f74,f62,f92])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    sK1 = k2_relat_1(sK3) | (~spl5_4 | ~spl5_7)),
% 0.23/0.51    inference(forward_demodulation,[],[f84,f63])).
% 0.23/0.51  fof(f63,plain,(
% 0.23/0.51    sK1 = k2_relset_1(sK0,sK1,sK3) | ~spl5_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f62])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl5_7),
% 0.23/0.51    inference(resolution,[],[f44,f75])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    spl5_9 | ~spl5_3 | ~spl5_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f85,f66,f58,f87])).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    spl5_3 <=> sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    sK2 = k2_relat_1(sK4) | (~spl5_3 | ~spl5_5)),
% 0.23/0.51    inference(forward_demodulation,[],[f83,f59])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    sK2 = k2_relset_1(sK1,sK2,sK4) | ~spl5_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f58])).
% 0.23/0.51  fof(f83,plain,(
% 0.23/0.51    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) | ~spl5_5),
% 0.23/0.51    inference(resolution,[],[f44,f67])).
% 0.23/0.51  fof(f80,plain,(
% 0.23/0.51    spl5_8),
% 0.23/0.51    inference(avatar_split_clause,[],[f32,f78])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    v1_funct_1(sK3)),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f30,f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.23/0.51    inference(flattening,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.23/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.23/0.51  fof(f11,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.23/0.51    inference(negated_conjecture,[],[f10])).
% 0.23/0.51  fof(f10,conjecture,(
% 0.23/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).
% 0.23/0.51  fof(f76,plain,(
% 0.23/0.51    spl5_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f33,f74])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f72,plain,(
% 0.23/0.51    spl5_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f34,f70])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    v1_funct_1(sK4)),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f68,plain,(
% 0.23/0.51    spl5_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f35,f66])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    spl5_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f36,f62])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    spl5_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f37,f58])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ~spl5_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f39,f50])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (9263)------------------------------
% 0.23/0.51  % (9263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (9263)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (9263)Memory used [KB]: 11001
% 0.23/0.51  % (9263)Time elapsed: 0.061 s
% 0.23/0.51  % (9263)------------------------------
% 0.23/0.51  % (9263)------------------------------
% 0.23/0.51  % (9256)Success in time 0.138 s
%------------------------------------------------------------------------------
