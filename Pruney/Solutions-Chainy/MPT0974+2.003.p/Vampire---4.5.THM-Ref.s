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
% DateTime   : Thu Dec  3 13:01:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 234 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 (1006 expanded)
%              Number of equality atoms :  111 ( 375 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f64,f68,f72,f76,f80,f84,f109,f114,f122,f132,f156,f171,f193,f215,f280,f284,f310])).

fof(f310,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | k2_relat_1(k5_relat_1(sK3,sK4)) != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( spl5_37
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f266,f213,f282])).

fof(f282,plain,
    ( spl5_37
  <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f213,plain,
    ( spl5_26
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f266,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ spl5_26 ),
    inference(resolution,[],[f214,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f214,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f280,plain,
    ( spl5_36
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f276,f213,f129,f119,f78,f70,f278])).

fof(f278,plain,
    ( spl5_36
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f70,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f78,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f119,plain,
    ( spl5_13
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f129,plain,
    ( spl5_14
  <=> sK1 = k9_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f276,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f275,f120])).

fof(f120,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f275,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f265,f130])).

fof(f130,plain,
    ( sK1 = k9_relat_1(sK3,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f265,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k9_relat_1(sK3,sK0))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_26 ),
    inference(resolution,[],[f214,f142])).

fof(f142,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k9_relat_1(sK4,k9_relat_1(sK3,X1)) = k2_relat_1(k5_relat_1(sK3,sK4)) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f139,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(global_subsumption,[],[f44,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f41,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(global_subsumption,[],[f43,f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f139,plain,
    ( ! [X1] : k9_relat_1(k5_relat_1(sK3,sK4),X1) = k9_relat_1(sK4,k9_relat_1(sK3,X1))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f136,f79])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f136,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k9_relat_1(k5_relat_1(X0,sK4),X1) = k9_relat_1(sK4,k9_relat_1(X0,X1)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f135,f71])).

fof(f71,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f135,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f42,f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f215,plain,
    ( ~ spl5_8
    | spl5_26
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f211,f191,f169,f78,f213,f82])).

fof(f82,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f169,plain,
    ( spl5_18
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f191,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f211,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_18
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f205,f170])).

fof(f170,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f205,plain,
    ( ~ v1_funct_1(sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_7
    | ~ spl5_22 ),
    inference(resolution,[],[f192,f79])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( ~ spl5_6
    | spl5_22
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f188,f70,f191,f74])).

fof(f74,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f52,f71])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f171,plain,
    ( spl5_18
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f163,f154,f78,f82,f169])).

fof(f154,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f163,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(resolution,[],[f155,f79])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( ~ spl5_6
    | spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f150,f70,f154,f74])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f50,f71])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f132,plain,
    ( ~ spl5_7
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f126,f112,f129,f78])).

fof(f112,plain,
    ( spl5_12
  <=> sK1 = k7_relset_1(sK0,sK1,sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f126,plain,
    ( sK1 = k9_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_12 ),
    inference(superposition,[],[f49,f113])).

fof(f113,plain,
    ( sK1 = k7_relset_1(sK0,sK1,sK3,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f122,plain,
    ( ~ spl5_5
    | spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f116,f107,f119,f70])).

fof(f107,plain,
    ( spl5_11
  <=> sK2 = k7_relset_1(sK1,sK2,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f116,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_11 ),
    inference(superposition,[],[f49,f108])).

fof(f108,plain,
    ( sK2 = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f110,f78,f66,f112])).

fof(f66,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f110,plain,
    ( sK1 = k7_relset_1(sK0,sK1,sK3,sK0)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f104,f67])).

fof(f67,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f104,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f47,f79])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f109,plain,
    ( spl5_11
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f105,f70,f62,f107])).

fof(f62,plain,
    ( spl5_3
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f105,plain,
    ( sK2 = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f103,f63])).

fof(f63,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f103,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f47,f71])).

fof(f84,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK2
    & sK2 = k2_relset_1(sK1,sK2,sK4)
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f80,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f54])).

fof(f54,plain,
    ( spl5_1
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f40,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (7190)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (7186)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (7184)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (7199)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (7186)Refutation not found, incomplete strategy% (7186)------------------------------
% 0.22/0.49  % (7186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7192)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (7186)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7186)Memory used [KB]: 10618
% 0.22/0.50  % (7186)Time elapsed: 0.058 s
% 0.22/0.50  % (7186)------------------------------
% 0.22/0.50  % (7186)------------------------------
% 0.22/0.50  % (7193)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (7191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (7197)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (7188)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (7187)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (7204)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (7201)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (7198)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (7189)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (7195)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (7200)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (7194)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (7205)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (7191)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f56,f64,f68,f72,f76,f80,f84,f109,f114,f122,f132,f156,f171,f193,f215,f280,f284,f310])).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4) | k2_relat_1(k5_relat_1(sK3,sK4)) != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    spl5_37 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f266,f213,f282])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    spl5_37 <=> k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl5_26 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~spl5_26),
% 0.22/0.52    inference(resolution,[],[f214,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f213])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    spl5_36 | ~spl5_5 | ~spl5_7 | ~spl5_13 | ~spl5_14 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f276,f213,f129,f119,f78,f70,f278])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    spl5_36 <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl5_13 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl5_14 <=> sK1 = k9_relat_1(sK3,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | (~spl5_5 | ~spl5_7 | ~spl5_13 | ~spl5_14 | ~spl5_26)),
% 0.22/0.52    inference(forward_demodulation,[],[f275,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    sK2 = k9_relat_1(sK4,sK1) | ~spl5_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f275,plain,(
% 0.22/0.52    k9_relat_1(sK4,sK1) = k2_relat_1(k5_relat_1(sK3,sK4)) | (~spl5_5 | ~spl5_7 | ~spl5_14 | ~spl5_26)),
% 0.22/0.52    inference(forward_demodulation,[],[f265,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    sK1 = k9_relat_1(sK3,sK0) | ~spl5_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k9_relat_1(sK3,sK0)) | (~spl5_5 | ~spl5_7 | ~spl5_26)),
% 0.22/0.52    inference(resolution,[],[f214,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k9_relat_1(sK4,k9_relat_1(sK3,X1)) = k2_relat_1(k5_relat_1(sK3,sK4))) ) | (~spl5_5 | ~spl5_7)),
% 0.22/0.52    inference(superposition,[],[f139,f101])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.52    inference(global_subsumption,[],[f44,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.52    inference(superposition,[],[f41,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.52    inference(global_subsumption,[],[f43,f44,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X1] : (k9_relat_1(k5_relat_1(sK3,sK4),X1) = k9_relat_1(sK4,k9_relat_1(sK3,X1))) ) | (~spl5_5 | ~spl5_7)),
% 0.22/0.52    inference(resolution,[],[f136,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k9_relat_1(k5_relat_1(X0,sK4),X1) = k9_relat_1(sK4,k9_relat_1(X0,X1))) ) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f135,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.22/0.52    inference(resolution,[],[f102,f44])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.52    inference(resolution,[],[f42,f44])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    ~spl5_8 | spl5_26 | ~spl5_7 | ~spl5_18 | ~spl5_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f211,f191,f169,f78,f213,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl5_8 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl5_18 <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    spl5_22 <=> ! [X1,X0,X2] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_18 | ~spl5_22)),
% 0.22/0.52    inference(forward_demodulation,[],[f205,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl5_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_7 | ~spl5_22)),
% 0.22/0.52    inference(resolution,[],[f192,f79])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f191])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ~spl5_6 | spl5_22 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f188,f70,f191,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl5_6 <=> v1_funct_1(sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f52,f71])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl5_18 | ~spl5_8 | ~spl5_7 | ~spl5_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f163,f154,f78,f82,f169])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    spl5_15 <=> ! [X1,X0,X2] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_7 | ~spl5_15)),
% 0.22/0.52    inference(resolution,[],[f155,f79])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)) ) | ~spl5_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f154])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ~spl5_6 | spl5_15 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f150,f70,f154,f74])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f50,f71])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~spl5_7 | spl5_14 | ~spl5_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f126,f112,f129,f78])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl5_12 <=> sK1 = k7_relset_1(sK0,sK1,sK3,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    sK1 = k9_relat_1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_12),
% 0.22/0.52    inference(superposition,[],[f49,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    sK1 = k7_relset_1(sK0,sK1,sK3,sK0) | ~spl5_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f112])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ~spl5_5 | spl5_13 | ~spl5_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f116,f107,f119,f70])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl5_11 <=> sK2 = k7_relset_1(sK1,sK2,sK4,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    sK2 = k9_relat_1(sK4,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_11),
% 0.22/0.52    inference(superposition,[],[f49,f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    sK2 = k7_relset_1(sK1,sK2,sK4,sK1) | ~spl5_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl5_12 | ~spl5_4 | ~spl5_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f110,f78,f66,f112])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    sK1 = k7_relset_1(sK0,sK1,sK3,sK0) | (~spl5_4 | ~spl5_7)),
% 0.22/0.52    inference(forward_demodulation,[],[f104,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK3) | ~spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0) | ~spl5_7),
% 0.22/0.52    inference(resolution,[],[f47,f79])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl5_11 | ~spl5_3 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f70,f62,f107])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl5_3 <=> sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    sK2 = k7_relset_1(sK1,sK2,sK4,sK1) | (~spl5_3 | ~spl5_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f103,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    sK2 = k2_relset_1(sK1,sK2,sK4) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f47,f71])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f33,f82])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f31,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl5_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f78])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f74])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f70])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f66])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f62])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl5_1 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7191)------------------------------
% 0.22/0.53  % (7191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7191)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7191)Memory used [KB]: 10874
% 0.22/0.53  % (7191)Time elapsed: 0.055 s
% 0.22/0.53  % (7191)------------------------------
% 0.22/0.53  % (7191)------------------------------
% 0.22/0.53  % (7205)Refutation not found, incomplete strategy% (7205)------------------------------
% 0.22/0.53  % (7205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7205)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7205)Memory used [KB]: 10618
% 0.22/0.53  % (7205)Time elapsed: 0.106 s
% 0.22/0.53  % (7205)------------------------------
% 0.22/0.53  % (7205)------------------------------
% 0.22/0.53  % (7181)Success in time 0.159 s
%------------------------------------------------------------------------------
