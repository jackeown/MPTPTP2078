%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 396 expanded)
%              Number of leaves         :   47 ( 186 expanded)
%              Depth                    :   13
%              Number of atoms          :  678 (1803 expanded)
%              Number of equality atoms :  141 ( 487 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f95,f99,f103,f109,f113,f127,f137,f152,f161,f165,f169,f192,f208,f227,f260,f270,f280,f287,f298,f309,f339,f345,f360,f363,f366,f368])).

fof(f368,plain,
    ( ~ spl3_30
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl3_30
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f222,f359])).

fof(f359,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl3_46
  <=> ! [X1,X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f222,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f366,plain,
    ( spl3_30
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f365,f197,f130,f221])).

fof(f130,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f197,plain,
    ( spl3_26
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f131,f198])).

fof(f198,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f197])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f363,plain,
    ( ~ spl3_15
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl3_15
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f131,f356])).

fof(f356,plain,
    ( ! [X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2)))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_45
  <=> ! [X2] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f360,plain,
    ( spl3_44
    | ~ spl3_7
    | spl3_45
    | spl3_46
    | ~ spl3_31
    | spl3_17
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f351,f221,f197,f150,f225,f358,f355,f89,f343])).

fof(f343,plain,
    ( spl3_44
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f89,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f225,plain,
    ( spl3_31
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f150,plain,
    ( spl3_17
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f351,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2)))
        | ~ v1_funct_1(sK2)
        | k2_struct_0(sK0) = k1_relat_1(sK2) )
    | spl3_17
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(resolution,[],[f350,f222])).

fof(f350,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) = X3 )
    | spl3_17
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f349,f198])).

fof(f349,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(X0,X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_struct_0(sK1))))
        | k1_relat_1(X0) = X3 )
    | spl3_17
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f347,f198])).

fof(f347,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X0,X3,k2_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_struct_0(sK1))))
        | k1_relat_1(X0) = X3 )
    | spl3_17 ),
    inference(resolution,[],[f248,f151])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f248,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( v1_xboole_0(X9)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8)))
      | ~ v1_funct_2(X4,X5,X9)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9)))
      | k1_relat_1(X4) = X5 ) ),
    inference(resolution,[],[f244,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f244,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f182,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f345,plain,
    ( ~ spl3_18
    | ~ spl3_7
    | ~ spl3_3
    | ~ spl3_44
    | spl3_43 ),
    inference(avatar_split_clause,[],[f340,f337,f343,f73,f89,f155])).

fof(f155,plain,
    ( spl3_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f73,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f337,plain,
    ( spl3_43
  <=> k2_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f340,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_43 ),
    inference(superposition,[],[f338,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f338,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f337])).

fof(f339,plain,
    ( ~ spl3_43
    | spl3_38
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f335,f307,f296,f337])).

fof(f296,plain,
    ( spl3_38
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f307,plain,
    ( spl3_39
  <=> k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f335,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | spl3_38
    | ~ spl3_39 ),
    inference(superposition,[],[f297,f308])).

fof(f308,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f307])).

fof(f297,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f296])).

fof(f309,plain,
    ( ~ spl3_30
    | ~ spl3_7
    | ~ spl3_31
    | spl3_39
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f300,f278,f307,f225,f89,f221])).

fof(f278,plain,
    ( spl3_36
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f300,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_36 ),
    inference(superposition,[],[f245,f279])).

fof(f279,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f278])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X1,k2_tops_2(X1,X2,X0)) = k2_relat_1(k2_tops_2(X1,X2,X0))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f298,plain,
    ( ~ spl3_38
    | spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f294,f278,f197,f111,f107,f69,f296])).

fof(f69,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f111,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f294,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f293,f279])).

fof(f293,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f292,f112])).

fof(f112,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f292,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f291,f198])).

fof(f291,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f70,f108])).

fof(f108,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f70,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f287,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f280,plain,
    ( ~ spl3_31
    | spl3_36
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f276,f268,f197,f130,f115,f278,f225])).

fof(f115,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f268,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f276,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f274,f116])).

fof(f116,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f274,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f273,f198])).

fof(f273,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f271,f198])).

fof(f271,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_35 ),
    inference(resolution,[],[f269,f131])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f268])).

fof(f270,plain,
    ( ~ spl3_7
    | spl3_35
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f266,f73,f268,f89])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f260,plain,
    ( spl3_33
    | ~ spl3_31
    | ~ spl3_7
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f252,f221,f89,f225,f257])).

fof(f257,plain,
    ( spl3_33
  <=> k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f252,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_7
    | ~ spl3_30 ),
    inference(resolution,[],[f249,f222])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relset_1(X1,X0,k2_tops_2(X0,X1,sK2)) = k1_relat_1(k2_tops_2(X0,X1,sK2)) )
    | ~ spl3_7 ),
    inference(resolution,[],[f246,f90])).

fof(f90,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f246,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X4,X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_relset_1(X5,X4,k2_tops_2(X4,X5,X3)) = k1_relat_1(k2_tops_2(X4,X5,X3)) ) ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f227,plain,
    ( spl3_31
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f212,f197,f135,f225])).

fof(f135,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f212,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(superposition,[],[f136,f198])).

fof(f136,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f208,plain,
    ( spl3_26
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f206,f190,f115,f197])).

fof(f190,plain,
    ( spl3_24
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f206,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(superposition,[],[f116,f191])).

fof(f191,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl3_24
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f188,f130,f190])).

fof(f188,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f58,f131])).

fof(f169,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f168,f111,f107,f81,f130])).

fof(f81,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f167,f112])).

fof(f167,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f82,f108])).

fof(f82,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f165,plain,
    ( ~ spl3_5
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl3_5
    | spl3_18 ),
    inference(subsumption_resolution,[],[f82,f162])).

fof(f162,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_18 ),
    inference(resolution,[],[f156,f56])).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f161,plain,
    ( ~ spl3_18
    | ~ spl3_7
    | spl3_19
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f153,f73,f159,f89,f155])).

fof(f159,plain,
    ( spl3_19
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f153,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f74])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f152,plain,
    ( ~ spl3_8
    | ~ spl3_17
    | spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f147,f107,f97,f150,f93])).

fof(f93,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f97,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f147,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f146,f108])).

fof(f146,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_9 ),
    inference(resolution,[],[f49,f98])).

fof(f98,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f49,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f137,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f133,f111,f107,f85,f135])).

fof(f85,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f133,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f120,f112])).

fof(f120,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f86,f108])).

fof(f86,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f127,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f126,f111,f107,f77,f115])).

fof(f77,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f126,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f118,f112])).

fof(f118,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f78,f108])).

fof(f78,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f113,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f105,f101,f111])).

fof(f101,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f48,f102])).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f109,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f104,f93,f107])).

fof(f104,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f48,f94])).

fof(f94,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f103,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f99,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f43,f85])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f81])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f45,f77])).

fof(f45,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f73])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f69,f66])).

fof(f66,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (25298)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (25299)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (25306)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (25299)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (25306)Refutation not found, incomplete strategy% (25306)------------------------------
% 0.20/0.48  % (25306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25306)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25306)Memory used [KB]: 1663
% 0.20/0.48  % (25306)Time elapsed: 0.069 s
% 0.20/0.48  % (25306)------------------------------
% 0.20/0.48  % (25306)------------------------------
% 0.20/0.48  % (25307)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f369,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f95,f99,f103,f109,f113,f127,f137,f152,f161,f165,f169,f192,f208,f227,f260,f270,f280,f287,f298,f309,f339,f345,f360,f363,f366,f368])).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    ~spl3_30 | ~spl3_46),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f367])).
% 0.20/0.50  fof(f367,plain,(
% 0.20/0.50    $false | (~spl3_30 | ~spl3_46)),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f359])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f358])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    spl3_46 <=> ! [X1,X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    spl3_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.50  fof(f366,plain,(
% 0.20/0.50    spl3_30 | ~spl3_15 | ~spl3_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f365,f197,f130,f221])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    spl3_26 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_15 | ~spl3_26)),
% 0.20/0.50    inference(forward_demodulation,[],[f131,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f197])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    ~spl3_15 | ~spl3_45),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f361])).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    $false | (~spl3_15 | ~spl3_45)),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f356])).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2)))) ) | ~spl3_45),
% 0.20/0.50    inference(avatar_component_clause,[],[f355])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    spl3_45 <=> ! [X2] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    spl3_44 | ~spl3_7 | spl3_45 | spl3_46 | ~spl3_31 | spl3_17 | ~spl3_26 | ~spl3_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f351,f221,f197,f150,f225,f358,f355,f89,f343])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    spl3_44 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl3_7 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    spl3_31 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    spl3_17 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2))) | ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2)) ) | (spl3_17 | ~spl3_26 | ~spl3_30)),
% 0.20/0.50    inference(resolution,[],[f350,f222])).
% 0.20/0.50  fof(f350,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(sK2)))) | ~v1_funct_2(X0,X3,k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | k1_relat_1(X0) = X3) ) | (spl3_17 | ~spl3_26)),
% 0.20/0.50    inference(forward_demodulation,[],[f349,f198])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X0,X3,k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_struct_0(sK1)))) | k1_relat_1(X0) = X3) ) | (spl3_17 | ~spl3_26)),
% 0.20/0.50    inference(forward_demodulation,[],[f347,f198])).
% 0.20/0.50  fof(f347,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X0,X3,k2_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k2_struct_0(sK1)))) | k1_relat_1(X0) = X3) ) | spl3_17),
% 0.20/0.50    inference(resolution,[],[f248,f151])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f150])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    ( ! [X6,X4,X8,X7,X5,X9] : (v1_xboole_0(X9) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X8))) | ~v1_funct_2(X4,X5,X9) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X9))) | k1_relat_1(X4) = X5) )),
% 0.20/0.50    inference(resolution,[],[f244,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.20/0.50    inference(resolution,[],[f182,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.20/0.50    inference(resolution,[],[f54,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f345,plain,(
% 0.20/0.50    ~spl3_18 | ~spl3_7 | ~spl3_3 | ~spl3_44 | spl3_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f340,f337,f343,f73,f89,f155])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl3_18 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl3_3 <=> v2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    spl3_43 <=> k2_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_43),
% 0.20/0.50    inference(superposition,[],[f338,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f338,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | spl3_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f337])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    ~spl3_43 | spl3_38 | ~spl3_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f335,f307,f296,f337])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl3_38 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl3_39 <=> k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | (spl3_38 | ~spl3_39)),
% 0.20/0.50    inference(superposition,[],[f297,f308])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f307])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | spl3_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    ~spl3_30 | ~spl3_7 | ~spl3_31 | spl3_39 | ~spl3_36),
% 0.20/0.50    inference(avatar_split_clause,[],[f300,f278,f307,f225,f89,f221])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    spl3_36 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_36),
% 0.20/0.50    inference(superposition,[],[f245,f279])).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f278])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X2,X1,k2_tops_2(X1,X2,X0)) = k2_relat_1(k2_tops_2(X1,X2,X0)) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(resolution,[],[f62,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~spl3_38 | spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_26 | ~spl3_36),
% 0.20/0.50    inference(avatar_split_clause,[],[f294,f278,f197,f111,f107,f69,f296])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    spl3_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl3_12 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_26 | ~spl3_36)),
% 0.20/0.50    inference(forward_demodulation,[],[f293,f279])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_26)),
% 0.20/0.50    inference(forward_demodulation,[],[f292,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_11 | ~spl3_26)),
% 0.20/0.50    inference(forward_demodulation,[],[f291,f198])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f70,f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f107])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f69])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    ~spl3_31 | spl3_36 | ~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f276,f268,f197,f130,f115,f278,f225])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl3_13 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    spl3_35 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_35)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f275])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f274,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f273,f198])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f271,f198])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_35)),
% 0.20/0.50    inference(resolution,[],[f269,f131])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f268])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~spl3_7 | spl3_35 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f266,f73,f268,f89])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f63,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    spl3_33 | ~spl3_31 | ~spl3_7 | ~spl3_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f252,f221,f89,f225,f257])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    spl3_33 <=> k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_7 | ~spl3_30)),
% 0.20/0.50    inference(resolution,[],[f249,f222])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k1_relset_1(X1,X0,k2_tops_2(X0,X1,sK2)) = k1_relat_1(k2_tops_2(X0,X1,sK2))) ) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f246,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f89])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X4,X5) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_relset_1(X5,X4,k2_tops_2(X4,X5,X3)) = k1_relat_1(k2_tops_2(X4,X5,X3))) )),
% 0.20/0.50    inference(resolution,[],[f62,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    spl3_31 | ~spl3_16 | ~spl3_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f212,f197,f135,f225])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl3_16 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_26)),
% 0.20/0.50    inference(superposition,[],[f136,f198])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    spl3_26 | ~spl3_13 | ~spl3_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f206,f190,f115,f197])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl3_24 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_13 | ~spl3_24)),
% 0.20/0.50    inference(superposition,[],[f116,f191])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl3_24 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f188,f130,f190])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_15),
% 0.20/0.50    inference(resolution,[],[f58,f131])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f168,f111,f107,f81,f130])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f167,f112])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f82,f108])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f81])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~spl3_5 | spl3_18),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f163])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    $false | (~spl3_5 | spl3_18)),
% 0.20/0.50    inference(subsumption_resolution,[],[f82,f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_18),
% 0.20/0.50    inference(resolution,[],[f156,f56])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl3_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ~spl3_18 | ~spl3_7 | spl3_19 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f153,f73,f159,f89,f155])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl3_19 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f50,f74])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~spl3_8 | ~spl3_17 | spl3_9 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f147,f107,f97,f150,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl3_8 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl3_9 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | (spl3_9 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f146,f108])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | spl3_9),
% 0.20/0.50    inference(resolution,[],[f49,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~v2_struct_0(sK1) | spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl3_16 | ~spl3_6 | ~spl3_11 | ~spl3_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f133,f111,f107,f85,f135])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11 | ~spl3_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f120,f112])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11)),
% 0.20/0.50    inference(superposition,[],[f86,f108])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f85])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    spl3_13 | ~spl3_4 | ~spl3_11 | ~spl3_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f126,f111,f107,f77,f115])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f118,f112])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11)),
% 0.20/0.50    inference(superposition,[],[f78,f108])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl3_12 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f105,f101,f111])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    spl3_10 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(resolution,[],[f48,f102])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f101])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl3_11 | ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f104,f93,f107])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.20/0.50    inference(resolution,[],[f48,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    l1_struct_0(sK1) | ~spl3_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f101])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f97])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f93])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f89])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f85])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f81])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f77])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f73])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f69,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (25299)------------------------------
% 0.20/0.50  % (25299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25299)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (25299)Memory used [KB]: 11001
% 0.20/0.50  % (25299)Time elapsed: 0.060 s
% 0.20/0.50  % (25299)------------------------------
% 0.20/0.50  % (25299)------------------------------
% 0.20/0.50  % (25292)Success in time 0.143 s
%------------------------------------------------------------------------------
