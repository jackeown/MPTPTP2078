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
% DateTime   : Thu Dec  3 13:02:30 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 429 expanded)
%              Number of leaves         :   48 ( 153 expanded)
%              Depth                    :    9
%              Number of atoms          :  823 (2322 expanded)
%              Number of equality atoms :  170 ( 643 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f220,f225,f244,f400,f402,f416,f448,f459,f467,f484,f509,f511,f513,f554,f640,f671,f685,f715,f726,f771,f783,f786,f801,f933,f960,f1063,f1095,f1391,f1409,f1447])).

fof(f1447,plain,(
    ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f1410])).

fof(f1410,plain,
    ( $false
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f66,f594])).

fof(f594,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl4_32
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f66,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1409,plain,
    ( ~ spl4_44
    | ~ spl4_45
    | ~ spl4_36
    | spl4_32
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f1405,f700,f592,f621,f708,f704])).

fof(f704,plain,
    ( spl4_44
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f708,plain,
    ( spl4_45
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f621,plain,
    ( spl4_36
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f700,plain,
    ( spl4_43
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1405,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f78,f702])).

fof(f702,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f700])).

fof(f78,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f1391,plain,
    ( ~ spl4_15
    | ~ spl4_21
    | ~ spl4_36
    | spl4_17
    | spl4_45
    | ~ spl4_47
    | ~ spl4_29
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f1388,f1093,f551,f717,f708,f382,f621,f408,f374])).

fof(f374,plain,
    ( spl4_15
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f408,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f382,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f717,plain,
    ( spl4_47
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f551,plain,
    ( spl4_29
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1093,plain,
    ( spl4_90
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1388,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_29
    | ~ spl4_90 ),
    inference(superposition,[],[f1094,f553])).

fof(f553,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f551])).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1095,plain,
    ( ~ spl4_25
    | spl4_90
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f1091,f387,f212,f1093,f502])).

fof(f502,plain,
    ( spl4_25
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f212,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f387,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f1086])).

fof(f1086,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f108,f61])).

fof(f61,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1063,plain,
    ( spl4_46
    | ~ spl4_71 ),
    inference(avatar_contradiction_clause,[],[f1062])).

fof(f1062,plain,
    ( $false
    | spl4_46
    | ~ spl4_71 ),
    inference(trivial_inequality_removal,[],[f1061])).

fof(f1061,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | spl4_46
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f714,f958])).

fof(f958,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f956])).

fof(f956,plain,
    ( spl4_71
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f714,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl4_46
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f960,plain,
    ( ~ spl4_21
    | spl4_71
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f949,f930,f956,f408])).

fof(f930,plain,
    ( spl4_69
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f949,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_69 ),
    inference(superposition,[],[f90,f932])).

fof(f932,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f930])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f933,plain,
    ( spl4_69
    | ~ spl4_36
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_21
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f925,f374,f408,f502,f387,f212,f621,f930])).

fof(f925,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f119,f114])).

fof(f114,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f70,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(definition_unfolding,[],[f104,f70])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f801,plain,
    ( ~ spl4_7
    | ~ spl4_50
    | ~ spl4_26
    | ~ spl4_24
    | ~ spl4_49
    | ~ spl4_25
    | spl4_47
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f788,f780,f717,f502,f754,f498,f506,f758,f230])).

fof(f230,plain,
    ( spl4_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f758,plain,
    ( spl4_50
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f506,plain,
    ( spl4_26
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f498,plain,
    ( spl4_24
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f754,plain,
    ( spl4_49
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f780,plain,
    ( spl4_52
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f788,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_52 ),
    inference(superposition,[],[f79,f782])).

fof(f782,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f780])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f786,plain,(
    spl4_50 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | spl4_50 ),
    inference(unit_resulting_resolution,[],[f136,f63,f67,f760,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f760,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f758])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f136,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f783,plain,
    ( spl4_52
    | spl4_20
    | ~ spl4_26
    | ~ spl4_25
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f778,f387,f212,f502,f506,f395,f780])).

fof(f395,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f778,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f775])).

fof(f775,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f118,f61])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(definition_unfolding,[],[f102,f70])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f771,plain,(
    spl4_49 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl4_49 ),
    inference(unit_resulting_resolution,[],[f136,f67,f756,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f756,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f754])).

fof(f726,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_44 ),
    inference(subsumption_resolution,[],[f135,f706])).

fof(f706,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_44 ),
    inference(avatar_component_clause,[],[f704])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f715,plain,
    ( spl4_43
    | ~ spl4_44
    | ~ spl4_45
    | ~ spl4_25
    | ~ spl4_7
    | ~ spl4_36
    | ~ spl4_46
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f698,f674,f412,f216,f712,f621,f230,f502,f708,f704,f700])).

fof(f216,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f412,plain,
    ( spl4_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f674,plain,
    ( spl4_41
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f698,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_41 ),
    inference(trivial_inequality_removal,[],[f697])).

fof(f697,plain,
    ( sK1 != sK1
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f696,f218])).

fof(f218,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f216])).

fof(f696,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_22
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f694,f414])).

fof(f414,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f412])).

fof(f694,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_41 ),
    inference(superposition,[],[f80,f676])).

fof(f676,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f674])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f685,plain,
    ( ~ spl4_25
    | ~ spl4_21
    | ~ spl4_36
    | ~ spl4_5
    | spl4_41
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f682,f551,f674,f212,f621,f408,f502])).

fof(f682,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_29 ),
    inference(superposition,[],[f111,f553])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f671,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f67,f58,f60,f69,f549,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f549,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl4_28
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f640,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl4_36 ),
    inference(subsumption_resolution,[],[f58,f623])).

fof(f623,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f621])).

fof(f554,plain,
    ( ~ spl4_28
    | spl4_29 ),
    inference(avatar_split_clause,[],[f544,f551,f547])).

fof(f544,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f418,f114])).

fof(f418,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
      | k6_relat_1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f110,f115])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f513,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f63,f508])).

fof(f508,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f506])).

fof(f511,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f67,f504])).

fof(f504,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f502])).

fof(f509,plain,
    ( spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f496,f387,f212,f506,f502,f498])).

fof(f496,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f493])).

fof(f493,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f99,f61])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f484,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f64,f384])).

fof(f384,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f382])).

fof(f64,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f467,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f461,f382,f378,f374])).

fof(f378,plain,
    ( spl4_16
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f461,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f60,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f459,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f60,f410])).

fof(f410,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f408])).

fof(f448,plain,(
    ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f65,f397])).

fof(f397,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f395])).

fof(f65,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f416,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f405,f378,f412,f408])).

fof(f405,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_16 ),
    inference(superposition,[],[f89,f380])).

fof(f380,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f378])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f402,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f68,f389])).

fof(f389,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f387])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f400,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f59,f376])).

fof(f376,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f374])).

fof(f59,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f244,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f136,f232])).

fof(f232,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f230])).

fof(f225,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f69,f214])).

fof(f214,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f212])).

fof(f220,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f210,f216,f212])).

fof(f210,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f61,f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21039)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (21031)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (21053)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (21056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.51  % (21036)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (21052)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (21041)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (21038)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (21040)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (21035)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21045)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (21044)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (21051)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (21048)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (21037)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21058)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (21034)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (21060)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (21043)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (21042)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (21046)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21059)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (21032)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (21033)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (21055)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (21050)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (21054)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (21057)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (21047)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (21047)Refutation not found, incomplete strategy% (21047)------------------------------
% 0.22/0.55  % (21047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21047)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21047)Memory used [KB]: 10746
% 0.22/0.55  % (21047)Time elapsed: 0.152 s
% 0.22/0.55  % (21047)------------------------------
% 0.22/0.55  % (21047)------------------------------
% 0.22/0.56  % (21049)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.76/0.61  % (21044)Refutation found. Thanks to Tanya!
% 1.76/0.61  % SZS status Theorem for theBenchmark
% 1.76/0.61  % SZS output start Proof for theBenchmark
% 1.76/0.61  fof(f1455,plain,(
% 1.76/0.61    $false),
% 1.76/0.61    inference(avatar_sat_refutation,[],[f220,f225,f244,f400,f402,f416,f448,f459,f467,f484,f509,f511,f513,f554,f640,f671,f685,f715,f726,f771,f783,f786,f801,f933,f960,f1063,f1095,f1391,f1409,f1447])).
% 1.76/0.61  fof(f1447,plain,(
% 1.76/0.61    ~spl4_32),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f1410])).
% 1.76/0.61  fof(f1410,plain,(
% 1.76/0.61    $false | ~spl4_32),
% 1.76/0.61    inference(subsumption_resolution,[],[f66,f594])).
% 1.76/0.61  fof(f594,plain,(
% 1.76/0.61    sK3 = k2_funct_1(sK2) | ~spl4_32),
% 1.76/0.61    inference(avatar_component_clause,[],[f592])).
% 1.76/0.61  fof(f592,plain,(
% 1.76/0.61    spl4_32 <=> sK3 = k2_funct_1(sK2)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.76/0.61  fof(f66,plain,(
% 1.76/0.61    sK3 != k2_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f26,plain,(
% 1.76/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.76/0.61    inference(flattening,[],[f25])).
% 1.76/0.61  fof(f25,plain,(
% 1.76/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.76/0.61    inference(ennf_transformation,[],[f24])).
% 1.76/0.61  fof(f24,negated_conjecture,(
% 1.76/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.61    inference(negated_conjecture,[],[f23])).
% 1.76/0.61  fof(f23,conjecture,(
% 1.76/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.76/0.61  fof(f1409,plain,(
% 1.76/0.61    ~spl4_44 | ~spl4_45 | ~spl4_36 | spl4_32 | ~spl4_43),
% 1.76/0.61    inference(avatar_split_clause,[],[f1405,f700,f592,f621,f708,f704])).
% 1.76/0.61  fof(f704,plain,(
% 1.76/0.61    spl4_44 <=> v1_relat_1(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.76/0.61  fof(f708,plain,(
% 1.76/0.61    spl4_45 <=> v2_funct_1(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.76/0.61  fof(f621,plain,(
% 1.76/0.61    spl4_36 <=> v1_funct_1(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.76/0.61  fof(f700,plain,(
% 1.76/0.61    spl4_43 <=> sK2 = k2_funct_1(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.76/0.61  fof(f1405,plain,(
% 1.76/0.61    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_43),
% 1.76/0.61    inference(superposition,[],[f78,f702])).
% 1.76/0.61  fof(f702,plain,(
% 1.76/0.61    sK2 = k2_funct_1(sK3) | ~spl4_43),
% 1.76/0.61    inference(avatar_component_clause,[],[f700])).
% 1.76/0.61  fof(f78,plain,(
% 1.76/0.61    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f32])).
% 1.76/0.61  fof(f32,plain,(
% 1.76/0.61    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f31])).
% 1.76/0.61  fof(f31,plain,(
% 1.76/0.61    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f8])).
% 1.76/0.61  fof(f8,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.76/0.61  fof(f1391,plain,(
% 1.76/0.61    ~spl4_15 | ~spl4_21 | ~spl4_36 | spl4_17 | spl4_45 | ~spl4_47 | ~spl4_29 | ~spl4_90),
% 1.76/0.61    inference(avatar_split_clause,[],[f1388,f1093,f551,f717,f708,f382,f621,f408,f374])).
% 1.76/0.61  fof(f374,plain,(
% 1.76/0.61    spl4_15 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.76/0.61  fof(f408,plain,(
% 1.76/0.61    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.76/0.61  fof(f382,plain,(
% 1.76/0.61    spl4_17 <=> k1_xboole_0 = sK0),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.76/0.61  fof(f717,plain,(
% 1.76/0.61    spl4_47 <=> v2_funct_1(k6_relat_1(sK0))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.76/0.61  fof(f551,plain,(
% 1.76/0.61    spl4_29 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.76/0.61  fof(f1093,plain,(
% 1.76/0.61    spl4_90 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.76/0.61  fof(f1388,plain,(
% 1.76/0.61    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_29 | ~spl4_90)),
% 1.76/0.61    inference(superposition,[],[f1094,f553])).
% 1.76/0.61  fof(f553,plain,(
% 1.76/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_29),
% 1.76/0.61    inference(avatar_component_clause,[],[f551])).
% 1.76/0.61  fof(f1094,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_90),
% 1.76/0.61    inference(avatar_component_clause,[],[f1093])).
% 1.76/0.61  fof(f1095,plain,(
% 1.76/0.61    ~spl4_25 | spl4_90 | ~spl4_5 | ~spl4_18),
% 1.76/0.61    inference(avatar_split_clause,[],[f1091,f387,f212,f1093,f502])).
% 1.76/0.61  fof(f502,plain,(
% 1.76/0.61    spl4_25 <=> v1_funct_1(sK2)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.76/0.61  fof(f212,plain,(
% 1.76/0.61    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.76/0.61  fof(f387,plain,(
% 1.76/0.61    spl4_18 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.76/0.61  fof(f1091,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.76/0.61    inference(trivial_inequality_removal,[],[f1086])).
% 1.76/0.61  fof(f1086,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.76/0.61    inference(superposition,[],[f108,f61])).
% 1.76/0.61  fof(f61,plain,(
% 1.76/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f108,plain,(
% 1.76/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f51])).
% 1.76/0.61  fof(f51,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.76/0.61    inference(flattening,[],[f50])).
% 1.76/0.61  fof(f50,plain,(
% 1.76/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.76/0.61    inference(ennf_transformation,[],[f20])).
% 1.76/0.61  fof(f20,axiom,(
% 1.76/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.76/0.61  fof(f1063,plain,(
% 1.76/0.61    spl4_46 | ~spl4_71),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f1062])).
% 1.76/0.61  fof(f1062,plain,(
% 1.76/0.61    $false | (spl4_46 | ~spl4_71)),
% 1.76/0.61    inference(trivial_inequality_removal,[],[f1061])).
% 1.76/0.61  fof(f1061,plain,(
% 1.76/0.61    k6_relat_1(sK0) != k6_relat_1(sK0) | (spl4_46 | ~spl4_71)),
% 1.76/0.61    inference(forward_demodulation,[],[f714,f958])).
% 1.76/0.61  fof(f958,plain,(
% 1.76/0.61    sK0 = k2_relat_1(sK3) | ~spl4_71),
% 1.76/0.61    inference(avatar_component_clause,[],[f956])).
% 1.76/0.61  fof(f956,plain,(
% 1.76/0.61    spl4_71 <=> sK0 = k2_relat_1(sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.76/0.61  fof(f714,plain,(
% 1.76/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | spl4_46),
% 1.76/0.61    inference(avatar_component_clause,[],[f712])).
% 1.76/0.61  fof(f712,plain,(
% 1.76/0.61    spl4_46 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.76/0.61  fof(f960,plain,(
% 1.76/0.61    ~spl4_21 | spl4_71 | ~spl4_69),
% 1.76/0.61    inference(avatar_split_clause,[],[f949,f930,f956,f408])).
% 1.76/0.61  fof(f930,plain,(
% 1.76/0.61    spl4_69 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.76/0.61  fof(f949,plain,(
% 1.76/0.61    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_69),
% 1.76/0.61    inference(superposition,[],[f90,f932])).
% 1.76/0.61  fof(f932,plain,(
% 1.76/0.61    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_69),
% 1.76/0.61    inference(avatar_component_clause,[],[f930])).
% 1.76/0.61  fof(f90,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f40])).
% 1.76/0.61  fof(f40,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(ennf_transformation,[],[f12])).
% 1.76/0.61  fof(f12,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.76/0.61  fof(f933,plain,(
% 1.76/0.61    spl4_69 | ~spl4_36 | ~spl4_5 | ~spl4_18 | ~spl4_25 | ~spl4_21 | ~spl4_15),
% 1.76/0.61    inference(avatar_split_clause,[],[f925,f374,f408,f502,f387,f212,f621,f930])).
% 1.76/0.61  fof(f925,plain,(
% 1.76/0.61    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.76/0.61    inference(resolution,[],[f119,f114])).
% 1.76/0.61  fof(f114,plain,(
% 1.76/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.76/0.61    inference(definition_unfolding,[],[f62,f70])).
% 1.76/0.61  fof(f70,plain,(
% 1.76/0.61    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f18])).
% 1.76/0.61  fof(f18,axiom,(
% 1.76/0.61    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.76/0.61  fof(f62,plain,(
% 1.76/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f119,plain,(
% 1.76/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.76/0.61    inference(definition_unfolding,[],[f104,f70])).
% 1.76/0.61  fof(f104,plain,(
% 1.76/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f49])).
% 1.76/0.61  fof(f49,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.61    inference(flattening,[],[f48])).
% 1.76/0.61  fof(f48,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.61    inference(ennf_transformation,[],[f19])).
% 1.76/0.61  fof(f19,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.76/0.61  fof(f801,plain,(
% 1.76/0.61    ~spl4_7 | ~spl4_50 | ~spl4_26 | ~spl4_24 | ~spl4_49 | ~spl4_25 | spl4_47 | ~spl4_52),
% 1.76/0.61    inference(avatar_split_clause,[],[f788,f780,f717,f502,f754,f498,f506,f758,f230])).
% 1.76/0.61  fof(f230,plain,(
% 1.76/0.61    spl4_7 <=> v1_relat_1(sK2)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.76/0.61  fof(f758,plain,(
% 1.76/0.61    spl4_50 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.76/0.61  fof(f506,plain,(
% 1.76/0.61    spl4_26 <=> v2_funct_1(sK2)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.76/0.61  fof(f498,plain,(
% 1.76/0.61    spl4_24 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.76/0.61  fof(f754,plain,(
% 1.76/0.61    spl4_49 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.76/0.61  fof(f780,plain,(
% 1.76/0.61    spl4_52 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.76/0.61  fof(f788,plain,(
% 1.76/0.61    v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_52),
% 1.76/0.61    inference(superposition,[],[f79,f782])).
% 1.76/0.61  fof(f782,plain,(
% 1.76/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_52),
% 1.76/0.61    inference(avatar_component_clause,[],[f780])).
% 1.76/0.61  fof(f79,plain,(
% 1.76/0.61    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f34])).
% 1.76/0.61  fof(f34,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f33])).
% 1.76/0.61  fof(f33,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f6])).
% 1.76/0.61  fof(f6,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).
% 1.76/0.61  fof(f786,plain,(
% 1.76/0.61    spl4_50),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f784])).
% 1.76/0.61  fof(f784,plain,(
% 1.76/0.61    $false | spl4_50),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f136,f63,f67,f760,f75])).
% 1.76/0.61  fof(f75,plain,(
% 1.76/0.61    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f28])).
% 1.76/0.61  fof(f28,plain,(
% 1.76/0.61    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f27])).
% 1.76/0.61  fof(f27,plain,(
% 1.76/0.61    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f5])).
% 1.76/0.61  fof(f5,axiom,(
% 1.76/0.61    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.76/0.61  fof(f760,plain,(
% 1.76/0.61    ~v2_funct_1(k2_funct_1(sK2)) | spl4_50),
% 1.76/0.61    inference(avatar_component_clause,[],[f758])).
% 1.76/0.61  fof(f67,plain,(
% 1.76/0.61    v1_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f63,plain,(
% 1.76/0.61    v2_funct_1(sK2)),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f136,plain,(
% 1.76/0.61    v1_relat_1(sK2)),
% 1.76/0.61    inference(resolution,[],[f88,f69])).
% 1.76/0.61  fof(f69,plain,(
% 1.76/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f88,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f38])).
% 1.76/0.61  fof(f38,plain,(
% 1.76/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.61    inference(ennf_transformation,[],[f9])).
% 1.76/0.61  fof(f9,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.76/0.61  fof(f783,plain,(
% 1.76/0.61    spl4_52 | spl4_20 | ~spl4_26 | ~spl4_25 | ~spl4_5 | ~spl4_18),
% 1.76/0.61    inference(avatar_split_clause,[],[f778,f387,f212,f502,f506,f395,f780])).
% 1.76/0.61  fof(f395,plain,(
% 1.76/0.61    spl4_20 <=> k1_xboole_0 = sK1),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.76/0.61  fof(f778,plain,(
% 1.76/0.61    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(trivial_inequality_removal,[],[f775])).
% 1.76/0.61  fof(f775,plain,(
% 1.76/0.61    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.76/0.61    inference(superposition,[],[f118,f61])).
% 1.76/0.61  fof(f118,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.76/0.61    inference(definition_unfolding,[],[f102,f70])).
% 1.76/0.61  fof(f102,plain,(
% 1.76/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f47])).
% 1.76/0.61  fof(f47,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.61    inference(flattening,[],[f46])).
% 1.76/0.61  fof(f46,plain,(
% 1.76/0.61    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.61    inference(ennf_transformation,[],[f22])).
% 1.76/0.61  fof(f22,axiom,(
% 1.76/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.76/0.61  fof(f771,plain,(
% 1.76/0.61    spl4_49),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f767])).
% 1.76/0.61  fof(f767,plain,(
% 1.76/0.61    $false | spl4_49),
% 1.76/0.61    inference(unit_resulting_resolution,[],[f136,f67,f756,f76])).
% 1.76/0.61  fof(f76,plain,(
% 1.76/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f30])).
% 1.76/0.61  fof(f30,plain,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(flattening,[],[f29])).
% 1.76/0.61  fof(f29,plain,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f4])).
% 1.76/0.61  fof(f4,axiom,(
% 1.76/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.76/0.61  fof(f756,plain,(
% 1.76/0.61    ~v1_relat_1(k2_funct_1(sK2)) | spl4_49),
% 1.76/0.61    inference(avatar_component_clause,[],[f754])).
% 1.76/0.61  fof(f726,plain,(
% 1.76/0.61    spl4_44),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f721])).
% 1.76/0.61  fof(f721,plain,(
% 1.76/0.61    $false | spl4_44),
% 1.76/0.61    inference(subsumption_resolution,[],[f135,f706])).
% 1.76/0.61  fof(f706,plain,(
% 1.76/0.61    ~v1_relat_1(sK3) | spl4_44),
% 1.76/0.61    inference(avatar_component_clause,[],[f704])).
% 1.76/0.61  fof(f135,plain,(
% 1.76/0.61    v1_relat_1(sK3)),
% 1.76/0.61    inference(resolution,[],[f88,f60])).
% 1.76/0.61  fof(f60,plain,(
% 1.76/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.76/0.61    inference(cnf_transformation,[],[f26])).
% 1.76/0.61  fof(f715,plain,(
% 1.76/0.61    spl4_43 | ~spl4_44 | ~spl4_45 | ~spl4_25 | ~spl4_7 | ~spl4_36 | ~spl4_46 | ~spl4_6 | ~spl4_22 | ~spl4_41),
% 1.76/0.61    inference(avatar_split_clause,[],[f698,f674,f412,f216,f712,f621,f230,f502,f708,f704,f700])).
% 1.76/0.62  fof(f216,plain,(
% 1.76/0.62    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.76/0.62  fof(f412,plain,(
% 1.76/0.62    spl4_22 <=> sK1 = k1_relat_1(sK3)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.76/0.62  fof(f674,plain,(
% 1.76/0.62    spl4_41 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.76/0.62  fof(f698,plain,(
% 1.76/0.62    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_22 | ~spl4_41)),
% 1.76/0.62    inference(trivial_inequality_removal,[],[f697])).
% 1.76/0.62  fof(f697,plain,(
% 1.76/0.62    sK1 != sK1 | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_22 | ~spl4_41)),
% 1.76/0.62    inference(forward_demodulation,[],[f696,f218])).
% 1.76/0.62  fof(f218,plain,(
% 1.76/0.62    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.76/0.62    inference(avatar_component_clause,[],[f216])).
% 1.76/0.62  fof(f696,plain,(
% 1.76/0.62    sK1 != k2_relat_1(sK2) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_22 | ~spl4_41)),
% 1.76/0.62    inference(forward_demodulation,[],[f694,f414])).
% 1.76/0.62  fof(f414,plain,(
% 1.76/0.62    sK1 = k1_relat_1(sK3) | ~spl4_22),
% 1.76/0.62    inference(avatar_component_clause,[],[f412])).
% 1.76/0.62  fof(f694,plain,(
% 1.76/0.62    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_41),
% 1.76/0.62    inference(superposition,[],[f80,f676])).
% 1.76/0.62  fof(f676,plain,(
% 1.76/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_41),
% 1.76/0.62    inference(avatar_component_clause,[],[f674])).
% 1.76/0.62  fof(f80,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.76/0.62    inference(cnf_transformation,[],[f36])).
% 1.76/0.62  fof(f36,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.62    inference(flattening,[],[f35])).
% 1.76/0.62  fof(f35,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f7])).
% 1.76/0.62  fof(f7,axiom,(
% 1.76/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.76/0.62  fof(f685,plain,(
% 1.76/0.62    ~spl4_25 | ~spl4_21 | ~spl4_36 | ~spl4_5 | spl4_41 | ~spl4_29),
% 1.76/0.62    inference(avatar_split_clause,[],[f682,f551,f674,f212,f621,f408,f502])).
% 1.76/0.62  fof(f682,plain,(
% 1.76/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_29),
% 1.76/0.62    inference(superposition,[],[f111,f553])).
% 1.76/0.62  fof(f111,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f55])).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.62    inference(flattening,[],[f54])).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.62    inference(ennf_transformation,[],[f17])).
% 1.76/0.62  fof(f17,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.76/0.62  fof(f671,plain,(
% 1.76/0.62    spl4_28),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f655])).
% 1.76/0.62  fof(f655,plain,(
% 1.76/0.62    $false | spl4_28),
% 1.76/0.62    inference(unit_resulting_resolution,[],[f67,f58,f60,f69,f549,f113])).
% 1.76/0.62  fof(f113,plain,(
% 1.76/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f57])).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.76/0.62    inference(flattening,[],[f56])).
% 1.76/0.62  fof(f56,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.76/0.62    inference(ennf_transformation,[],[f15])).
% 1.76/0.62  fof(f15,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.76/0.62  fof(f549,plain,(
% 1.76/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_28),
% 1.76/0.62    inference(avatar_component_clause,[],[f547])).
% 1.76/0.62  fof(f547,plain,(
% 1.76/0.62    spl4_28 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.76/0.62  fof(f58,plain,(
% 1.76/0.62    v1_funct_1(sK3)),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f640,plain,(
% 1.76/0.62    spl4_36),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f639])).
% 1.76/0.62  fof(f639,plain,(
% 1.76/0.62    $false | spl4_36),
% 1.76/0.62    inference(subsumption_resolution,[],[f58,f623])).
% 1.76/0.62  fof(f623,plain,(
% 1.76/0.62    ~v1_funct_1(sK3) | spl4_36),
% 1.76/0.62    inference(avatar_component_clause,[],[f621])).
% 1.76/0.62  fof(f554,plain,(
% 1.76/0.62    ~spl4_28 | spl4_29),
% 1.76/0.62    inference(avatar_split_clause,[],[f544,f551,f547])).
% 1.76/0.62  fof(f544,plain,(
% 1.76/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.76/0.62    inference(resolution,[],[f418,f114])).
% 1.76/0.62  fof(f418,plain,(
% 1.76/0.62    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_relat_1(X2)) | k6_relat_1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.76/0.62    inference(resolution,[],[f110,f115])).
% 1.76/0.62  fof(f115,plain,(
% 1.76/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f72,f70])).
% 1.76/0.62  fof(f72,plain,(
% 1.76/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f16])).
% 1.76/0.62  fof(f16,axiom,(
% 1.76/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.76/0.62  fof(f110,plain,(
% 1.76/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f53])).
% 1.76/0.62  fof(f53,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(flattening,[],[f52])).
% 1.76/0.62  fof(f52,plain,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.76/0.62    inference(ennf_transformation,[],[f13])).
% 1.76/0.62  fof(f13,axiom,(
% 1.76/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.76/0.62  fof(f513,plain,(
% 1.76/0.62    spl4_26),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f512])).
% 1.76/0.62  fof(f512,plain,(
% 1.76/0.62    $false | spl4_26),
% 1.76/0.62    inference(subsumption_resolution,[],[f63,f508])).
% 1.76/0.62  fof(f508,plain,(
% 1.76/0.62    ~v2_funct_1(sK2) | spl4_26),
% 1.76/0.62    inference(avatar_component_clause,[],[f506])).
% 1.76/0.62  fof(f511,plain,(
% 1.76/0.62    spl4_25),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f510])).
% 1.76/0.62  fof(f510,plain,(
% 1.76/0.62    $false | spl4_25),
% 1.76/0.62    inference(subsumption_resolution,[],[f67,f504])).
% 1.76/0.62  fof(f504,plain,(
% 1.76/0.62    ~v1_funct_1(sK2) | spl4_25),
% 1.76/0.62    inference(avatar_component_clause,[],[f502])).
% 1.76/0.62  fof(f509,plain,(
% 1.76/0.62    spl4_24 | ~spl4_25 | ~spl4_26 | ~spl4_5 | ~spl4_18),
% 1.76/0.62    inference(avatar_split_clause,[],[f496,f387,f212,f506,f502,f498])).
% 1.76/0.62  fof(f496,plain,(
% 1.76/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(trivial_inequality_removal,[],[f493])).
% 1.76/0.62  fof(f493,plain,(
% 1.76/0.62    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.76/0.62    inference(superposition,[],[f99,f61])).
% 1.76/0.62  fof(f99,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f45])).
% 1.76/0.62  fof(f45,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.76/0.62    inference(flattening,[],[f44])).
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.76/0.62    inference(ennf_transformation,[],[f21])).
% 1.76/0.62  fof(f21,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.76/0.62  fof(f484,plain,(
% 1.76/0.62    ~spl4_17),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f468])).
% 1.76/0.62  fof(f468,plain,(
% 1.76/0.62    $false | ~spl4_17),
% 1.76/0.62    inference(subsumption_resolution,[],[f64,f384])).
% 1.76/0.62  fof(f384,plain,(
% 1.76/0.62    k1_xboole_0 = sK0 | ~spl4_17),
% 1.76/0.62    inference(avatar_component_clause,[],[f382])).
% 1.76/0.62  fof(f64,plain,(
% 1.76/0.62    k1_xboole_0 != sK0),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f467,plain,(
% 1.76/0.62    ~spl4_15 | spl4_16 | spl4_17),
% 1.76/0.62    inference(avatar_split_clause,[],[f461,f382,f378,f374])).
% 1.76/0.62  fof(f378,plain,(
% 1.76/0.62    spl4_16 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.76/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.76/0.62  fof(f461,plain,(
% 1.76/0.62    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.62    inference(resolution,[],[f60,f98])).
% 1.76/0.62  fof(f98,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f43])).
% 1.76/0.62  fof(f43,plain,(
% 1.76/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(flattening,[],[f42])).
% 1.76/0.62  fof(f42,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(ennf_transformation,[],[f14])).
% 1.76/0.62  fof(f14,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.76/0.62  fof(f459,plain,(
% 1.76/0.62    spl4_21),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f455])).
% 1.76/0.62  fof(f455,plain,(
% 1.76/0.62    $false | spl4_21),
% 1.76/0.62    inference(subsumption_resolution,[],[f60,f410])).
% 1.76/0.62  fof(f410,plain,(
% 1.76/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 1.76/0.62    inference(avatar_component_clause,[],[f408])).
% 1.76/0.62  fof(f448,plain,(
% 1.76/0.62    ~spl4_20),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f431])).
% 1.76/0.62  fof(f431,plain,(
% 1.76/0.62    $false | ~spl4_20),
% 1.76/0.62    inference(subsumption_resolution,[],[f65,f397])).
% 1.76/0.62  fof(f397,plain,(
% 1.76/0.62    k1_xboole_0 = sK1 | ~spl4_20),
% 1.76/0.62    inference(avatar_component_clause,[],[f395])).
% 1.76/0.62  fof(f65,plain,(
% 1.76/0.62    k1_xboole_0 != sK1),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f416,plain,(
% 1.76/0.62    ~spl4_21 | spl4_22 | ~spl4_16),
% 1.76/0.62    inference(avatar_split_clause,[],[f405,f378,f412,f408])).
% 1.76/0.62  fof(f405,plain,(
% 1.76/0.62    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_16),
% 1.76/0.62    inference(superposition,[],[f89,f380])).
% 1.76/0.62  fof(f380,plain,(
% 1.76/0.62    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_16),
% 1.76/0.62    inference(avatar_component_clause,[],[f378])).
% 1.76/0.62  fof(f89,plain,(
% 1.76/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f39])).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.62    inference(ennf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,axiom,(
% 1.76/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.76/0.62  fof(f402,plain,(
% 1.76/0.62    spl4_18),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f401])).
% 1.76/0.62  fof(f401,plain,(
% 1.76/0.62    $false | spl4_18),
% 1.76/0.62    inference(subsumption_resolution,[],[f68,f389])).
% 1.76/0.62  fof(f389,plain,(
% 1.76/0.62    ~v1_funct_2(sK2,sK0,sK1) | spl4_18),
% 1.76/0.62    inference(avatar_component_clause,[],[f387])).
% 1.76/0.62  fof(f68,plain,(
% 1.76/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f400,plain,(
% 1.76/0.62    spl4_15),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f399])).
% 1.76/0.62  fof(f399,plain,(
% 1.76/0.62    $false | spl4_15),
% 1.76/0.62    inference(subsumption_resolution,[],[f59,f376])).
% 1.76/0.62  fof(f376,plain,(
% 1.76/0.62    ~v1_funct_2(sK3,sK1,sK0) | spl4_15),
% 1.76/0.62    inference(avatar_component_clause,[],[f374])).
% 1.76/0.62  fof(f59,plain,(
% 1.76/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f244,plain,(
% 1.76/0.62    spl4_7),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f241])).
% 1.76/0.62  fof(f241,plain,(
% 1.76/0.62    $false | spl4_7),
% 1.76/0.62    inference(subsumption_resolution,[],[f136,f232])).
% 1.76/0.62  fof(f232,plain,(
% 1.76/0.62    ~v1_relat_1(sK2) | spl4_7),
% 1.76/0.62    inference(avatar_component_clause,[],[f230])).
% 1.76/0.62  fof(f225,plain,(
% 1.76/0.62    spl4_5),
% 1.76/0.62    inference(avatar_contradiction_clause,[],[f221])).
% 1.76/0.62  fof(f221,plain,(
% 1.76/0.62    $false | spl4_5),
% 1.76/0.62    inference(subsumption_resolution,[],[f69,f214])).
% 1.76/0.62  fof(f214,plain,(
% 1.76/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.76/0.62    inference(avatar_component_clause,[],[f212])).
% 1.76/0.62  fof(f220,plain,(
% 1.76/0.62    ~spl4_5 | spl4_6),
% 1.76/0.62    inference(avatar_split_clause,[],[f210,f216,f212])).
% 1.76/0.62  fof(f210,plain,(
% 1.76/0.62    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.76/0.62    inference(superposition,[],[f61,f90])).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (21044)------------------------------
% 1.76/0.62  % (21044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (21044)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (21044)Memory used [KB]: 7291
% 1.76/0.62  % (21044)Time elapsed: 0.195 s
% 1.76/0.62  % (21044)------------------------------
% 1.76/0.62  % (21044)------------------------------
% 1.76/0.63  % (21030)Success in time 0.264 s
%------------------------------------------------------------------------------
