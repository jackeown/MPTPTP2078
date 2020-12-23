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
% DateTime   : Thu Dec  3 13:03:01 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 413 expanded)
%              Number of leaves         :   49 ( 159 expanded)
%              Depth                    :    8
%              Number of atoms          :  737 (2024 expanded)
%              Number of equality atoms :  156 ( 574 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2035,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f124,f128,f149,f229,f231,f234,f263,f451,f453,f467,f480,f532,f540,f552,f575,f584,f597,f635,f803,f867,f874,f903,f967,f986,f1503,f1511,f1945,f1981,f2013])).

fof(f2013,plain,(
    ~ spl4_180 ),
    inference(avatar_contradiction_clause,[],[f1982])).

fof(f1982,plain,
    ( $false
    | ~ spl4_180 ),
    inference(subsumption_resolution,[],[f55,f1980])).

fof(f1980,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_180 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f1978,plain,
    ( spl4_180
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f55,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1981,plain,
    ( ~ spl4_1
    | spl4_180
    | ~ spl4_65
    | ~ spl4_175 ),
    inference(avatar_split_clause,[],[f1976,f1940,f800,f1978,f104])).

fof(f104,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f800,plain,
    ( spl4_65
  <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1940,plain,
    ( spl4_175
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_175])])).

fof(f1976,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_65
    | ~ spl4_175 ),
    inference(forward_demodulation,[],[f1964,f802])).

fof(f802,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f800])).

fof(f1964,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_175 ),
    inference(superposition,[],[f95,f1942])).

fof(f1942,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_175 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1945,plain,
    ( ~ spl4_1
    | ~ spl4_79
    | ~ spl4_30
    | spl4_175
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1944,f900,f1940,f431,f895,f104])).

fof(f895,plain,
    ( spl4_79
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f431,plain,
    ( spl4_30
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f900,plain,
    ( spl4_80
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1944,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f1923,f93])).

fof(f93,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1923,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_80 ),
    inference(superposition,[],[f73,f902])).

fof(f902,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f900])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f1511,plain,(
    spl4_141 ),
    inference(avatar_contradiction_clause,[],[f1508])).

fof(f1508,plain,
    ( $false
    | spl4_141 ),
    inference(unit_resulting_resolution,[],[f90,f1502])).

fof(f1502,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_141 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f1500,plain,
    ( spl4_141
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1503,plain,
    ( ~ spl4_74
    | ~ spl4_29
    | ~ spl4_30
    | spl4_78
    | spl4_79
    | ~ spl4_141
    | ~ spl4_18
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f1496,f984,f260,f1500,f895,f891,f431,f427,f864])).

fof(f864,plain,
    ( spl4_74
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f427,plain,
    ( spl4_29
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f891,plain,
    ( spl4_78
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f260,plain,
    ( spl4_18
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f984,plain,
    ( spl4_86
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f1496,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_18
    | ~ spl4_86 ),
    inference(superposition,[],[f985,f262])).

fof(f262,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f985,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f984])).

fof(f986,plain,
    ( ~ spl4_12
    | spl4_86
    | ~ spl4_5
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f982,f529,f139,f984,f216])).

fof(f216,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f529,plain,
    ( spl4_41
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f982,plain,(
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
    inference(trivial_inequality_removal,[],[f977])).

fof(f977,plain,(
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
    inference(superposition,[],[f83,f50])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f967,plain,(
    ~ spl4_78 ),
    inference(avatar_contradiction_clause,[],[f944])).

fof(f944,plain,
    ( $false
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f53,f893])).

fof(f893,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f891])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f903,plain,
    ( spl4_80
    | spl4_78
    | ~ spl4_79
    | ~ spl4_30
    | ~ spl4_29
    | ~ spl4_74
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f879,f860,f864,f427,f431,f895,f891,f900])).

fof(f860,plain,
    ( spl4_73
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f879,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_73 ),
    inference(trivial_inequality_removal,[],[f877])).

fof(f877,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_73 ),
    inference(superposition,[],[f77,f862])).

fof(f862,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f860])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f874,plain,(
    spl4_74 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | spl4_74 ),
    inference(subsumption_resolution,[],[f48,f866])).

fof(f866,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f864])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f867,plain,
    ( spl4_73
    | ~ spl4_30
    | ~ spl4_5
    | ~ spl4_41
    | ~ spl4_12
    | ~ spl4_29
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f855,f864,f427,f216,f529,f139,f431,f860])).

fof(f855,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f803,plain,
    ( ~ spl4_1
    | spl4_65
    | ~ spl4_33
    | ~ spl4_46
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f798,f633,f594,f470,f800,f104])).

fof(f470,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f594,plain,
    ( spl4_46
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f633,plain,
    ( spl4_51
  <=> ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f798,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33
    | ~ spl4_46
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f789,f596])).

fof(f596,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f594])).

fof(f789,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33
    | ~ spl4_51 ),
    inference(superposition,[],[f634,f472])).

fof(f472,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f470])).

fof(f634,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f633])).

fof(f635,plain,
    ( ~ spl4_13
    | ~ spl4_3
    | spl4_51
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f617,f581,f633,f113,f220])).

fof(f220,plain,
    ( spl4_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f113,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f581,plain,
    ( spl4_44
  <=> k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f617,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_44 ),
    inference(superposition,[],[f67,f583])).

fof(f583,plain,
    ( k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f581])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f597,plain,
    ( ~ spl4_3
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | spl4_46
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f587,f547,f594,f220,f216,f212,f113])).

fof(f212,plain,
    ( spl4_11
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f547,plain,
    ( spl4_42
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f587,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_42 ),
    inference(superposition,[],[f135,f549])).

fof(f549,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f547])).

fof(f135,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f94,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f94,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f584,plain,
    ( spl4_44
    | spl4_40
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_5
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f579,f529,f139,f216,f212,f525,f581])).

fof(f525,plain,
    ( spl4_40
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f579,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(trivial_inequality_removal,[],[f576])).

fof(f576,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(superposition,[],[f78,f50])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f575,plain,(
    ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f54,f527])).

fof(f527,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f525])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f552,plain,
    ( ~ spl4_3
    | ~ spl4_11
    | ~ spl4_12
    | spl4_42
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f551,f521,f547,f216,f212,f113])).

fof(f521,plain,
    ( spl4_39
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f551,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f542,f93])).

fof(f542,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_39 ),
    inference(superposition,[],[f73,f523])).

fof(f523,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f521])).

fof(f540,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f57,f531])).

fof(f531,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f529])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f532,plain,
    ( spl4_39
    | spl4_40
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_5
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f519,f529,f139,f216,f212,f525,f521])).

fof(f519,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f516])).

fof(f516,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f77,f50])).

fof(f480,plain,
    ( ~ spl4_12
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_5
    | spl4_33
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f477,f260,f470,f139,f431,f427,f216])).

fof(f477,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f86,f262])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f467,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f56,f47,f49,f58,f258,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f258,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_17
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f453,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl4_30 ),
    inference(subsumption_resolution,[],[f47,f433])).

fof(f433,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f431])).

fof(f451,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f49,f429])).

fof(f429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f427])).

fof(f263,plain,
    ( ~ spl4_17
    | spl4_18 ),
    inference(avatar_split_clause,[],[f253,f260,f256])).

fof(f253,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f242,f51])).

fof(f242,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f85,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f234,plain,
    ( ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl4_3
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f115,f56,f222,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f222,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f231,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f56,f218])).

fof(f218,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f229,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f52,f214])).

fof(f214,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f149,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f58,f141])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f128,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f75,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f124,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f75,f110])).

fof(f110,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f120,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f117,f113])).

fof(f101,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f111,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f100,f108,f104])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:18:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19331)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (19323)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (19320)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (19316)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (19315)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (19324)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (19319)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (19329)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (19337)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (19328)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (19331)Refutation not found, incomplete strategy% (19331)------------------------------
% 0.22/0.53  % (19331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19331)Memory used [KB]: 10746
% 0.22/0.53  % (19331)Time elapsed: 0.118 s
% 0.22/0.53  % (19331)------------------------------
% 0.22/0.53  % (19331)------------------------------
% 0.22/0.54  % (19318)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (19317)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (19336)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (19325)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (19342)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (19338)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (19334)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (19330)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (19344)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (19321)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (19341)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (19340)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (19326)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (19322)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (19333)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (19332)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (19339)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (19327)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.59  % (19335)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.59  % (19343)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.16/0.65  % (19345)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.66  % (19328)Refutation found. Thanks to Tanya!
% 2.16/0.66  % SZS status Theorem for theBenchmark
% 2.16/0.66  % SZS output start Proof for theBenchmark
% 2.16/0.66  fof(f2035,plain,(
% 2.16/0.66    $false),
% 2.16/0.66    inference(avatar_sat_refutation,[],[f111,f120,f124,f128,f149,f229,f231,f234,f263,f451,f453,f467,f480,f532,f540,f552,f575,f584,f597,f635,f803,f867,f874,f903,f967,f986,f1503,f1511,f1945,f1981,f2013])).
% 2.16/0.66  fof(f2013,plain,(
% 2.16/0.66    ~spl4_180),
% 2.16/0.66    inference(avatar_contradiction_clause,[],[f1982])).
% 2.16/0.66  fof(f1982,plain,(
% 2.16/0.66    $false | ~spl4_180),
% 2.16/0.66    inference(subsumption_resolution,[],[f55,f1980])).
% 2.16/0.66  fof(f1980,plain,(
% 2.16/0.66    sK3 = k2_funct_1(sK2) | ~spl4_180),
% 2.16/0.66    inference(avatar_component_clause,[],[f1978])).
% 2.16/0.66  fof(f1978,plain,(
% 2.16/0.66    spl4_180 <=> sK3 = k2_funct_1(sK2)),
% 2.16/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).
% 2.16/0.66  fof(f55,plain,(
% 2.16/0.66    sK3 != k2_funct_1(sK2)),
% 2.16/0.66    inference(cnf_transformation,[],[f23])).
% 2.16/0.66  fof(f23,plain,(
% 2.16/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.16/0.66    inference(flattening,[],[f22])).
% 2.16/0.66  fof(f22,plain,(
% 2.16/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.16/0.66    inference(ennf_transformation,[],[f21])).
% 2.16/0.66  fof(f21,negated_conjecture,(
% 2.16/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.16/0.66    inference(negated_conjecture,[],[f20])).
% 2.16/0.66  fof(f20,conjecture,(
% 2.16/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.16/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.16/0.66  fof(f1981,plain,(
% 2.16/0.66    ~spl4_1 | spl4_180 | ~spl4_65 | ~spl4_175),
% 2.16/0.66    inference(avatar_split_clause,[],[f1976,f1940,f800,f1978,f104])).
% 2.16/0.66  fof(f104,plain,(
% 2.16/0.66    spl4_1 <=> v1_relat_1(sK3)),
% 2.16/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.16/0.66  fof(f800,plain,(
% 2.16/0.66    spl4_65 <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.16/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 2.16/0.66  fof(f1940,plain,(
% 2.16/0.66    spl4_175 <=> sK1 = k1_relat_1(sK3)),
% 2.16/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_175])])).
% 2.16/0.66  fof(f1976,plain,(
% 2.16/0.66    sK3 = k2_funct_1(sK2) | ~v1_relat_1(sK3) | (~spl4_65 | ~spl4_175)),
% 2.16/0.66    inference(forward_demodulation,[],[f1964,f802])).
% 2.16/0.66  fof(f802,plain,(
% 2.16/0.66    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_65),
% 2.16/0.66    inference(avatar_component_clause,[],[f800])).
% 2.16/0.66  fof(f1964,plain,(
% 2.16/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | ~spl4_175),
% 2.16/0.66    inference(superposition,[],[f95,f1942])).
% 2.16/0.66  fof(f1942,plain,(
% 2.16/0.66    sK1 = k1_relat_1(sK3) | ~spl4_175),
% 2.16/0.66    inference(avatar_component_clause,[],[f1940])).
% 2.16/0.66  fof(f95,plain,(
% 2.16/0.66    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f66,f59])).
% 2.16/0.66  fof(f59,plain,(
% 2.16/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f16])).
% 2.16/0.67  fof(f16,axiom,(
% 2.16/0.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.16/0.67  fof(f66,plain,(
% 2.16/0.67    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f25])).
% 2.16/0.67  fof(f25,plain,(
% 2.16/0.67    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f5])).
% 2.16/0.67  fof(f5,axiom,(
% 2.16/0.67    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.16/0.67  fof(f1945,plain,(
% 2.16/0.67    ~spl4_1 | ~spl4_79 | ~spl4_30 | spl4_175 | ~spl4_80),
% 2.16/0.67    inference(avatar_split_clause,[],[f1944,f900,f1940,f431,f895,f104])).
% 2.16/0.67  fof(f895,plain,(
% 2.16/0.67    spl4_79 <=> v2_funct_1(sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 2.16/0.67  fof(f431,plain,(
% 2.16/0.67    spl4_30 <=> v1_funct_1(sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.16/0.67  fof(f900,plain,(
% 2.16/0.67    spl4_80 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 2.16/0.67  fof(f1944,plain,(
% 2.16/0.67    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_80),
% 2.16/0.67    inference(forward_demodulation,[],[f1923,f93])).
% 2.16/0.67  fof(f93,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.16/0.67    inference(definition_unfolding,[],[f63,f59])).
% 2.16/0.67  fof(f63,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f4])).
% 2.16/0.67  fof(f4,axiom,(
% 2.16/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.16/0.67  fof(f1923,plain,(
% 2.16/0.67    k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_80),
% 2.16/0.67    inference(superposition,[],[f73,f902])).
% 2.16/0.67  fof(f902,plain,(
% 2.16/0.67    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_80),
% 2.16/0.67    inference(avatar_component_clause,[],[f900])).
% 2.16/0.67  fof(f73,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f33])).
% 2.16/0.67  fof(f33,plain,(
% 2.16/0.67    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(flattening,[],[f32])).
% 2.16/0.67  fof(f32,plain,(
% 2.16/0.67    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.67    inference(ennf_transformation,[],[f10])).
% 2.16/0.67  fof(f10,axiom,(
% 2.16/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 2.16/0.67  fof(f1511,plain,(
% 2.16/0.67    spl4_141),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f1508])).
% 2.16/0.67  fof(f1508,plain,(
% 2.16/0.67    $false | spl4_141),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f90,f1502])).
% 2.16/0.67  fof(f1502,plain,(
% 2.16/0.67    ~v2_funct_1(k6_partfun1(sK0)) | spl4_141),
% 2.16/0.67    inference(avatar_component_clause,[],[f1500])).
% 2.16/0.67  fof(f1500,plain,(
% 2.16/0.67    spl4_141 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 2.16/0.67  fof(f90,plain,(
% 2.16/0.67    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.16/0.67    inference(definition_unfolding,[],[f62,f59])).
% 2.16/0.67  fof(f62,plain,(
% 2.16/0.67    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f8])).
% 2.16/0.67  fof(f8,axiom,(
% 2.16/0.67    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.16/0.67  fof(f1503,plain,(
% 2.16/0.67    ~spl4_74 | ~spl4_29 | ~spl4_30 | spl4_78 | spl4_79 | ~spl4_141 | ~spl4_18 | ~spl4_86),
% 2.16/0.67    inference(avatar_split_clause,[],[f1496,f984,f260,f1500,f895,f891,f431,f427,f864])).
% 2.16/0.67  fof(f864,plain,(
% 2.16/0.67    spl4_74 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 2.16/0.67  fof(f427,plain,(
% 2.16/0.67    spl4_29 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.16/0.67  fof(f891,plain,(
% 2.16/0.67    spl4_78 <=> k1_xboole_0 = sK0),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 2.16/0.67  fof(f260,plain,(
% 2.16/0.67    spl4_18 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.16/0.67  fof(f984,plain,(
% 2.16/0.67    spl4_86 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 2.16/0.67  fof(f1496,plain,(
% 2.16/0.67    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_18 | ~spl4_86)),
% 2.16/0.67    inference(superposition,[],[f985,f262])).
% 2.16/0.67  fof(f262,plain,(
% 2.16/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_18),
% 2.16/0.67    inference(avatar_component_clause,[],[f260])).
% 2.16/0.67  fof(f985,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_86),
% 2.16/0.67    inference(avatar_component_clause,[],[f984])).
% 2.16/0.67  fof(f986,plain,(
% 2.16/0.67    ~spl4_12 | spl4_86 | ~spl4_5 | ~spl4_41),
% 2.16/0.67    inference(avatar_split_clause,[],[f982,f529,f139,f984,f216])).
% 2.16/0.67  fof(f216,plain,(
% 2.16/0.67    spl4_12 <=> v1_funct_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.16/0.67  fof(f139,plain,(
% 2.16/0.67    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.16/0.67  fof(f529,plain,(
% 2.16/0.67    spl4_41 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.16/0.67  fof(f982,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.16/0.67    inference(trivial_inequality_removal,[],[f977])).
% 2.16/0.67  fof(f977,plain,(
% 2.16/0.67    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.16/0.67    inference(superposition,[],[f83,f50])).
% 2.16/0.67  fof(f50,plain,(
% 2.16/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f83,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f40])).
% 2.16/0.67  fof(f40,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.16/0.67    inference(flattening,[],[f39])).
% 2.16/0.67  fof(f39,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.16/0.67    inference(ennf_transformation,[],[f18])).
% 2.16/0.67  fof(f18,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.16/0.67  fof(f967,plain,(
% 2.16/0.67    ~spl4_78),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f944])).
% 2.16/0.67  fof(f944,plain,(
% 2.16/0.67    $false | ~spl4_78),
% 2.16/0.67    inference(subsumption_resolution,[],[f53,f893])).
% 2.16/0.67  fof(f893,plain,(
% 2.16/0.67    k1_xboole_0 = sK0 | ~spl4_78),
% 2.16/0.67    inference(avatar_component_clause,[],[f891])).
% 2.16/0.67  fof(f53,plain,(
% 2.16/0.67    k1_xboole_0 != sK0),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f903,plain,(
% 2.16/0.67    spl4_80 | spl4_78 | ~spl4_79 | ~spl4_30 | ~spl4_29 | ~spl4_74 | ~spl4_73),
% 2.16/0.67    inference(avatar_split_clause,[],[f879,f860,f864,f427,f431,f895,f891,f900])).
% 2.16/0.67  fof(f860,plain,(
% 2.16/0.67    spl4_73 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 2.16/0.67  fof(f879,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_73),
% 2.16/0.67    inference(trivial_inequality_removal,[],[f877])).
% 2.16/0.67  fof(f877,plain,(
% 2.16/0.67    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_73),
% 2.16/0.67    inference(superposition,[],[f77,f862])).
% 2.16/0.67  fof(f862,plain,(
% 2.16/0.67    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_73),
% 2.16/0.67    inference(avatar_component_clause,[],[f860])).
% 2.16/0.67  fof(f77,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f36])).
% 2.16/0.67  fof(f36,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.16/0.67    inference(flattening,[],[f35])).
% 2.16/0.67  fof(f35,plain,(
% 2.16/0.67    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.16/0.67    inference(ennf_transformation,[],[f19])).
% 2.16/0.67  fof(f19,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.16/0.67  fof(f874,plain,(
% 2.16/0.67    spl4_74),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f873])).
% 2.16/0.67  fof(f873,plain,(
% 2.16/0.67    $false | spl4_74),
% 2.16/0.67    inference(subsumption_resolution,[],[f48,f866])).
% 2.16/0.67  fof(f866,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,sK1,sK0) | spl4_74),
% 2.16/0.67    inference(avatar_component_clause,[],[f864])).
% 2.16/0.67  fof(f48,plain,(
% 2.16/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f867,plain,(
% 2.16/0.67    spl4_73 | ~spl4_30 | ~spl4_5 | ~spl4_41 | ~spl4_12 | ~spl4_29 | ~spl4_74),
% 2.16/0.67    inference(avatar_split_clause,[],[f855,f864,f427,f216,f529,f139,f431,f860])).
% 2.16/0.67  fof(f855,plain,(
% 2.16/0.67    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.16/0.67    inference(resolution,[],[f79,f51])).
% 2.16/0.67  fof(f51,plain,(
% 2.16/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f79,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.16/0.67    inference(cnf_transformation,[],[f38])).
% 2.16/0.67  fof(f38,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.16/0.67    inference(flattening,[],[f37])).
% 2.16/0.67  fof(f37,plain,(
% 2.16/0.67    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.16/0.67    inference(ennf_transformation,[],[f17])).
% 2.16/0.67  fof(f17,axiom,(
% 2.16/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.16/0.67  fof(f803,plain,(
% 2.16/0.67    ~spl4_1 | spl4_65 | ~spl4_33 | ~spl4_46 | ~spl4_51),
% 2.16/0.67    inference(avatar_split_clause,[],[f798,f633,f594,f470,f800,f104])).
% 2.16/0.67  fof(f470,plain,(
% 2.16/0.67    spl4_33 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.16/0.67  fof(f594,plain,(
% 2.16/0.67    spl4_46 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.16/0.67  fof(f633,plain,(
% 2.16/0.67    spl4_51 <=> ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(X0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.16/0.67  fof(f798,plain,(
% 2.16/0.67    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | (~spl4_33 | ~spl4_46 | ~spl4_51)),
% 2.16/0.67    inference(forward_demodulation,[],[f789,f596])).
% 2.16/0.67  fof(f596,plain,(
% 2.16/0.67    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_46),
% 2.16/0.67    inference(avatar_component_clause,[],[f594])).
% 2.16/0.67  fof(f789,plain,(
% 2.16/0.67    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | (~spl4_33 | ~spl4_51)),
% 2.16/0.67    inference(superposition,[],[f634,f472])).
% 2.16/0.67  fof(f472,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_33),
% 2.16/0.67    inference(avatar_component_clause,[],[f470])).
% 2.16/0.67  fof(f634,plain,(
% 2.16/0.67    ( ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(X0)) ) | ~spl4_51),
% 2.16/0.67    inference(avatar_component_clause,[],[f633])).
% 2.16/0.67  fof(f635,plain,(
% 2.16/0.67    ~spl4_13 | ~spl4_3 | spl4_51 | ~spl4_44),
% 2.16/0.67    inference(avatar_split_clause,[],[f617,f581,f633,f113,f220])).
% 2.16/0.67  fof(f220,plain,(
% 2.16/0.67    spl4_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.16/0.67  fof(f113,plain,(
% 2.16/0.67    spl4_3 <=> v1_relat_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.16/0.67  fof(f581,plain,(
% 2.16/0.67    spl4_44 <=> k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.16/0.67  fof(f617,plain,(
% 2.16/0.67    ( ! [X0] : (k5_relat_1(k6_partfun1(sK1),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl4_44),
% 2.16/0.67    inference(superposition,[],[f67,f583])).
% 2.16/0.67  fof(f583,plain,(
% 2.16/0.67    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) | ~spl4_44),
% 2.16/0.67    inference(avatar_component_clause,[],[f581])).
% 2.16/0.67  fof(f67,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f26])).
% 2.16/0.67  fof(f26,plain,(
% 2.16/0.67    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f3])).
% 2.16/0.67  fof(f3,axiom,(
% 2.16/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.16/0.67  fof(f597,plain,(
% 2.16/0.67    ~spl4_3 | ~spl4_11 | ~spl4_12 | ~spl4_13 | spl4_46 | ~spl4_42),
% 2.16/0.67    inference(avatar_split_clause,[],[f587,f547,f594,f220,f216,f212,f113])).
% 2.16/0.67  fof(f212,plain,(
% 2.16/0.67    spl4_11 <=> v2_funct_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.16/0.67  fof(f547,plain,(
% 2.16/0.67    spl4_42 <=> sK0 = k1_relat_1(sK2)),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.16/0.67  fof(f587,plain,(
% 2.16/0.67    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_42),
% 2.16/0.67    inference(superposition,[],[f135,f549])).
% 2.16/0.67  fof(f549,plain,(
% 2.16/0.67    sK0 = k1_relat_1(sK2) | ~spl4_42),
% 2.16/0.67    inference(avatar_component_clause,[],[f547])).
% 2.16/0.67  fof(f135,plain,(
% 2.16/0.67    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(superposition,[],[f94,f72])).
% 2.16/0.67  fof(f72,plain,(
% 2.16/0.67    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f31])).
% 2.16/0.67  fof(f31,plain,(
% 2.16/0.67    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(flattening,[],[f30])).
% 2.16/0.67  fof(f30,plain,(
% 2.16/0.67    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.67    inference(ennf_transformation,[],[f9])).
% 2.16/0.67  fof(f9,axiom,(
% 2.16/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.16/0.67  fof(f94,plain,(
% 2.16/0.67    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(definition_unfolding,[],[f65,f59])).
% 2.16/0.67  fof(f65,plain,(
% 2.16/0.67    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.16/0.67    inference(cnf_transformation,[],[f24])).
% 2.16/0.67  fof(f24,plain,(
% 2.16/0.67    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f6])).
% 2.16/0.67  fof(f6,axiom,(
% 2.16/0.67    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.16/0.67  fof(f584,plain,(
% 2.16/0.67    spl4_44 | spl4_40 | ~spl4_11 | ~spl4_12 | ~spl4_5 | ~spl4_41),
% 2.16/0.67    inference(avatar_split_clause,[],[f579,f529,f139,f216,f212,f525,f581])).
% 2.16/0.67  fof(f525,plain,(
% 2.16/0.67    spl4_40 <=> k1_xboole_0 = sK1),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.16/0.67  fof(f579,plain,(
% 2.16/0.67    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.16/0.67    inference(trivial_inequality_removal,[],[f576])).
% 2.16/0.67  fof(f576,plain,(
% 2.16/0.67    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.16/0.67    inference(superposition,[],[f78,f50])).
% 2.16/0.67  fof(f78,plain,(
% 2.16/0.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f36])).
% 2.16/0.67  fof(f575,plain,(
% 2.16/0.67    ~spl4_40),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f557])).
% 2.16/0.67  fof(f557,plain,(
% 2.16/0.67    $false | ~spl4_40),
% 2.16/0.67    inference(subsumption_resolution,[],[f54,f527])).
% 2.16/0.67  fof(f527,plain,(
% 2.16/0.67    k1_xboole_0 = sK1 | ~spl4_40),
% 2.16/0.67    inference(avatar_component_clause,[],[f525])).
% 2.16/0.67  fof(f54,plain,(
% 2.16/0.67    k1_xboole_0 != sK1),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f552,plain,(
% 2.16/0.67    ~spl4_3 | ~spl4_11 | ~spl4_12 | spl4_42 | ~spl4_39),
% 2.16/0.67    inference(avatar_split_clause,[],[f551,f521,f547,f216,f212,f113])).
% 2.16/0.67  fof(f521,plain,(
% 2.16/0.67    spl4_39 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.16/0.67  fof(f551,plain,(
% 2.16/0.67    sK0 = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_39),
% 2.16/0.67    inference(forward_demodulation,[],[f542,f93])).
% 2.16/0.67  fof(f542,plain,(
% 2.16/0.67    k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_39),
% 2.16/0.67    inference(superposition,[],[f73,f523])).
% 2.16/0.67  fof(f523,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_39),
% 2.16/0.67    inference(avatar_component_clause,[],[f521])).
% 2.16/0.67  fof(f540,plain,(
% 2.16/0.67    spl4_41),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f539])).
% 2.16/0.67  fof(f539,plain,(
% 2.16/0.67    $false | spl4_41),
% 2.16/0.67    inference(subsumption_resolution,[],[f57,f531])).
% 2.16/0.67  fof(f531,plain,(
% 2.16/0.67    ~v1_funct_2(sK2,sK0,sK1) | spl4_41),
% 2.16/0.67    inference(avatar_component_clause,[],[f529])).
% 2.16/0.67  fof(f57,plain,(
% 2.16/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f532,plain,(
% 2.16/0.67    spl4_39 | spl4_40 | ~spl4_11 | ~spl4_12 | ~spl4_5 | ~spl4_41),
% 2.16/0.67    inference(avatar_split_clause,[],[f519,f529,f139,f216,f212,f525,f521])).
% 2.16/0.67  fof(f519,plain,(
% 2.16/0.67    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.16/0.67    inference(trivial_inequality_removal,[],[f516])).
% 2.16/0.67  fof(f516,plain,(
% 2.16/0.67    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.16/0.67    inference(superposition,[],[f77,f50])).
% 2.16/0.67  fof(f480,plain,(
% 2.16/0.67    ~spl4_12 | ~spl4_29 | ~spl4_30 | ~spl4_5 | spl4_33 | ~spl4_18),
% 2.16/0.67    inference(avatar_split_clause,[],[f477,f260,f470,f139,f431,f427,f216])).
% 2.16/0.67  fof(f477,plain,(
% 2.16/0.67    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_18),
% 2.16/0.67    inference(superposition,[],[f86,f262])).
% 2.16/0.67  fof(f86,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f44])).
% 2.16/0.67  fof(f44,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.67    inference(flattening,[],[f43])).
% 2.16/0.67  fof(f43,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.67    inference(ennf_transformation,[],[f15])).
% 2.16/0.67  fof(f15,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.16/0.67  fof(f467,plain,(
% 2.16/0.67    spl4_17),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f458])).
% 2.16/0.67  fof(f458,plain,(
% 2.16/0.67    $false | spl4_17),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f56,f47,f49,f58,f258,f88])).
% 2.16/0.67  fof(f88,plain,(
% 2.16/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f46])).
% 2.16/0.67  fof(f46,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.16/0.67    inference(flattening,[],[f45])).
% 2.16/0.67  fof(f45,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.16/0.67    inference(ennf_transformation,[],[f14])).
% 2.16/0.67  fof(f14,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.16/0.67  fof(f258,plain,(
% 2.16/0.67    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_17),
% 2.16/0.67    inference(avatar_component_clause,[],[f256])).
% 2.16/0.67  fof(f256,plain,(
% 2.16/0.67    spl4_17 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.16/0.67  fof(f58,plain,(
% 2.16/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f49,plain,(
% 2.16/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f47,plain,(
% 2.16/0.67    v1_funct_1(sK3)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f56,plain,(
% 2.16/0.67    v1_funct_1(sK2)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f453,plain,(
% 2.16/0.67    spl4_30),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f452])).
% 2.16/0.67  fof(f452,plain,(
% 2.16/0.67    $false | spl4_30),
% 2.16/0.67    inference(subsumption_resolution,[],[f47,f433])).
% 2.16/0.67  fof(f433,plain,(
% 2.16/0.67    ~v1_funct_1(sK3) | spl4_30),
% 2.16/0.67    inference(avatar_component_clause,[],[f431])).
% 2.16/0.67  fof(f451,plain,(
% 2.16/0.67    spl4_29),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f450])).
% 2.16/0.67  fof(f450,plain,(
% 2.16/0.67    $false | spl4_29),
% 2.16/0.67    inference(subsumption_resolution,[],[f49,f429])).
% 2.16/0.67  fof(f429,plain,(
% 2.16/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_29),
% 2.16/0.67    inference(avatar_component_clause,[],[f427])).
% 2.16/0.67  fof(f263,plain,(
% 2.16/0.67    ~spl4_17 | spl4_18),
% 2.16/0.67    inference(avatar_split_clause,[],[f253,f260,f256])).
% 2.16/0.67  fof(f253,plain,(
% 2.16/0.67    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.16/0.67    inference(resolution,[],[f242,f51])).
% 2.16/0.67  fof(f242,plain,(
% 2.16/0.67    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.16/0.67    inference(resolution,[],[f85,f89])).
% 2.16/0.67  fof(f89,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.16/0.67    inference(definition_unfolding,[],[f60,f59])).
% 2.16/0.67  fof(f60,plain,(
% 2.16/0.67    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f13])).
% 2.16/0.67  fof(f13,axiom,(
% 2.16/0.67    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.16/0.67  fof(f85,plain,(
% 2.16/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f42])).
% 2.16/0.67  fof(f42,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.67    inference(flattening,[],[f41])).
% 2.16/0.67  fof(f41,plain,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.16/0.67    inference(ennf_transformation,[],[f12])).
% 2.16/0.67  fof(f12,axiom,(
% 2.16/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.16/0.67  fof(f234,plain,(
% 2.16/0.67    ~spl4_3 | spl4_13),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f232])).
% 2.16/0.67  fof(f232,plain,(
% 2.16/0.67    $false | (~spl4_3 | spl4_13)),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f115,f56,f222,f69])).
% 2.16/0.67  fof(f69,plain,(
% 2.16/0.67    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f29])).
% 2.16/0.67  fof(f29,plain,(
% 2.16/0.67    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(flattening,[],[f28])).
% 2.16/0.67  fof(f28,plain,(
% 2.16/0.67    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/0.67    inference(ennf_transformation,[],[f7])).
% 2.16/0.67  fof(f7,axiom,(
% 2.16/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.16/0.67  fof(f222,plain,(
% 2.16/0.67    ~v1_relat_1(k2_funct_1(sK2)) | spl4_13),
% 2.16/0.67    inference(avatar_component_clause,[],[f220])).
% 2.16/0.67  fof(f115,plain,(
% 2.16/0.67    v1_relat_1(sK2) | ~spl4_3),
% 2.16/0.67    inference(avatar_component_clause,[],[f113])).
% 2.16/0.67  fof(f231,plain,(
% 2.16/0.67    spl4_12),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f230])).
% 2.16/0.67  fof(f230,plain,(
% 2.16/0.67    $false | spl4_12),
% 2.16/0.67    inference(subsumption_resolution,[],[f56,f218])).
% 2.16/0.67  fof(f218,plain,(
% 2.16/0.67    ~v1_funct_1(sK2) | spl4_12),
% 2.16/0.67    inference(avatar_component_clause,[],[f216])).
% 2.16/0.67  fof(f229,plain,(
% 2.16/0.67    spl4_11),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f228])).
% 2.16/0.67  fof(f228,plain,(
% 2.16/0.67    $false | spl4_11),
% 2.16/0.67    inference(subsumption_resolution,[],[f52,f214])).
% 2.16/0.67  fof(f214,plain,(
% 2.16/0.67    ~v2_funct_1(sK2) | spl4_11),
% 2.16/0.67    inference(avatar_component_clause,[],[f212])).
% 2.16/0.67  fof(f52,plain,(
% 2.16/0.67    v2_funct_1(sK2)),
% 2.16/0.67    inference(cnf_transformation,[],[f23])).
% 2.16/0.67  fof(f149,plain,(
% 2.16/0.67    spl4_5),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f148])).
% 2.16/0.67  fof(f148,plain,(
% 2.16/0.67    $false | spl4_5),
% 2.16/0.67    inference(subsumption_resolution,[],[f58,f141])).
% 2.16/0.67  fof(f141,plain,(
% 2.16/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.16/0.67    inference(avatar_component_clause,[],[f139])).
% 2.16/0.67  fof(f128,plain,(
% 2.16/0.67    spl4_4),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f125])).
% 2.16/0.67  fof(f125,plain,(
% 2.16/0.67    $false | spl4_4),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f75,f119])).
% 2.16/0.67  fof(f119,plain,(
% 2.16/0.67    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.16/0.67    inference(avatar_component_clause,[],[f117])).
% 2.16/0.67  fof(f117,plain,(
% 2.16/0.67    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.16/0.67  fof(f75,plain,(
% 2.16/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.16/0.67    inference(cnf_transformation,[],[f2])).
% 2.16/0.67  fof(f2,axiom,(
% 2.16/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.16/0.67  fof(f124,plain,(
% 2.16/0.67    spl4_2),
% 2.16/0.67    inference(avatar_contradiction_clause,[],[f121])).
% 2.16/0.67  fof(f121,plain,(
% 2.16/0.67    $false | spl4_2),
% 2.16/0.67    inference(unit_resulting_resolution,[],[f75,f110])).
% 2.16/0.67  fof(f110,plain,(
% 2.16/0.67    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.16/0.67    inference(avatar_component_clause,[],[f108])).
% 2.16/0.67  fof(f108,plain,(
% 2.16/0.67    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.16/0.67  fof(f120,plain,(
% 2.16/0.67    spl4_3 | ~spl4_4),
% 2.16/0.67    inference(avatar_split_clause,[],[f101,f117,f113])).
% 2.16/0.67  fof(f101,plain,(
% 2.16/0.67    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.16/0.67    inference(resolution,[],[f68,f58])).
% 2.16/0.67  fof(f68,plain,(
% 2.16/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.16/0.67    inference(cnf_transformation,[],[f27])).
% 2.16/0.67  fof(f27,plain,(
% 2.16/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.16/0.67    inference(ennf_transformation,[],[f1])).
% 2.16/0.67  fof(f1,axiom,(
% 2.16/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.16/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.16/0.67  fof(f111,plain,(
% 2.16/0.67    spl4_1 | ~spl4_2),
% 2.16/0.67    inference(avatar_split_clause,[],[f100,f108,f104])).
% 2.16/0.67  fof(f100,plain,(
% 2.16/0.67    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.16/0.67    inference(resolution,[],[f68,f49])).
% 2.16/0.67  % SZS output end Proof for theBenchmark
% 2.16/0.67  % (19328)------------------------------
% 2.16/0.67  % (19328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.67  % (19328)Termination reason: Refutation
% 2.16/0.67  
% 2.16/0.67  % (19328)Memory used [KB]: 8059
% 2.16/0.67  % (19328)Time elapsed: 0.243 s
% 2.16/0.67  % (19328)------------------------------
% 2.16/0.67  % (19328)------------------------------
% 2.16/0.67  % (19314)Success in time 0.3 s
%------------------------------------------------------------------------------
