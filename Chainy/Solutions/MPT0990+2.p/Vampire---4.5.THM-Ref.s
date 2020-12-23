%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0990+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 24.28s
% Output     : Refutation 24.59s
% Verified   : 
% Statistics : Number of formulae       :  336 (1133 expanded)
%              Number of leaves         :   53 ( 389 expanded)
%              Depth                    :   25
%              Number of atoms          : 1703 (5748 expanded)
%              Number of equality atoms :  303 (1397 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26956,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2741,f2746,f2751,f2890,f2895,f2900,f2905,f2910,f3264,f3269,f3274,f3504,f3571,f3576,f3679,f3879,f3894,f3904,f3923,f3992,f5833,f8745,f12545,f13224,f13306,f13316,f13730,f20341,f20581,f21263,f23617])).

fof(f23617,plain,
    ( ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | spl103_93
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_113
    | ~ spl103_174 ),
    inference(avatar_contradiction_clause,[],[f23616])).

fof(f23616,plain,
    ( $false
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | spl103_93
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_113
    | ~ spl103_174 ),
    inference(subsumption_resolution,[],[f23615,f12544])).

fof(f12544,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl103_93 ),
    inference(avatar_component_clause,[],[f12542])).

fof(f12542,plain,
    ( spl103_93
  <=> sK3 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_93])])).

fof(f23615,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_113
    | ~ spl103_174 ),
    inference(forward_demodulation,[],[f23614,f23516])).

fof(f23516,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_2
    | ~ spl103_15
    | ~ spl103_36 ),
    inference(subsumption_resolution,[],[f9944,f3575])).

fof(f3575,plain,
    ( v1_relat_1(sK3)
    | ~ spl103_15 ),
    inference(avatar_component_clause,[],[f3573])).

fof(f3573,plain,
    ( spl103_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_15])])).

fof(f9944,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl103_2
    | ~ spl103_36 ),
    inference(subsumption_resolution,[],[f8205,f2745])).

fof(f2745,plain,
    ( v1_funct_1(sK3)
    | ~ spl103_2 ),
    inference(avatar_component_clause,[],[f2743])).

fof(f2743,plain,
    ( spl103_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_2])])).

fof(f8205,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl103_36 ),
    inference(resolution,[],[f4300,f2134])).

fof(f2134,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1557])).

fof(f1557,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1556])).

fof(f1556,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1036])).

fof(f1036,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f4300,plain,
    ( v2_funct_1(sK3)
    | ~ spl103_36 ),
    inference(avatar_component_clause,[],[f4299])).

fof(f4299,plain,
    ( spl103_36
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_36])])).

fof(f23614,plain,
    ( k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_113
    | ~ spl103_174 ),
    inference(subsumption_resolution,[],[f23613,f22675])).

fof(f22675,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_113 ),
    inference(forward_demodulation,[],[f22674,f4185])).

fof(f4185,plain,
    ( sK1 = k1_relat_1(k6_partfun1(sK1))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4137,f4182])).

fof(f4182,plain,
    ( sK1 = k2_relat_1(k6_partfun1(sK1))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4114,f4181])).

fof(f4181,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_21
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4180,f3678])).

fof(f3678,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl103_21 ),
    inference(avatar_component_clause,[],[f3676])).

fof(f3676,plain,
    ( spl103_21
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_21])])).

fof(f4180,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4088,f4090])).

fof(f4090,plain,
    ( sK2 = k4_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4069,f3570])).

fof(f3570,plain,
    ( v1_relat_1(sK2)
    | ~ spl103_14 ),
    inference(avatar_component_clause,[],[f3568])).

fof(f3568,plain,
    ( spl103_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_14])])).

fof(f4069,plain,
    ( sK2 = k4_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f2871,f4068])).

fof(f4068,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4067,f3878])).

fof(f3878,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_25 ),
    inference(avatar_component_clause,[],[f3876])).

fof(f3876,plain,
    ( spl103_25
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_25])])).

fof(f4067,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4011,f3278])).

fof(f3278,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl103_12 ),
    inference(avatar_component_clause,[],[f3276])).

fof(f3276,plain,
    ( spl103_12
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_12])])).

fof(f4011,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2135])).

fof(f2135,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1558])).

fof(f1558,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f3991,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(avatar_component_clause,[],[f3989])).

fof(f3989,plain,
    ( spl103_29
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_29])])).

fof(f2871,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(subsumption_resolution,[],[f2833,f2740])).

fof(f2740,plain,
    ( v1_funct_1(sK2)
    | ~ spl103_1 ),
    inference(avatar_component_clause,[],[f2738])).

fof(f2738,plain,
    ( spl103_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_1])])).

fof(f2833,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl103_3 ),
    inference(resolution,[],[f2750,f2134])).

fof(f2750,plain,
    ( v2_funct_1(sK2)
    | ~ spl103_3 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f2748,plain,
    ( spl103_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_3])])).

fof(f4088,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k4_relat_1(k2_funct_1(sK2)))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4064,f4068])).

fof(f4064,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4063,f3878])).

fof(f4063,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4009,f3278])).

fof(f4009,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2133])).

fof(f2133,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f1555,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1554])).

fof(f1554,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1026])).

fof(f1026,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f4114,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4113,f3017])).

fof(f3017,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3016,f2740])).

fof(f3016,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3015,f2075])).

fof(f2075,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1854])).

fof(f1854,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1521,f1853,f1852])).

fof(f1852,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1853,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1521,plain,(
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
    inference(flattening,[],[f1520])).

fof(f1520,plain,(
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
    inference(ennf_transformation,[],[f1511])).

fof(f1511,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1510])).

fof(f1510,conjecture,(
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

fof(f3015,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3014,f2079])).

fof(f2079,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1854])).

fof(f3014,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3013,f2750])).

fof(f3013,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f2943,f2894])).

fof(f2894,plain,
    ( k1_xboole_0 != sK1
    | spl103_5 ),
    inference(avatar_component_clause,[],[f2892])).

fof(f2892,plain,
    ( spl103_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_5])])).

fof(f2943,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl103_6 ),
    inference(resolution,[],[f2899,f2401])).

fof(f2401,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1710])).

fof(f1710,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1709])).

fof(f1709,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1509])).

fof(f1509,axiom,(
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

fof(f2899,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl103_6 ),
    inference(avatar_component_clause,[],[f2897])).

fof(f2897,plain,
    ( spl103_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_6])])).

fof(f4113,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4084,f4090])).

fof(f4084,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),k4_relat_1(k2_funct_1(sK2))))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4056,f4068])).

fof(f4056,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4055,f3878])).

fof(f4055,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4005,f3278])).

fof(f4005,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2129])).

fof(f2129,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1551])).

fof(f1551,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1550])).

fof(f1550,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1029])).

fof(f1029,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f4137,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4111,f4114])).

fof(f4111,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4110,f3017])).

fof(f4110,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4083,f4090])).

fof(f4083,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),k4_relat_1(k2_funct_1(sK2))))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4054,f4068])).

fof(f4054,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4053,f3878])).

fof(f4053,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4004,f3278])).

fof(f4004,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2128])).

fof(f2128,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1551])).

fof(f22674,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(sK1))
    | ~ spl103_2
    | ~ spl103_15
    | ~ spl103_36
    | ~ spl103_113 ),
    inference(forward_demodulation,[],[f22673,f13729])).

fof(f13729,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl103_113 ),
    inference(avatar_component_clause,[],[f13727])).

fof(f13727,plain,
    ( spl103_113
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_113])])).

fof(f22673,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ spl103_2
    | ~ spl103_15
    | ~ spl103_36 ),
    inference(subsumption_resolution,[],[f10019,f3575])).

fof(f10019,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl103_2
    | ~ spl103_36 ),
    inference(subsumption_resolution,[],[f8199,f2745])).

fof(f8199,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl103_36 ),
    inference(resolution,[],[f4300,f2128])).

fof(f23613,plain,
    ( sK1 != k1_relat_1(sK3)
    | k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_174 ),
    inference(forward_demodulation,[],[f23612,f23516])).

fof(f23612,plain,
    ( sK1 != k1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103
    | ~ spl103_174 ),
    inference(subsumption_resolution,[],[f23565,f20340])).

fof(f20340,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl103_174 ),
    inference(avatar_component_clause,[],[f20338])).

fof(f20338,plain,
    ( spl103_174
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_174])])).

fof(f23565,plain,
    ( k6_partfun1(sK0) != k5_relat_1(sK2,sK3)
    | sK1 != k1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_15
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_36
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103 ),
    inference(backward_demodulation,[],[f20160,f23516])).

fof(f20160,plain,
    ( k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(k2_funct_1(sK3)))
    | sK1 != k1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_67
    | ~ spl103_101
    | ~ spl103_103 ),
    inference(subsumption_resolution,[],[f20118,f13223])).

fof(f13223,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ spl103_101 ),
    inference(avatar_component_clause,[],[f13221])).

fof(f13221,plain,
    ( spl103_101
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_101])])).

fof(f20118,plain,
    ( k6_partfun1(sK0) != k5_relat_1(sK2,k2_funct_1(k2_funct_1(sK3)))
    | sK1 != k1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | k4_relat_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_67
    | ~ spl103_103 ),
    inference(resolution,[],[f13305,f8811])).

fof(f8811,plain,
    ( ! [X23] :
        ( ~ v1_funct_1(X23)
        | k6_partfun1(sK0) != k5_relat_1(sK2,X23)
        | sK1 != k1_relat_1(X23)
        | k4_relat_1(sK2) = X23
        | ~ v1_relat_1(X23) )
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29
    | ~ spl103_67 ),
    inference(backward_demodulation,[],[f4256,f8744])).

fof(f8744,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl103_67 ),
    inference(avatar_component_clause,[],[f8742])).

fof(f8742,plain,
    ( spl103_67
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_67])])).

fof(f4256,plain,
    ( ! [X23] :
        ( k6_partfun1(sK0) != k5_relat_1(sK2,X23)
        | sK1 != k1_relat_1(X23)
        | k2_funct_1(sK2) = X23
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X23) )
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4255,f3570])).

fof(f4255,plain,
    ( ! [X23] :
        ( k6_partfun1(sK0) != k5_relat_1(sK2,X23)
        | sK1 != k1_relat_1(X23)
        | k2_funct_1(sK2) = X23
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(sK2) )
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f3365,f4252])).

fof(f4252,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4251,f3009])).

fof(f3009,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3008,f2740])).

fof(f3008,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3007,f2075])).

fof(f3007,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3006,f2079])).

fof(f3006,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl103_3
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f3005,f2750])).

fof(f3005,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl103_5
    | ~ spl103_6 ),
    inference(subsumption_resolution,[],[f2942,f2894])).

fof(f2942,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl103_6 ),
    inference(resolution,[],[f2899,f2400])).

fof(f2400,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1710])).

fof(f4251,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4250,f4091])).

fof(f4091,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4068,f4090])).

fof(f4250,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4249,f4155])).

fof(f4155,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_12
    | ~ spl103_14
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(forward_demodulation,[],[f4087,f4090])).

fof(f4087,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k4_relat_1(k2_funct_1(sK2)))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(backward_demodulation,[],[f4062,f4068])).

fof(f4062,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4061,f3878])).

fof(f4061,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4008,f3278])).

fof(f4008,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2132])).

fof(f2132,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f4249,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl103_12
    | ~ spl103_25
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4248,f3878])).

fof(f4248,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_12
    | ~ spl103_29 ),
    inference(subsumption_resolution,[],[f4028,f3278])).

fof(f4028,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl103_29 ),
    inference(resolution,[],[f3991,f2645])).

fof(f2645,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2127,f2404])).

fof(f2404,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1487])).

fof(f1487,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f2127,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1549])).

fof(f1549,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1548])).

fof(f1548,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1032])).

fof(f1032,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f3365,plain,
    ( ! [X23] :
        ( sK1 != k1_relat_1(X23)
        | k5_relat_1(sK2,X23) != k6_partfun1(k1_relat_1(sK2))
        | k2_funct_1(sK2) = X23
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(sK2) )
    | ~ spl103_1
    | ~ spl103_3
    | ~ spl103_9
    | ~ spl103_11 ),
    inference(backward_demodulation,[],[f2882,f3350])).

fof(f3350,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl103_9
    | ~ spl103_11 ),
    inference(forward_demodulation,[],[f3295,f3273])).

fof(f3273,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl103_11 ),
    inference(avatar_component_clause,[],[f3271])).

fof(f3271,plain,
    ( spl103_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_11])])).

fof(f3295,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl103_9 ),
    inference(resolution,[],[f3263,f2442])).

fof(f2442,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1740])).

fof(f1740,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f3263,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl103_9 ),
    inference(avatar_component_clause,[],[f3261])).

fof(f3261,plain,
    ( spl103_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_9])])).

fof(f2882,plain,
    ( ! [X23] :
        ( k5_relat_1(sK2,X23) != k6_partfun1(k1_relat_1(sK2))
        | k2_relat_1(sK2) != k1_relat_1(X23)
        | k2_funct_1(sK2) = X23
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(sK2) )
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(subsumption_resolution,[],[f2849,f2740])).

fof(f2849,plain,
    ( ! [X23] :
        ( k5_relat_1(sK2,X23) != k6_partfun1(k1_relat_1(sK2))
        | k2_relat_1(sK2) != k1_relat_1(X23)
        | k2_funct_1(sK2) = X23
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl103_3 ),
    inference(resolution,[],[f2750,f2643])).

fof(f2643,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2104,f2404])).

fof(f2104,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1537])).

fof(f1537,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1536])).

fof(f1536,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1034])).

fof(f1034,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f13305,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ spl103_103 ),
    inference(avatar_component_clause,[],[f13303])).

fof(f13303,plain,
    ( spl103_103
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_103])])).

fof(f21263,plain,
    ( ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_10
    | ~ spl103_21
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105
    | ~ spl103_174 ),
    inference(avatar_contradiction_clause,[],[f21262])).

fof(f21262,plain,
    ( $false
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_10
    | ~ spl103_21
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105
    | ~ spl103_174 ),
    inference(subsumption_resolution,[],[f21261,f2652])).

fof(f2652,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f2360,f2404])).

fof(f2360,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1023])).

fof(f1023,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f21261,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_10
    | ~ spl103_21
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105
    | ~ spl103_174 ),
    inference(forward_demodulation,[],[f21260,f20606])).

fof(f20606,plain,
    ( k6_partfun1(sK0) = k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_10
    | ~ spl103_105
    | ~ spl103_174 ),
    inference(backward_demodulation,[],[f20222,f20340])).

fof(f20222,plain,
    ( k5_relat_1(sK2,sK3) = k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_10
    | ~ spl103_105 ),
    inference(subsumption_resolution,[],[f20192,f2740])).

fof(f20192,plain,
    ( k5_relat_1(sK2,sK3) = k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | ~ spl103_10
    | ~ spl103_105 ),
    inference(resolution,[],[f3457,f13315])).

fof(f13315,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl103_105 ),
    inference(avatar_component_clause,[],[f13313])).

fof(f13313,plain,
    ( spl103_105
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_105])])).

fof(f3457,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | k5_relat_1(X12,sK3) = k1_partfun1(X13,X14,sK1,sK0,X12,sK3)
        | ~ v1_funct_1(X12) )
    | ~ spl103_2
    | ~ spl103_10 ),
    inference(subsumption_resolution,[],[f3400,f2745])).

fof(f3400,plain,
    ( ! [X14,X12,X13] :
        ( k5_relat_1(X12,sK3) = k1_partfun1(X13,X14,sK1,sK0,X12,sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X12) )
    | ~ spl103_10 ),
    inference(resolution,[],[f3268,f2407])).

fof(f2407,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f1714])).

fof(f1714,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f1713])).

fof(f1713,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1486])).

fof(f1486,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f3268,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl103_10 ),
    inference(avatar_component_clause,[],[f3266])).

fof(f3266,plain,
    ( spl103_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_10])])).

fof(f21260,plain,
    ( ~ v2_funct_1(k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3))
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_21
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105 ),
    inference(subsumption_resolution,[],[f21259,f2740])).

fof(f21259,plain,
    ( ~ v2_funct_1(k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_21
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105 ),
    inference(subsumption_resolution,[],[f21258,f13567])).

fof(f13567,plain,
    ( sK1 = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl103_21
    | ~ spl103_105 ),
    inference(forward_demodulation,[],[f13513,f3678])).

fof(f13513,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ spl103_105 ),
    inference(resolution,[],[f13315,f2442])).

fof(f21258,plain,
    ( ~ v2_funct_1(k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | spl103_36
    | ~ spl103_57
    | ~ spl103_105 ),
    inference(subsumption_resolution,[],[f21246,f13315])).

fof(f21246,plain,
    ( ~ v2_funct_1(k1_partfun1(k1_relat_1(sK2),sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | sK1 != k2_relset_1(k1_relat_1(sK2),sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | spl103_36
    | ~ spl103_57 ),
    inference(resolution,[],[f16224,f5832])).

fof(f5832,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl103_57 ),
    inference(avatar_component_clause,[],[f5830])).

fof(f5830,plain,
    ( spl103_57
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_57])])).

fof(f16224,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_2(X15,X14,sK1)
        | ~ v2_funct_1(k1_partfun1(X14,sK1,sK1,sK0,X15,sK3))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,sK1)))
        | sK1 != k2_relset_1(X14,sK1,X15)
        | ~ v1_funct_1(X15) )
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | spl103_36 ),
    inference(subsumption_resolution,[],[f3222,f4301])).

fof(f4301,plain,
    ( ~ v2_funct_1(sK3)
    | spl103_36 ),
    inference(avatar_component_clause,[],[f4299])).

fof(f3222,plain,
    ( ! [X14,X15] :
        ( sK1 != k2_relset_1(X14,sK1,X15)
        | ~ v2_funct_1(k1_partfun1(X14,sK1,sK1,sK0,X15,sK3))
        | v2_funct_1(sK3)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,sK1)))
        | ~ v1_funct_2(X15,X14,sK1)
        | ~ v1_funct_1(X15) )
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3221,f2745])).

fof(f3221,plain,
    ( ! [X14,X15] :
        ( sK1 != k2_relset_1(X14,sK1,X15)
        | ~ v2_funct_1(k1_partfun1(X14,sK1,sK1,sK0,X15,sK3))
        | v2_funct_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,sK1)))
        | ~ v1_funct_2(X15,X14,sK1)
        | ~ v1_funct_1(X15) )
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3220,f2078])).

fof(f2078,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f1854])).

fof(f3220,plain,
    ( ! [X14,X15] :
        ( sK1 != k2_relset_1(X14,sK1,X15)
        | ~ v2_funct_1(k1_partfun1(X14,sK1,sK1,sK0,X15,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | v2_funct_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,sK1)))
        | ~ v1_funct_2(X15,X14,sK1)
        | ~ v1_funct_1(X15) )
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3093,f2889])).

fof(f2889,plain,
    ( k1_xboole_0 != sK0
    | spl103_4 ),
    inference(avatar_component_clause,[],[f2887])).

fof(f2887,plain,
    ( spl103_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_4])])).

fof(f3093,plain,
    ( ! [X14,X15] :
        ( k1_xboole_0 = sK0
        | sK1 != k2_relset_1(X14,sK1,X15)
        | ~ v2_funct_1(k1_partfun1(X14,sK1,sK1,sK0,X15,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | v2_funct_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,sK1)))
        | ~ v1_funct_2(X15,X14,sK1)
        | ~ v1_funct_1(X15) )
    | ~ spl103_7 ),
    inference(resolution,[],[f2904,f2411])).

fof(f2411,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f1718,plain,(
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
    inference(flattening,[],[f1717])).

fof(f1717,plain,(
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
    inference(ennf_transformation,[],[f1504])).

fof(f1504,axiom,(
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

fof(f2904,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl103_7 ),
    inference(avatar_component_clause,[],[f2902])).

fof(f2902,plain,
    ( spl103_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_7])])).

fof(f20581,plain,
    ( ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10
    | spl103_173 ),
    inference(avatar_contradiction_clause,[],[f20580])).

fof(f20580,plain,
    ( $false
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10
    | spl103_173 ),
    inference(subsumption_resolution,[],[f20579,f20336])).

fof(f20336,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl103_173 ),
    inference(avatar_component_clause,[],[f20334])).

fof(f20334,plain,
    ( spl103_173
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_173])])).

fof(f20579,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10 ),
    inference(forward_demodulation,[],[f20578,f20211])).

fof(f20211,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10 ),
    inference(subsumption_resolution,[],[f20191,f2740])).

fof(f20191,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10 ),
    inference(resolution,[],[f3457,f3263])).

fof(f20578,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10 ),
    inference(subsumption_resolution,[],[f20560,f2740])).

fof(f20560,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10 ),
    inference(resolution,[],[f3456,f3263])).

fof(f3456,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | m1_subset_1(k1_partfun1(X9,X10,sK1,sK0,X11,sK3),k1_zfmisc_1(k2_zfmisc_1(X9,sK0)))
        | ~ v1_funct_1(X11) )
    | ~ spl103_2
    | ~ spl103_10 ),
    inference(subsumption_resolution,[],[f3399,f2745])).

fof(f3399,plain,
    ( ! [X10,X11,X9] :
        ( m1_subset_1(k1_partfun1(X9,X10,sK1,sK0,X11,sK3),k1_zfmisc_1(k2_zfmisc_1(X9,sK0)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X11) )
    | ~ spl103_10 ),
    inference(resolution,[],[f3268,f2406])).

fof(f2406,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f1712])).

fof(f1712,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f1711])).

fof(f1711,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1476])).

fof(f1476,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f20341,plain,
    ( ~ spl103_173
    | spl103_174
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(avatar_split_clause,[],[f20221,f3501,f3266,f3261,f2743,f2738,f20338,f20334])).

fof(f3501,plain,
    ( spl103_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_13])])).

fof(f20221,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(forward_demodulation,[],[f20216,f20211])).

fof(f20216,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(backward_demodulation,[],[f3515,f20211])).

fof(f3515,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3508,f2403])).

fof(f2403,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f1477])).

fof(f1477,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f3508,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl103_13 ),
    inference(resolution,[],[f3503,f2361])).

fof(f2361,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1954])).

fof(f1954,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1688])).

fof(f1688,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1687])).

fof(f1687,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1236])).

fof(f1236,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f3503,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl103_13 ),
    inference(avatar_component_clause,[],[f3501])).

fof(f13730,plain,
    ( spl103_113
    | ~ spl103_36
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(avatar_split_clause,[],[f3556,f3501,f3266,f3261,f2902,f2897,f2887,f2743,f2738,f4299,f13727])).

fof(f3556,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(trivial_inequality_removal,[],[f3537])).

fof(f3537,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl103_1
    | ~ spl103_2
    | spl103_4
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(backward_demodulation,[],[f3469,f3528])).

fof(f3528,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(backward_demodulation,[],[f3405,f3527])).

fof(f3527,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl103_1
    | ~ spl103_2
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3526,f2745])).

fof(f3526,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl103_1
    | ~ spl103_6
    | ~ spl103_7
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3525,f2904])).

fof(f3525,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl103_1
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_10
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3524,f3268])).

fof(f3524,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl103_1
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3523,f2740])).

fof(f3523,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl103_6
    | ~ spl103_9
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3522,f2899])).

fof(f3522,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl103_9
    | ~ spl103_13 ),
    inference(subsumption_resolution,[],[f3511,f3263])).

fof(f3511,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl103_13 ),
    inference(resolution,[],[f3503,f2368])).

fof(f2368,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1698])).

fof(f1698,plain,(
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
    inference(flattening,[],[f1697])).

fof(f1697,plain,(
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
    inference(ennf_transformation,[],[f1498])).

fof(f1498,axiom,(
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

fof(f3405,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl103_10 ),
    inference(resolution,[],[f3268,f2442])).

fof(f3469,plain,
    ( sK0 != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7
    | ~ spl103_10 ),
    inference(backward_demodulation,[],[f3210,f3405])).

fof(f3210,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl103_2
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3209,f2745])).

fof(f3209,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3208,f2078])).

fof(f3208,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl103_4
    | ~ spl103_7 ),
    inference(subsumption_resolution,[],[f3089,f2889])).

fof(f3089,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl103_7 ),
    inference(resolution,[],[f2904,f2400])).

fof(f13316,plain,
    ( spl103_105
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_14 ),
    inference(avatar_split_clause,[],[f5691,f3568,f3271,f3261,f2738,f13313])).

fof(f5691,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_14 ),
    inference(subsumption_resolution,[],[f3352,f3570])).

fof(f3352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11 ),
    inference(backward_demodulation,[],[f2773,f3350])).

fof(f2773,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1 ),
    inference(resolution,[],[f2740,f2616])).

fof(f2616,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1832])).

fof(f1832,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1831])).

fof(f1831,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1512])).

fof(f1512,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f13306,plain,
    ( spl103_103
    | ~ spl103_27
    | ~ spl103_28 ),
    inference(avatar_split_clause,[],[f3957,f3920,f3901,f13303])).

fof(f3901,plain,
    ( spl103_27
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_27])])).

fof(f3920,plain,
    ( spl103_28
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_28])])).

fof(f3957,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ spl103_27
    | ~ spl103_28 ),
    inference(subsumption_resolution,[],[f3925,f3903])).

fof(f3903,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl103_27 ),
    inference(avatar_component_clause,[],[f3901])).

fof(f3925,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl103_28 ),
    inference(resolution,[],[f3922,f2138])).

fof(f2138,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1563])).

fof(f1563,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1562])).

fof(f1562,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f908,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f3922,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl103_28 ),
    inference(avatar_component_clause,[],[f3920])).

fof(f13224,plain,
    ( spl103_101
    | ~ spl103_27
    | ~ spl103_28 ),
    inference(avatar_split_clause,[],[f3956,f3920,f3901,f13221])).

fof(f3956,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ spl103_27
    | ~ spl103_28 ),
    inference(subsumption_resolution,[],[f3924,f3903])).

fof(f3924,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl103_28 ),
    inference(resolution,[],[f3922,f2137])).

fof(f2137,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1563])).

fof(f12545,plain,
    ( ~ spl103_93
    | spl103_8
    | ~ spl103_67 ),
    inference(avatar_split_clause,[],[f9193,f8742,f2907,f12542])).

fof(f2907,plain,
    ( spl103_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl103_8])])).

fof(f9193,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl103_8
    | ~ spl103_67 ),
    inference(superposition,[],[f2909,f8744])).

fof(f2909,plain,
    ( k2_funct_1(sK2) != sK3
    | spl103_8 ),
    inference(avatar_component_clause,[],[f2907])).

fof(f8745,plain,
    ( ~ spl103_14
    | spl103_67
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(avatar_split_clause,[],[f2872,f2748,f2738,f8742,f3568])).

fof(f2872,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(subsumption_resolution,[],[f2834,f2740])).

fof(f2834,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl103_3 ),
    inference(resolution,[],[f2750,f2135])).

fof(f5833,plain,
    ( spl103_57
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_14 ),
    inference(avatar_split_clause,[],[f5692,f3568,f3271,f3261,f2738,f5830])).

fof(f5692,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11
    | ~ spl103_14 ),
    inference(subsumption_resolution,[],[f3351,f3570])).

fof(f3351,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_9
    | ~ spl103_11 ),
    inference(backward_demodulation,[],[f2772,f3350])).

fof(f2772,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1 ),
    inference(resolution,[],[f2740,f2615])).

fof(f2615,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1832])).

fof(f3992,plain,
    ( ~ spl103_14
    | spl103_29
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(avatar_split_clause,[],[f2873,f2748,f2738,f3989,f3568])).

fof(f2873,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1
    | ~ spl103_3 ),
    inference(subsumption_resolution,[],[f2835,f2740])).

fof(f2835,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl103_3 ),
    inference(resolution,[],[f2750,f2136])).

fof(f2136,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1561])).

fof(f1561,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1560])).

fof(f1560,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1033])).

fof(f1033,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f3923,plain,
    ( ~ spl103_15
    | spl103_28
    | ~ spl103_2 ),
    inference(avatar_split_clause,[],[f2785,f2743,f3920,f3573])).

fof(f2785,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl103_2 ),
    inference(resolution,[],[f2745,f2138])).

fof(f3904,plain,
    ( ~ spl103_15
    | spl103_27
    | ~ spl103_2 ),
    inference(avatar_split_clause,[],[f2784,f2743,f3901,f3573])).

fof(f2784,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl103_2 ),
    inference(resolution,[],[f2745,f2137])).

fof(f3894,plain,
    ( ~ spl103_14
    | spl103_12
    | ~ spl103_1 ),
    inference(avatar_split_clause,[],[f2753,f2738,f3276,f3568])).

fof(f2753,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1 ),
    inference(resolution,[],[f2740,f2138])).

fof(f3879,plain,
    ( ~ spl103_14
    | spl103_25
    | ~ spl103_1 ),
    inference(avatar_split_clause,[],[f2752,f2738,f3876,f3568])).

fof(f2752,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl103_1 ),
    inference(resolution,[],[f2740,f2137])).

fof(f3679,plain,
    ( spl103_21
    | ~ spl103_9
    | ~ spl103_11 ),
    inference(avatar_split_clause,[],[f3350,f3271,f3261,f3676])).

fof(f3576,plain,
    ( spl103_15
    | ~ spl103_10 ),
    inference(avatar_split_clause,[],[f3419,f3266,f3573])).

fof(f3419,plain,
    ( v1_relat_1(sK3)
    | ~ spl103_10 ),
    inference(resolution,[],[f3268,f2465])).

fof(f2465,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f1764,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3571,plain,
    ( spl103_14
    | ~ spl103_9 ),
    inference(avatar_split_clause,[],[f3309,f3261,f3568])).

fof(f3309,plain,
    ( v1_relat_1(sK2)
    | ~ spl103_9 ),
    inference(resolution,[],[f3263,f2465])).

fof(f3504,plain,(
    spl103_13 ),
    inference(avatar_split_clause,[],[f2080,f3501])).

fof(f2080,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f1854])).

fof(f3274,plain,(
    spl103_11 ),
    inference(avatar_split_clause,[],[f2079,f3271])).

fof(f3269,plain,(
    spl103_10 ),
    inference(avatar_split_clause,[],[f2078,f3266])).

fof(f3264,plain,(
    spl103_9 ),
    inference(avatar_split_clause,[],[f2075,f3261])).

fof(f2910,plain,(
    ~ spl103_8 ),
    inference(avatar_split_clause,[],[f2084,f2907])).

fof(f2084,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f1854])).

fof(f2905,plain,(
    spl103_7 ),
    inference(avatar_split_clause,[],[f2077,f2902])).

fof(f2077,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f1854])).

fof(f2900,plain,(
    spl103_6 ),
    inference(avatar_split_clause,[],[f2074,f2897])).

fof(f2074,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f1854])).

fof(f2895,plain,(
    ~ spl103_5 ),
    inference(avatar_split_clause,[],[f2083,f2892])).

fof(f2083,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1854])).

fof(f2890,plain,(
    ~ spl103_4 ),
    inference(avatar_split_clause,[],[f2082,f2887])).

fof(f2082,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1854])).

fof(f2751,plain,(
    spl103_3 ),
    inference(avatar_split_clause,[],[f2081,f2748])).

fof(f2081,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1854])).

fof(f2746,plain,(
    spl103_2 ),
    inference(avatar_split_clause,[],[f2076,f2743])).

fof(f2076,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f1854])).

fof(f2741,plain,(
    spl103_1 ),
    inference(avatar_split_clause,[],[f2073,f2738])).

fof(f2073,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1854])).
%------------------------------------------------------------------------------
