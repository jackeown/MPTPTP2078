%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:34 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 388 expanded)
%              Number of leaves         :   43 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  711 (1941 expanded)
%              Number of equality atoms :  160 ( 572 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f525,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f106,f153,f155,f157,f171,f184,f195,f215,f217,f223,f233,f253,f259,f261,f266,f298,f358,f365,f385,f394,f407,f413,f455,f459,f467,f511,f513,f522])).

fof(f522,plain,(
    ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f46,f506])).

fof(f506,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl4_45
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f513,plain,(
    spl4_46 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl4_46 ),
    inference(subsumption_resolution,[],[f43,f510])).

fof(f510,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl4_46
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f511,plain,
    ( spl4_45
    | ~ spl4_14
    | ~ spl4_46
    | ~ spl4_19
    | ~ spl4_18
    | ~ spl4_15
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f502,f464,f403,f180,f100,f205,f243,f247,f508,f201,f504])).

fof(f201,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f247,plain,
    ( spl4_19
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f243,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f205,plain,
    ( spl4_15
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f100,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f180,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f403,plain,
    ( spl4_36
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f464,plain,
    ( spl4_42
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f502,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f501])).

fof(f501,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f500,f182])).

fof(f182,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f500,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f499,f405])).

fof(f405,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f403])).

fof(f499,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f498])).

fof(f498,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f493,f102])).

fof(f102,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f493,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_42 ),
    inference(superposition,[],[f79,f466])).

fof(f466,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f464])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f467,plain,
    ( ~ spl4_18
    | ~ spl4_17
    | ~ spl4_19
    | spl4_42
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f462,f378,f167,f464,f247,f239,f243])).

fof(f239,plain,
    ( spl4_17
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f167,plain,
    ( spl4_12
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f378,plain,
    ( spl4_32
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f462,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f460,f169])).

fof(f169,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f460,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32 ),
    inference(superposition,[],[f78,f380])).

fof(f380,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f378])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f459,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f75,f454])).

fof(f454,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl4_41
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f455,plain,
    ( ~ spl4_14
    | ~ spl4_15
    | ~ spl4_41
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f450,f313,f251,f100,f452,f205,f201])).

fof(f251,plain,
    ( spl4_20
  <=> ! [X2] :
        ( k2_relat_1(X2) != sK1
        | ~ v2_funct_1(k5_relat_1(X2,sK3))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f313,plain,
    ( spl4_26
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f450,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f449,f315])).

fof(f315,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f313])).

fof(f449,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f447])).

fof(f447,plain,
    ( sK1 != sK1
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(superposition,[],[f252,f102])).

fof(f252,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | ~ v2_funct_1(k5_relat_1(X2,sK3))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f251])).

fof(f413,plain,
    ( spl4_33
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl4_33
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f408])).

fof(f408,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_33
    | ~ spl4_36 ),
    inference(superposition,[],[f384,f405])).

fof(f384,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f407,plain,
    ( ~ spl4_11
    | spl4_36
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f401,f391,f403,f163])).

fof(f163,plain,
    ( spl4_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f391,plain,
    ( spl4_34
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f401,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_34 ),
    inference(superposition,[],[f62,f393])).

fof(f393,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f391])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f394,plain,
    ( spl4_34
    | ~ spl4_19
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_11
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f386,f129,f163,f205,f142,f96,f247,f391])).

fof(f96,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f142,plain,
    ( spl4_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f129,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f386,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f385,plain,
    ( spl4_32
    | ~ spl4_18
    | ~ spl4_17
    | ~ spl4_15
    | ~ spl4_14
    | ~ spl4_19
    | ~ spl4_33
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f376,f313,f167,f100,f382,f247,f201,f205,f239,f243,f378])).

fof(f376,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f374,f102])).

fof(f374,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_12
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f373,f169])).

fof(f373,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_26 ),
    inference(superposition,[],[f79,f315])).

fof(f365,plain,
    ( ~ spl4_15
    | ~ spl4_11
    | ~ spl4_19
    | ~ spl4_1
    | spl4_26
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f362,f295,f313,f96,f247,f163,f205])).

fof(f295,plain,
    ( spl4_23
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f362,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f72,f297])).

fof(f297,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f295])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f358,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f293,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f293,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl4_22
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f298,plain,
    ( ~ spl4_22
    | spl4_23 ),
    inference(avatar_split_clause,[],[f288,f295,f291])).

fof(f288,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f173,f42])).

fof(f173,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f266,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f263,f137,f133,f129])).

fof(f133,plain,
    ( spl4_6
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f137,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f263,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f40,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f261,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f38,f249])).

fof(f249,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f259,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f87,f245])).

fof(f245,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f87,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f253,plain,
    ( spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f235,f167,f251,f247,f243,f239])).

fof(f235,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != sK1
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(k5_relat_1(X2,sK3))
        | ~ v1_relat_1(sK3)
        | v2_funct_1(sK3) )
    | ~ spl4_12 ),
    inference(superposition,[],[f59,f169])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f233,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f44,f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f223,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f40,f165])).

fof(f165,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f217,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f47,f207])).

fof(f207,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f215,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f88,f203])).

fof(f203,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f88,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f49])).

fof(f195,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f45,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f184,plain,
    ( ~ spl4_1
    | spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f177,f146,f180,f96])).

fof(f146,plain,
    ( spl4_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f177,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(superposition,[],[f61,f148])).

fof(f148,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f171,plain,
    ( ~ spl4_11
    | spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f160,f133,f167,f163])).

fof(f160,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f61,f135])).

fof(f135,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f157,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f48,f144])).

fof(f144,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f155,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f39,f131])).

fof(f131,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f153,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f127,f150,f146,f142])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f68,f49])).

fof(f106,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f49,f98])).

fof(f98,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f104,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f62])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:43:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31940)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (31924)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31932)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.53  % (31919)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.53  % (31921)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.53  % (31918)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.54  % (31922)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.54  % (31923)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (31931)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.25/0.54  % (31930)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.25/0.55  % (31929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.25/0.55  % (31926)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.55  % (31935)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (31920)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.55  % (31947)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (31946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.56  % (31945)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.56  % (31942)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.56  % (31927)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (31939)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.56  % (31943)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.57  % (31934)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.57  % (31937)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.57  % (31934)Refutation not found, incomplete strategy% (31934)------------------------------
% 1.42/0.57  % (31934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31934)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31934)Memory used [KB]: 10746
% 1.42/0.57  % (31934)Time elapsed: 0.157 s
% 1.42/0.57  % (31934)------------------------------
% 1.42/0.57  % (31934)------------------------------
% 1.42/0.57  % (31938)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.57  % (31928)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.57  % (31936)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.58  % (31931)Refutation found. Thanks to Tanya!
% 1.42/0.58  % SZS status Theorem for theBenchmark
% 1.42/0.58  % SZS output start Proof for theBenchmark
% 1.42/0.58  fof(f525,plain,(
% 1.42/0.58    $false),
% 1.42/0.58    inference(avatar_sat_refutation,[],[f104,f106,f153,f155,f157,f171,f184,f195,f215,f217,f223,f233,f253,f259,f261,f266,f298,f358,f365,f385,f394,f407,f413,f455,f459,f467,f511,f513,f522])).
% 1.42/0.58  fof(f522,plain,(
% 1.42/0.58    ~spl4_45),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f519])).
% 1.42/0.58  fof(f519,plain,(
% 1.42/0.58    $false | ~spl4_45),
% 1.42/0.58    inference(subsumption_resolution,[],[f46,f506])).
% 1.42/0.58  fof(f506,plain,(
% 1.42/0.58    sK3 = k2_funct_1(sK2) | ~spl4_45),
% 1.42/0.58    inference(avatar_component_clause,[],[f504])).
% 1.42/0.58  fof(f504,plain,(
% 1.42/0.58    spl4_45 <=> sK3 = k2_funct_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.42/0.58  fof(f46,plain,(
% 1.42/0.58    sK3 != k2_funct_1(sK2)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f18,plain,(
% 1.42/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.58    inference(flattening,[],[f17])).
% 1.42/0.58  fof(f17,plain,(
% 1.42/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.58    inference(ennf_transformation,[],[f16])).
% 1.42/0.58  fof(f16,negated_conjecture,(
% 1.42/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.42/0.58    inference(negated_conjecture,[],[f15])).
% 1.42/0.58  fof(f15,conjecture,(
% 1.42/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.42/0.58  fof(f513,plain,(
% 1.42/0.58    spl4_46),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f512])).
% 1.42/0.58  fof(f512,plain,(
% 1.42/0.58    $false | spl4_46),
% 1.42/0.58    inference(subsumption_resolution,[],[f43,f510])).
% 1.42/0.58  fof(f510,plain,(
% 1.42/0.58    ~v2_funct_1(sK2) | spl4_46),
% 1.42/0.58    inference(avatar_component_clause,[],[f508])).
% 1.42/0.58  fof(f508,plain,(
% 1.42/0.58    spl4_46 <=> v2_funct_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.42/0.58  fof(f43,plain,(
% 1.42/0.58    v2_funct_1(sK2)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f511,plain,(
% 1.42/0.58    spl4_45 | ~spl4_14 | ~spl4_46 | ~spl4_19 | ~spl4_18 | ~spl4_15 | ~spl4_2 | ~spl4_13 | ~spl4_36 | ~spl4_42),
% 1.42/0.58    inference(avatar_split_clause,[],[f502,f464,f403,f180,f100,f205,f243,f247,f508,f201,f504])).
% 1.42/0.58  fof(f201,plain,(
% 1.42/0.58    spl4_14 <=> v1_relat_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.42/0.58  fof(f247,plain,(
% 1.42/0.58    spl4_19 <=> v1_funct_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.42/0.58  fof(f243,plain,(
% 1.42/0.58    spl4_18 <=> v1_relat_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.42/0.58  fof(f205,plain,(
% 1.42/0.58    spl4_15 <=> v1_funct_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.42/0.58  fof(f100,plain,(
% 1.42/0.58    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.42/0.58  fof(f180,plain,(
% 1.42/0.58    spl4_13 <=> sK0 = k1_relat_1(sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.42/0.58  fof(f403,plain,(
% 1.42/0.58    spl4_36 <=> sK0 = k2_relat_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.42/0.58  fof(f464,plain,(
% 1.42/0.58    spl4_42 <=> k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.42/0.58  fof(f502,plain,(
% 1.42/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_2 | ~spl4_13 | ~spl4_36 | ~spl4_42)),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f501])).
% 1.42/0.58  fof(f501,plain,(
% 1.42/0.58    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_2 | ~spl4_13 | ~spl4_36 | ~spl4_42)),
% 1.42/0.58    inference(forward_demodulation,[],[f500,f182])).
% 1.42/0.58  fof(f182,plain,(
% 1.42/0.58    sK0 = k1_relat_1(sK2) | ~spl4_13),
% 1.42/0.58    inference(avatar_component_clause,[],[f180])).
% 1.42/0.58  fof(f500,plain,(
% 1.42/0.58    sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_2 | ~spl4_36 | ~spl4_42)),
% 1.42/0.58    inference(forward_demodulation,[],[f499,f405])).
% 1.42/0.58  fof(f405,plain,(
% 1.42/0.58    sK0 = k2_relat_1(sK3) | ~spl4_36),
% 1.42/0.58    inference(avatar_component_clause,[],[f403])).
% 1.42/0.58  fof(f499,plain,(
% 1.42/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_2 | ~spl4_42)),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f498])).
% 1.42/0.58  fof(f498,plain,(
% 1.42/0.58    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_2 | ~spl4_42)),
% 1.42/0.58    inference(forward_demodulation,[],[f493,f102])).
% 1.42/0.58  fof(f102,plain,(
% 1.42/0.58    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 1.42/0.58    inference(avatar_component_clause,[],[f100])).
% 1.42/0.58  fof(f493,plain,(
% 1.42/0.58    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~spl4_42),
% 1.42/0.58    inference(superposition,[],[f79,f466])).
% 1.42/0.58  fof(f466,plain,(
% 1.42/0.58    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~spl4_42),
% 1.42/0.58    inference(avatar_component_clause,[],[f464])).
% 1.42/0.58  fof(f79,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.42/0.58    inference(definition_unfolding,[],[f57,f50])).
% 1.42/0.58  fof(f50,plain,(
% 1.42/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f13])).
% 1.42/0.58  fof(f13,axiom,(
% 1.42/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.42/0.58  fof(f57,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f22])).
% 1.42/0.58  fof(f22,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(flattening,[],[f21])).
% 1.42/0.58  fof(f21,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.58    inference(ennf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.42/0.58  fof(f467,plain,(
% 1.42/0.58    ~spl4_18 | ~spl4_17 | ~spl4_19 | spl4_42 | ~spl4_12 | ~spl4_32),
% 1.42/0.58    inference(avatar_split_clause,[],[f462,f378,f167,f464,f247,f239,f243])).
% 1.42/0.58  fof(f239,plain,(
% 1.42/0.58    spl4_17 <=> v2_funct_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.42/0.58  fof(f167,plain,(
% 1.42/0.58    spl4_12 <=> sK1 = k1_relat_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.42/0.58  fof(f378,plain,(
% 1.42/0.58    spl4_32 <=> sK2 = k2_funct_1(sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.42/0.58  fof(f462,plain,(
% 1.42/0.58    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_32)),
% 1.42/0.58    inference(forward_demodulation,[],[f460,f169])).
% 1.42/0.58  fof(f169,plain,(
% 1.42/0.58    sK1 = k1_relat_1(sK3) | ~spl4_12),
% 1.42/0.58    inference(avatar_component_clause,[],[f167])).
% 1.42/0.58  fof(f460,plain,(
% 1.42/0.58    k6_partfun1(k1_relat_1(sK3)) = k5_relat_1(sK3,sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_32),
% 1.42/0.58    inference(superposition,[],[f78,f380])).
% 1.42/0.58  fof(f380,plain,(
% 1.42/0.58    sK2 = k2_funct_1(sK3) | ~spl4_32),
% 1.42/0.58    inference(avatar_component_clause,[],[f378])).
% 1.42/0.58  fof(f78,plain,(
% 1.42/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/0.58    inference(definition_unfolding,[],[f55,f50])).
% 1.42/0.58  fof(f55,plain,(
% 1.42/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f20])).
% 1.42/0.58  fof(f20,plain,(
% 1.42/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(flattening,[],[f19])).
% 1.42/0.58  fof(f19,plain,(
% 1.42/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.58    inference(ennf_transformation,[],[f3])).
% 1.42/0.58  fof(f3,axiom,(
% 1.42/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.42/0.58  fof(f459,plain,(
% 1.42/0.58    spl4_41),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f456])).
% 1.42/0.58  fof(f456,plain,(
% 1.42/0.58    $false | spl4_41),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f75,f454])).
% 1.42/0.58  fof(f454,plain,(
% 1.42/0.58    ~v2_funct_1(k6_partfun1(sK0)) | spl4_41),
% 1.42/0.58    inference(avatar_component_clause,[],[f452])).
% 1.42/0.58  fof(f452,plain,(
% 1.42/0.58    spl4_41 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.42/0.58  fof(f75,plain,(
% 1.42/0.58    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.42/0.58    inference(definition_unfolding,[],[f52,f50])).
% 1.42/0.58  fof(f52,plain,(
% 1.42/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f1])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.42/0.58  fof(f455,plain,(
% 1.42/0.58    ~spl4_14 | ~spl4_15 | ~spl4_41 | ~spl4_2 | ~spl4_20 | ~spl4_26),
% 1.42/0.58    inference(avatar_split_clause,[],[f450,f313,f251,f100,f452,f205,f201])).
% 1.42/0.58  fof(f251,plain,(
% 1.42/0.58    spl4_20 <=> ! [X2] : (k2_relat_1(X2) != sK1 | ~v2_funct_1(k5_relat_1(X2,sK3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.42/0.58  fof(f313,plain,(
% 1.42/0.58    spl4_26 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.42/0.58  fof(f450,plain,(
% 1.42/0.58    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_2 | ~spl4_20 | ~spl4_26)),
% 1.42/0.58    inference(forward_demodulation,[],[f449,f315])).
% 1.42/0.58  fof(f315,plain,(
% 1.42/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_26),
% 1.42/0.58    inference(avatar_component_clause,[],[f313])).
% 1.42/0.58  fof(f449,plain,(
% 1.42/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_2 | ~spl4_20)),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f447])).
% 1.42/0.58  fof(f447,plain,(
% 1.42/0.58    sK1 != sK1 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_2 | ~spl4_20)),
% 1.42/0.58    inference(superposition,[],[f252,f102])).
% 1.42/0.58  fof(f252,plain,(
% 1.42/0.58    ( ! [X2] : (k2_relat_1(X2) != sK1 | ~v2_funct_1(k5_relat_1(X2,sK3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl4_20),
% 1.42/0.58    inference(avatar_component_clause,[],[f251])).
% 1.42/0.58  fof(f413,plain,(
% 1.42/0.58    spl4_33 | ~spl4_36),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f412])).
% 1.42/0.58  fof(f412,plain,(
% 1.42/0.58    $false | (spl4_33 | ~spl4_36)),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f408])).
% 1.42/0.58  fof(f408,plain,(
% 1.42/0.58    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_33 | ~spl4_36)),
% 1.42/0.58    inference(superposition,[],[f384,f405])).
% 1.42/0.58  fof(f384,plain,(
% 1.42/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_33),
% 1.42/0.58    inference(avatar_component_clause,[],[f382])).
% 1.42/0.58  fof(f382,plain,(
% 1.42/0.58    spl4_33 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.42/0.58  fof(f407,plain,(
% 1.42/0.58    ~spl4_11 | spl4_36 | ~spl4_34),
% 1.42/0.58    inference(avatar_split_clause,[],[f401,f391,f403,f163])).
% 1.42/0.58  fof(f163,plain,(
% 1.42/0.58    spl4_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.42/0.58  fof(f391,plain,(
% 1.42/0.58    spl4_34 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.42/0.58  fof(f401,plain,(
% 1.42/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_34),
% 1.42/0.58    inference(superposition,[],[f62,f393])).
% 1.42/0.58  fof(f393,plain,(
% 1.42/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_34),
% 1.42/0.58    inference(avatar_component_clause,[],[f391])).
% 1.42/0.58  fof(f62,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f27])).
% 1.42/0.58  fof(f27,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.42/0.58  fof(f394,plain,(
% 1.42/0.58    spl4_34 | ~spl4_19 | ~spl4_1 | ~spl4_8 | ~spl4_15 | ~spl4_11 | ~spl4_5),
% 1.42/0.58    inference(avatar_split_clause,[],[f386,f129,f163,f205,f142,f96,f247,f391])).
% 1.42/0.58  fof(f96,plain,(
% 1.42/0.58    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.42/0.58  fof(f142,plain,(
% 1.42/0.58    spl4_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.42/0.58  fof(f129,plain,(
% 1.42/0.58    spl4_5 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.42/0.58  fof(f386,plain,(
% 1.42/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.42/0.58    inference(resolution,[],[f69,f42])).
% 1.42/0.58  fof(f42,plain,(
% 1.42/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f69,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f31])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/0.58    inference(flattening,[],[f30])).
% 1.42/0.58  fof(f30,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/0.58    inference(ennf_transformation,[],[f14])).
% 1.42/0.58  fof(f14,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.42/0.58  fof(f385,plain,(
% 1.42/0.58    spl4_32 | ~spl4_18 | ~spl4_17 | ~spl4_15 | ~spl4_14 | ~spl4_19 | ~spl4_33 | ~spl4_2 | ~spl4_12 | ~spl4_26),
% 1.42/0.58    inference(avatar_split_clause,[],[f376,f313,f167,f100,f382,f247,f201,f205,f239,f243,f378])).
% 1.42/0.58  fof(f376,plain,(
% 1.42/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_12 | ~spl4_26)),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f375])).
% 1.42/0.58  fof(f375,plain,(
% 1.42/0.58    sK1 != sK1 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_12 | ~spl4_26)),
% 1.42/0.58    inference(forward_demodulation,[],[f374,f102])).
% 1.42/0.58  fof(f374,plain,(
% 1.42/0.58    sK1 != k2_relat_1(sK2) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_12 | ~spl4_26)),
% 1.42/0.58    inference(forward_demodulation,[],[f373,f169])).
% 1.42/0.58  fof(f373,plain,(
% 1.42/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_26),
% 1.42/0.58    inference(superposition,[],[f79,f315])).
% 1.42/0.58  fof(f365,plain,(
% 1.42/0.58    ~spl4_15 | ~spl4_11 | ~spl4_19 | ~spl4_1 | spl4_26 | ~spl4_23),
% 1.42/0.58    inference(avatar_split_clause,[],[f362,f295,f313,f96,f247,f163,f205])).
% 1.42/0.58  fof(f295,plain,(
% 1.42/0.58    spl4_23 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.42/0.58  fof(f362,plain,(
% 1.42/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_23),
% 1.42/0.58    inference(superposition,[],[f72,f297])).
% 1.42/0.58  fof(f297,plain,(
% 1.42/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_23),
% 1.42/0.58    inference(avatar_component_clause,[],[f295])).
% 1.42/0.58  fof(f72,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f35])).
% 1.42/0.58  fof(f35,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.58    inference(flattening,[],[f34])).
% 1.42/0.58  fof(f34,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.58    inference(ennf_transformation,[],[f12])).
% 1.42/0.58  fof(f12,axiom,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.42/0.58  fof(f358,plain,(
% 1.42/0.58    spl4_22),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f344])).
% 1.42/0.58  fof(f344,plain,(
% 1.42/0.58    $false | spl4_22),
% 1.42/0.58    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f293,f74])).
% 1.42/0.58  fof(f74,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f37])).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.58    inference(flattening,[],[f36])).
% 1.42/0.58  fof(f36,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.58    inference(ennf_transformation,[],[f10])).
% 1.42/0.58  fof(f10,axiom,(
% 1.42/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.42/0.58  fof(f293,plain,(
% 1.42/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_22),
% 1.42/0.58    inference(avatar_component_clause,[],[f291])).
% 1.42/0.58  fof(f291,plain,(
% 1.42/0.58    spl4_22 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.42/0.58  fof(f49,plain,(
% 1.42/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f40,plain,(
% 1.42/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f38,plain,(
% 1.42/0.58    v1_funct_1(sK3)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f47,plain,(
% 1.42/0.58    v1_funct_1(sK2)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f298,plain,(
% 1.42/0.58    ~spl4_22 | spl4_23),
% 1.42/0.58    inference(avatar_split_clause,[],[f288,f295,f291])).
% 1.42/0.58  fof(f288,plain,(
% 1.42/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.58    inference(resolution,[],[f173,f42])).
% 1.42/0.58  fof(f173,plain,(
% 1.42/0.58    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.42/0.58    inference(resolution,[],[f71,f54])).
% 1.42/0.58  fof(f54,plain,(
% 1.42/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f11])).
% 1.42/0.58  fof(f11,axiom,(
% 1.42/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.42/0.58  fof(f71,plain,(
% 1.42/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f33])).
% 1.42/0.58  fof(f33,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(flattening,[],[f32])).
% 1.42/0.58  fof(f32,plain,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.42/0.58    inference(ennf_transformation,[],[f8])).
% 1.42/0.58  fof(f8,axiom,(
% 1.42/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.42/0.58  fof(f266,plain,(
% 1.42/0.58    ~spl4_5 | spl4_6 | spl4_7),
% 1.42/0.58    inference(avatar_split_clause,[],[f263,f137,f133,f129])).
% 1.42/0.58  fof(f133,plain,(
% 1.42/0.58    spl4_6 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.42/0.58  fof(f137,plain,(
% 1.42/0.58    spl4_7 <=> k1_xboole_0 = sK0),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.42/0.58  fof(f263,plain,(
% 1.42/0.58    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.58    inference(resolution,[],[f40,f68])).
% 1.42/0.58  fof(f68,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f29])).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(flattening,[],[f28])).
% 1.42/0.58  fof(f28,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f9])).
% 1.42/0.58  fof(f9,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.42/0.58  fof(f261,plain,(
% 1.42/0.58    spl4_19),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f260])).
% 1.42/0.58  fof(f260,plain,(
% 1.42/0.58    $false | spl4_19),
% 1.42/0.58    inference(subsumption_resolution,[],[f38,f249])).
% 1.42/0.58  fof(f249,plain,(
% 1.42/0.58    ~v1_funct_1(sK3) | spl4_19),
% 1.42/0.58    inference(avatar_component_clause,[],[f247])).
% 1.42/0.58  fof(f259,plain,(
% 1.42/0.58    spl4_18),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f258])).
% 1.42/0.58  fof(f258,plain,(
% 1.42/0.58    $false | spl4_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f87,f245])).
% 1.42/0.58  fof(f245,plain,(
% 1.42/0.58    ~v1_relat_1(sK3) | spl4_18),
% 1.42/0.58    inference(avatar_component_clause,[],[f243])).
% 1.42/0.58  fof(f87,plain,(
% 1.42/0.58    v1_relat_1(sK3)),
% 1.42/0.58    inference(resolution,[],[f60,f40])).
% 1.42/0.58  fof(f60,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f25])).
% 1.42/0.58  fof(f25,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.58  fof(f253,plain,(
% 1.42/0.58    spl4_17 | ~spl4_18 | ~spl4_19 | spl4_20 | ~spl4_12),
% 1.42/0.58    inference(avatar_split_clause,[],[f235,f167,f251,f247,f243,f239])).
% 1.42/0.58  fof(f235,plain,(
% 1.42/0.58    ( ! [X2] : (k2_relat_1(X2) != sK1 | ~v1_funct_1(sK3) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(k5_relat_1(X2,sK3)) | ~v1_relat_1(sK3) | v2_funct_1(sK3)) ) | ~spl4_12),
% 1.42/0.58    inference(superposition,[],[f59,f169])).
% 1.42/0.58  fof(f59,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f24])).
% 1.42/0.58  fof(f24,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.58    inference(flattening,[],[f23])).
% 1.42/0.58  fof(f23,plain,(
% 1.42/0.58    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.58    inference(ennf_transformation,[],[f2])).
% 1.42/0.58  fof(f2,axiom,(
% 1.42/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.42/0.58  fof(f233,plain,(
% 1.42/0.58    ~spl4_7),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 1.42/0.58  fof(f224,plain,(
% 1.42/0.58    $false | ~spl4_7),
% 1.42/0.58    inference(subsumption_resolution,[],[f44,f139])).
% 1.42/0.58  fof(f139,plain,(
% 1.42/0.58    k1_xboole_0 = sK0 | ~spl4_7),
% 1.42/0.58    inference(avatar_component_clause,[],[f137])).
% 1.42/0.58  fof(f44,plain,(
% 1.42/0.58    k1_xboole_0 != sK0),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f223,plain,(
% 1.42/0.58    spl4_11),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f222])).
% 1.42/0.58  fof(f222,plain,(
% 1.42/0.58    $false | spl4_11),
% 1.42/0.58    inference(subsumption_resolution,[],[f40,f165])).
% 1.42/0.58  fof(f165,plain,(
% 1.42/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_11),
% 1.42/0.58    inference(avatar_component_clause,[],[f163])).
% 1.42/0.58  fof(f217,plain,(
% 1.42/0.58    spl4_15),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f216])).
% 1.42/0.58  fof(f216,plain,(
% 1.42/0.58    $false | spl4_15),
% 1.42/0.58    inference(subsumption_resolution,[],[f47,f207])).
% 1.42/0.58  fof(f207,plain,(
% 1.42/0.58    ~v1_funct_1(sK2) | spl4_15),
% 1.42/0.58    inference(avatar_component_clause,[],[f205])).
% 1.42/0.58  fof(f215,plain,(
% 1.42/0.58    spl4_14),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f212])).
% 1.42/0.58  fof(f212,plain,(
% 1.42/0.58    $false | spl4_14),
% 1.42/0.58    inference(subsumption_resolution,[],[f88,f203])).
% 1.42/0.58  fof(f203,plain,(
% 1.42/0.58    ~v1_relat_1(sK2) | spl4_14),
% 1.42/0.58    inference(avatar_component_clause,[],[f201])).
% 1.42/0.58  fof(f88,plain,(
% 1.42/0.58    v1_relat_1(sK2)),
% 1.42/0.58    inference(resolution,[],[f60,f49])).
% 1.42/0.58  fof(f195,plain,(
% 1.42/0.58    ~spl4_10),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f185])).
% 1.42/0.58  fof(f185,plain,(
% 1.42/0.58    $false | ~spl4_10),
% 1.42/0.58    inference(subsumption_resolution,[],[f45,f152])).
% 1.42/0.58  fof(f152,plain,(
% 1.42/0.58    k1_xboole_0 = sK1 | ~spl4_10),
% 1.42/0.58    inference(avatar_component_clause,[],[f150])).
% 1.42/0.58  fof(f150,plain,(
% 1.42/0.58    spl4_10 <=> k1_xboole_0 = sK1),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.42/0.58  fof(f45,plain,(
% 1.42/0.58    k1_xboole_0 != sK1),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f184,plain,(
% 1.42/0.58    ~spl4_1 | spl4_13 | ~spl4_9),
% 1.42/0.58    inference(avatar_split_clause,[],[f177,f146,f180,f96])).
% 1.42/0.58  fof(f146,plain,(
% 1.42/0.58    spl4_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.42/0.58  fof(f177,plain,(
% 1.42/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 1.42/0.58    inference(superposition,[],[f61,f148])).
% 1.42/0.58  fof(f148,plain,(
% 1.42/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_9),
% 1.42/0.58    inference(avatar_component_clause,[],[f146])).
% 1.42/0.58  fof(f61,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f26])).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f6])).
% 1.42/0.58  fof(f6,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.42/0.58  fof(f171,plain,(
% 1.42/0.58    ~spl4_11 | spl4_12 | ~spl4_6),
% 1.42/0.58    inference(avatar_split_clause,[],[f160,f133,f167,f163])).
% 1.42/0.58  fof(f160,plain,(
% 1.42/0.58    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_6),
% 1.42/0.58    inference(superposition,[],[f61,f135])).
% 1.42/0.58  fof(f135,plain,(
% 1.42/0.58    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_6),
% 1.42/0.58    inference(avatar_component_clause,[],[f133])).
% 1.42/0.58  fof(f157,plain,(
% 1.42/0.58    spl4_8),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f156])).
% 1.42/0.58  fof(f156,plain,(
% 1.42/0.58    $false | spl4_8),
% 1.42/0.58    inference(subsumption_resolution,[],[f48,f144])).
% 1.42/0.58  fof(f144,plain,(
% 1.42/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl4_8),
% 1.42/0.58    inference(avatar_component_clause,[],[f142])).
% 1.42/0.58  fof(f48,plain,(
% 1.42/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f155,plain,(
% 1.42/0.58    spl4_5),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f154])).
% 1.42/0.58  fof(f154,plain,(
% 1.42/0.58    $false | spl4_5),
% 1.42/0.58    inference(subsumption_resolution,[],[f39,f131])).
% 1.42/0.58  fof(f131,plain,(
% 1.42/0.58    ~v1_funct_2(sK3,sK1,sK0) | spl4_5),
% 1.42/0.58    inference(avatar_component_clause,[],[f129])).
% 1.42/0.58  fof(f39,plain,(
% 1.42/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  fof(f153,plain,(
% 1.42/0.58    ~spl4_8 | spl4_9 | spl4_10),
% 1.42/0.58    inference(avatar_split_clause,[],[f127,f150,f146,f142])).
% 1.42/0.58  fof(f127,plain,(
% 1.42/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.58    inference(resolution,[],[f68,f49])).
% 1.42/0.58  fof(f106,plain,(
% 1.42/0.58    spl4_1),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f105])).
% 1.42/0.58  fof(f105,plain,(
% 1.42/0.58    $false | spl4_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f49,f98])).
% 1.42/0.58  fof(f98,plain,(
% 1.42/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f96])).
% 1.42/0.58  fof(f104,plain,(
% 1.42/0.58    ~spl4_1 | spl4_2),
% 1.42/0.58    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.42/0.58  fof(f94,plain,(
% 1.42/0.58    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.58    inference(superposition,[],[f41,f62])).
% 1.42/0.58  fof(f41,plain,(
% 1.42/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.42/0.58    inference(cnf_transformation,[],[f18])).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (31931)------------------------------
% 1.42/0.58  % (31931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (31931)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (31931)Memory used [KB]: 6652
% 1.42/0.58  % (31931)Time elapsed: 0.145 s
% 1.42/0.58  % (31931)------------------------------
% 1.42/0.58  % (31931)------------------------------
% 1.42/0.58  % (31917)Success in time 0.213 s
%------------------------------------------------------------------------------
