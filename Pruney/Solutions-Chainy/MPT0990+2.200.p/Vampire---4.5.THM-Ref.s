%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 403 expanded)
%              Number of leaves         :   43 ( 154 expanded)
%              Depth                    :   10
%              Number of atoms          :  720 (1981 expanded)
%              Number of equality atoms :  160 ( 581 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f690,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f112,f116,f139,f174,f184,f186,f188,f211,f213,f215,f217,f227,f241,f257,f267,f320,f341,f388,f407,f429,f455,f510,f631,f639,f641,f675,f687])).

fof(f687,plain,(
    ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f47,f336])).

fof(f336,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl4_28
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f47,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f675,plain,
    ( spl4_29
    | ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | spl4_29
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f340,f672])).

fof(f672,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f662,f78])).

fof(f78,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f662,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_49 ),
    inference(superposition,[],[f78,f500])).

fof(f500,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_49
  <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f340,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl4_29
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f641,plain,
    ( ~ spl4_1
    | ~ spl4_39
    | ~ spl4_9
    | spl4_49
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f494,f426,f499,f156,f421,f92])).

fof(f92,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f421,plain,
    ( spl4_39
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f156,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f426,plain,
    ( spl4_40
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f494,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_40 ),
    inference(superposition,[],[f428,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f428,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f426])).

fof(f639,plain,(
    spl4_68 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl4_68 ),
    inference(unit_resulting_resolution,[],[f76,f630])).

fof(f630,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_68 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl4_68
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f76,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f54,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f631,plain,
    ( ~ spl4_35
    | ~ spl4_8
    | ~ spl4_9
    | spl4_38
    | spl4_39
    | ~ spl4_68
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f624,f508,f136,f628,f421,f417,f156,f152,f385])).

fof(f385,plain,
    ( spl4_35
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f152,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f417,plain,
    ( spl4_38
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f136,plain,
    ( spl4_6
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f508,plain,
    ( spl4_50
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f624,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_6
    | ~ spl4_50 ),
    inference(superposition,[],[f509,f138])).

fof(f138,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f509,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f508])).

fof(f510,plain,
    ( ~ spl4_7
    | spl4_50
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f506,f208,f160,f508,f148])).

fof(f148,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f160,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f208,plain,
    ( spl4_16
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f506,plain,(
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
    inference(trivial_inequality_removal,[],[f503])).

fof(f503,plain,(
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
    inference(superposition,[],[f69,f42])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f455,plain,(
    ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f45,f419])).

fof(f419,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f417])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f429,plain,
    ( spl4_40
    | spl4_38
    | ~ spl4_39
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_35
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f410,f381,f385,f152,f156,f421,f417,f426])).

fof(f381,plain,
    ( spl4_34
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f410,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_34 ),
    inference(trivial_inequality_removal,[],[f409])).

fof(f409,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_34 ),
    inference(superposition,[],[f63,f383])).

fof(f383,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f381])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f407,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f40,f387])).

fof(f387,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f385])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f388,plain,
    ( spl4_34
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f374,f385,f152,f148,f208,f160,f156,f381])).

fof(f374,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f341,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_9
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_29
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f332,f306,f263,f237,f338,f148,f92,f156,f204,f101,f334])).

fof(f101,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f204,plain,
    ( spl4_15
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f237,plain,
    ( spl4_17
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f263,plain,
    ( spl4_19
  <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f306,plain,
    ( spl4_26
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f332,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f331,f302])).

fof(f302,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f298,f78])).

fof(f298,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_19 ),
    inference(superposition,[],[f78,f265])).

fof(f265,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f263])).

fof(f331,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f328,f239])).

fof(f239,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f237])).

fof(f328,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f83,f308])).

fof(f308,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f306])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f61,f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f320,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | spl4_26
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f317,f136,f306,f160,f156,f152,f148])).

fof(f317,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f72,f138])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f267,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | ~ spl4_7
    | spl4_19
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f259,f254,f263,f148,f204,f101])).

fof(f254,plain,
    ( spl4_18
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f259,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f80,f256])).

fof(f256,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f80,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f257,plain,
    ( spl4_18
    | spl4_14
    | ~ spl4_15
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f252,f208,f160,f148,f204,f200,f254])).

fof(f200,plain,
    ( spl4_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f252,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[],[f64,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f241,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | ~ spl4_7
    | spl4_17
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f233,f196,f237,f148,f204,f101])).

fof(f196,plain,
    ( spl4_13
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f233,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f81,f198])).

fof(f198,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f227,plain,(
    ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f46,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f217,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f49,f210])).

fof(f210,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f215,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f44,f206])).

fof(f206,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f213,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f50,f162])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f211,plain,
    ( spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f194,f208,f160,f148,f204,f200,f196])).

fof(f194,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f63,f42])).

fof(f188,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f39,f158])).

fof(f158,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f186,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f41,f154])).

fof(f154,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f48,f39,f41,f50,f134,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f134,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_5
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f174,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f48,f150])).

fof(f150,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f139,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f129,f136,f132])).

fof(f129,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f126,f43])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f116,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f107])).

fof(f107,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f112,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f62,f98])).

fof(f98,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f105,f101])).

fof(f89,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f99,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f88,f96,f92])).

fof(f88,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:50:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (31170)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (31178)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.50  % (31164)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (31177)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (31173)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (31186)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (31162)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (31160)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (31182)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (31185)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (31172)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (31174)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (31163)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (31161)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (31165)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (31166)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (31188)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (31176)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (31175)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (31187)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (31176)Refutation not found, incomplete strategy% (31176)------------------------------
% 0.20/0.54  % (31176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31176)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31176)Memory used [KB]: 10746
% 0.20/0.54  % (31176)Time elapsed: 0.138 s
% 0.20/0.54  % (31176)------------------------------
% 0.20/0.54  % (31176)------------------------------
% 0.20/0.54  % (31180)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (31168)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (31167)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (31189)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (31179)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (31184)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (31183)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (31181)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (31171)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (31169)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (31173)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f690,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f99,f108,f112,f116,f139,f174,f184,f186,f188,f211,f213,f215,f217,f227,f241,f257,f267,f320,f341,f388,f407,f429,f455,f510,f631,f639,f641,f675,f687])).
% 0.20/0.56  fof(f687,plain,(
% 0.20/0.56    ~spl4_28),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f679])).
% 0.20/0.56  fof(f679,plain,(
% 0.20/0.56    $false | ~spl4_28),
% 0.20/0.56    inference(subsumption_resolution,[],[f47,f336])).
% 0.20/0.56  fof(f336,plain,(
% 0.20/0.56    sK3 = k2_funct_1(sK2) | ~spl4_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f334])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    spl4_28 <=> sK3 = k2_funct_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    sK3 != k2_funct_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.56    inference(negated_conjecture,[],[f16])).
% 0.20/0.56  fof(f16,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.56  fof(f675,plain,(
% 0.20/0.56    spl4_29 | ~spl4_49),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f674])).
% 0.20/0.56  fof(f674,plain,(
% 0.20/0.56    $false | (spl4_29 | ~spl4_49)),
% 0.20/0.56    inference(subsumption_resolution,[],[f340,f672])).
% 0.20/0.56  fof(f672,plain,(
% 0.20/0.56    sK1 = k1_relat_1(sK3) | ~spl4_49),
% 0.20/0.56    inference(forward_demodulation,[],[f662,f78])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f56,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.56  fof(f662,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_49),
% 0.20/0.56    inference(superposition,[],[f78,f500])).
% 0.20/0.56  fof(f500,plain,(
% 0.20/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~spl4_49),
% 0.20/0.56    inference(avatar_component_clause,[],[f499])).
% 0.20/0.56  fof(f499,plain,(
% 0.20/0.56    spl4_49 <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.20/0.56  fof(f340,plain,(
% 0.20/0.56    sK1 != k1_relat_1(sK3) | spl4_29),
% 0.20/0.56    inference(avatar_component_clause,[],[f338])).
% 0.20/0.56  fof(f338,plain,(
% 0.20/0.56    spl4_29 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.56  fof(f641,plain,(
% 0.20/0.56    ~spl4_1 | ~spl4_39 | ~spl4_9 | spl4_49 | ~spl4_40),
% 0.20/0.56    inference(avatar_split_clause,[],[f494,f426,f499,f156,f421,f92])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    spl4_1 <=> v1_relat_1(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.56  fof(f421,plain,(
% 0.20/0.56    spl4_39 <=> v2_funct_1(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    spl4_9 <=> v1_funct_1(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.56  fof(f426,plain,(
% 0.20/0.56    spl4_40 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.56  fof(f494,plain,(
% 0.20/0.56    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_40),
% 0.20/0.56    inference(superposition,[],[f428,f81])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f58,f51])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.56  fof(f428,plain,(
% 0.20/0.56    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_40),
% 0.20/0.56    inference(avatar_component_clause,[],[f426])).
% 0.20/0.56  fof(f639,plain,(
% 0.20/0.56    spl4_68),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f636])).
% 0.20/0.56  fof(f636,plain,(
% 0.20/0.56    $false | spl4_68),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f76,f630])).
% 0.20/0.56  fof(f630,plain,(
% 0.20/0.56    ~v2_funct_1(k6_partfun1(sK0)) | spl4_68),
% 0.20/0.56    inference(avatar_component_clause,[],[f628])).
% 0.20/0.56  fof(f628,plain,(
% 0.20/0.56    spl4_68 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f54,f51])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.56  fof(f631,plain,(
% 0.20/0.56    ~spl4_35 | ~spl4_8 | ~spl4_9 | spl4_38 | spl4_39 | ~spl4_68 | ~spl4_6 | ~spl4_50),
% 0.20/0.56    inference(avatar_split_clause,[],[f624,f508,f136,f628,f421,f417,f156,f152,f385])).
% 0.20/0.56  fof(f385,plain,(
% 0.20/0.56    spl4_35 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    spl4_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.56  fof(f417,plain,(
% 0.20/0.56    spl4_38 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    spl4_6 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.56  fof(f508,plain,(
% 0.20/0.56    spl4_50 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.20/0.56  fof(f624,plain,(
% 0.20/0.56    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_6 | ~spl4_50)),
% 0.20/0.56    inference(superposition,[],[f509,f138])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f136])).
% 0.20/0.56  fof(f509,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_50),
% 0.20/0.56    inference(avatar_component_clause,[],[f508])).
% 0.20/0.56  fof(f510,plain,(
% 0.20/0.56    ~spl4_7 | spl4_50 | ~spl4_10 | ~spl4_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f506,f208,f160,f508,f148])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    spl4_7 <=> v1_funct_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.56  fof(f160,plain,(
% 0.20/0.56    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.56  fof(f208,plain,(
% 0.20/0.56    spl4_16 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.56  fof(f506,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f503])).
% 0.20/0.56  fof(f503,plain,(
% 0.20/0.56    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 0.20/0.57    inference(superposition,[],[f69,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 0.20/0.57  fof(f455,plain,(
% 0.20/0.57    ~spl4_38),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f440])).
% 0.20/0.57  fof(f440,plain,(
% 0.20/0.57    $false | ~spl4_38),
% 0.20/0.57    inference(subsumption_resolution,[],[f45,f419])).
% 0.20/0.57  fof(f419,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl4_38),
% 0.20/0.57    inference(avatar_component_clause,[],[f417])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    k1_xboole_0 != sK0),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f429,plain,(
% 0.20/0.57    spl4_40 | spl4_38 | ~spl4_39 | ~spl4_9 | ~spl4_8 | ~spl4_35 | ~spl4_34),
% 0.20/0.57    inference(avatar_split_clause,[],[f410,f381,f385,f152,f156,f421,f417,f426])).
% 0.20/0.57  fof(f381,plain,(
% 0.20/0.57    spl4_34 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_34),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f409])).
% 0.20/0.57  fof(f409,plain,(
% 0.20/0.57    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_34),
% 0.20/0.57    inference(superposition,[],[f63,f383])).
% 0.20/0.57  fof(f383,plain,(
% 0.20/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_34),
% 0.20/0.57    inference(avatar_component_clause,[],[f381])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.57  fof(f407,plain,(
% 0.20/0.57    spl4_35),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f406])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    $false | spl4_35),
% 0.20/0.57    inference(subsumption_resolution,[],[f40,f387])).
% 0.20/0.57  fof(f387,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl4_35),
% 0.20/0.57    inference(avatar_component_clause,[],[f385])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f388,plain,(
% 0.20/0.57    spl4_34 | ~spl4_9 | ~spl4_10 | ~spl4_16 | ~spl4_7 | ~spl4_8 | ~spl4_35),
% 0.20/0.57    inference(avatar_split_clause,[],[f374,f385,f152,f148,f208,f160,f156,f381])).
% 0.20/0.57  fof(f374,plain,(
% 0.20/0.57    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.57    inference(resolution,[],[f65,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.57  fof(f341,plain,(
% 0.20/0.57    spl4_28 | ~spl4_3 | ~spl4_15 | ~spl4_9 | ~spl4_1 | ~spl4_7 | ~spl4_29 | ~spl4_17 | ~spl4_19 | ~spl4_26),
% 0.20/0.57    inference(avatar_split_clause,[],[f332,f306,f263,f237,f338,f148,f92,f156,f204,f101,f334])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    spl4_3 <=> v1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.57  fof(f204,plain,(
% 0.20/0.57    spl4_15 <=> v2_funct_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.57  fof(f237,plain,(
% 0.20/0.57    spl4_17 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.57  fof(f263,plain,(
% 0.20/0.57    spl4_19 <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    spl4_26 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.57  fof(f332,plain,(
% 0.20/0.57    sK1 != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_17 | ~spl4_19 | ~spl4_26)),
% 0.20/0.57    inference(forward_demodulation,[],[f331,f302])).
% 0.20/0.57  fof(f302,plain,(
% 0.20/0.57    sK1 = k2_relat_1(sK2) | ~spl4_19),
% 0.20/0.57    inference(forward_demodulation,[],[f298,f78])).
% 0.20/0.57  fof(f298,plain,(
% 0.20/0.57    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_19),
% 0.20/0.57    inference(superposition,[],[f78,f265])).
% 0.20/0.57  fof(f265,plain,(
% 0.20/0.57    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~spl4_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f263])).
% 0.20/0.57  fof(f331,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_17 | ~spl4_26)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f330])).
% 0.20/0.57  fof(f330,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_17 | ~spl4_26)),
% 0.20/0.57    inference(forward_demodulation,[],[f328,f239])).
% 0.20/0.57  fof(f239,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f237])).
% 0.20/0.57  fof(f328,plain,(
% 0.20/0.57    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~spl4_26),
% 0.20/0.57    inference(superposition,[],[f83,f308])).
% 0.20/0.57  fof(f308,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_26),
% 0.20/0.57    inference(avatar_component_clause,[],[f306])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.20/0.57    inference(definition_unfolding,[],[f61,f51])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.20/0.57  fof(f320,plain,(
% 0.20/0.57    ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | spl4_26 | ~spl4_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f317,f136,f306,f160,f156,f152,f148])).
% 0.20/0.57  fof(f317,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.57    inference(superposition,[],[f72,f138])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    ~spl4_3 | ~spl4_15 | ~spl4_7 | spl4_19 | ~spl4_18),
% 0.20/0.57    inference(avatar_split_clause,[],[f259,f254,f263,f148,f204,f101])).
% 0.20/0.57  fof(f254,plain,(
% 0.20/0.57    spl4_18 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.57  fof(f259,plain,(
% 0.20/0.57    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_18),
% 0.20/0.57    inference(superposition,[],[f80,f256])).
% 0.20/0.57  fof(f256,plain,(
% 0.20/0.57    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~spl4_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f254])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f59,f51])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f257,plain,(
% 0.20/0.57    spl4_18 | spl4_14 | ~spl4_15 | ~spl4_7 | ~spl4_10 | ~spl4_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f252,f208,f160,f148,f204,f200,f254])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    spl4_14 <=> k1_xboole_0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.57  fof(f252,plain,(
% 0.20/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f251])).
% 0.20/0.57  fof(f251,plain,(
% 0.20/0.57    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 0.20/0.57    inference(superposition,[],[f64,f42])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f241,plain,(
% 0.20/0.57    ~spl4_3 | ~spl4_15 | ~spl4_7 | spl4_17 | ~spl4_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f233,f196,f237,f148,f204,f101])).
% 0.20/0.57  fof(f196,plain,(
% 0.20/0.57    spl4_13 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.57  fof(f233,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_13),
% 0.20/0.57    inference(superposition,[],[f81,f198])).
% 0.20/0.57  fof(f198,plain,(
% 0.20/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f196])).
% 0.20/0.57  fof(f227,plain,(
% 0.20/0.57    ~spl4_14),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f218])).
% 0.20/0.57  fof(f218,plain,(
% 0.20/0.57    $false | ~spl4_14),
% 0.20/0.57    inference(subsumption_resolution,[],[f46,f202])).
% 0.20/0.57  fof(f202,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~spl4_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f200])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    spl4_16),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.57  fof(f216,plain,(
% 0.20/0.57    $false | spl4_16),
% 0.20/0.57    inference(subsumption_resolution,[],[f49,f210])).
% 0.20/0.57  fof(f210,plain,(
% 0.20/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl4_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f208])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    spl4_15),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f214])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    $false | spl4_15),
% 0.20/0.57    inference(subsumption_resolution,[],[f44,f206])).
% 0.20/0.57  fof(f206,plain,(
% 0.20/0.57    ~v2_funct_1(sK2) | spl4_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f204])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    v2_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f213,plain,(
% 0.20/0.57    spl4_10),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f212])).
% 0.20/0.57  fof(f212,plain,(
% 0.20/0.57    $false | spl4_10),
% 0.20/0.57    inference(subsumption_resolution,[],[f50,f162])).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f160])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f211,plain,(
% 0.20/0.57    spl4_13 | spl4_14 | ~spl4_15 | ~spl4_7 | ~spl4_10 | ~spl4_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f194,f208,f160,f148,f204,f200,f196])).
% 0.20/0.57  fof(f194,plain,(
% 0.20/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f193])).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.57    inference(superposition,[],[f63,f42])).
% 0.20/0.57  fof(f188,plain,(
% 0.20/0.57    spl4_9),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.57  fof(f187,plain,(
% 0.20/0.57    $false | spl4_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f39,f158])).
% 0.20/0.57  fof(f158,plain,(
% 0.20/0.57    ~v1_funct_1(sK3) | spl4_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f156])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    v1_funct_1(sK3)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f186,plain,(
% 0.20/0.57    spl4_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.57  fof(f185,plain,(
% 0.20/0.57    $false | spl4_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f41,f154])).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f152])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f184,plain,(
% 0.20/0.57    spl4_5),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    $false | spl4_5),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f39,f41,f50,f134,f74])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.57    inference(flattening,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f132])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    spl4_5 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f174,plain,(
% 0.20/0.57    spl4_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.57  fof(f173,plain,(
% 0.20/0.57    $false | spl4_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f48,f150])).
% 0.20/0.57  fof(f150,plain,(
% 0.20/0.57    ~v1_funct_1(sK2) | spl4_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f148])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ~spl4_5 | spl4_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f129,f136,f132])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.57    inference(resolution,[],[f126,f43])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 0.20/0.57    inference(resolution,[],[f71,f75])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f52,f51])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    spl4_4),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    $false | spl4_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f62,f107])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    spl4_2),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    $false | spl4_2),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f62,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f96])).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    spl4_3 | ~spl4_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f89,f105,f101])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.20/0.57    inference(resolution,[],[f57,f50])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl4_1 | ~spl4_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f88,f96,f92])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 0.20/0.57    inference(resolution,[],[f57,f41])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (31173)------------------------------
% 0.20/0.57  % (31173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (31173)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (31173)Memory used [KB]: 6780
% 0.20/0.57  % (31173)Time elapsed: 0.161 s
% 0.20/0.57  % (31173)------------------------------
% 0.20/0.57  % (31173)------------------------------
% 0.20/0.57  % (31159)Success in time 0.215 s
%------------------------------------------------------------------------------
