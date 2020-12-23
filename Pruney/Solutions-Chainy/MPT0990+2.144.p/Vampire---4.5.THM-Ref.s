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
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 342 expanded)
%              Number of leaves         :   44 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :  630 (1673 expanded)
%              Number of equality atoms :  136 ( 464 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f113,f117,f131,f133,f138,f150,f152,f201,f203,f217,f256,f266,f283,f289,f294,f321,f351,f364,f384,f398,f411,f417,f441,f457,f465,f467])).

fof(f467,plain,
    ( ~ spl4_1
    | spl4_7
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f466,f461,f128,f93])).

fof(f93,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f128,plain,
    ( spl4_7
  <=> sK3 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f461,plain,
    ( spl4_43
  <=> sK2 = k4_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f466,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43 ),
    inference(superposition,[],[f58,f463])).

fof(f463,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f461])).

fof(f58,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f465,plain,
    ( ~ spl4_1
    | ~ spl4_22
    | ~ spl4_23
    | spl4_43
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f459,f377,f461,f277,f273,f93])).

fof(f273,plain,
    ( spl4_22
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f277,plain,
    ( spl4_23
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f377,plain,
    ( spl4_32
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f459,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32 ),
    inference(superposition,[],[f60,f379])).

fof(f379,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f377])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f457,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl4_40 ),
    inference(unit_resulting_resolution,[],[f79,f440])).

fof(f440,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl4_40
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f441,plain,
    ( ~ spl4_3
    | ~ spl4_6
    | ~ spl4_40
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f436,f354,f281,f146,f438,f124,f102])).

fof(f102,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,
    ( spl4_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f146,plain,
    ( spl4_9
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f281,plain,
    ( spl4_24
  <=> ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f354,plain,
    ( spl4_30
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f436,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f435,f356])).

fof(f356,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f354])).

fof(f435,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( sK1 != sK1
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(superposition,[],[f282,f148])).

fof(f148,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f282,plain,
    ( ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f281])).

fof(f417,plain,
    ( spl4_33
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl4_33
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_33
    | ~ spl4_36 ),
    inference(superposition,[],[f383,f409])).

fof(f409,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl4_36
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f383,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f411,plain,
    ( ~ spl4_18
    | spl4_36
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f405,f395,f407,f209])).

fof(f209,plain,
    ( spl4_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f395,plain,
    ( spl4_34
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f405,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_34 ),
    inference(superposition,[],[f66,f397])).

fof(f397,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f395])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f398,plain,
    ( spl4_34
    | ~ spl4_23
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_6
    | ~ spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f390,f175,f209,f124,f188,f142,f277,f395])).

fof(f142,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f188,plain,
    ( spl4_15
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f175,plain,
    ( spl4_12
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

% (6989)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f390,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f384,plain,
    ( spl4_32
    | ~ spl4_1
    | ~ spl4_22
    | ~ spl4_6
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_33
    | ~ spl4_9
    | ~ spl4_19
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f375,f354,f213,f146,f381,f277,f102,f124,f273,f93,f377])).

fof(f213,plain,
    ( spl4_19
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f375,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_19
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_19
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f373,f148])).

fof(f373,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_19
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f372,f215])).

fof(f215,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f213])).

fof(f372,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f81,f356])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f364,plain,
    ( ~ spl4_6
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_8
    | spl4_30
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f361,f318,f354,f142,f277,f209,f124])).

fof(f318,plain,
    ( spl4_27
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f361,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f76,f320])).

fof(f320,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f318])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f351,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f50,f41,f43,f52,f316,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

% (6987)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f316,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_26
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f321,plain,
    ( ~ spl4_26
    | spl4_27 ),
    inference(avatar_split_clause,[],[f311,f318,f314])).

fof(f311,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f249,f45])).

fof(f249,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f294,plain,
    ( ~ spl4_12
    | spl4_13
    | spl4_14 ),
    inference(avatar_split_clause,[],[f291,f183,f179,f175])).

fof(f179,plain,
    ( spl4_13
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f183,plain,
    ( spl4_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f291,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f43,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f289,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl4_23 ),
    inference(subsumption_resolution,[],[f41,f279])).

fof(f279,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f277])).

fof(f283,plain,
    ( spl4_22
    | ~ spl4_1
    | ~ spl4_23
    | spl4_24
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f269,f213,f281,f277,f93,f273])).

fof(f269,plain,
    ( ! [X3] :
        ( sK1 != k2_relat_1(X3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,sK3))
        | ~ v1_relat_1(sK3)
        | v2_funct_1(sK3) )
    | ~ spl4_19 ),
    inference(superposition,[],[f63,f215])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f266,plain,(
    ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f47,f185])).

fof(f185,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f47,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f256,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f43,f211])).

fof(f211,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f217,plain,
    ( ~ spl4_18
    | spl4_19
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f206,f179,f213,f209])).

fof(f206,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_13 ),
    inference(superposition,[],[f65,f181])).

fof(f181,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f203,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f51,f190])).

fof(f190,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f201,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f42,f177])).

fof(f177,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f42,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f52,f144])).

fof(f144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f150,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f140,f146,f142])).

fof(f140,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f44,f66])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f138,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f50,f126])).

fof(f126,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f133,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f46,f122])).

fof(f122,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f131,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f118,f128,f124,f120,f102])).

fof(f118,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f49,f60])).

fof(f49,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f64,f108])).

fof(f108,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f64,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f109,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f90,f106,f102])).

fof(f90,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f52])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f100,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f89,f97,f93])).

fof(f89,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:19:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (7003)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (7011)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (6995)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.57  % (6995)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f468,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(avatar_sat_refutation,[],[f100,f109,f113,f117,f131,f133,f138,f150,f152,f201,f203,f217,f256,f266,f283,f289,f294,f321,f351,f364,f384,f398,f411,f417,f441,f457,f465,f467])).
% 1.36/0.57  fof(f467,plain,(
% 1.36/0.57    ~spl4_1 | spl4_7 | ~spl4_43),
% 1.36/0.57    inference(avatar_split_clause,[],[f466,f461,f128,f93])).
% 1.36/0.57  fof(f93,plain,(
% 1.36/0.57    spl4_1 <=> v1_relat_1(sK3)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.57  fof(f128,plain,(
% 1.36/0.57    spl4_7 <=> sK3 = k4_relat_1(sK2)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.36/0.57  fof(f461,plain,(
% 1.36/0.57    spl4_43 <=> sK2 = k4_relat_1(sK3)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.36/0.57  fof(f466,plain,(
% 1.36/0.57    sK3 = k4_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_43),
% 1.36/0.57    inference(superposition,[],[f58,f463])).
% 1.36/0.57  fof(f463,plain,(
% 1.36/0.57    sK2 = k4_relat_1(sK3) | ~spl4_43),
% 1.36/0.57    inference(avatar_component_clause,[],[f461])).
% 1.36/0.57  fof(f58,plain,(
% 1.36/0.57    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f21])).
% 1.36/0.57  fof(f21,plain,(
% 1.36/0.57    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f3])).
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.36/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.36/0.57  fof(f465,plain,(
% 1.36/0.57    ~spl4_1 | ~spl4_22 | ~spl4_23 | spl4_43 | ~spl4_32),
% 1.36/0.57    inference(avatar_split_clause,[],[f459,f377,f461,f277,f273,f93])).
% 1.36/0.57  fof(f273,plain,(
% 1.36/0.57    spl4_22 <=> v2_funct_1(sK3)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.36/0.57  fof(f277,plain,(
% 1.36/0.57    spl4_23 <=> v1_funct_1(sK3)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.36/0.57  fof(f377,plain,(
% 1.36/0.57    spl4_32 <=> sK2 = k2_funct_1(sK3)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.36/0.57  fof(f459,plain,(
% 1.36/0.57    sK2 = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_32),
% 1.36/0.57    inference(superposition,[],[f60,f379])).
% 1.36/0.57  fof(f379,plain,(
% 1.36/0.57    sK2 = k2_funct_1(sK3) | ~spl4_32),
% 1.36/0.57    inference(avatar_component_clause,[],[f377])).
% 1.36/0.57  fof(f60,plain,(
% 1.36/0.57    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(flattening,[],[f23])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f4])).
% 1.71/0.58  fof(f4,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.71/0.58  fof(f457,plain,(
% 1.71/0.58    spl4_40),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f454])).
% 1.71/0.58  fof(f454,plain,(
% 1.71/0.58    $false | spl4_40),
% 1.71/0.58    inference(unit_resulting_resolution,[],[f79,f440])).
% 1.71/0.58  fof(f440,plain,(
% 1.71/0.58    ~v2_funct_1(k6_partfun1(sK0)) | spl4_40),
% 1.71/0.58    inference(avatar_component_clause,[],[f438])).
% 1.71/0.58  fof(f438,plain,(
% 1.71/0.58    spl4_40 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.71/0.58  fof(f79,plain,(
% 1.71/0.58    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.71/0.58    inference(definition_unfolding,[],[f55,f53])).
% 1.71/0.58  fof(f53,plain,(
% 1.71/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f15])).
% 1.71/0.58  fof(f15,axiom,(
% 1.71/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.71/0.58  fof(f55,plain,(
% 1.71/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f5])).
% 1.71/0.58  fof(f5,axiom,(
% 1.71/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.71/0.58  fof(f441,plain,(
% 1.71/0.58    ~spl4_3 | ~spl4_6 | ~spl4_40 | ~spl4_9 | ~spl4_24 | ~spl4_30),
% 1.71/0.58    inference(avatar_split_clause,[],[f436,f354,f281,f146,f438,f124,f102])).
% 1.71/0.58  fof(f102,plain,(
% 1.71/0.58    spl4_3 <=> v1_relat_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.58  fof(f124,plain,(
% 1.71/0.58    spl4_6 <=> v1_funct_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.58  fof(f146,plain,(
% 1.71/0.58    spl4_9 <=> sK1 = k2_relat_1(sK2)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.71/0.58  fof(f281,plain,(
% 1.71/0.58    spl4_24 <=> ! [X3] : (sK1 != k2_relat_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.71/0.58  fof(f354,plain,(
% 1.71/0.58    spl4_30 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.71/0.58  fof(f436,plain,(
% 1.71/0.58    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_9 | ~spl4_24 | ~spl4_30)),
% 1.71/0.58    inference(forward_demodulation,[],[f435,f356])).
% 1.71/0.58  fof(f356,plain,(
% 1.71/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_30),
% 1.71/0.58    inference(avatar_component_clause,[],[f354])).
% 1.71/0.58  fof(f435,plain,(
% 1.71/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_9 | ~spl4_24)),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f433])).
% 1.71/0.58  fof(f433,plain,(
% 1.71/0.58    sK1 != sK1 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_9 | ~spl4_24)),
% 1.71/0.58    inference(superposition,[],[f282,f148])).
% 1.71/0.58  fof(f148,plain,(
% 1.71/0.58    sK1 = k2_relat_1(sK2) | ~spl4_9),
% 1.71/0.58    inference(avatar_component_clause,[],[f146])).
% 1.71/0.58  fof(f282,plain,(
% 1.71/0.58    ( ! [X3] : (sK1 != k2_relat_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | ~spl4_24),
% 1.71/0.58    inference(avatar_component_clause,[],[f281])).
% 1.71/0.58  fof(f417,plain,(
% 1.71/0.58    spl4_33 | ~spl4_36),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f416])).
% 1.71/0.58  fof(f416,plain,(
% 1.71/0.58    $false | (spl4_33 | ~spl4_36)),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f412])).
% 1.71/0.58  fof(f412,plain,(
% 1.71/0.58    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_33 | ~spl4_36)),
% 1.71/0.58    inference(superposition,[],[f383,f409])).
% 1.71/0.58  fof(f409,plain,(
% 1.71/0.58    sK0 = k2_relat_1(sK3) | ~spl4_36),
% 1.71/0.58    inference(avatar_component_clause,[],[f407])).
% 1.71/0.58  fof(f407,plain,(
% 1.71/0.58    spl4_36 <=> sK0 = k2_relat_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.71/0.58  fof(f383,plain,(
% 1.71/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_33),
% 1.71/0.58    inference(avatar_component_clause,[],[f381])).
% 1.71/0.58  fof(f381,plain,(
% 1.71/0.58    spl4_33 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.71/0.58  fof(f411,plain,(
% 1.71/0.58    ~spl4_18 | spl4_36 | ~spl4_34),
% 1.71/0.58    inference(avatar_split_clause,[],[f405,f395,f407,f209])).
% 1.71/0.58  fof(f209,plain,(
% 1.71/0.58    spl4_18 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.71/0.58  fof(f395,plain,(
% 1.71/0.58    spl4_34 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.71/0.58  fof(f405,plain,(
% 1.71/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_34),
% 1.71/0.58    inference(superposition,[],[f66,f397])).
% 1.71/0.58  fof(f397,plain,(
% 1.71/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_34),
% 1.71/0.58    inference(avatar_component_clause,[],[f395])).
% 1.71/0.58  fof(f66,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f30])).
% 1.71/0.58  fof(f30,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(ennf_transformation,[],[f9])).
% 1.71/0.58  fof(f9,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.71/0.58  fof(f398,plain,(
% 1.71/0.58    spl4_34 | ~spl4_23 | ~spl4_8 | ~spl4_15 | ~spl4_6 | ~spl4_18 | ~spl4_12),
% 1.71/0.58    inference(avatar_split_clause,[],[f390,f175,f209,f124,f188,f142,f277,f395])).
% 1.71/0.58  fof(f142,plain,(
% 1.71/0.58    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.71/0.58  fof(f188,plain,(
% 1.71/0.58    spl4_15 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.71/0.58  fof(f175,plain,(
% 1.71/0.58    spl4_12 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.71/0.58  % (6989)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.71/0.58  fof(f390,plain,(
% 1.71/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.71/0.58    inference(resolution,[],[f73,f45])).
% 1.71/0.58  fof(f45,plain,(
% 1.71/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f20,plain,(
% 1.71/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.71/0.58    inference(flattening,[],[f19])).
% 1.71/0.58  fof(f19,plain,(
% 1.71/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f18])).
% 1.71/0.58  fof(f18,negated_conjecture,(
% 1.71/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.71/0.58    inference(negated_conjecture,[],[f17])).
% 1.71/0.58  fof(f17,conjecture,(
% 1.71/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.71/0.58  fof(f73,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.71/0.58    inference(cnf_transformation,[],[f34])).
% 1.71/0.58  fof(f34,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.71/0.58    inference(flattening,[],[f33])).
% 1.71/0.58  fof(f33,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.71/0.58    inference(ennf_transformation,[],[f16])).
% 1.71/0.58  fof(f16,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.71/0.58  fof(f384,plain,(
% 1.71/0.58    spl4_32 | ~spl4_1 | ~spl4_22 | ~spl4_6 | ~spl4_3 | ~spl4_23 | ~spl4_33 | ~spl4_9 | ~spl4_19 | ~spl4_30),
% 1.71/0.58    inference(avatar_split_clause,[],[f375,f354,f213,f146,f381,f277,f102,f124,f273,f93,f377])).
% 1.71/0.58  fof(f213,plain,(
% 1.71/0.58    spl4_19 <=> sK1 = k1_relat_1(sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.71/0.58  fof(f375,plain,(
% 1.71/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_19 | ~spl4_30)),
% 1.71/0.58    inference(trivial_inequality_removal,[],[f374])).
% 1.71/0.58  fof(f374,plain,(
% 1.71/0.58    sK1 != sK1 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_19 | ~spl4_30)),
% 1.71/0.58    inference(forward_demodulation,[],[f373,f148])).
% 1.71/0.58  fof(f373,plain,(
% 1.71/0.58    sK1 != k2_relat_1(sK2) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_19 | ~spl4_30)),
% 1.71/0.58    inference(forward_demodulation,[],[f372,f215])).
% 1.71/0.58  fof(f215,plain,(
% 1.71/0.58    sK1 = k1_relat_1(sK3) | ~spl4_19),
% 1.71/0.58    inference(avatar_component_clause,[],[f213])).
% 1.71/0.58  fof(f372,plain,(
% 1.71/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_30),
% 1.71/0.58    inference(superposition,[],[f81,f356])).
% 1.71/0.58  fof(f81,plain,(
% 1.71/0.58    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.71/0.58    inference(definition_unfolding,[],[f61,f53])).
% 1.71/0.58  fof(f61,plain,(
% 1.71/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.71/0.58    inference(cnf_transformation,[],[f26])).
% 1.71/0.58  fof(f26,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.58    inference(flattening,[],[f25])).
% 1.71/0.58  fof(f25,plain,(
% 1.71/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.58    inference(ennf_transformation,[],[f7])).
% 1.71/0.58  fof(f7,axiom,(
% 1.71/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.71/0.58  fof(f364,plain,(
% 1.71/0.58    ~spl4_6 | ~spl4_18 | ~spl4_23 | ~spl4_8 | spl4_30 | ~spl4_27),
% 1.71/0.58    inference(avatar_split_clause,[],[f361,f318,f354,f142,f277,f209,f124])).
% 1.71/0.58  fof(f318,plain,(
% 1.71/0.58    spl4_27 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.71/0.58  fof(f361,plain,(
% 1.71/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_27),
% 1.71/0.58    inference(superposition,[],[f76,f320])).
% 1.71/0.58  fof(f320,plain,(
% 1.71/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_27),
% 1.71/0.58    inference(avatar_component_clause,[],[f318])).
% 1.71/0.58  fof(f76,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f38])).
% 1.71/0.58  fof(f38,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.58    inference(flattening,[],[f37])).
% 1.71/0.58  fof(f37,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.58    inference(ennf_transformation,[],[f14])).
% 1.71/0.58  fof(f14,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.71/0.58  fof(f351,plain,(
% 1.71/0.58    spl4_26),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f339])).
% 1.71/0.58  fof(f339,plain,(
% 1.71/0.58    $false | spl4_26),
% 1.71/0.58    inference(unit_resulting_resolution,[],[f50,f41,f43,f52,f316,f78])).
% 1.71/0.58  fof(f78,plain,(
% 1.71/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f40])).
% 1.71/0.58  fof(f40,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.58    inference(flattening,[],[f39])).
% 1.71/0.58  % (6987)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.71/0.58  fof(f39,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.58    inference(ennf_transformation,[],[f12])).
% 1.71/0.58  fof(f12,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.71/0.58  fof(f316,plain,(
% 1.71/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_26),
% 1.71/0.58    inference(avatar_component_clause,[],[f314])).
% 1.71/0.58  fof(f314,plain,(
% 1.71/0.58    spl4_26 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.71/0.58  fof(f52,plain,(
% 1.71/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f43,plain,(
% 1.71/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f41,plain,(
% 1.71/0.58    v1_funct_1(sK3)),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f50,plain,(
% 1.71/0.58    v1_funct_1(sK2)),
% 1.71/0.58    inference(cnf_transformation,[],[f20])).
% 1.71/0.58  fof(f321,plain,(
% 1.71/0.58    ~spl4_26 | spl4_27),
% 1.71/0.58    inference(avatar_split_clause,[],[f311,f318,f314])).
% 1.71/0.58  fof(f311,plain,(
% 1.71/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/0.58    inference(resolution,[],[f249,f45])).
% 1.71/0.58  fof(f249,plain,(
% 1.71/0.58    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.71/0.58    inference(resolution,[],[f75,f57])).
% 1.71/0.58  fof(f57,plain,(
% 1.71/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.71/0.58    inference(cnf_transformation,[],[f13])).
% 1.71/0.58  fof(f13,axiom,(
% 1.71/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.71/0.58  fof(f75,plain,(
% 1.71/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f36])).
% 1.71/0.58  fof(f36,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(flattening,[],[f35])).
% 1.71/0.58  fof(f35,plain,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.58    inference(ennf_transformation,[],[f10])).
% 1.71/0.58  fof(f10,axiom,(
% 1.71/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.71/0.58  fof(f294,plain,(
% 1.71/0.58    ~spl4_12 | spl4_13 | spl4_14),
% 1.71/0.58    inference(avatar_split_clause,[],[f291,f183,f179,f175])).
% 1.71/0.58  fof(f179,plain,(
% 1.71/0.58    spl4_13 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.71/0.58  fof(f183,plain,(
% 1.71/0.58    spl4_14 <=> k1_xboole_0 = sK0),
% 1.71/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.71/0.58  fof(f291,plain,(
% 1.71/0.58    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.58    inference(resolution,[],[f43,f72])).
% 1.71/0.58  fof(f72,plain,(
% 1.71/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.71/0.58    inference(cnf_transformation,[],[f32])).
% 1.71/0.58  fof(f32,plain,(
% 1.71/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(flattening,[],[f31])).
% 1.71/0.58  fof(f31,plain,(
% 1.71/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.58    inference(ennf_transformation,[],[f11])).
% 1.71/0.58  fof(f11,axiom,(
% 1.71/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.58  fof(f289,plain,(
% 1.71/0.58    spl4_23),
% 1.71/0.58    inference(avatar_contradiction_clause,[],[f288])).
% 1.71/0.59  fof(f288,plain,(
% 1.71/0.59    $false | spl4_23),
% 1.71/0.59    inference(subsumption_resolution,[],[f41,f279])).
% 1.71/0.59  fof(f279,plain,(
% 1.71/0.59    ~v1_funct_1(sK3) | spl4_23),
% 1.71/0.59    inference(avatar_component_clause,[],[f277])).
% 1.71/0.59  fof(f283,plain,(
% 1.71/0.59    spl4_22 | ~spl4_1 | ~spl4_23 | spl4_24 | ~spl4_19),
% 1.71/0.59    inference(avatar_split_clause,[],[f269,f213,f281,f277,f93,f273])).
% 1.71/0.59  fof(f269,plain,(
% 1.71/0.59    ( ! [X3] : (sK1 != k2_relat_1(X3) | ~v1_funct_1(sK3) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,sK3)) | ~v1_relat_1(sK3) | v2_funct_1(sK3)) ) | ~spl4_19),
% 1.71/0.59    inference(superposition,[],[f63,f215])).
% 1.71/0.59  fof(f63,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f28])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.71/0.59    inference(flattening,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.71/0.59  fof(f266,plain,(
% 1.71/0.59    ~spl4_14),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f257])).
% 1.71/0.59  fof(f257,plain,(
% 1.71/0.59    $false | ~spl4_14),
% 1.71/0.59    inference(subsumption_resolution,[],[f47,f185])).
% 1.71/0.59  fof(f185,plain,(
% 1.71/0.59    k1_xboole_0 = sK0 | ~spl4_14),
% 1.71/0.59    inference(avatar_component_clause,[],[f183])).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    k1_xboole_0 != sK0),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f256,plain,(
% 1.71/0.59    spl4_18),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f255])).
% 1.71/0.59  fof(f255,plain,(
% 1.71/0.59    $false | spl4_18),
% 1.71/0.59    inference(subsumption_resolution,[],[f43,f211])).
% 1.71/0.59  fof(f211,plain,(
% 1.71/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_18),
% 1.71/0.59    inference(avatar_component_clause,[],[f209])).
% 1.71/0.59  fof(f217,plain,(
% 1.71/0.59    ~spl4_18 | spl4_19 | ~spl4_13),
% 1.71/0.59    inference(avatar_split_clause,[],[f206,f179,f213,f209])).
% 1.71/0.59  fof(f206,plain,(
% 1.71/0.59    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_13),
% 1.71/0.59    inference(superposition,[],[f65,f181])).
% 1.71/0.59  fof(f181,plain,(
% 1.71/0.59    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_13),
% 1.71/0.59    inference(avatar_component_clause,[],[f179])).
% 1.71/0.59  fof(f65,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f29])).
% 1.71/0.59  fof(f29,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f8])).
% 1.71/0.59  fof(f8,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.59  fof(f203,plain,(
% 1.71/0.59    spl4_15),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f202])).
% 1.71/0.59  fof(f202,plain,(
% 1.71/0.59    $false | spl4_15),
% 1.71/0.59    inference(subsumption_resolution,[],[f51,f190])).
% 1.71/0.59  fof(f190,plain,(
% 1.71/0.59    ~v1_funct_2(sK2,sK0,sK1) | spl4_15),
% 1.71/0.59    inference(avatar_component_clause,[],[f188])).
% 1.71/0.59  fof(f51,plain,(
% 1.71/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f201,plain,(
% 1.71/0.59    spl4_12),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f200])).
% 1.71/0.59  fof(f200,plain,(
% 1.71/0.59    $false | spl4_12),
% 1.71/0.59    inference(subsumption_resolution,[],[f42,f177])).
% 1.71/0.59  fof(f177,plain,(
% 1.71/0.59    ~v1_funct_2(sK3,sK1,sK0) | spl4_12),
% 1.71/0.59    inference(avatar_component_clause,[],[f175])).
% 1.71/0.59  fof(f42,plain,(
% 1.71/0.59    v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f152,plain,(
% 1.71/0.59    spl4_8),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f151])).
% 1.71/0.59  fof(f151,plain,(
% 1.71/0.59    $false | spl4_8),
% 1.71/0.59    inference(subsumption_resolution,[],[f52,f144])).
% 1.71/0.59  fof(f144,plain,(
% 1.71/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_8),
% 1.71/0.59    inference(avatar_component_clause,[],[f142])).
% 1.71/0.59  fof(f150,plain,(
% 1.71/0.59    ~spl4_8 | spl4_9),
% 1.71/0.59    inference(avatar_split_clause,[],[f140,f146,f142])).
% 1.71/0.59  fof(f140,plain,(
% 1.71/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.59    inference(superposition,[],[f44,f66])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f138,plain,(
% 1.71/0.59    spl4_6),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f137])).
% 1.71/0.59  fof(f137,plain,(
% 1.71/0.59    $false | spl4_6),
% 1.71/0.59    inference(subsumption_resolution,[],[f50,f126])).
% 1.71/0.59  fof(f126,plain,(
% 1.71/0.59    ~v1_funct_1(sK2) | spl4_6),
% 1.71/0.59    inference(avatar_component_clause,[],[f124])).
% 1.71/0.59  fof(f133,plain,(
% 1.71/0.59    spl4_5),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f132])).
% 1.71/0.59  fof(f132,plain,(
% 1.71/0.59    $false | spl4_5),
% 1.71/0.59    inference(subsumption_resolution,[],[f46,f122])).
% 1.71/0.59  fof(f122,plain,(
% 1.71/0.59    ~v2_funct_1(sK2) | spl4_5),
% 1.71/0.59    inference(avatar_component_clause,[],[f120])).
% 1.71/0.59  fof(f120,plain,(
% 1.71/0.59    spl4_5 <=> v2_funct_1(sK2)),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    v2_funct_1(sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f131,plain,(
% 1.71/0.59    ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7),
% 1.71/0.59    inference(avatar_split_clause,[],[f118,f128,f124,f120,f102])).
% 1.71/0.59  fof(f118,plain,(
% 1.71/0.59    sK3 != k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.71/0.59    inference(superposition,[],[f49,f60])).
% 1.71/0.59  fof(f49,plain,(
% 1.71/0.59    sK3 != k2_funct_1(sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f20])).
% 1.71/0.59  fof(f117,plain,(
% 1.71/0.59    spl4_4),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f114])).
% 1.71/0.59  fof(f114,plain,(
% 1.71/0.59    $false | spl4_4),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f64,f108])).
% 1.71/0.59  fof(f108,plain,(
% 1.71/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.71/0.59    inference(avatar_component_clause,[],[f106])).
% 1.71/0.59  fof(f106,plain,(
% 1.71/0.59    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.59  fof(f64,plain,(
% 1.71/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f2])).
% 1.71/0.59  fof(f2,axiom,(
% 1.71/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.59  fof(f113,plain,(
% 1.71/0.59    spl4_2),
% 1.71/0.59    inference(avatar_contradiction_clause,[],[f110])).
% 1.71/0.59  fof(f110,plain,(
% 1.71/0.59    $false | spl4_2),
% 1.71/0.59    inference(unit_resulting_resolution,[],[f64,f99])).
% 1.71/0.59  fof(f99,plain,(
% 1.71/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.71/0.59    inference(avatar_component_clause,[],[f97])).
% 1.71/0.59  fof(f97,plain,(
% 1.71/0.59    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.71/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.59  fof(f109,plain,(
% 1.71/0.59    spl4_3 | ~spl4_4),
% 1.71/0.59    inference(avatar_split_clause,[],[f90,f106,f102])).
% 1.71/0.59  fof(f90,plain,(
% 1.71/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.71/0.59    inference(resolution,[],[f59,f52])).
% 1.71/0.59  fof(f59,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f22])).
% 1.71/0.59  fof(f22,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f1])).
% 1.71/0.59  fof(f1,axiom,(
% 1.71/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.59  fof(f100,plain,(
% 1.71/0.59    spl4_1 | ~spl4_2),
% 1.71/0.59    inference(avatar_split_clause,[],[f89,f97,f93])).
% 1.71/0.59  fof(f89,plain,(
% 1.71/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.71/0.59    inference(resolution,[],[f59,f43])).
% 1.71/0.59  % SZS output end Proof for theBenchmark
% 1.71/0.59  % (6995)------------------------------
% 1.71/0.59  % (6995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (6995)Termination reason: Refutation
% 1.71/0.59  
% 1.71/0.59  % (6995)Memory used [KB]: 6524
% 1.71/0.59  % (6995)Time elapsed: 0.159 s
% 1.71/0.59  % (6995)------------------------------
% 1.71/0.59  % (6995)------------------------------
% 1.71/0.59  % (6982)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.71/0.59  % (6981)Success in time 0.234 s
%------------------------------------------------------------------------------
