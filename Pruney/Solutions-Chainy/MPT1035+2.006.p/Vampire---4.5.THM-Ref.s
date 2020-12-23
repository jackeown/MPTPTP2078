%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 374 expanded)
%              Number of leaves         :   40 ( 160 expanded)
%              Depth                    :   11
%              Number of atoms          :  660 (2221 expanded)
%              Number of equality atoms :  149 ( 639 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f86,f93,f97,f101,f105,f109,f113,f138,f145,f160,f172,f215,f218,f253,f262,f350,f351,f370,f375,f379,f383,f386,f391,f395,f403,f404])).

fof(f404,plain,
    ( spl6_21
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f315,f99,f91,f174])).

fof(f174,plain,
    ( spl6_21
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f91,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f99,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f315,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f100,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f100,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f403,plain,
    ( ~ spl6_21
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl6_21
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f175,f347])).

fof(f347,plain,
    ( ! [X1] : ~ v1_funct_2(sK3,k1_xboole_0,X1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl6_38
  <=> ! [X1] : ~ v1_funct_2(sK3,k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f175,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f395,plain,
    ( spl6_2
    | ~ spl6_15
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f393,f389,f136,f75])).

fof(f75,plain,
    ( spl6_2
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f136,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f389,plain,
    ( spl6_43
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f393,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl6_15
    | ~ spl6_43 ),
    inference(resolution,[],[f137,f390])).

fof(f390,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f389])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f391,plain,
    ( ~ spl6_10
    | spl6_43
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f387,f79,f389,f107])).

fof(f107,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f79,plain,
    ( spl6_3
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f387,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(superposition,[],[f80,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f80,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f386,plain,
    ( ~ spl6_29
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_9
    | spl6_15
    | ~ spl6_41
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f385,f169,f72,f368,f136,f103,f200,f111,f247])).

fof(f247,plain,
    ( spl6_29
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f111,plain,
    ( spl6_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f200,plain,
    ( spl6_26
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f103,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f368,plain,
    ( spl6_41
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f72,plain,
    ( spl6_1
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f169,plain,
    ( spl6_20
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f384,f170])).

fof(f170,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f82,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f82,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f383,plain,
    ( ~ spl6_29
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_9
    | spl6_1
    | ~ spl6_41
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f382,f365,f169,f368,f72,f103,f200,f111,f247])).

fof(f365,plain,
    ( spl6_40
  <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f382,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f381,f170])).

fof(f381,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_40 ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_40 ),
    inference(superposition,[],[f49,f366])).

fof(f366,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f365])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f379,plain,
    ( ~ spl6_10
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl6_10
    | spl6_42 ),
    inference(subsumption_resolution,[],[f108,f376])).

fof(f376,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl6_42 ),
    inference(resolution,[],[f374,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f374,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl6_42
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f375,plain,
    ( ~ spl6_29
    | ~ spl6_42
    | spl6_41 ),
    inference(avatar_split_clause,[],[f371,f368,f373,f247])).

fof(f371,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl6_41 ),
    inference(resolution,[],[f369,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f369,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f368])).

fof(f370,plain,
    ( spl6_1
    | ~ spl6_9
    | ~ spl6_26
    | spl6_40
    | ~ spl6_41
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f359,f251,f169,f368,f365,f200,f103,f72])).

fof(f251,plain,
    ( spl6_30
  <=> ! [X0] :
        ( r1_partfun1(sK2,X0)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f359,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | r1_partfun1(sK2,sK3)
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(superposition,[],[f252,f170])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK2,X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f351,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f350,plain,
    ( spl6_38
    | spl6_33
    | ~ spl6_18
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f349,f158,f158,f273,f346])).

fof(f273,plain,
    ( spl6_33
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f158,plain,
    ( spl6_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(sK3)
        | ~ v1_funct_2(sK3,k1_xboole_0,X0) )
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f343,f65])).

fof(f65,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f343,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_funct_2(sK3,k1_xboole_0,X0) )
    | ~ spl6_18 ),
    inference(superposition,[],[f56,f327])).

fof(f327,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK3)
        | ~ v1_funct_2(sK3,k1_xboole_0,X0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f159,f124])).

fof(f124,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f70,f65])).

fof(f70,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f262,plain,
    ( ~ spl6_28
    | ~ spl6_10
    | spl6_29 ),
    inference(avatar_split_clause,[],[f255,f247,f107,f213])).

fof(f213,plain,
    ( spl6_28
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f255,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_10
    | spl6_29 ),
    inference(resolution,[],[f254,f108])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_29 ),
    inference(resolution,[],[f248,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f248,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f253,plain,
    ( ~ spl6_29
    | ~ spl6_11
    | spl6_30
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f245,f136,f251,f111,f247])).

fof(f245,plain,
    ( ! [X0] :
        ( r1_partfun1(sK2,X0)
        | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) )
    | ~ spl6_15 ),
    inference(resolution,[],[f48,f137])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f218,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl6_28 ),
    inference(resolution,[],[f214,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f214,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( ~ spl6_28
    | ~ spl6_7
    | spl6_26 ),
    inference(avatar_split_clause,[],[f211,f200,f95,f213])).

fof(f95,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f211,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_7
    | spl6_26 ),
    inference(resolution,[],[f206,f96])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_26 ),
    inference(resolution,[],[f201,f46])).

fof(f201,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f200])).

fof(f172,plain,
    ( ~ spl6_7
    | spl6_20
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f167,f143,f169,f95])).

fof(f143,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f167,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f56,f144])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f160,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f156,f95,f91,f158])).

fof(f156,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f148,f65])).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(superposition,[],[f96,f92])).

fof(f145,plain,
    ( ~ spl6_7
    | spl6_5
    | spl6_16
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f139,f99,f143,f88,f95])).

fof(f88,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f139,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(resolution,[],[f58,f100])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f138,plain,
    ( ~ spl6_10
    | spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f133,f84,f136,f107])).

fof(f84,plain,
    ( spl6_4
  <=> ! [X5] :
        ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl6_4 ),
    inference(superposition,[],[f85,f56])).

fof(f85,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f113,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f37,f111])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X5] :
          ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
                & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
            | r1_partfun1(sK2,X3) )
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
              & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
          | ~ r1_partfun1(sK2,X3) )
        & ( ! [X5] :
              ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
          | r1_partfun1(sK2,X3) )
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ( ? [X4] :
            ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
            & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
        | ~ r1_partfun1(sK2,sK3) )
      & ( ! [X5] :
            ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
        | r1_partfun1(sK2,sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
        & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
   => ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f109,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f38,f107])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f39,f103])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

% (15986)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f40,f99])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f41,f95])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f42,f91,f88])).

fof(f42,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f43,f84,f72])).

fof(f43,plain,(
    ! [X5] :
      ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f44,f79,f72])).

fof(f44,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f45,f75,f72])).

fof(f45,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (15980)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (15981)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (15981)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (15988)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (15989)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f77,f81,f86,f93,f97,f101,f105,f109,f113,f138,f145,f160,f172,f215,f218,f253,f262,f350,f351,f370,f375,f379,f383,f386,f391,f395,f403,f404])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    spl6_21 | ~spl6_6 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f315,f99,f91,f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    spl6_21 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl6_6 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl6_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl6_6 | ~spl6_8)),
% 0.21/0.50    inference(superposition,[],[f100,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    ~spl6_21 | ~spl6_38),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f401])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    $false | (~spl6_21 | ~spl6_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f175,f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_funct_2(sK3,k1_xboole_0,X1)) ) | ~spl6_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f346])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    spl6_38 <=> ! [X1] : ~v1_funct_2(sK3,k1_xboole_0,X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f174])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    spl6_2 | ~spl6_15 | ~spl6_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f393,f389,f136,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl6_2 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl6_15 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    spl6_43 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | (~spl6_15 | ~spl6_43)),
% 0.21/0.50    inference(resolution,[],[f137,f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl6_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f389])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~spl6_10 | spl6_43 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f387,f79,f389,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl6_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl6_3 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.21/0.50    inference(superposition,[],[f80,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    ~spl6_29 | ~spl6_11 | ~spl6_26 | ~spl6_9 | spl6_15 | ~spl6_41 | ~spl6_1 | ~spl6_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f385,f169,f72,f368,f136,f103,f200,f111,f247])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    spl6_29 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl6_11 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl6_26 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl6_9 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    spl6_41 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl6_1 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    spl6_20 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl6_1 | ~spl6_20)),
% 0.21/0.50    inference(forward_demodulation,[],[f384,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl6_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f169])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f82,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r1_partfun1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    ~spl6_29 | ~spl6_11 | ~spl6_26 | ~spl6_9 | spl6_1 | ~spl6_41 | ~spl6_20 | ~spl6_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f382,f365,f169,f368,f72,f103,f200,f111,f247])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    spl6_40 <=> k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_20 | ~spl6_40)),
% 0.21/0.50    inference(forward_demodulation,[],[f381,f170])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_40),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_40),
% 0.21/0.50    inference(superposition,[],[f49,f366])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~spl6_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f365])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~spl6_10 | spl6_42),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    $false | (~spl6_10 | spl6_42)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f376])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl6_42),
% 0.21/0.50    inference(resolution,[],[f374,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,sK0) | spl6_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f373])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    spl6_42 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    ~spl6_29 | ~spl6_42 | spl6_41),
% 0.21/0.50    inference(avatar_split_clause,[],[f371,f368,f373,f247])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl6_41),
% 0.21/0.50    inference(resolution,[],[f369,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | spl6_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f368])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl6_1 | ~spl6_9 | ~spl6_26 | spl6_40 | ~spl6_41 | ~spl6_20 | ~spl6_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f359,f251,f169,f368,f365,f200,f103,f72])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    spl6_30 <=> ! [X0] : (r1_partfun1(sK2,X0) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | r1_partfun1(sK2,sK3) | (~spl6_20 | ~spl6_30)),
% 0.21/0.50    inference(superposition,[],[f252,f170])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r1_partfun1(sK2,X0)) ) | ~spl6_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f251])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(sK3) | sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    spl6_38 | spl6_33 | ~spl6_18 | ~spl6_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f349,f158,f158,f273,f346])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    spl6_33 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl6_18 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_funct_2(sK3,k1_xboole_0,X0)) ) | ~spl6_18),
% 0.21/0.50    inference(forward_demodulation,[],[f343,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_funct_2(sK3,k1_xboole_0,X0)) ) | ~spl6_18),
% 0.21/0.50    inference(superposition,[],[f56,f327])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,X0)) ) | ~spl6_18),
% 0.21/0.50    inference(resolution,[],[f159,f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f70,f65])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f158])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ~spl6_28 | ~spl6_10 | spl6_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f255,f247,f107,f213])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl6_28 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_10 | spl6_29)),
% 0.21/0.51    inference(resolution,[],[f254,f108])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_29),
% 0.21/0.51    inference(resolution,[],[f248,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | spl6_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f247])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~spl6_29 | ~spl6_11 | spl6_30 | ~spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f245,f136,f251,f111,f247])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X0] : (r1_partfun1(sK2,X0) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK5(sK2,X0)) = k1_funct_1(sK3,sK5(sK2,X0))) ) | ~spl6_15),
% 0.21/0.51    inference(resolution,[],[f48,f137])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    spl6_28),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    $false | spl6_28),
% 0.21/0.51    inference(resolution,[],[f214,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~spl6_28 | ~spl6_7 | spl6_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f200,f95,f213])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_7 | spl6_26)),
% 0.21/0.51    inference(resolution,[],[f206,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_26),
% 0.21/0.51    inference(resolution,[],[f201,f46])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl6_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f200])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~spl6_7 | spl6_20 | ~spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f143,f169,f95])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 0.21/0.51    inference(superposition,[],[f56,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f143])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl6_18 | ~spl6_6 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f156,f95,f91,f158])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_6 | ~spl6_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f148,f65])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_6 | ~spl6_7)),
% 0.21/0.51    inference(superposition,[],[f96,f92])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~spl6_7 | spl6_5 | spl6_16 | ~spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f99,f143,f88,f95])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl6_5 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.21/0.51    inference(resolution,[],[f58,f100])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~spl6_10 | spl6_15 | ~spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f84,f136,f107])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl6_4 <=> ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl6_4),
% 0.21/0.51    inference(superposition,[],[f85,f56])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X5] : (~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f111])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f27,f26,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) => (k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(rectify,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f107])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f103])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % (15986)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f99])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f95])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~spl6_5 | spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f91,f88])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl6_1 | spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f84,f72])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~spl6_1 | spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f79,f72])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f75,f72])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (15981)------------------------------
% 0.21/0.51  % (15981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15981)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (15981)Memory used [KB]: 10874
% 0.21/0.51  % (15981)Time elapsed: 0.070 s
% 0.21/0.51  % (15981)------------------------------
% 0.21/0.51  % (15981)------------------------------
% 0.21/0.51  % (15974)Success in time 0.146 s
%------------------------------------------------------------------------------
