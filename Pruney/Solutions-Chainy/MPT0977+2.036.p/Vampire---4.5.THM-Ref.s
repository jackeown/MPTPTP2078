%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 172 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  252 ( 420 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f68,f70,f96,f105,f107,f109,f111,f117,f127,f133,f135,f141,f147,f150])).

fof(f150,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f126,f78])).

fof(f78,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f126,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_12
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f147,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f140,f76])).

fof(f76,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f140,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_14
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f141,plain,
    ( ~ spl3_4
    | ~ spl3_14
    | spl3_13 ),
    inference(avatar_split_clause,[],[f136,f130,f138,f65])).

fof(f65,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( spl3_13
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f136,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f132,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f132,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f135,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f122,f74])).

fof(f74,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f42,f31])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_11
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f133,plain,
    ( ~ spl3_4
    | ~ spl3_13
    | ~ spl3_12
    | spl3_9 ),
    inference(avatar_split_clause,[],[f128,f102,f124,f130,f65])).

fof(f102,plain,
    ( spl3_9
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f128,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(superposition,[],[f104,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f33,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f104,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f127,plain,
    ( ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | spl3_10 ),
    inference(avatar_split_clause,[],[f118,f114,f124,f120,f65])).

fof(f114,plain,
    ( spl3_10
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(superposition,[],[f116,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f116,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( ~ spl3_4
    | ~ spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f112,f93,f114,f65])).

fof(f93,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f112,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(superposition,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f100,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f100,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_8
  <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f109,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f87,f34])).

fof(f87,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_5
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f91,f31])).

fof(f91,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f105,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_2 ),
    inference(avatar_split_clause,[],[f83,f54,f102,f98,f89])).

fof(f54,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f56,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f56,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f96,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f82,f50,f93,f89,f85])).

fof(f50,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f52,f45])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f63,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f63,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_3
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f58,f65,f61])).

fof(f58,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f57,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10944)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (10946)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (10943)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (10945)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (10946)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f57,f68,f70,f96,f105,f107,f109,f111,f117,f127,f133,f135,f141,f147,f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    spl3_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    $false | spl3_12),
% 0.22/0.48    inference(resolution,[],[f126,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.48    inference(resolution,[],[f48,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.48    inference(condensation,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f124])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl3_12 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    spl3_14),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    $false | spl3_14),
% 0.22/0.48    inference(resolution,[],[f140,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    v5_relat_1(sK2,sK1)),
% 0.22/0.48    inference(resolution,[],[f43,f31])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ~v5_relat_1(sK2,sK1) | spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl3_14 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_14 | spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f136,f130,f138,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl3_13 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.49    inference(resolution,[],[f132,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    $false | spl3_11),
% 0.22/0.49    inference(resolution,[],[f122,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    v4_relat_1(sK2,sK0)),
% 0.22/0.49    inference(resolution,[],[f42,f31])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,sK0) | spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl3_11 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_13 | ~spl3_12 | spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f102,f124,f130,f65])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl3_9 <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.49    inference(superposition,[],[f104,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f38,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_11 | ~spl3_12 | spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f118,f114,f124,f120,f65])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_10 <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.49    inference(superposition,[],[f116,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ~spl3_4 | ~spl3_10 | spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f93,f114,f65])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_7 <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.49    inference(superposition,[],[f95,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f37,f33])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    $false | spl3_8),
% 0.22/0.49    inference(resolution,[],[f100,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl3_8 <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    $false | spl3_5),
% 0.22/0.49    inference(resolution,[],[f87,f34])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_5 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    $false | spl3_6),
% 0.22/0.49    inference(resolution,[],[f91,f31])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~spl3_6 | ~spl3_8 | ~spl3_9 | spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f83,f54,f102,f98,f89])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.49    inference(superposition,[],[f56,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~spl3_5 | ~spl3_6 | ~spl3_7 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f82,f50,f93,f89,f85])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_1),
% 0.22/0.49    inference(superposition,[],[f52,f45])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    $false | spl3_3),
% 0.22/0.49    inference(resolution,[],[f63,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl3_3 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~spl3_3 | spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f65,f61])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f35,f31])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f54,f50])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10946)------------------------------
% 0.22/0.49  % (10946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10946)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10946)Memory used [KB]: 6140
% 0.22/0.49  % (10946)Time elapsed: 0.039 s
% 0.22/0.49  % (10946)------------------------------
% 0.22/0.49  % (10946)------------------------------
% 0.22/0.49  % (10941)Success in time 0.127 s
%------------------------------------------------------------------------------
