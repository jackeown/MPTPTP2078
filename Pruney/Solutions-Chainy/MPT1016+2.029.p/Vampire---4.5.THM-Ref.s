%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 449 expanded)
%              Number of leaves         :   28 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  636 (3141 expanded)
%              Number of equality atoms :  130 ( 872 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f94,f195,f213,f392,f429,f435,f449,f450,f487,f519])).

fof(f519,plain,
    ( spl8_9
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl8_9
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f517,f128])).

fof(f128,plain,
    ( ~ sP0(sK3)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_9
  <=> sP0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f517,plain,
    ( sP0(sK3)
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f515])).

fof(f515,plain,
    ( sK6(sK3) != sK6(sK3)
    | sP0(sK3)
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(superposition,[],[f57,f511])).

fof(f511,plain,
    ( sK7(sK3) = sK6(sK3)
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f510,f193])).

fof(f193,plain,
    ( r2_hidden(sK6(sK3),sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_16
  <=> r2_hidden(sK6(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f510,plain,
    ( sK7(sK3) = sK6(sK3)
    | ~ r2_hidden(sK6(sK3),sK2)
    | ~ spl8_11 ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | sK7(sK3) = X0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_11
  <=> ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | sK7(sK3) = X0
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f57,plain,(
    ! [X0] :
      ( sK6(X0) != sK7(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f487,plain,
    ( spl8_11
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f486,f131,f127,f92,f135])).

fof(f92,plain,
    ( spl8_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,sK2)
        | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f131,plain,
    ( spl8_10
  <=> r2_hidden(sK7(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f486,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | ~ r2_hidden(X0,sK2)
        | sK7(sK3) = X0 )
    | ~ spl8_6
    | spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f485,f128])).

fof(f485,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | ~ r2_hidden(X0,sK2)
        | sK7(sK3) = X0
        | sP0(sK3) )
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f479,f132])).

fof(f132,plain,
    ( r2_hidden(sK7(sK3),sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f479,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(sK7(sK3),sK2)
        | sK7(sK3) = X0
        | sP0(sK3) )
    | ~ spl8_6 ),
    inference(superposition,[],[f93,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
        | ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,sK2)
        | X4 = X5 )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f450,plain,
    ( spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f183,f131,f127])).

fof(f183,plain,
    ( r2_hidden(sK7(sK3),sK2)
    | sP0(sK3) ),
    inference(resolution,[],[f151,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f151,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK3))
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f146,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f146,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f145,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
        & r2_hidden(X3,sK2)
        & r2_hidden(X2,sK2) )
   => ( sK4 != sK5
      & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f449,plain,
    ( spl8_9
    | spl8_16 ),
    inference(avatar_split_clause,[],[f407,f191,f127])).

fof(f407,plain,
    ( r2_hidden(sK6(sK3),sK2)
    | sP0(sK3) ),
    inference(resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f435,plain,
    ( ~ spl8_1
    | spl8_27
    | ~ spl8_3
    | spl8_18 ),
    inference(avatar_split_clause,[],[f434,f210,f77,f303,f68])).

fof(f68,plain,
    ( spl8_1
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f303,plain,
    ( spl8_27
  <=> ! [X18,X17] :
        ( k1_xboole_0 = X17
        | ~ v1_funct_2(sK3,X18,X17)
        | ~ r2_hidden(sK5,X18)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f77,plain,
    ( spl8_3
  <=> k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f210,plain,
    ( spl8_18
  <=> sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f434,plain,
    ( ! [X17,X18] :
        ( k1_xboole_0 = X17
        | ~ r2_hidden(sK5,X18)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v1_funct_2(sK3,X18,X17) )
    | ~ spl8_3
    | spl8_18 ),
    inference(subsumption_resolution,[],[f433,f41])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f433,plain,
    ( ! [X17,X18] :
        ( k1_xboole_0 = X17
        | ~ r2_hidden(sK5,X18)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v1_funct_2(sK3,X18,X17)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_3
    | spl8_18 ),
    inference(subsumption_resolution,[],[f295,f211])).

fof(f211,plain,
    ( sK5 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f295,plain,
    ( ! [X17,X18] :
        ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
        | k1_xboole_0 = X17
        | ~ r2_hidden(sK5,X18)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v1_funct_2(sK3,X18,X17)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_3 ),
    inference(superposition,[],[f66,f79])).

fof(f79,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f429,plain,
    ( ~ spl8_4
    | spl8_17
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl8_4
    | spl8_17
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f417,f214])).

fof(f214,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0)
    | spl8_17 ),
    inference(resolution,[],[f208,f111])).

fof(f111,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f208,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_17
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f417,plain,
    ( r2_hidden(sK5,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(backward_demodulation,[],[f84,f414])).

fof(f414,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f413,f84])).

fof(f413,plain,
    ( ~ r2_hidden(sK5,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f412,f42])).

fof(f42,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f412,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ r2_hidden(sK5,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_27 ),
    inference(resolution,[],[f304,f43])).

fof(f304,plain,
    ( ! [X17,X18] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v1_funct_2(sK3,X18,X17)
        | ~ r2_hidden(sK5,X18)
        | k1_xboole_0 = X17 )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f303])).

fof(f84,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_4
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f392,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f379,f362])).

fof(f362,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f320,f111])).

fof(f320,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f319,f101])).

fof(f101,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f99,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f319,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f318,f41])).

fof(f318,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f317,f69])).

fof(f69,plain,
    ( v2_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f317,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f307,f74])).

fof(f74,plain,
    ( sK4 != sK5
    | spl8_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_2
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f307,plain,
    ( sK4 = sK5
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_18 ),
    inference(superposition,[],[f212,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f212,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f379,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f89,f375])).

fof(f375,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f374,f42])).

fof(f374,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f373,f89])).

fof(f373,plain,
    ( ~ r2_hidden(sK4,sK2)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(resolution,[],[f316,f43])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r2_hidden(sK4,X1)
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f315,f41])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f314,f69])).

fof(f314,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | spl8_2
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f306,f74])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( sK4 = sK5
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK4,X1)
        | ~ v2_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl8_18 ),
    inference(superposition,[],[f212,f66])).

fof(f89,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_5
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f213,plain,
    ( ~ spl8_17
    | spl8_18
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f204,f77,f68,f210,f206])).

fof(f204,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f203,f101])).

fof(f203,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f202,f41])).

fof(f202,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f199,f69])).

fof(f199,plain,
    ( sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(superposition,[],[f61,f79])).

fof(f195,plain,
    ( spl8_1
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f178,f127,f68])).

fof(f178,plain,
    ( v2_funct_1(sK3)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f177,f41])).

fof(f177,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f176,f101])).

fof(f176,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl8_9 ),
    inference(resolution,[],[f129,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f58,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f28,f27])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f129,plain,
    ( sP0(sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f94,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f44,f92,f68])).

fof(f44,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f45,f87,f68])).

fof(f45,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f46,f82,f68])).

fof(f46,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f47,f77,f68])).

fof(f47,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f48,f72,f68])).

fof(f48,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (4789)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (4790)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (4780)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (4787)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (4789)Refutation not found, incomplete strategy% (4789)------------------------------
% 0.21/0.51  % (4789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4788)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (4789)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4789)Memory used [KB]: 6140
% 0.21/0.51  % (4789)Time elapsed: 0.081 s
% 0.21/0.51  % (4789)------------------------------
% 0.21/0.51  % (4789)------------------------------
% 0.21/0.51  % (4799)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (4792)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (4783)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (4786)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (4797)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (4793)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (4782)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (4776)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (4782)Refutation not found, incomplete strategy% (4782)------------------------------
% 0.21/0.52  % (4782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4782)Memory used [KB]: 10618
% 0.21/0.52  % (4782)Time elapsed: 0.082 s
% 0.21/0.52  % (4782)------------------------------
% 0.21/0.52  % (4782)------------------------------
% 0.21/0.52  % (4776)Refutation not found, incomplete strategy% (4776)------------------------------
% 0.21/0.52  % (4776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4776)Memory used [KB]: 10618
% 0.21/0.52  % (4776)Time elapsed: 0.124 s
% 0.21/0.52  % (4776)------------------------------
% 0.21/0.52  % (4776)------------------------------
% 0.21/0.53  % (4777)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (4800)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (4781)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (4780)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f520,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f94,f195,f213,f392,f429,f435,f449,f450,f487,f519])).
% 0.21/0.53  fof(f519,plain,(
% 0.21/0.53    spl8_9 | ~spl8_11 | ~spl8_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f518])).
% 0.21/0.53  fof(f518,plain,(
% 0.21/0.53    $false | (spl8_9 | ~spl8_11 | ~spl8_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f517,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~sP0(sK3) | spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl8_9 <=> sP0(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f517,plain,(
% 0.21/0.53    sP0(sK3) | (~spl8_11 | ~spl8_16)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f515])).
% 0.21/0.53  fof(f515,plain,(
% 0.21/0.53    sK6(sK3) != sK6(sK3) | sP0(sK3) | (~spl8_11 | ~spl8_16)),
% 0.21/0.53    inference(superposition,[],[f57,f511])).
% 0.21/0.53  fof(f511,plain,(
% 0.21/0.53    sK7(sK3) = sK6(sK3) | (~spl8_11 | ~spl8_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f510,f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    r2_hidden(sK6(sK3),sK2) | ~spl8_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl8_16 <=> r2_hidden(sK6(sK3),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.53  fof(f510,plain,(
% 0.21/0.53    sK7(sK3) = sK6(sK3) | ~r2_hidden(sK6(sK3),sK2) | ~spl8_11),
% 0.21/0.53    inference(equality_resolution,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2)) ) | ~spl8_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl8_11 <=> ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | sK7(sK3) = X0 | ~r2_hidden(X0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (sK6(X0) != sK7(X0) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.53    inference(rectify,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f487,plain,(
% 0.21/0.53    spl8_11 | ~spl8_6 | spl8_9 | ~spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f486,f131,f127,f92,f135])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl8_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl8_10 <=> r2_hidden(sK7(sK3),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f486,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | ~r2_hidden(X0,sK2) | sK7(sK3) = X0) ) | (~spl8_6 | spl8_9 | ~spl8_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f485,f128])).
% 0.21/0.53  fof(f485,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | ~r2_hidden(X0,sK2) | sK7(sK3) = X0 | sP0(sK3)) ) | (~spl8_6 | ~spl8_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f479,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    r2_hidden(sK7(sK3),sK2) | ~spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f131])).
% 0.21/0.53  fof(f479,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK3,X0) != k1_funct_1(sK3,sK6(sK3)) | ~r2_hidden(X0,sK2) | ~r2_hidden(sK7(sK3),sK2) | sK7(sK3) = X0 | sP0(sK3)) ) | ~spl8_6),
% 0.21/0.53    inference(superposition,[],[f93,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK2) | X4 = X5) ) | ~spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f450,plain,(
% 0.21/0.53    spl8_9 | spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f183,f131,f127])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    r2_hidden(sK7(sK3),sK2) | sP0(sK3)),
% 0.21/0.53    inference(resolution,[],[f151,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK3)) | r2_hidden(X1,sK2)) )),
% 0.21/0.53    inference(resolution,[],[f146,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f145,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) => (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(rectify,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(superposition,[],[f64,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    spl8_9 | spl8_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f407,f191,f127])).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    r2_hidden(sK6(sK3),sK2) | sP0(sK3)),
% 0.21/0.53    inference(resolution,[],[f151,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    ~spl8_1 | spl8_27 | ~spl8_3 | spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f434,f210,f77,f303,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl8_1 <=> v2_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    spl8_27 <=> ! [X18,X17] : (k1_xboole_0 = X17 | ~v1_funct_2(sK3,X18,X17) | ~r2_hidden(sK5,X18) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl8_3 <=> k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    spl8_18 <=> sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    ( ! [X17,X18] : (k1_xboole_0 = X17 | ~r2_hidden(sK5,X18) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) | ~v1_funct_2(sK3,X18,X17)) ) | (~spl8_3 | spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f433,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    ( ! [X17,X18] : (k1_xboole_0 = X17 | ~r2_hidden(sK5,X18) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) | ~v1_funct_2(sK3,X18,X17) | ~v1_funct_1(sK3)) ) | (~spl8_3 | spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f295,f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    sK5 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f210])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    ( ! [X17,X18] : (sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | k1_xboole_0 = X17 | ~r2_hidden(sK5,X18) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) | ~v1_funct_2(sK3,X18,X17) | ~v1_funct_1(sK3)) ) | ~spl8_3),
% 0.21/0.53    inference(superposition,[],[f66,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    ~spl8_4 | spl8_17 | ~spl8_27),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    $false | (~spl8_4 | spl8_17 | ~spl8_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f417,f214])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ~r2_hidden(sK5,k1_xboole_0) | spl8_17),
% 0.21/0.53    inference(resolution,[],[f208,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f60,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl8_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    spl8_17 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    r2_hidden(sK5,k1_xboole_0) | (~spl8_4 | ~spl8_27)),
% 0.21/0.53    inference(backward_demodulation,[],[f84,f414])).
% 0.21/0.53  fof(f414,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | (~spl8_4 | ~spl8_27)),
% 0.21/0.53    inference(subsumption_resolution,[],[f413,f84])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    ~r2_hidden(sK5,sK2) | k1_xboole_0 = sK2 | ~spl8_27),
% 0.21/0.53    inference(subsumption_resolution,[],[f412,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK2,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK2,sK2) | ~r2_hidden(sK5,sK2) | k1_xboole_0 = sK2 | ~spl8_27),
% 0.21/0.53    inference(resolution,[],[f304,f43])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    ( ! [X17,X18] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) | ~v1_funct_2(sK3,X18,X17) | ~r2_hidden(sK5,X18) | k1_xboole_0 = X17) ) | ~spl8_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f303])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    r2_hidden(sK5,sK2) | ~spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl8_4 <=> r2_hidden(sK5,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_18),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f391])).
% 0.21/0.53  fof(f391,plain,(
% 0.21/0.53    $false | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f379,f362])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k1_xboole_0) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(resolution,[],[f320,f111])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k1_relat_1(sK3)) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f319,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK2))),
% 0.21/0.53    inference(resolution,[],[f50,f43])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f318,f41])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f317,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    v2_funct_1(sK3) | ~spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f68])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f307,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    sK4 != sK5 | spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl8_2 <=> sK4 = sK5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    sK4 = sK5 | ~r2_hidden(sK4,k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_18),
% 0.21/0.53    inference(superposition,[],[f212,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f210])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    r2_hidden(sK4,k1_xboole_0) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_18)),
% 0.21/0.53    inference(backward_demodulation,[],[f89,f375])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f374,f42])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK2,sK2) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f373,f89])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    ~r2_hidden(sK4,sK2) | k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK2,sK2) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(resolution,[],[f316,f43])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(sK4,X1) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0)) ) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f315,f41])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | (~spl8_1 | spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f314,f69])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | (spl8_2 | ~spl8_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f306,f74])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK4 = sK5 | k1_xboole_0 = X0 | ~r2_hidden(sK4,X1) | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | ~v1_funct_1(sK3)) ) | ~spl8_18),
% 0.21/0.53    inference(superposition,[],[f212,f66])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    r2_hidden(sK4,sK2) | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl8_5 <=> r2_hidden(sK4,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ~spl8_17 | spl8_18 | ~spl8_1 | ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f204,f77,f68,f210,f206])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl8_1 | ~spl8_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f203,f101])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f202,f41])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f199,f69])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    sK5 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.53    inference(superposition,[],[f61,f79])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl8_1 | ~spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f178,f127,f68])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    v2_funct_1(sK3) | ~spl8_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f41])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl8_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f101])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | v2_funct_1(sK3) | ~spl8_9),
% 0.21/0.53    inference(resolution,[],[f129,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f58,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(definition_folding,[],[f17,f28,f27])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    sP0(sK3) | ~spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl8_1 | spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f92,f68])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~spl8_1 | spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f87,f68])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~spl8_1 | spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f82,f68])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~spl8_1 | spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f77,f68])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f72,f68])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    sK4 != sK5 | ~v2_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4780)------------------------------
% 0.21/0.53  % (4780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4780)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4780)Memory used [KB]: 6396
% 0.21/0.53  % (4780)Time elapsed: 0.111 s
% 0.21/0.53  % (4780)------------------------------
% 0.21/0.53  % (4780)------------------------------
% 0.21/0.53  % (4778)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (4772)Success in time 0.175 s
%------------------------------------------------------------------------------
