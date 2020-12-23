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
% DateTime   : Thu Dec  3 13:00:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 218 expanded)
%              Number of leaves         :   36 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  442 ( 806 expanded)
%              Number of equality atoms :   97 ( 170 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f99,f111,f122,f126,f136,f139,f152,f157,f173,f197,f209,f266,f283,f302,f318,f319])).

fof(f319,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK6(sK3,sK2),sK0)
    | ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f318,plain,
    ( ~ spl7_2
    | spl7_39
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f312,f260,f315,f78])).

fof(f78,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f315,plain,
    ( spl7_39
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f260,plain,
    ( spl7_29
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f312,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_29 ),
    inference(superposition,[],[f54,f261])).

fof(f261,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f260])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f302,plain,
    ( spl7_13
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl7_13
    | ~ spl7_33 ),
    inference(resolution,[],[f282,f141])).

fof(f141,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl7_13 ),
    inference(resolution,[],[f135,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f135,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_13
  <=> v5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f282,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl7_33
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f283,plain,
    ( spl7_33
    | ~ spl7_2
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f271,f263,f78,f281])).

fof(f263,plain,
    ( spl7_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f271,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_30 ),
    inference(superposition,[],[f79,f264])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f266,plain,
    ( spl7_29
    | spl7_30
    | ~ spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f258,f78,f82,f263,f260])).

fof(f82,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f258,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f57,f79])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f209,plain,
    ( ~ spl7_24
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f205,f195,f207])).

fof(f207,plain,
    ( spl7_24
  <=> r2_hidden(sK6(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f195,plain,
    ( spl7_22
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f205,plain,
    ( ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl7_22 ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl7_22 ),
    inference(superposition,[],[f41,f196])).

fof(f196,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f41,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK2 != k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f197,plain,
    ( spl7_22
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f192,f171,f124,f195])).

fof(f124,plain,
    ( spl7_11
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f171,plain,
    ( spl7_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f192,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(resolution,[],[f172,f125])).

fof(f125,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( ~ spl7_12
    | spl7_18
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f169,f86,f171,f131])).

fof(f131,plain,
    ( spl7_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f86,plain,
    ( spl7_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f66,f87])).

fof(f87,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f66,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f157,plain,
    ( spl7_15
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f153,f150,f124,f155])).

fof(f155,plain,
    ( spl7_15
  <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f150,plain,
    ( spl7_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f153,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(resolution,[],[f151,f125])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( ~ spl7_12
    | spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f148,f86,f150,f131])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f67,f87])).

fof(f67,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,
    ( ~ spl7_2
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl7_2
    | spl7_12 ),
    inference(subsumption_resolution,[],[f79,f137])).

fof(f137,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_12 ),
    inference(resolution,[],[f132,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f136,plain,
    ( ~ spl7_12
    | ~ spl7_13
    | spl7_10 ),
    inference(avatar_split_clause,[],[f128,f120,f134,f131])).

fof(f120,plain,
    ( spl7_10
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f128,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(resolution,[],[f121,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f121,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f126,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f114,f109,f74,f124])).

fof(f74,plain,
    ( spl7_1
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f109,plain,
    ( spl7_8
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f114,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(superposition,[],[f75,f110])).

fof(f110,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f75,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f122,plain,
    ( ~ spl7_10
    | spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f113,f109,f97,f120])).

fof(f97,plain,
    ( spl7_6
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f113,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f98,f110])).

fof(f98,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f111,plain,
    ( spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f106,f78,f109])).

fof(f106,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f99,plain,
    ( ~ spl7_6
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f95,f90,f74,f97])).

fof(f90,plain,
    ( spl7_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f95,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f94,f75])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f63,f91])).

fof(f91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f92,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f42,f90])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f88,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f40,f74])).

fof(f40,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:05:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (6733)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (6739)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (6741)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (6731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (6731)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f99,f111,f122,f126,f136,f139,f152,f157,f173,f197,f209,f266,f283,f302,f318,f319])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    sK0 != k1_relat_1(sK3) | r2_hidden(sK6(sK3,sK2),sK0) | ~r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~spl7_2 | spl7_39 | ~spl7_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f312,f260,f315,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    spl7_39 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    spl7_29 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_29),
% 0.22/0.50    inference(superposition,[],[f54,f261])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f260])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    spl7_13 | ~spl7_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f298])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    $false | (spl7_13 | ~spl7_33)),
% 0.22/0.50    inference(resolution,[],[f282,f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl7_13),
% 0.22/0.50    inference(resolution,[],[f135,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~v5_relat_1(sK3,k1_xboole_0) | spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl7_13 <=> v5_relat_1(sK3,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f281])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    spl7_33 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    spl7_33 | ~spl7_2 | ~spl7_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f271,f263,f78,f281])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    spl7_30 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_30)),
% 0.22/0.50    inference(superposition,[],[f79,f264])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl7_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f263])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    spl7_29 | spl7_30 | ~spl7_3 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f258,f78,f82,f263,f260])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl7_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_2),
% 0.22/0.50    inference(resolution,[],[f57,f79])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~spl7_24 | ~spl7_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f205,f195,f207])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    spl7_24 <=> r2_hidden(sK6(sK3,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl7_22 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl7_22),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f204])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    sK2 != sK2 | ~r2_hidden(sK6(sK3,sK2),sK0) | ~spl7_22),
% 0.22/0.50    inference(superposition,[],[f41,f196])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~spl7_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f195])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl7_22 | ~spl7_11 | ~spl7_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f192,f171,f124,f195])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl7_11 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl7_18 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | (~spl7_11 | ~spl7_18)),
% 0.22/0.50    inference(resolution,[],[f172,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f124])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0) ) | ~spl7_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f171])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ~spl7_12 | spl7_18 | ~spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f169,f86,f171,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl7_12 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl7_4 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f66,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl7_15 | ~spl7_11 | ~spl7_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f153,f150,f124,f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl7_15 <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl7_14 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | (~spl7_11 | ~spl7_14)),
% 0.22/0.50    inference(resolution,[],[f151,f125])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))) ) | ~spl7_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f150])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ~spl7_12 | spl7_14 | ~spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f148,f86,f150,f131])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f67,f87])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~spl7_2 | spl7_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    $false | (~spl7_2 | spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f79,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_12),
% 0.22/0.50    inference(resolution,[],[f132,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl7_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ~spl7_12 | ~spl7_13 | spl7_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f120,f134,f131])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl7_10 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~v5_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | spl7_10),
% 0.22/0.50    inference(resolution,[],[f121,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f120])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl7_11 | ~spl7_1 | ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f114,f109,f74,f124])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl7_1 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl7_8 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    r2_hidden(sK2,k2_relat_1(sK3)) | (~spl7_1 | ~spl7_8)),
% 0.22/0.50    inference(superposition,[],[f75,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~spl7_10 | spl7_6 | ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f113,f109,f97,f120])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl7_6 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | (spl7_6 | ~spl7_8)),
% 0.22/0.50    inference(superposition,[],[f98,f110])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0) | spl7_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl7_8 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f106,f78,f109])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_2),
% 0.22/0.50    inference(resolution,[],[f55,f79])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~spl7_6 | ~spl7_1 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f90,f74,f97])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl7_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ~r1_tarski(k2_relset_1(sK0,sK1,sK3),k1_xboole_0) | (~spl7_1 | ~spl7_5)),
% 0.22/0.50    inference(resolution,[],[f94,f75])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,k1_xboole_0)) ) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f93,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f63,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f90])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f86])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f82])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f78])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f74])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (6731)------------------------------
% 0.22/0.50  % (6731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6731)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (6731)Memory used [KB]: 10874
% 0.22/0.50  % (6731)Time elapsed: 0.020 s
% 0.22/0.50  % (6731)------------------------------
% 0.22/0.50  % (6731)------------------------------
% 0.22/0.51  % (6729)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (6722)Success in time 0.139 s
%------------------------------------------------------------------------------
