%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 163 expanded)
%              Number of leaves         :   20 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  351 ( 853 expanded)
%              Number of equality atoms :   82 ( 217 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f72,f77,f92,f100,f101,f107,f128])).

fof(f128,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f41,plain,
    ( sK2 != sK3
    | spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f126,plain,
    ( sK2 = sK3
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f56,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f123,plain,
    ( ~ r2_hidden(sK2,sK0)
    | sK2 = sK3
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK3 = X0 )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f114,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_12
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f114,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f51,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,sK0)
        | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f112,f105])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f111,f91])).

fof(f91,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f111,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f110,f76])).

fof(f76,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f110,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f108,f61])).

fof(f61,plain,
    ( v2_funct_1(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f108,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(superposition,[],[f30,f46])).

fof(f46,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f30,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
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
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f107,plain,
    ( spl6_12
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f106,f94,f84,f103])).

fof(f84,plain,
    ( spl6_9
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f94,plain,
    ( spl6_11
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f106,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f86,f96])).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f86,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f101,plain,
    ( spl6_9
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f82,f64,f84])).

fof(f64,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f82,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f66,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f100,plain,
    ( spl6_11
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f99,f74,f69,f64,f94])).

fof(f69,plain,
    ( spl6_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f98,f76])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f81,f71])).

fof(f71,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f81,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f92,plain,
    ( spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f79,f64,f89])).

fof(f79,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f77,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f22,f74])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f72,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f23,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (11222)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.46  % (11214)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (11214)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f67,f72,f77,f92,f100,f101,f107,f128])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f126,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    sK2 != sK3 | spl6_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl6_1 <=> sK2 = sK3),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    sK2 = sK3 | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f123,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    r2_hidden(sK2,sK0) | ~spl6_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl6_4 <=> r2_hidden(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK0) | sK2 = sK3 | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(equality_resolution,[],[f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,sK0) | sK3 = X0) ) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(forward_demodulation,[],[f114,f105])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1) | ~spl6_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl6_12 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f113,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0) | ~spl6_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl6_3 <=> r2_hidden(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK3,sK0) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl6_2 | ~spl6_5 | ~spl6_8 | ~spl6_10 | ~spl6_12)),
% 0.21/0.46    inference(forward_demodulation,[],[f112,f105])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl6_2 | ~spl6_5 | ~spl6_8 | ~spl6_10)),
% 0.21/0.46    inference(subsumption_resolution,[],[f111,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl6_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl6_10 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl6_2 | ~spl6_5 | ~spl6_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f110,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    v1_funct_1(sK1) | ~spl6_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    spl6_8 <=> v1_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl6_2 | ~spl6_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f108,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    v2_funct_1(sK1) | ~spl6_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl6_5 <=> v2_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X0] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK3 = X0 | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl6_2),
% 0.21/0.46    inference(superposition,[],[f30,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl6_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl6_2 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(rectify,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl6_12 | ~spl6_9 | ~spl6_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f106,f94,f84,f103])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl6_9 <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl6_11 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1) | (~spl6_9 | ~spl6_11)),
% 0.21/0.46    inference(forward_demodulation,[],[f86,f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl6_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl6_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f84])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl6_9 | ~spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f82,f64,f84])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl6_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl6_6),
% 0.21/0.46    inference(resolution,[],[f66,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f64])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    spl6_11 | ~spl6_6 | ~spl6_7 | ~spl6_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f99,f74,f69,f64,f94])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl6_7 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl6_6 | ~spl6_7 | ~spl6_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f76])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl6_6 | ~spl6_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f81,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    v1_funct_2(sK1,sK0,sK0) | ~spl6_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_6),
% 0.21/0.46    inference(resolution,[],[f66,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    spl6_10 | ~spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f79,f64,f89])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl6_6),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f66,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl6_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f74])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl6_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f69])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f64])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl6_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    v2_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl6_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    r2_hidden(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f49])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl6_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f44])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ~spl6_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f39])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    sK2 != sK3),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (11214)------------------------------
% 0.21/0.46  % (11214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11214)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (11214)Memory used [KB]: 6140
% 0.21/0.46  % (11214)Time elapsed: 0.050 s
% 0.21/0.46  % (11214)------------------------------
% 0.21/0.46  % (11214)------------------------------
% 0.21/0.47  % (11200)Success in time 0.104 s
%------------------------------------------------------------------------------
