%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 162 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  291 ( 633 expanded)
%              Number of equality atoms :   71 ( 153 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f79,f86,f90,f119,f120,f177,f180,f189,f193,f197])).

fof(f197,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f192,f32])).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f192,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_20
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f193,plain,
    ( ~ spl3_20
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_split_clause,[],[f149,f129,f60,f191])).

fof(f60,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f129,plain,
    ( spl3_14
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_4
    | spl3_14 ),
    inference(resolution,[],[f140,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_14 ),
    inference(resolution,[],[f130,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f189,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f186,f175,f52,f48,f56])).

fof(f56,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( spl3_1
  <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( spl3_2
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f175,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f186,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f176,f53])).

fof(f53,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f175])).

fof(f180,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f146,f84,f88,f100])).

fof(f100,plain,
    ( spl3_11
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f88,plain,
    ( spl3_9
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f84,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f146,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f85,f46])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f177,plain,
    ( ~ spl3_14
    | spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f125,f116,f175,f129])).

fof(f116,plain,
    ( spl3_13
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) )
    | ~ spl3_13 ),
    inference(superposition,[],[f68,f117])).

fof(f117,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f120,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f119,plain,
    ( ~ spl3_4
    | spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f113,f73,f116,f60])).

fof(f73,plain,
    ( spl3_6
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f113,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f74])).

fof(f74,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f90,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f81,f76,f64,f88])).

fof(f64,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f81,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f65,f77])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f65,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f86,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f80,f76,f60,f84])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f61,f77])).

fof(f79,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f60,f64,f76,f73])).

fof(f71,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f36,f61])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0) )
   => ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

% (5260)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f9,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0) )
           => ! [X2] :
                ( ( v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f48])).

fof(f29,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (5266)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (5266)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (5262)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (5275)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f50,f54,f58,f62,f66,f79,f86,f90,f119,f120,f177,f180,f189,f193,f197])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl3_20),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f195])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    $false | spl3_20),
% 0.20/0.47    inference(resolution,[],[f192,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl3_20 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ~spl3_20 | ~spl3_4 | spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f149,f129,f60,f191])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl3_14 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | (~spl3_4 | spl3_14)),
% 0.20/0.47    inference(resolution,[],[f140,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_14),
% 0.20/0.47    inference(resolution,[],[f130,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~v1_relat_1(sK1) | spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f129])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~spl3_3 | spl3_1 | ~spl3_2 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f186,f175,f52,f48,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_1 <=> k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl3_2 <=> v5_relat_1(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl3_19 <=> ! [X0] : (~v5_relat_1(X0,sK0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_19)),
% 0.20/0.47    inference(resolution,[],[f176,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    v5_relat_1(sK2,sK0) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X0] : (~v5_relat_1(X0,sK0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X0)) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f175])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    spl3_11 | ~spl3_9 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f146,f84,f88,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_11 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl3_9 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl3_8),
% 0.20/0.47    inference(resolution,[],[f85,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.47    inference(equality_resolution,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~spl3_14 | spl3_19 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f125,f116,f175,f129])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl3_13 <=> sK0 = k1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~v5_relat_1(X0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK1))) ) | ~spl3_13),
% 0.20/0.47    inference(superposition,[],[f68,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK1) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v5_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v5_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(resolution,[],[f30,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~spl3_4 | spl3_13 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f113,f73,f116,f60])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_6 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_6),
% 0.20/0.47    inference(superposition,[],[f35,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f73])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl3_9 | ~spl3_5 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f81,f76,f64,f88])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_5 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_7 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl3_5 | ~spl3_7)),
% 0.20/0.47    inference(superposition,[],[f65,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    v1_funct_2(sK1,sK0,sK0) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_8 | ~spl3_4 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f80,f76,f60,f84])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_4 | ~spl3_7)),
% 0.20/0.47    inference(superposition,[],[f61,f77])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl3_6 | spl3_7 | ~spl3_5 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f71,f60,f64,f76,f73])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f36,f61])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f64])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.48  % (5260)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0)) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f60])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f56])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f52])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v5_relat_1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f48])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (5266)------------------------------
% 0.20/0.48  % (5266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5266)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (5266)Memory used [KB]: 10746
% 0.20/0.48  % (5266)Time elapsed: 0.058 s
% 0.20/0.48  % (5266)------------------------------
% 0.20/0.48  % (5266)------------------------------
% 0.20/0.48  % (5256)Success in time 0.123 s
%------------------------------------------------------------------------------
