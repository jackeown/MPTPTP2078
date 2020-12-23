%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 182 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  300 ( 867 expanded)
%              Number of equality atoms :   89 ( 257 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f73,f82,f94,f111,f127,f128,f154,f157,f183,f195,f197,f198])).

fof(f198,plain,
    ( spl4_21
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f191,f181,f51,f47,f169])).

fof(f169,plain,
    ( spl4_21
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f47,plain,
    ( spl4_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f51,plain,
    ( spl4_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f181,plain,
    ( spl4_22
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f191,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f189,f48])).

fof(f48,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f189,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_22 ),
    inference(resolution,[],[f182,f52])).

fof(f52,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f197,plain,
    ( sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f195,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f190,f181,f55,f193])).

fof(f193,plain,
    ( spl4_24
  <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f55,plain,
    ( spl4_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f190,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(resolution,[],[f182,f56])).

fof(f56,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f183,plain,
    ( ~ spl4_18
    | ~ spl4_8
    | ~ spl4_5
    | spl4_22
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f135,f124,f181,f59,f71,f138])).

fof(f138,plain,
    ( spl4_18
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f71,plain,
    ( spl4_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f59,plain,
    ( spl4_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f124,plain,
    ( spl4_17
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_17 ),
    inference(superposition,[],[f27,f125])).

fof(f125,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f124])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f157,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f156,f79,f63,f88])).

fof(f88,plain,
    ( spl4_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f63,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f79,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f156,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f64,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f154,plain,
    ( ~ spl4_6
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl4_6
    | spl4_18 ),
    inference(subsumption_resolution,[],[f64,f151])).

fof(f151,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_18 ),
    inference(resolution,[],[f139,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f139,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f128,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f127,plain,
    ( ~ spl4_6
    | spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f121,f76,f124,f63])).

fof(f76,plain,
    ( spl4_9
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(superposition,[],[f30,f77])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,
    ( spl4_15
    | ~ spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f104,f88,f92,f108])).

fof(f108,plain,
    ( spl4_15
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f92,plain,
    ( spl4_12
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f104,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f94,plain,
    ( spl4_12
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f84,f79,f67,f92])).

fof(f67,plain,
    ( spl4_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f84,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(superposition,[],[f68,f80])).

fof(f68,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f82,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f74,f63,f67,f79,f76])).

fof(f74,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f31,f64])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f19,f71])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f69,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f20,f67])).

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f63])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f43,plain,
    ( spl4_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f26,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (18443)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (18445)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (18434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (18435)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (18437)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (18435)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (18442)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f73,f82,f94,f111,f127,f128,f154,f157,f183,f195,f197,f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    spl4_21 | ~spl4_2 | ~spl4_3 | ~spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f191,f181,f51,f47,f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl4_21 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    spl4_2 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl4_3 <=> r2_hidden(sK3,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    spl4_22 <=> ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_22)),
% 0.20/0.51    inference(forward_demodulation,[],[f189,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f47])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl4_3 | ~spl4_22)),
% 0.20/0.51    inference(resolution,[],[f182,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    r2_hidden(sK3,sK0) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f51])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1) ) | ~spl4_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f181])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK2 = sK3),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    spl4_24 | ~spl4_4 | ~spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f190,f181,f55,f193])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    spl4_24 <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl4_4 <=> r2_hidden(sK2,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_4 | ~spl4_22)),
% 0.20/0.51    inference(resolution,[],[f182,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r2_hidden(sK2,sK0) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ~spl4_18 | ~spl4_8 | ~spl4_5 | spl4_22 | ~spl4_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f135,f124,f181,f59,f71,f138])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl4_18 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    spl4_8 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl4_5 <=> v2_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl4_17 <=> sK0 = k1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl4_17),
% 0.20/0.51    inference(superposition,[],[f27,f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK1) | ~spl4_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    spl4_11 | ~spl4_6 | ~spl4_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f156,f79,f63,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl4_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl4_10 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_6 | ~spl4_10)),
% 0.20/0.52    inference(forward_demodulation,[],[f64,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl4_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f79])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ~spl4_6 | spl4_18),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    $false | (~spl4_6 | spl4_18)),
% 0.20/0.52    inference(subsumption_resolution,[],[f64,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_18),
% 0.20/0.52    inference(resolution,[],[f139,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | spl4_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f138])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ~spl4_6 | spl4_17 | ~spl4_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f121,f76,f124,f63])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl4_9 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 0.20/0.52    inference(superposition,[],[f30,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f76])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl4_15 | ~spl4_12 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f104,f88,f92,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl4_15 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl4_12 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl4_11),
% 0.20/0.52    inference(resolution,[],[f89,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f88])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl4_12 | ~spl4_7 | ~spl4_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f84,f79,f67,f92])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    spl4_7 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl4_7 | ~spl4_10)),
% 0.20/0.52    inference(superposition,[],[f68,f80])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0) | ~spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f67])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    spl4_9 | spl4_10 | ~spl4_7 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f74,f63,f67,f79,f76])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_6),
% 0.20/0.52    inference(resolution,[],[f31,f64])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f71])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.52    inference(flattening,[],[f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f5])).
% 0.20/0.52  fof(f5,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f67])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f63])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f59])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    v2_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f51])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    r2_hidden(sK3,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f47])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl4_1 <=> sK2 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    sK2 != sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18435)------------------------------
% 0.20/0.52  % (18435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18435)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18435)Memory used [KB]: 10746
% 0.20/0.52  % (18435)Time elapsed: 0.071 s
% 0.20/0.52  % (18435)------------------------------
% 0.20/0.52  % (18435)------------------------------
% 0.20/0.52  % (18428)Success in time 0.155 s
%------------------------------------------------------------------------------
