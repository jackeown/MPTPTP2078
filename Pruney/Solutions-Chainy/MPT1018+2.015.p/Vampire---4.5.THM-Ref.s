%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 191 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  314 ( 887 expanded)
%              Number of equality atoms :   89 ( 257 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f84,f92,f96,f113,f129,f130,f192,f203,f205,f206,f210,f214])).

fof(f214,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_26 ),
    inference(resolution,[],[f209,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f209,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_26
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f210,plain,
    ( ~ spl4_26
    | ~ spl4_6
    | spl4_18 ),
    inference(avatar_split_clause,[],[f162,f140,f65,f208])).

fof(f65,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f140,plain,
    ( spl4_18
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f162,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl4_6
    | spl4_18 ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_18 ),
    inference(resolution,[],[f141,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f141,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f206,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f199,f190,f53,f49,f178])).

fof(f178,plain,
    ( spl4_22
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f49,plain,
    ( spl4_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f190,plain,
    ( spl4_23
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f199,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f197,f50])).

fof(f50,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f197,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(resolution,[],[f191,f54])).

fof(f54,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f205,plain,
    ( sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f203,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f198,f190,f57,f201])).

fof(f201,plain,
    ( spl4_25
  <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f57,plain,
    ( spl4_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f198,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(resolution,[],[f191,f58])).

fof(f58,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f192,plain,
    ( ~ spl4_18
    | ~ spl4_8
    | ~ spl4_5
    | spl4_23
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f137,f126,f190,f61,f73,f140])).

fof(f73,plain,
    ( spl4_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f61,plain,
    ( spl4_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f126,plain,
    ( spl4_17
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f137,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_17 ),
    inference(superposition,[],[f30,f127])).

fof(f127,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f130,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f129,plain,
    ( ~ spl4_6
    | spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f123,f78,f126,f65])).

fof(f78,plain,
    ( spl4_9
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_9 ),
    inference(superposition,[],[f32,f79])).

fof(f79,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( spl4_15
    | ~ spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f106,f90,f94,f110])).

fof(f110,plain,
    ( spl4_15
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f94,plain,
    ( spl4_12
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f90,plain,
    ( spl4_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f106,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f91,f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f96,plain,
    ( spl4_12
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f86,f81,f69,f94])).

fof(f69,plain,
    ( spl4_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f81,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f86,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(superposition,[],[f70,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f70,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f92,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f85,f81,f65,f90])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(superposition,[],[f66,f82])).

fof(f84,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f65,f69,f81,f78])).

fof(f76,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f33,f66])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f73])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f69])).

fof(f21,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f65])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f45,plain,
    ( spl4_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f27,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (10987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (10986)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (10999)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (10987)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (10995)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (10991)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (10991)Refutation not found, incomplete strategy% (10991)------------------------------
% 0.21/0.50  % (10991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10991)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10991)Memory used [KB]: 6012
% 0.21/0.50  % (10991)Time elapsed: 0.065 s
% 0.21/0.50  % (10991)------------------------------
% 0.21/0.50  % (10991)------------------------------
% 1.23/0.51  % SZS output start Proof for theBenchmark
% 1.23/0.51  fof(f215,plain,(
% 1.23/0.51    $false),
% 1.23/0.51    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f84,f92,f96,f113,f129,f130,f192,f203,f205,f206,f210,f214])).
% 1.23/0.51  fof(f214,plain,(
% 1.23/0.51    spl4_26),
% 1.23/0.51    inference(avatar_contradiction_clause,[],[f212])).
% 1.23/0.51  fof(f212,plain,(
% 1.23/0.51    $false | spl4_26),
% 1.23/0.51    inference(resolution,[],[f209,f29])).
% 1.23/0.51  fof(f29,plain,(
% 1.23/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.23/0.51    inference(cnf_transformation,[],[f2])).
% 1.23/0.51  fof(f2,axiom,(
% 1.23/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.23/0.51  fof(f209,plain,(
% 1.23/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl4_26),
% 1.23/0.51    inference(avatar_component_clause,[],[f208])).
% 1.23/0.51  fof(f208,plain,(
% 1.23/0.51    spl4_26 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.23/0.51  fof(f210,plain,(
% 1.23/0.51    ~spl4_26 | ~spl4_6 | spl4_18),
% 1.23/0.51    inference(avatar_split_clause,[],[f162,f140,f65,f208])).
% 1.23/0.51  fof(f65,plain,(
% 1.23/0.51    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.23/0.51  fof(f140,plain,(
% 1.23/0.51    spl4_18 <=> v1_relat_1(sK1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.23/0.51  fof(f162,plain,(
% 1.23/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | (~spl4_6 | spl4_18)),
% 1.23/0.51    inference(resolution,[],[f153,f66])).
% 1.23/0.51  fof(f66,plain,(
% 1.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_6),
% 1.23/0.51    inference(avatar_component_clause,[],[f65])).
% 1.23/0.51  fof(f153,plain,(
% 1.23/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_18),
% 1.23/0.51    inference(resolution,[],[f141,f28])).
% 1.23/0.51  fof(f28,plain,(
% 1.23/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.23/0.51    inference(cnf_transformation,[],[f10])).
% 1.23/0.51  fof(f10,plain,(
% 1.23/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.23/0.51    inference(ennf_transformation,[],[f1])).
% 1.23/0.51  fof(f1,axiom,(
% 1.23/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.23/0.51  fof(f141,plain,(
% 1.23/0.51    ~v1_relat_1(sK1) | spl4_18),
% 1.23/0.51    inference(avatar_component_clause,[],[f140])).
% 1.23/0.51  fof(f206,plain,(
% 1.23/0.51    spl4_22 | ~spl4_2 | ~spl4_3 | ~spl4_23),
% 1.23/0.51    inference(avatar_split_clause,[],[f199,f190,f53,f49,f178])).
% 1.23/0.51  fof(f178,plain,(
% 1.23/0.51    spl4_22 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.23/0.51  fof(f49,plain,(
% 1.23/0.51    spl4_2 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.23/0.51  fof(f53,plain,(
% 1.23/0.51    spl4_3 <=> r2_hidden(sK3,sK0)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.23/0.51  fof(f190,plain,(
% 1.23/0.51    spl4_23 <=> ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.23/0.51  fof(f199,plain,(
% 1.23/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_23)),
% 1.23/0.51    inference(forward_demodulation,[],[f197,f50])).
% 1.23/0.51  fof(f50,plain,(
% 1.23/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_2),
% 1.23/0.51    inference(avatar_component_clause,[],[f49])).
% 1.23/0.51  fof(f197,plain,(
% 1.23/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl4_3 | ~spl4_23)),
% 1.23/0.51    inference(resolution,[],[f191,f54])).
% 1.23/0.51  fof(f54,plain,(
% 1.23/0.51    r2_hidden(sK3,sK0) | ~spl4_3),
% 1.23/0.51    inference(avatar_component_clause,[],[f53])).
% 1.23/0.51  fof(f191,plain,(
% 1.23/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1) ) | ~spl4_23),
% 1.23/0.51    inference(avatar_component_clause,[],[f190])).
% 1.23/0.51  fof(f205,plain,(
% 1.23/0.51    sK2 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK3 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK2 = sK3),
% 1.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 1.23/0.51  fof(f203,plain,(
% 1.23/0.51    spl4_25 | ~spl4_4 | ~spl4_23),
% 1.23/0.51    inference(avatar_split_clause,[],[f198,f190,f57,f201])).
% 1.23/0.51  fof(f201,plain,(
% 1.23/0.51    spl4_25 <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.23/0.51  fof(f57,plain,(
% 1.23/0.51    spl4_4 <=> r2_hidden(sK2,sK0)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.23/0.51  fof(f198,plain,(
% 1.23/0.51    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_4 | ~spl4_23)),
% 1.23/0.51    inference(resolution,[],[f191,f58])).
% 1.23/0.51  fof(f58,plain,(
% 1.23/0.51    r2_hidden(sK2,sK0) | ~spl4_4),
% 1.23/0.51    inference(avatar_component_clause,[],[f57])).
% 1.23/0.51  fof(f192,plain,(
% 1.23/0.51    ~spl4_18 | ~spl4_8 | ~spl4_5 | spl4_23 | ~spl4_17),
% 1.23/0.51    inference(avatar_split_clause,[],[f137,f126,f190,f61,f73,f140])).
% 1.23/0.51  fof(f73,plain,(
% 1.23/0.51    spl4_8 <=> v1_funct_1(sK1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.23/0.51  fof(f61,plain,(
% 1.23/0.51    spl4_5 <=> v2_funct_1(sK1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.23/0.51  fof(f126,plain,(
% 1.23/0.51    spl4_17 <=> sK0 = k1_relat_1(sK1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.23/0.51  fof(f137,plain,(
% 1.23/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl4_17),
% 1.23/0.51    inference(superposition,[],[f30,f127])).
% 1.23/0.51  fof(f127,plain,(
% 1.23/0.51    sK0 = k1_relat_1(sK1) | ~spl4_17),
% 1.23/0.51    inference(avatar_component_clause,[],[f126])).
% 1.23/0.51  fof(f30,plain,(
% 1.23/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.23/0.51    inference(cnf_transformation,[],[f12])).
% 1.23/0.51  fof(f12,plain,(
% 1.23/0.51    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.23/0.51    inference(flattening,[],[f11])).
% 1.23/0.51  fof(f11,plain,(
% 1.23/0.51    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.23/0.51    inference(ennf_transformation,[],[f3])).
% 1.23/0.51  fof(f3,axiom,(
% 1.23/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.23/0.51  fof(f130,plain,(
% 1.23/0.51    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 1.23/0.51  fof(f129,plain,(
% 1.23/0.51    ~spl4_6 | spl4_17 | ~spl4_9),
% 1.23/0.51    inference(avatar_split_clause,[],[f123,f78,f126,f65])).
% 1.23/0.51  fof(f78,plain,(
% 1.23/0.51    spl4_9 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.23/0.51  fof(f123,plain,(
% 1.23/0.51    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_9),
% 1.23/0.51    inference(superposition,[],[f32,f79])).
% 1.23/0.51  fof(f79,plain,(
% 1.23/0.51    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_9),
% 1.23/0.51    inference(avatar_component_clause,[],[f78])).
% 1.23/0.51  fof(f32,plain,(
% 1.23/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.51    inference(cnf_transformation,[],[f13])).
% 1.23/0.51  fof(f13,plain,(
% 1.23/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.51    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.23/0.52  fof(f113,plain,(
% 1.23/0.52    spl4_15 | ~spl4_12 | ~spl4_11),
% 1.23/0.52    inference(avatar_split_clause,[],[f106,f90,f94,f110])).
% 1.23/0.52  fof(f110,plain,(
% 1.23/0.52    spl4_15 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.23/0.52  fof(f94,plain,(
% 1.23/0.52    spl4_12 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.23/0.52  fof(f90,plain,(
% 1.23/0.52    spl4_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.23/0.52  fof(f106,plain,(
% 1.23/0.52    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl4_11),
% 1.23/0.52    inference(resolution,[],[f91,f43])).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.23/0.52    inference(equality_resolution,[],[f34])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.52    inference(nnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.52    inference(flattening,[],[f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.52    inference(ennf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.23/0.52  fof(f91,plain,(
% 1.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_11),
% 1.23/0.52    inference(avatar_component_clause,[],[f90])).
% 1.23/0.52  fof(f96,plain,(
% 1.23/0.52    spl4_12 | ~spl4_7 | ~spl4_10),
% 1.23/0.52    inference(avatar_split_clause,[],[f86,f81,f69,f94])).
% 1.23/0.52  fof(f69,plain,(
% 1.23/0.52    spl4_7 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    spl4_10 <=> k1_xboole_0 = sK0),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.23/0.52  fof(f86,plain,(
% 1.23/0.52    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (~spl4_7 | ~spl4_10)),
% 1.23/0.52    inference(superposition,[],[f70,f82])).
% 1.23/0.52  fof(f82,plain,(
% 1.23/0.52    k1_xboole_0 = sK0 | ~spl4_10),
% 1.23/0.52    inference(avatar_component_clause,[],[f81])).
% 1.23/0.52  fof(f70,plain,(
% 1.23/0.52    v1_funct_2(sK1,sK0,sK0) | ~spl4_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f69])).
% 1.23/0.52  fof(f92,plain,(
% 1.23/0.52    spl4_11 | ~spl4_6 | ~spl4_10),
% 1.23/0.52    inference(avatar_split_clause,[],[f85,f81,f65,f90])).
% 1.23/0.52  fof(f85,plain,(
% 1.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_6 | ~spl4_10)),
% 1.23/0.52    inference(superposition,[],[f66,f82])).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    spl4_9 | spl4_10 | ~spl4_7 | ~spl4_6),
% 1.23/0.52    inference(avatar_split_clause,[],[f76,f65,f69,f81,f78])).
% 1.23/0.52  fof(f76,plain,(
% 1.23/0.52    ~v1_funct_2(sK1,sK0,sK0) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_6),
% 1.23/0.52    inference(resolution,[],[f33,f66])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    spl4_8),
% 1.23/0.52    inference(avatar_split_clause,[],[f20,f73])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    v1_funct_1(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f9,plain,(
% 1.23/0.52    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.23/0.52    inference(flattening,[],[f8])).
% 1.23/0.52  fof(f8,plain,(
% 1.23/0.52    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.23/0.52    inference(ennf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,negated_conjecture,(
% 1.23/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.23/0.52    inference(negated_conjecture,[],[f6])).
% 1.23/0.52  fof(f6,conjecture,(
% 1.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 1.23/0.52  fof(f71,plain,(
% 1.23/0.52    spl4_7),
% 1.23/0.52    inference(avatar_split_clause,[],[f21,f69])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    v1_funct_2(sK1,sK0,sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f67,plain,(
% 1.23/0.52    spl4_6),
% 1.23/0.52    inference(avatar_split_clause,[],[f22,f65])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f63,plain,(
% 1.23/0.52    spl4_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f23,f61])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    v2_funct_1(sK1)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f59,plain,(
% 1.23/0.52    spl4_4),
% 1.23/0.52    inference(avatar_split_clause,[],[f24,f57])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    r2_hidden(sK2,sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    spl4_3),
% 1.23/0.52    inference(avatar_split_clause,[],[f25,f53])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    r2_hidden(sK3,sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f51,plain,(
% 1.23/0.52    spl4_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f26,f49])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f47,plain,(
% 1.23/0.52    ~spl4_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f27,f45])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    spl4_1 <=> sK2 = sK3),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    sK2 != sK3),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (10987)------------------------------
% 1.23/0.52  % (10987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (10987)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (10987)Memory used [KB]: 10746
% 1.23/0.52  % (10987)Time elapsed: 0.069 s
% 1.23/0.52  % (10987)------------------------------
% 1.23/0.52  % (10987)------------------------------
% 1.23/0.52  % (10980)Success in time 0.151 s
%------------------------------------------------------------------------------
