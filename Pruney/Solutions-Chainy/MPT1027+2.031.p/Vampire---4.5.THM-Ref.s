%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 219 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  356 ( 743 expanded)
%              Number of equality atoms :   96 ( 257 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f64,f66,f70,f78,f93,f104,f105,f109,f124,f128,f152,f157,f159,f403,f428,f429,f443])).

fof(f443,plain,
    ( ~ spl4_7
    | spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f441,f405,f417,f76])).

fof(f76,plain,
    ( spl4_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f417,plain,
    ( spl4_21
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f405,plain,
    ( spl4_20
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f441,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(superposition,[],[f80,f406])).

fof(f406,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f405])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f47,f43])).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f429,plain,
    ( ~ spl4_21
    | spl4_16
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f413,f401,f144,f417])).

fof(f144,plain,
    ( spl4_16
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f401,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f413,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_16
    | ~ spl4_19 ),
    inference(superposition,[],[f145,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f401])).

fof(f145,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f428,plain,
    ( spl4_20
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f412,f401,f131,f405])).

fof(f131,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f412,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(superposition,[],[f132,f402])).

fof(f132,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f403,plain,
    ( spl4_19
    | ~ spl4_6
    | spl4_16 ),
    inference(avatar_split_clause,[],[f397,f144,f73,f401])).

fof(f73,plain,
    ( spl4_6
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f397,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6
    | spl4_16 ),
    inference(resolution,[],[f74,f145])).

fof(f74,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f159,plain,
    ( ~ spl4_16
    | spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f139,f117,f107,f144])).

fof(f107,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f139,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl4_11
    | ~ spl4_13 ),
    inference(superposition,[],[f108,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f108,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f157,plain,
    ( spl4_15
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f137,f117,f95,f131])).

fof(f95,plain,
    ( spl4_9
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f137,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(superposition,[],[f96,f118])).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f152,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f150,f117,f90,f56,f76])).

fof(f56,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f90,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f150,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f149,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f149,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f135,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f135,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f63,f118])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f128,plain,
    ( spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f127,f122,f117])).

fof(f122,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f127,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14 ),
    inference(resolution,[],[f123,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f123,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f124,plain,
    ( spl4_14
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f120,f102,f68,f122])).

fof(f68,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f102,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f120,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f112,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f112,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f103,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,
    ( ~ spl4_11
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f99,f90,f53,f107])).

fof(f53,plain,
    ( spl4_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f54,f91])).

fof(f54,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f105,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f90,f60,f95])).

fof(f60,plain,
    ( spl4_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f61,f91])).

fof(f61,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f104,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f100,f90,f56,f102])).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f97,f42])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(superposition,[],[f63,f91])).

fof(f93,plain,
    ( ~ spl4_3
    | spl4_8
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f88,f60,f53,f90,f56])).

fof(f88,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( sK0 != sK0
    | v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f37,f61])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f71,f76,f73])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f50,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & sK0 = k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f64,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f27,f56,f53,f50])).

fof(f27,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:14:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (30969)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (30969)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (30977)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f58,f62,f64,f66,f70,f78,f93,f104,f105,f109,f124,f128,f152,f157,f159,f403,f428,f429,f443])).
% 0.21/0.48  fof(f443,plain,(
% 0.21/0.48    ~spl4_7 | spl4_21 | ~spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f441,f405,f417,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl4_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    spl4_21 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.48  fof(f405,plain,(
% 0.21/0.48    spl4_20 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f441,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_20),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f440])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_20),
% 0.21/0.48    inference(superposition,[],[f80,f406])).
% 0.21/0.48  fof(f406,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f405])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f47,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    ~spl4_21 | spl4_16 | ~spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f413,f401,f144,f417])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl4_16 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    spl4_19 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_16 | ~spl4_19)),
% 0.21/0.48    inference(superposition,[],[f145,f402])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f401])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl4_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f144])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    spl4_20 | ~spl4_15 | ~spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f412,f401,f131,f405])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl4_15 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_15 | ~spl4_19)),
% 0.21/0.48    inference(superposition,[],[f132,f402])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    spl4_19 | ~spl4_6 | spl4_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f397,f144,f73,f401])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl4_6 <=> ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (~spl4_6 | spl4_16)),
% 0.21/0.48    inference(resolution,[],[f74,f145])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~spl4_16 | spl4_11 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f139,f117,f107,f144])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl4_11 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl4_13 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl4_11 | ~spl4_13)),
% 0.21/0.48    inference(superposition,[],[f108,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl4_15 | ~spl4_9 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f137,f117,f95,f131])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl4_9 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl4_9 | ~spl4_13)),
% 0.21/0.48    inference(superposition,[],[f96,f118])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl4_7 | ~spl4_3 | ~spl4_8 | ~spl4_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f150,f117,f90,f56,f76])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl4_8 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_8 | ~spl4_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f149,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_3 | ~spl4_8 | ~spl4_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | ~spl4_13)),
% 0.21/0.48    inference(superposition,[],[f63,f118])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl4_13 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f122,f117])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl4_14 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_14),
% 0.21/0.48    inference(resolution,[],[f123,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f122])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl4_14 | ~spl4_5 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f120,f102,f68,f122])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    v1_xboole_0(sK2) | (~spl4_5 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f112,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | (~spl4_5 | ~spl4_10)),
% 0.21/0.49    inference(resolution,[],[f103,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f41,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~spl4_11 | spl4_2 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f99,f90,f53,f107])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl4_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (spl4_2 | ~spl4_8)),
% 0.21/0.49    inference(superposition,[],[f54,f91])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,sK0,sK1) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl4_9 | ~spl4_4 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f90,f60,f95])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl4_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl4_4 | ~spl4_8)),
% 0.21/0.49    inference(superposition,[],[f61,f91])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl4_10 | ~spl4_3 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f100,f90,f56,f102])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_8)),
% 0.21/0.49    inference(forward_demodulation,[],[f97,f42])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_3 | ~spl4_8)),
% 0.21/0.49    inference(superposition,[],[f63,f91])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~spl4_3 | spl4_8 | spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f60,f53,f90,f56])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    sK0 != sK0 | v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.49    inference(superposition,[],[f37,f61])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl4_6 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f76,f73])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f45,f42])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f68])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl4_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f60])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f56,f53,f50])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30969)------------------------------
% 0.21/0.49  % (30969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30969)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30969)Memory used [KB]: 10746
% 0.21/0.49  % (30969)Time elapsed: 0.069 s
% 0.21/0.49  % (30969)------------------------------
% 0.21/0.49  % (30969)------------------------------
% 0.21/0.49  % (30963)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (30962)Success in time 0.135 s
%------------------------------------------------------------------------------
