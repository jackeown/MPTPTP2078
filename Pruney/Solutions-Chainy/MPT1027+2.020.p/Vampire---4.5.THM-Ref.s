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
% DateTime   : Thu Dec  3 13:06:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 195 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 ( 676 expanded)
%              Number of equality atoms :   91 ( 226 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f67,f69,f77,f82,f88,f104,f115,f134,f151,f163,f175,f193,f195,f323])).

fof(f323,plain,
    ( spl3_20
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f322,f186,f128,f75,f173])).

fof(f173,plain,
    ( spl3_20
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f75,plain,
    ( spl3_6
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f186,plain,
    ( spl3_21
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f322,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f321,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f321,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f317,f129])).

fof(f317,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_21 ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_21 ),
    inference(superposition,[],[f79,f187])).

fof(f187,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f186])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f50,f46])).

fof(f46,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f195,plain,
    ( spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f139,f132,f128])).

fof(f132,plain,
    ( spl3_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(resolution,[],[f133,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f133,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f193,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f192,f161,f101,f63,f186])).

fof(f63,plain,
    ( spl3_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f101,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f161,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f192,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f170,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f170,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f64,f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f64,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f175,plain,
    ( ~ spl3_20
    | spl3_16
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f167,f161,f149,f173])).

fof(f149,plain,
    ( spl3_16
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f167,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_16
    | ~ spl3_18 ),
    inference(superposition,[],[f150,f162])).

fof(f150,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f163,plain,
    ( spl3_18
    | ~ spl3_5
    | spl3_16 ),
    inference(avatar_split_clause,[],[f159,f149,f72,f161])).

fof(f72,plain,
    ( spl3_5
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5
    | spl3_16 ),
    inference(resolution,[],[f150,f73])).

fof(f73,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f151,plain,
    ( ~ spl3_16
    | spl3_2
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f147,f128,f101,f56,f149])).

fof(f56,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f147,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f141,f102])).

fof(f141,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl3_2
    | ~ spl3_13 ),
    inference(superposition,[],[f57,f129])).

fof(f57,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f134,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f123,f113,f86,f132])).

fof(f86,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f113,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f123,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f114,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f87,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f111,f101,f59,f113])).

fof(f59,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f108,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f66,f102])).

fof(f66,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f104,plain,
    ( ~ spl3_3
    | spl3_8
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f63,f56,f101,f59])).

fof(f99,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( sK0 != sK0
    | v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f41,f64])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f84,f86])).

fof(f84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f83,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f82,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f76,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f76,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f70,f75,f72])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f48,f45])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f53,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).

fof(f21,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f67,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f59,f56,f53])).

fof(f29,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (9657)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (9658)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (9658)Refutation not found, incomplete strategy% (9658)------------------------------
% 0.20/0.47  % (9658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9658)Memory used [KB]: 6140
% 0.20/0.47  % (9658)Time elapsed: 0.004 s
% 0.20/0.47  % (9658)------------------------------
% 0.20/0.47  % (9658)------------------------------
% 0.20/0.47  % (9659)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (9649)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (9645)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (9663)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (9663)Refutation not found, incomplete strategy% (9663)------------------------------
% 0.20/0.48  % (9663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9655)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9655)Refutation not found, incomplete strategy% (9655)------------------------------
% 0.20/0.48  % (9655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9663)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9663)Memory used [KB]: 10618
% 0.20/0.48  % (9663)Time elapsed: 0.071 s
% 0.20/0.48  % (9663)------------------------------
% 0.20/0.48  % (9663)------------------------------
% 0.20/0.48  % (9650)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (9655)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9655)Memory used [KB]: 6140
% 0.20/0.48  % (9655)Time elapsed: 0.072 s
% 0.20/0.48  % (9655)------------------------------
% 0.20/0.48  % (9655)------------------------------
% 0.20/0.48  % (9643)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (9643)Refutation not found, incomplete strategy% (9643)------------------------------
% 0.20/0.48  % (9643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9643)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9643)Memory used [KB]: 6140
% 0.20/0.48  % (9643)Time elapsed: 0.072 s
% 0.20/0.48  % (9643)------------------------------
% 0.20/0.48  % (9643)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f324,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f61,f65,f67,f69,f77,f82,f88,f104,f115,f134,f151,f163,f175,f193,f195,f323])).
% 0.20/0.49  fof(f323,plain,(
% 0.20/0.49    spl3_20 | ~spl3_6 | ~spl3_13 | ~spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f322,f186,f128,f75,f173])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    spl3_20 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_6 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl3_13 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    spl3_21 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_13 | ~spl3_21)),
% 0.20/0.49    inference(forward_demodulation,[],[f321,f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f128])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_13 | ~spl3_21)),
% 0.20/0.49    inference(forward_demodulation,[],[f317,f129])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_21),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f316])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_21),
% 0.20/0.49    inference(superposition,[],[f79,f187])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f186])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f50,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl3_13 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f139,f132,f128])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl3_14 <=> v1_xboole_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl3_14),
% 0.20/0.49    inference(resolution,[],[f133,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    v1_xboole_0(sK2) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f132])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl3_21 | ~spl3_4 | ~spl3_8 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f192,f161,f101,f63,f186])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl3_8 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl3_18 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_4 | ~spl3_8 | ~spl3_18)),
% 0.20/0.49    inference(forward_demodulation,[],[f170,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | (~spl3_4 | ~spl3_18)),
% 0.20/0.49    inference(superposition,[],[f64,f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f161])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~spl3_20 | spl3_16 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f167,f161,f149,f173])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl3_16 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_16 | ~spl3_18)),
% 0.20/0.49    inference(superposition,[],[f150,f162])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f149])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl3_18 | ~spl3_5 | spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f159,f149,f72,f161])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_5 <=> ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | (~spl3_5 | spl3_16)),
% 0.20/0.49    inference(resolution,[],[f150,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ~spl3_16 | spl3_2 | ~spl3_8 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f147,f128,f101,f56,f149])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl3_2 | ~spl3_8 | ~spl3_13)),
% 0.20/0.49    inference(forward_demodulation,[],[f141,f102])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,sK0,sK1) | (spl3_2 | ~spl3_13)),
% 0.20/0.49    inference(superposition,[],[f57,f129])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,sK1) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl3_14 | ~spl3_7 | ~spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f123,f113,f86,f132])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    v1_xboole_0(sK2) | (~spl3_7 | ~spl3_10)),
% 0.20/0.49    inference(resolution,[],[f114,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl3_7),
% 0.20/0.49    inference(resolution,[],[f87,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f86])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_10 | ~spl3_3 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f111,f101,f59,f113])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f108,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_3 | ~spl3_8)),
% 0.20/0.49    inference(superposition,[],[f66,f102])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ~spl3_3 | spl3_8 | spl3_2 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f63,f56,f101,f59])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    sK0 != sK0 | v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.20/0.49    inference(superposition,[],[f41,f64])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f84,f86])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(resolution,[],[f83,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f35,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    $false | spl3_6),
% 0.20/0.49    inference(resolution,[],[f76,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_5 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f70,f75,f72])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f48,f45])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f59])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f28,f63])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f59,f56,f53])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9649)------------------------------
% 0.20/0.49  % (9649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9649)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9649)Memory used [KB]: 10746
% 0.20/0.49  % (9649)Time elapsed: 0.058 s
% 0.20/0.49  % (9649)------------------------------
% 0.20/0.49  % (9649)------------------------------
% 0.20/0.49  % (9642)Success in time 0.13 s
%------------------------------------------------------------------------------
