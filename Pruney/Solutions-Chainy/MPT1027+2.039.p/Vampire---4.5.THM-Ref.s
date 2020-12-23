%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 202 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 ( 746 expanded)
%              Number of equality atoms :   95 ( 218 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f71,f73,f77,f85,f95,f102,f112,f116,f154,f165,f197,f207,f208,f213])).

fof(f213,plain,
    ( spl5_18
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f200,f163,f75,f178])).

fof(f178,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f75,plain,
    ( spl5_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f163,plain,
    ( spl5_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f200,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f173,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f173,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(resolution,[],[f164,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f48,f76])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f208,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f207,plain,
    ( spl5_21
    | ~ spl5_6
    | spl5_20 ),
    inference(avatar_split_clause,[],[f202,f195,f80,f205])).

fof(f205,plain,
    ( spl5_21
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f80,plain,
    ( spl5_6
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f195,plain,
    ( spl5_20
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f202,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_6
    | spl5_20 ),
    inference(resolution,[],[f196,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f196,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( ~ spl5_20
    | spl5_2
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f193,f178,f152,f60,f195])).

fof(f60,plain,
    ( spl5_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f152,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f193,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_2
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f187,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f187,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl5_2
    | ~ spl5_18 ),
    inference(superposition,[],[f61,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f61,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f165,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f161,f152,f63,f163])).

fof(f63,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f158,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(superposition,[],[f70,f153])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f154,plain,
    ( ~ spl5_3
    | spl5_13
    | spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f150,f67,f60,f152,f63])).

fof(f67,plain,
    ( spl5_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_2
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f149])).

fof(f149,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f145,f68])).

fof(f68,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f145,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_2 ),
    inference(resolution,[],[f44,f61])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f116,plain,
    ( spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f100,f114])).

fof(f114,plain,
    ( spl5_10
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f100,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK4(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f107,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(superposition,[],[f38,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f38,plain,(
    ! [X0] : v1_funct_2(sK4(X0),X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_2(sK4(X0),X0,X0)
      & v1_funct_1(sK4(X0))
      & m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1)
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( v1_funct_2(sK4(X0),X0,X0)
        & v1_funct_1(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).

fof(f112,plain,
    ( spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f111,f100,f83])).

fof(f83,plain,
    ( spl5_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f106,f49])).

fof(f106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_9 ),
    inference(superposition,[],[f36,f101])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( spl5_9
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f98,f92,f75,f100])).

fof(f92,plain,
    ( spl5_8
  <=> m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f98,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f97,f33])).

fof(f97,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_xboole_0))
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f96,f93])).

fof(f93,plain,
    ( m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f90,f92])).

fof(f90,plain,(
    m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f36,f50])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,
    ( spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f78,f83,f80])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f52,f49])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f73,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f57,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19])).

fof(f19,plain,
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

fof(f71,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f63,f60,f57])).

fof(f31,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (31634)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (31634)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (31642)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f65,f69,f71,f73,f77,f85,f95,f102,f112,f116,f154,f165,f197,f207,f208,f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl5_18 | ~spl5_5 | ~spl5_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f200,f163,f75,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl5_18 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl5_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | (~spl5_5 | ~spl5_15)),
% 0.21/0.48    inference(resolution,[],[f173,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | (~spl5_5 | ~spl5_15)),
% 0.21/0.48    inference(resolution,[],[f164,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f48,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f163])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | v1_funct_2(sK2,sK0,sK1) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    spl5_21 | ~spl5_6 | spl5_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f202,f195,f80,f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl5_21 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_6 <=> ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl5_20 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (~spl5_6 | spl5_20)),
% 0.21/0.48    inference(resolution,[],[f196,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl5_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~spl5_20 | spl5_2 | ~spl5_13 | ~spl5_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f178,f152,f60,f195])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl5_13 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl5_2 | ~spl5_13 | ~spl5_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f187,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_funct_2(k1_xboole_0,sK0,sK1) | (spl5_2 | ~spl5_18)),
% 0.21/0.48    inference(superposition,[],[f61,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f178])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,sK1) | spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl5_15 | ~spl5_3 | ~spl5_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f161,f152,f63,f163])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_3 | ~spl5_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f158,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl5_3 | ~spl5_13)),
% 0.21/0.48    inference(superposition,[],[f70,f153])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~spl5_3 | spl5_13 | spl5_2 | ~spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f150,f67,f60,f152,f63])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl5_2 | ~spl5_4)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    sK0 != sK0 | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl5_2 | ~spl5_4)),
% 0.21/0.48    inference(forward_demodulation,[],[f145,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_2),
% 0.21/0.48    inference(resolution,[],[f44,f61])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl5_10 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f100,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl5_10 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_9 <=> k1_xboole_0 = sK4(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_9),
% 0.21/0.48    inference(superposition,[],[f38,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k1_xboole_0 = sK4(k1_xboole_0) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(sK4(X0),X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (v1_funct_2(sK4(X0),X0,X0) & v1_funct_1(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (v1_funct_2(sK4(X0),X0,X0) & v1_funct_1(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : ? [X1] : (v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : ? [X1] : (v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ? [X1] : (v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ? [X1] : (v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : (v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_funct_2)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl5_7 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f111,f100,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl5_9),
% 0.21/0.48    inference(forward_demodulation,[],[f106,f49])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_9),
% 0.21/0.48    inference(superposition,[],[f36,f101])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl5_9 | ~spl5_5 | ~spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f92,f75,f100])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_8 <=> m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = sK4(k1_xboole_0) | (~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f97,f33])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK4(k1_xboole_0))) ) | (~spl5_5 | ~spl5_8)),
% 0.21/0.48    inference(resolution,[],[f96,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f90,f92])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(superposition,[],[f36,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl5_6 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f83,f80])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f52,f49])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f75])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f63,f60,f57])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31634)------------------------------
% 0.21/0.48  % (31634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31634)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31634)Memory used [KB]: 10746
% 0.21/0.48  % (31634)Time elapsed: 0.067 s
% 0.21/0.48  % (31634)------------------------------
% 0.21/0.48  % (31634)------------------------------
% 0.21/0.48  % (31627)Success in time 0.119 s
%------------------------------------------------------------------------------
