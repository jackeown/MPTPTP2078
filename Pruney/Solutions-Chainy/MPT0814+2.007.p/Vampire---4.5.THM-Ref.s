%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 176 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  277 ( 495 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f61,f96,f110,f120,f125,f133,f142,f148,f236,f244,f258,f261,f262,f266])).

fof(f266,plain,
    ( ~ spl12_1
    | ~ spl12_14
    | spl12_19 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_14
    | spl12_19 ),
    inference(subsumption_resolution,[],[f264,f47])).

fof(f47,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl12_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f264,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl12_14
    | spl12_19 ),
    inference(resolution,[],[f257,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(sK1,sK2,X0),sK1)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(sK10(sK1,sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f257,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),sK1)
    | spl12_19 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl12_19
  <=> r2_hidden(sK10(sK1,sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f262,plain,
    ( sK3 != k2_zfmisc_1(sK1,sK2)
    | r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ r2_hidden(sK0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f261,plain,
    ( ~ spl12_1
    | ~ spl12_12
    | spl12_18 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_12
    | spl12_18 ),
    inference(subsumption_resolution,[],[f259,f47])).

fof(f259,plain,
    ( ~ r2_hidden(sK0,sK3)
    | ~ spl12_12
    | spl12_18 ),
    inference(resolution,[],[f253,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(sK1,sK2,X0),sK2)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl12_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(sK11(sK1,sK2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f253,plain,
    ( ~ r2_hidden(sK11(sK1,sK2,sK0),sK2)
    | spl12_18 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl12_18
  <=> r2_hidden(sK11(sK1,sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f258,plain,
    ( ~ spl12_18
    | ~ spl12_19
    | ~ spl12_15 ),
    inference(avatar_split_clause,[],[f154,f145,f255,f251])).

fof(f145,plain,
    ( spl12_15
  <=> sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f154,plain,
    ( ~ r2_hidden(sK10(sK1,sK2,sK0),sK1)
    | ~ r2_hidden(sK11(sK1,sK2,sK0),sK2)
    | ~ spl12_15 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK10(sK1,sK2,sK0),sK1)
    | ~ r2_hidden(sK11(sK1,sK2,sK0),sK2)
    | ~ spl12_15 ),
    inference(superposition,[],[f16,f147])).

fof(f147,plain,
    ( sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f16,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f244,plain,
    ( ~ spl12_9
    | ~ spl12_13 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_13 ),
    inference(resolution,[],[f186,f119])).

fof(f119,plain,
    ( r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl12_9
  <=> r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f186,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(sK1,X3))
    | ~ spl12_13 ),
    inference(resolution,[],[f156,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f156,plain,
    ( ! [X0,X1] : ~ sP7(X0,X1,sK1)
    | ~ spl12_13 ),
    inference(resolution,[],[f143,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl12_13 ),
    inference(resolution,[],[f138,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f138,plain,
    ( v1_xboole_0(sK1)
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl12_13
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f236,plain,
    ( ~ spl12_9
    | ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl12_9
    | ~ spl12_11 ),
    inference(resolution,[],[f180,f119])).

fof(f180,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(X3,sK2))
    | ~ spl12_11 ),
    inference(resolution,[],[f151,f41])).

fof(f151,plain,
    ( ! [X2,X3] : ~ sP7(X2,sK2,X3)
    | ~ spl12_11 ),
    inference(resolution,[],[f134,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl12_11 ),
    inference(resolution,[],[f129,f20])).

fof(f129,plain,
    ( v1_xboole_0(sK2)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl12_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f148,plain,
    ( spl12_15
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f102,f58,f45,f145])).

fof(f58,plain,
    ( spl12_3
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f102,plain,
    ( sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | k4_tarski(sK10(sK1,sK2,X1),sK11(sK1,sK2,X1)) = X1 )
    | ~ spl12_3 ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2)
      | k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( k4_tarski(X4,X5) = X3
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f60,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f142,plain,
    ( spl12_13
    | spl12_14
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f83,f58,f140,f136])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(sK1)
        | r2_hidden(sK10(sK1,sK2,X0),sK1) )
    | ~ spl12_3 ),
    inference(resolution,[],[f64,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f64,plain,
    ( ! [X2] :
        ( m1_subset_1(sK10(sK1,sK2,X2),sK1)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl12_3 ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2)
      | m1_subset_1(sK10(X0,X1,X3),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,
    ( spl12_11
    | spl12_12
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f67,f58,f131,f127])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(sK2)
        | r2_hidden(sK11(sK1,sK2,X0),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f62,f21])).

fof(f62,plain,
    ( ! [X0] :
        ( m1_subset_1(sK11(sK1,sK2,X0),sK2)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl12_3 ),
    inference(resolution,[],[f60,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X3,X2)
      | m1_subset_1(sK11(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f125,plain,
    ( ~ spl12_10
    | spl12_8 ),
    inference(avatar_split_clause,[],[f115,f107,f122])).

fof(f122,plain,
    ( spl12_10
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f107,plain,
    ( spl12_8
  <=> sP7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f115,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl12_8 ),
    inference(resolution,[],[f109,f41])).

fof(f109,plain,
    ( ~ sP7(sK0,sK2,sK1)
    | spl12_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f120,plain,
    ( spl12_9
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f97,f89,f117])).

fof(f89,plain,
    ( spl12_6
  <=> r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f97,plain,
    ( r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))
    | ~ spl12_6 ),
    inference(resolution,[],[f91,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f91,plain,
    ( r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f110,plain,(
    ~ spl12_8 ),
    inference(avatar_split_clause,[],[f101,f107])).

fof(f101,plain,(
    ~ sP7(sK0,sK2,sK1) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ sP7(X0,sK2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ sP7(X0,sK2,sK1)
      | ~ sP7(X0,sK2,sK1) ) ),
    inference(resolution,[],[f79,f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,sK2,X1),sK1)
      | sK0 != X1
      | ~ sP7(X1,sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,sK2,X1),sK1)
      | sK0 != X1
      | ~ sP7(X1,sK2,X0)
      | ~ sP7(X1,sK2,X0) ) ),
    inference(resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),sK2)
      | ~ r2_hidden(sK8(X0,X1,X2),sK1)
      | sK0 != X2
      | ~ sP7(X2,X1,X0) ) ),
    inference(superposition,[],[f16,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,
    ( spl12_6
    | spl12_7
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f66,f58,f93,f89])).

fof(f93,plain,
    ( spl12_7
  <=> sK3 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f66,plain,
    ( sK3 = k2_zfmisc_1(sK1,sK2)
    | r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl12_3 ),
    inference(resolution,[],[f60,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f61,plain,
    ( spl12_3
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f54,f50,f58])).

fof(f50,plain,
    ( spl12_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f54,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl12_2 ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f53,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f17,f50])).

fof(f17,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.43  % (8243)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (8243)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (8256)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f267,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f48,f53,f61,f96,f110,f120,f125,f133,f142,f148,f236,f244,f258,f261,f262,f266])).
% 0.21/0.44  fof(f266,plain,(
% 0.21/0.44    ~spl12_1 | ~spl12_14 | spl12_19),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.44  fof(f265,plain,(
% 0.21/0.44    $false | (~spl12_1 | ~spl12_14 | spl12_19)),
% 0.21/0.44    inference(subsumption_resolution,[],[f264,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    r2_hidden(sK0,sK3) | ~spl12_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl12_1 <=> r2_hidden(sK0,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.44  fof(f264,plain,(
% 0.21/0.44    ~r2_hidden(sK0,sK3) | (~spl12_14 | spl12_19)),
% 0.21/0.44    inference(resolution,[],[f257,f141])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK10(sK1,sK2,X0),sK1) | ~r2_hidden(X0,sK3)) ) | ~spl12_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f140])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    spl12_14 <=> ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(sK10(sK1,sK2,X0),sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    ~r2_hidden(sK10(sK1,sK2,sK0),sK1) | spl12_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f255])).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    spl12_19 <=> r2_hidden(sK10(sK1,sK2,sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    sK3 != k2_zfmisc_1(sK1,sK2) | r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,sK3)),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f261,plain,(
% 0.21/0.44    ~spl12_1 | ~spl12_12 | spl12_18),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f260])).
% 0.21/0.44  fof(f260,plain,(
% 0.21/0.44    $false | (~spl12_1 | ~spl12_12 | spl12_18)),
% 0.21/0.44    inference(subsumption_resolution,[],[f259,f47])).
% 0.21/0.44  fof(f259,plain,(
% 0.21/0.44    ~r2_hidden(sK0,sK3) | (~spl12_12 | spl12_18)),
% 0.21/0.44    inference(resolution,[],[f253,f132])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK11(sK1,sK2,X0),sK2) | ~r2_hidden(X0,sK3)) ) | ~spl12_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl12_12 <=> ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(sK11(sK1,sK2,X0),sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 0.21/0.44  fof(f253,plain,(
% 0.21/0.44    ~r2_hidden(sK11(sK1,sK2,sK0),sK2) | spl12_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f251])).
% 0.21/0.44  fof(f251,plain,(
% 0.21/0.44    spl12_18 <=> r2_hidden(sK11(sK1,sK2,sK0),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 0.21/0.44  fof(f258,plain,(
% 0.21/0.44    ~spl12_18 | ~spl12_19 | ~spl12_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f154,f145,f255,f251])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    spl12_15 <=> sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 0.21/0.44  fof(f154,plain,(
% 0.21/0.44    ~r2_hidden(sK10(sK1,sK2,sK0),sK1) | ~r2_hidden(sK11(sK1,sK2,sK0),sK2) | ~spl12_15),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    sK0 != sK0 | ~r2_hidden(sK10(sK1,sK2,sK0),sK1) | ~r2_hidden(sK11(sK1,sK2,sK0),sK2) | ~spl12_15),
% 0.21/0.44    inference(superposition,[],[f16,f147])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0)) | ~spl12_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f145])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.44  fof(f244,plain,(
% 0.21/0.44    ~spl12_9 | ~spl12_13),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.44  fof(f239,plain,(
% 0.21/0.44    $false | (~spl12_9 | ~spl12_13)),
% 0.21/0.44    inference(resolution,[],[f186,f119])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) | ~spl12_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f117])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl12_9 <=> r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(sK1,X3))) ) | ~spl12_13),
% 0.21/0.44    inference(resolution,[],[f156,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.44    inference(equality_resolution,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sP7(X0,X1,sK1)) ) | ~spl12_13),
% 0.21/0.44    inference(resolution,[],[f143,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~sP7(X3,X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl12_13),
% 0.21/0.44    inference(resolution,[],[f138,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    v1_xboole_0(sK1) | ~spl12_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f136])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    spl12_13 <=> v1_xboole_0(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.21/0.44  fof(f236,plain,(
% 0.21/0.44    ~spl12_9 | ~spl12_11),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    $false | (~spl12_9 | ~spl12_11)),
% 0.21/0.44    inference(resolution,[],[f180,f119])).
% 0.21/0.44  fof(f180,plain,(
% 0.21/0.44    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,sK2))) ) | ~spl12_11),
% 0.21/0.44    inference(resolution,[],[f151,f41])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    ( ! [X2,X3] : (~sP7(X2,sK2,X3)) ) | ~spl12_11),
% 0.21/0.44    inference(resolution,[],[f134,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl12_11),
% 0.21/0.44    inference(resolution,[],[f129,f20])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    v1_xboole_0(sK2) | ~spl12_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f127])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl12_11 <=> v1_xboole_0(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    spl12_15 | ~spl12_1 | ~spl12_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f102,f58,f45,f145])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl12_3 <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    sK0 = k4_tarski(sK10(sK1,sK2,sK0),sK11(sK1,sK2,sK0)) | (~spl12_1 | ~spl12_3)),
% 0.21/0.44    inference(resolution,[],[f63,f47])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X1] : (~r2_hidden(X1,sK3) | k4_tarski(sK10(sK1,sK2,X1),sK11(sK1,sK2,X1)) = X1) ) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f60,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2) | k4_tarski(sK10(X0,X1,X3),sK11(X0,X1,X3)) = X3) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (? [X4] : (? [X5] : (k4_tarski(X4,X5) = X3 & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl12_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f58])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    spl12_13 | spl12_14 | ~spl12_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f83,f58,f140,f136])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK3) | v1_xboole_0(sK1) | r2_hidden(sK10(sK1,sK2,X0),sK1)) ) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f64,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X2] : (m1_subset_1(sK10(sK1,sK2,X2),sK1) | ~r2_hidden(X2,sK3)) ) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f60,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2) | m1_subset_1(sK10(X0,X1,X3),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    spl12_11 | spl12_12 | ~spl12_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f67,f58,f131,f127])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK3) | v1_xboole_0(sK2) | r2_hidden(sK11(sK1,sK2,X0),sK2)) ) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f62,f21])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK11(sK1,sK2,X0),sK2) | ~r2_hidden(X0,sK3)) ) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f60,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X3,X2) | m1_subset_1(sK11(X0,X1,X3),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ~spl12_10 | spl12_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f115,f107,f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    spl12_10 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl12_8 <=> sP7(sK0,sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl12_8),
% 0.21/0.44    inference(resolution,[],[f109,f41])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ~sP7(sK0,sK2,sK1) | spl12_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f107])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    spl12_9 | ~spl12_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f97,f89,f117])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl12_6 <=> r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    r2_hidden(sK5(sK3,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) | ~spl12_6),
% 0.21/0.44    inference(resolution,[],[f91,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl12_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f89])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ~spl12_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f101,f107])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~sP7(sK0,sK2,sK1)),
% 0.21/0.44    inference(equality_resolution,[],[f100])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ( ! [X0] : (sK0 != X0 | ~sP7(X0,sK2,sK1)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    ( ! [X0] : (sK0 != X0 | ~sP7(X0,sK2,sK1) | ~sP7(X0,sK2,sK1)) )),
% 0.21/0.44    inference(resolution,[],[f79,f30])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(sK8(X0,sK2,X1),sK1) | sK0 != X1 | ~sP7(X1,sK2,X0)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(sK8(X0,sK2,X1),sK1) | sK0 != X1 | ~sP7(X1,sK2,X0) | ~sP7(X1,sK2,X0)) )),
% 0.21/0.44    inference(resolution,[],[f56,f31])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK9(X0,X1,X2),sK2) | ~r2_hidden(sK8(X0,X1,X2),sK1) | sK0 != X2 | ~sP7(X2,X1,X0)) )),
% 0.21/0.44    inference(superposition,[],[f16,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~sP7(X3,X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl12_6 | spl12_7 | ~spl12_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f66,f58,f93,f89])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl12_7 <=> sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    sK3 = k2_zfmisc_1(sK1,sK2) | r2_xboole_0(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl12_3),
% 0.21/0.44    inference(resolution,[],[f60,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl12_3 | ~spl12_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f54,f50,f58])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl12_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) | ~spl12_2),
% 0.21/0.44    inference(resolution,[],[f52,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl12_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl12_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f50])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl12_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    r2_hidden(sK0,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (8243)------------------------------
% 0.21/0.44  % (8243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8243)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (8243)Memory used [KB]: 10746
% 0.21/0.44  % (8243)Time elapsed: 0.062 s
% 0.21/0.44  % (8243)------------------------------
% 0.21/0.44  % (8243)------------------------------
% 0.21/0.44  % (8239)Success in time 0.094 s
%------------------------------------------------------------------------------
