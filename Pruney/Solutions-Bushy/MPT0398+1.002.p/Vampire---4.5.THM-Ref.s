%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0398+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 136 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :  239 ( 348 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f47,f51,f55,f63,f75,f81,f87,f92,f97,f102,f109,f113,f125,f135,f155])).

fof(f155,plain,
    ( spl4_12
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_12
    | ~ spl4_20 ),
    inference(resolution,[],[f134,f86])).

fof(f86,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_12
  <=> r1_setfam_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f134,plain,
    ( ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_20
  <=> ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f135,plain,
    ( spl4_20
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f127,f122,f111,f133])).

fof(f111,plain,
    ( spl4_17
  <=> ! [X0] : r1_setfam_1(sK1(k1_zfmisc_1(o_0_0_xboole_0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f122,plain,
    ( spl4_19
  <=> o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f127,plain,
    ( ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0)
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(superposition,[],[f112,f124])).

fof(f124,plain,
    ( o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f112,plain,
    ( ! [X0] : r1_setfam_1(sK1(k1_zfmisc_1(o_0_0_xboole_0)),X0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f125,plain,
    ( spl4_19
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f120,f106,f78,f45,f122])).

fof(f45,plain,
    ( spl4_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_11
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f106,plain,
    ( spl4_16
  <=> v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f120,plain,
    ( o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f115,f80])).

fof(f80,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f115,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(resolution,[],[f108,f46])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f108,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( spl4_17
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f104,f100,f61,f111])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_setfam_1(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f100,plain,
    ( spl4_15
  <=> ! [X0] : ~ r2_hidden(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f104,plain,
    ( ! [X0] : r1_setfam_1(sK1(k1_zfmisc_1(o_0_0_xboole_0)),X0)
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(resolution,[],[f101,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_setfam_1(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f109,plain,
    ( spl4_16
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f103,f100,f90,f106])).

fof(f90,plain,
    ( spl4_13
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f103,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(resolution,[],[f101,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f102,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f98,f95,f49,f100])).

fof(f49,plain,
    ( spl4_4
  <=> ! [X0] : m1_subset_1(sK1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f98,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,
    ( ! [X0] : m1_subset_1(sK1(X0),X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f93,f73,f40,f95])).

fof(f40,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f92,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f88,f53,f49,f90])).

fof(f53,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f88,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f54,f50])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f87,plain,
    ( ~ spl4_12
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f82,f78,f35,f84])).

fof(f35,plain,
    ( spl4_1
  <=> r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f82,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,sK0)
    | spl4_1
    | ~ spl4_11 ),
    inference(superposition,[],[f37,f80])).

fof(f37,plain,
    ( ~ r1_setfam_1(k1_xboole_0,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f81,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f76,f45,f40,f78])).

fof(f76,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f46,f42])).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK2(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK3(X1,X4))
              & r2_hidden(sK3(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f40])).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f38,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).

%------------------------------------------------------------------------------
