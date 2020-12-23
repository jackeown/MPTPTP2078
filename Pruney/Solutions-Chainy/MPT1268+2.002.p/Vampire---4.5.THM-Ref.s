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
% DateTime   : Thu Dec  3 13:12:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 246 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  461 (1569 expanded)
%              Number of equality atoms :   58 ( 227 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f93,f103,f109,f123,f129,f143,f176,f206,f208,f213,f218,f230,f314,f318])).

fof(f318,plain,
    ( spl3_22
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl3_22
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f212,f313,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f313,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_34
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f212,plain,
    ( k1_xboole_0 != sK2
    | spl3_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f314,plain,
    ( ~ spl3_11
    | ~ spl3_5
    | spl3_34
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f309,f215,f174,f140,f311,f90,f126])).

fof(f126,plain,
    ( spl3_11
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( spl3_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( spl3_14
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f174,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f215,plain,
    ( spl3_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f309,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ spl3_14
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(resolution,[],[f249,f217])).

fof(f217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_xboole_0)
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f175,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f230,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | spl3_14
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | spl3_14
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f108,f142,f83,f205])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_21
  <=> ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f142,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f108,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f218,plain,
    ( ~ spl3_4
    | spl3_23 ),
    inference(avatar_split_clause,[],[f44,f215,f86])).

fof(f86,plain,
    ( spl3_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f213,plain,
    ( ~ spl3_4
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f47,f210,f86])).

fof(f47,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f208,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f78,f142,f83,f87,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f87,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f206,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_21
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f202,f121,f100,f204,f76,f71])).

fof(f71,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f121,plain,
    ( spl3_10
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f202,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f201,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f201,plain,
    ( ! [X5] :
        ( ~ v3_pre_topc(X5,sK0)
        | k1_xboole_0 = X5
        | ~ r1_tarski(X5,sK1) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK1)
        | k1_xboole_0 = X5
        | ~ v3_pre_topc(X5,sK0)
        | ~ r1_tarski(X5,sK1) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f194,f102])).

fof(f102,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f194,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1)
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,X4) )
    | ~ spl3_10 ),
    inference(superposition,[],[f187,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK0)
        | ~ r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),sK1)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X1,X0))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_10 ),
    inference(superposition,[],[f171,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(X0,X1)),sK0)
        | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_10 ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl3_10 ),
    inference(resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f176,plain,
    ( ~ spl3_2
    | spl3_20
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f94,f81,f174,f76])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f143,plain,
    ( ~ spl3_2
    | spl3_4
    | ~ spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f96,f81,f140,f86,f76])).

fof(f96,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_split_clause,[],[f46,f126,f86])).

fof(f46,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f123,plain,
    ( spl3_4
    | spl3_10 ),
    inference(avatar_split_clause,[],[f43,f121,f86])).

fof(f43,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,
    ( ~ spl3_2
    | spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f97,f81,f106,f76])).

fof(f97,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f103,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f98,f81,f100])).

fof(f98,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f45,f90,f86])).

fof(f45,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (15891)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (15886)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (15897)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (15888)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (15909)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (15890)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (15915)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (15901)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (15887)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (15912)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (15892)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (15898)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (15907)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (15899)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (15889)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (15906)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (15893)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (15896)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (15911)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (15914)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (15900)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (15896)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f319,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f74,f79,f84,f93,f103,f109,f123,f129,f143,f176,f206,f208,f213,f218,f230,f314,f318])).
% 0.20/0.54  fof(f318,plain,(
% 0.20/0.54    spl3_22 | ~spl3_34),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f315])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    $false | (spl3_22 | ~spl3_34)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f212,f313,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.54  fof(f313,plain,(
% 0.20/0.54    r1_tarski(sK2,k1_xboole_0) | ~spl3_34),
% 0.20/0.54    inference(avatar_component_clause,[],[f311])).
% 0.20/0.54  fof(f311,plain,(
% 0.20/0.54    spl3_34 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    k1_xboole_0 != sK2 | spl3_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f210])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    spl3_22 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.54  fof(f314,plain,(
% 0.20/0.54    ~spl3_11 | ~spl3_5 | spl3_34 | ~spl3_14 | ~spl3_20 | ~spl3_23),
% 0.20/0.54    inference(avatar_split_clause,[],[f309,f215,f174,f140,f311,f90,f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    spl3_11 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    spl3_5 <=> r1_tarski(sK2,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    spl3_14 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    spl3_20 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    spl3_23 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(sK2,sK1) | ~v3_pre_topc(sK2,sK0) | (~spl3_14 | ~spl3_20 | ~spl3_23)),
% 0.20/0.54    inference(resolution,[],[f249,f217])).
% 0.20/0.54  fof(f217,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f215])).
% 0.20/0.54  fof(f249,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_xboole_0) | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0)) ) | (~spl3_14 | ~spl3_20)),
% 0.20/0.54    inference(backward_demodulation,[],[f175,f141])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f140])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0)) ) | ~spl3_20),
% 0.20/0.54    inference(avatar_component_clause,[],[f174])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    ~spl3_3 | ~spl3_7 | spl3_14 | ~spl3_21),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f226])).
% 0.20/0.54  fof(f226,plain,(
% 0.20/0.54    $false | (~spl3_3 | ~spl3_7 | spl3_14 | ~spl3_21)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f108,f142,f83,f205])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1)) ) | ~spl3_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f204])).
% 0.20/0.54  fof(f204,plain,(
% 0.20/0.54    spl3_21 <=> ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f140])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f106])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    spl3_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    ~spl3_4 | spl3_23),
% 0.20/0.54    inference(avatar_split_clause,[],[f44,f215,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    spl3_4 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(rectify,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f14])).
% 0.20/0.54  fof(f14,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    ~spl3_4 | ~spl3_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f47,f210,f86])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_14),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_14)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f78,f142,f83,f87,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    v2_tops_1(sK1,sK0) | ~spl3_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f86])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    l1_pre_topc(sK0) | ~spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    spl3_2 <=> l1_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    ~spl3_1 | ~spl3_2 | spl3_21 | ~spl3_6 | ~spl3_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f202,f121,f100,f204,f76,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    spl3_1 <=> v2_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl3_10 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl3_6 | ~spl3_10)),
% 0.20/0.54    inference(resolution,[],[f201,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.54  fof(f201,plain,(
% 0.20/0.54    ( ! [X5] : (~v3_pre_topc(X5,sK0) | k1_xboole_0 = X5 | ~r1_tarski(X5,sK1)) ) | (~spl3_6 | ~spl3_10)),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f200])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    ( ! [X5] : (~r1_tarski(X5,sK1) | k1_xboole_0 = X5 | ~v3_pre_topc(X5,sK0) | ~r1_tarski(X5,sK1)) ) | (~spl3_6 | ~spl3_10)),
% 0.20/0.54    inference(resolution,[],[f194,f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f100])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    ( ! [X4,X3] : (~r1_tarski(X4,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1) | k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X4)) ) | ~spl3_10),
% 0.20/0.54    inference(superposition,[],[f187,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f55,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK0) | ~r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),sK1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X1,X0)) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_10),
% 0.20/0.54    inference(superposition,[],[f171,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_pre_topc(k1_setfam_1(k2_tarski(X0,X1)),sK0) | ~r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_10),
% 0.20/0.54    inference(resolution,[],[f153,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f62,f54])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0) ) | ~spl3_10),
% 0.20/0.54    inference(resolution,[],[f122,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f121])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    ~spl3_2 | spl3_20 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f94,f81,f174,f76])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 0.20/0.54    inference(resolution,[],[f83,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    ~spl3_2 | spl3_4 | ~spl3_14 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f96,f81,f140,f86,f76])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.54    inference(resolution,[],[f83,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ~spl3_4 | spl3_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f46,f126,f86])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl3_4 | spl3_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f121,f86])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~spl3_2 | spl3_7 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f97,f81,f106,f76])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.54    inference(resolution,[],[f83,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    spl3_6 | ~spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f98,f81,f100])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.20/0.54    inference(resolution,[],[f83,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ~spl3_4 | spl3_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f45,f90,f86])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl3_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f42,f81])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f41,f76])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f40,f71])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    v2_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (15896)------------------------------
% 0.20/0.54  % (15896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15896)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (15896)Memory used [KB]: 10874
% 0.20/0.54  % (15896)Time elapsed: 0.140 s
% 0.20/0.54  % (15896)------------------------------
% 0.20/0.54  % (15896)------------------------------
% 0.20/0.54  % (15887)Refutation not found, incomplete strategy% (15887)------------------------------
% 0.20/0.54  % (15887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15887)Memory used [KB]: 1791
% 0.20/0.54  % (15887)Time elapsed: 0.136 s
% 0.20/0.54  % (15887)------------------------------
% 0.20/0.54  % (15887)------------------------------
% 0.20/0.54  % (15913)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (15903)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (15895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (15910)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (15908)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (15894)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (15898)Refutation not found, incomplete strategy% (15898)------------------------------
% 0.20/0.55  % (15898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15898)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15898)Memory used [KB]: 10874
% 0.20/0.55  % (15898)Time elapsed: 0.152 s
% 0.20/0.55  % (15898)------------------------------
% 0.20/0.55  % (15898)------------------------------
% 0.20/0.55  % (15905)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (15902)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (15915)Refutation not found, incomplete strategy% (15915)------------------------------
% 0.20/0.55  % (15915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15915)Memory used [KB]: 1663
% 0.20/0.55  % (15915)Time elapsed: 0.148 s
% 0.20/0.55  % (15915)------------------------------
% 0.20/0.55  % (15915)------------------------------
% 0.20/0.55  % (15902)Refutation not found, incomplete strategy% (15902)------------------------------
% 0.20/0.55  % (15902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (15902)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (15902)Memory used [KB]: 10746
% 0.20/0.55  % (15902)Time elapsed: 0.161 s
% 0.20/0.55  % (15902)------------------------------
% 0.20/0.55  % (15902)------------------------------
% 0.20/0.56  % (15904)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (15885)Success in time 0.202 s
%------------------------------------------------------------------------------
