%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 216 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :  358 (1291 expanded)
%              Number of equality atoms :   35 ( 155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f89,f100,f108,f114,f120,f139,f142])).

fof(f142,plain,(
    ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl3_18 ),
    inference(resolution,[],[f138,f39])).

fof(f39,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f138,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_18
  <=> r2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f139,plain,
    ( spl3_18
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f135,f118,f95,f137])).

fof(f95,plain,
    ( spl3_12
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f118,plain,
    ( spl3_15
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f135,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f123,f119])).

fof(f119,plain,
    ( r2_xboole_0(sK2,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f123,plain,
    ( ! [X1] :
        ( ~ r2_xboole_0(X1,sK1)
        | r2_xboole_0(X1,sK2) )
    | ~ spl3_12 ),
    inference(resolution,[],[f115,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r2_xboole_0(X0,sK2) )
    | ~ spl3_12 ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

fof(f96,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f120,plain,
    ( spl3_15
    | spl3_13
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f87,f57,f41,f98,f118])).

fof(f98,plain,
    ( spl3_13
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f41,plain,
    ( spl3_1
  <=> m1_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f87,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f92,f42])).

fof(f42,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ m1_orders_2(X1,sK0,sK1)
        | sK1 = X1
        | r2_xboole_0(X1,sK1) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(resolution,[],[f88,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f114,plain,
    ( spl3_10
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f110,f106,f49,f57,f61,f65,f69,f73,f77])).

fof(f77,plain,
    ( spl3_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f73,plain,
    ( spl3_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f69,plain,
    ( spl3_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f65,plain,
    ( spl3_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f61,plain,
    ( spl3_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f49,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( spl3_14
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f110,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_14 ),
    inference(resolution,[],[f107,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(f107,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f103,f98,f45,f106])).

fof(f45,plain,
    ( spl3_2
  <=> m1_orders_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f103,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(superposition,[],[f46,f99])).

fof(f99,plain,
    ( sK1 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f46,plain,
    ( m1_orders_2(sK1,sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f100,plain,
    ( spl3_12
    | spl3_13
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f93,f87,f53,f45,f98,f95])).

fof(f53,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f91,f46])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | sK2 = X0
        | r2_xboole_0(X0,sK2) )
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f90,f54])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f89,plain,
    ( spl3_10
    | ~ spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f81,f61,f87,f65,f69,f73,f77])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f33,f62])).

fof(f62,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X2,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f79,plain,(
    ~ spl3_10 ),
    inference(avatar_split_clause,[],[f21,f77])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    & m1_orders_2(sK1,sK0,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK0,X1)
              & m1_orders_2(X1,sK0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( m1_orders_2(X2,sK0,X1)
            & m1_orders_2(X1,sK0,X2)
            & k1_xboole_0 != X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( m1_orders_2(X2,sK0,sK1)
          & m1_orders_2(sK1,sK0,X2)
          & k1_xboole_0 != sK1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( m1_orders_2(X2,sK0,sK1)
        & m1_orders_2(sK1,sK0,X2)
        & k1_xboole_0 != sK1
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( m1_orders_2(sK2,sK0,sK1)
      & m1_orders_2(sK1,sK0,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f22,f73])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f45])).

fof(f29,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f41])).

fof(f30,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (24991)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (25001)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (24992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (24990)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (24988)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (24992)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f67,f71,f75,f79,f89,f100,f108,f114,f120,f139,f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ~spl3_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    $false | ~spl3_18),
% 0.20/0.48    inference(resolution,[],[f138,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK2) | ~spl3_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl3_18 <=> r2_xboole_0(sK2,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl3_18 | ~spl3_12 | ~spl3_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f135,f118,f95,f137])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl3_12 <=> r2_xboole_0(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl3_15 <=> r2_xboole_0(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK2) | (~spl3_12 | ~spl3_15)),
% 0.20/0.48    inference(resolution,[],[f123,f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    r2_xboole_0(sK2,sK1) | ~spl3_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_xboole_0(X1,sK1) | r2_xboole_0(X1,sK2)) ) | ~spl3_12),
% 0.20/0.48    inference(resolution,[],[f115,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | r2_xboole_0(X0,sK2)) ) | ~spl3_12),
% 0.20/0.48    inference(resolution,[],[f96,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    r2_xboole_0(sK1,sK2) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f95])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl3_15 | spl3_13 | ~spl3_1 | ~spl3_5 | ~spl3_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f116,f87,f57,f41,f98,f118])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl3_13 <=> sK1 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl3_1 <=> m1_orders_2(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl3_11 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    sK1 = sK2 | r2_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_5 | ~spl3_11)),
% 0.20/0.48    inference(resolution,[],[f92,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    m1_orders_2(sK2,sK0,sK1) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_orders_2(X1,sK0,sK1) | sK1 = X1 | r2_xboole_0(X1,sK1)) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.48    inference(resolution,[],[f90,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.20/0.48    inference(resolution,[],[f88,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl3_10 | ~spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_3 | ~spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f110,f106,f49,f57,f61,f65,f69,f73,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl3_10 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl3_9 <=> v3_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl3_8 <=> v4_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl3_7 <=> v5_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl3_6 <=> l1_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl3_3 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_14 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl3_14),
% 0.20/0.48    inference(resolution,[],[f107,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    m1_orders_2(sK1,sK0,sK1) | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl3_14 | ~spl3_2 | ~spl3_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f103,f98,f45,f106])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl3_2 <=> m1_orders_2(sK1,sK0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    m1_orders_2(sK1,sK0,sK1) | (~spl3_2 | ~spl3_13)),
% 0.20/0.48    inference(superposition,[],[f46,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    sK1 = sK2 | ~spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f98])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    m1_orders_2(sK1,sK0,sK2) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl3_12 | spl3_13 | ~spl3_2 | ~spl3_4 | ~spl3_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f87,f53,f45,f98,f95])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    sK1 = sK2 | r2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_4 | ~spl3_11)),
% 0.20/0.48    inference(resolution,[],[f91,f46])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | sK2 = X0 | r2_xboole_0(X0,sK2)) ) | (~spl3_4 | ~spl3_11)),
% 0.20/0.48    inference(resolution,[],[f90,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl3_10 | ~spl3_9 | ~spl3_8 | ~spl3_7 | spl3_11 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f81,f61,f87,f65,f69,f73,f77])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_6),
% 0.20/0.48    inference(resolution,[],[f33,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    l1_orders_2(sK0) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f61])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X2,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f77])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ((m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f73])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v3_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f69])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v4_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f65])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v5_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f61])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    l1_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f53])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f49])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f45])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    m1_orders_2(sK1,sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f41])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_orders_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24992)------------------------------
% 0.20/0.48  % (24992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24992)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24992)Memory used [KB]: 10618
% 0.20/0.48  % (24992)Time elapsed: 0.009 s
% 0.20/0.48  % (24992)------------------------------
% 0.20/0.48  % (24992)------------------------------
% 0.20/0.48  % (25000)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (24985)Success in time 0.13 s
%------------------------------------------------------------------------------
