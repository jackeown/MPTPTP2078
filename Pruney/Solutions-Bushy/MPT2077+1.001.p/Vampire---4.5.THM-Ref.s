%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  274 ( 761 expanded)
%              Number of leaves         :   61 ( 363 expanded)
%              Depth                    :   12
%              Number of atoms          : 1808 (5409 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (16869)Refutation not found, incomplete strategy% (16869)------------------------------
% (16869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16869)Termination reason: Refutation not found, incomplete strategy

% (16869)Memory used [KB]: 10746
% (16869)Time elapsed: 0.102 s
% (16869)------------------------------
% (16869)------------------------------
fof(f871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f128,f132,f160,f163,f169,f171,f177,f203,f205,f211,f213,f215,f219,f231,f244,f248,f257,f369,f371,f397,f399,f484,f533,f536,f580,f586,f597,f609,f620,f640,f646,f664,f696,f870])).

fof(f870,plain,(
    ~ spl7_67 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl7_67 ),
    inference(resolution,[],[f862,f68])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f862,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_67 ),
    inference(duplicate_literal_removal,[],[f861])).

fof(f861,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_67 ),
    inference(resolution,[],[f849,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f136,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f7,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK6(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK6(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f135,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK6(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f93,f85])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f849,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(sK6(k1_zfmisc_1(X7)))
        | ~ v1_xboole_0(X7) )
    | ~ spl7_67 ),
    inference(resolution,[],[f699,f135])).

fof(f699,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1),X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl7_67 ),
    inference(superposition,[],[f663,f94])).

fof(f94,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f69])).

fof(f69,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f663,plain,
    ( r2_hidden(sK4(sK0,sK1),o_0_0_xboole_0)
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl7_67
  <=> r2_hidden(sK4(sK0,sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f696,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_1
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_66 ),
    inference(avatar_split_clause,[],[f693,f657,f106,f111,f116,f121,f98,f184,f180,f150])).

fof(f150,plain,
    ( spl7_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f180,plain,
    ( spl7_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f184,plain,
    ( spl7_15
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f98,plain,
    ( spl7_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f121,plain,
    ( spl7_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f116,plain,
    ( spl7_5
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( spl7_4
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f106,plain,
    ( spl7_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f657,plain,
    ( spl7_66
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f693,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_66 ),
    inference(resolution,[],[f659,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK4(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK3(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK3(X0),X0)
            & v7_waybel_0(sK3(X0))
            & v4_orders_2(sK3(X0))
            & ~ v2_struct_0(sK3(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

fof(f659,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl7_66 ),
    inference(avatar_component_clause,[],[f657])).

fof(f664,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_1
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_66
    | spl7_67
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f649,f644,f661,f657,f106,f111,f116,f121,f98,f184,f180,f150])).

fof(f644,plain,
    ( spl7_65
  <=> ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f649,plain,
    ( r2_hidden(sK4(sK0,sK1),o_0_0_xboole_0)
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_65 ),
    inference(resolution,[],[f645,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK4(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f645,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f644])).

fof(f646,plain,
    ( ~ spl7_10
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_65
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f642,f638,f644,f106,f111,f116,f121,f184,f180,f150,f154])).

fof(f154,plain,
    ( spl7_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f638,plain,
    ( spl7_64
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK5(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f642,plain,
    ( ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_64 ),
    inference(duplicate_literal_removal,[],[f641])).

fof(f641,plain,
    ( ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_64 ),
    inference(resolution,[],[f639,f262])).

fof(f262,plain,(
    ! [X10,X11,X9] :
      ( ~ v2_struct_0(sK5(X9,X10,X11))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ r3_waybel_9(X9,X10,X11)
      | ~ l1_struct_0(X9) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X10,X11,X9] :
      ( ~ r3_waybel_9(X9,X10,X11)
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ v2_struct_0(sK5(X9,X10,X11))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_struct_0(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f82,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
                & m2_yellow_6(sK5(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f639,plain,
    ( ! [X0] :
        ( v2_struct_0(sK5(sK0,sK1,X0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f638])).

fof(f640,plain,
    ( ~ spl7_10
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_64
    | ~ spl7_63 ),
    inference(avatar_split_clause,[],[f636,f618,f638,f106,f111,f116,f121,f184,f180,f150,f154])).

fof(f618,plain,
    ( spl7_63
  <=> ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_63 ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_63 ),
    inference(resolution,[],[f619,f263])).

fof(f263,plain,(
    ! [X6,X8,X7] :
      ( v4_orders_2(sK5(X6,X7,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r3_waybel_9(X6,X7,X8)
      | ~ l1_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X6,X8,X7] :
      ( ~ r3_waybel_9(X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v4_orders_2(sK5(X6,X7,X8))
      | ~ l1_waybel_0(X7,X6)
      | ~ v7_waybel_0(X7)
      | ~ v4_orders_2(X7)
      | v2_struct_0(X7)
      | ~ l1_struct_0(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f82,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f619,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0) )
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f618])).

fof(f620,plain,
    ( ~ spl7_10
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_63
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f616,f595,f618,f106,f111,f116,f121,f184,f180,f150,f154])).

fof(f595,plain,
    ( spl7_62
  <=> ! [X0] :
        ( v2_struct_0(sK5(sK0,sK1,X0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f616,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_62 ),
    inference(duplicate_literal_removal,[],[f615])).

fof(f615,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_62 ),
    inference(resolution,[],[f596,f264])).

fof(f264,plain,(
    ! [X4,X5,X3] :
      ( v7_waybel_0(sK5(X3,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ r3_waybel_9(X3,X4,X5)
      | ~ l1_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_waybel_9(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | v7_waybel_0(sK5(X3,X4,X5))
      | ~ l1_waybel_0(X4,X3)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f82,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f596,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0)) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f595])).

fof(f609,plain,
    ( spl7_21
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_12
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f373,f363,f167,f200,f196,f192,f224])).

fof(f224,plain,
    ( spl7_21
  <=> v4_orders_2(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f192,plain,
    ( spl7_17
  <=> v7_waybel_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f196,plain,
    ( spl7_18
  <=> v4_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f200,plain,
    ( spl7_19
  <=> v2_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f167,plain,
    ( spl7_12
  <=> ! [X0] :
        ( v4_orders_2(sK2(X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f363,plain,
    ( spl7_30
  <=> l1_waybel_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f373,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v4_orders_2(sK2(sK3(sK0)))
    | ~ spl7_12
    | ~ spl7_30 ),
    inference(resolution,[],[f364,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v4_orders_2(sK2(X0)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f364,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f363])).

fof(f597,plain,
    ( ~ spl7_10
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_62
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f593,f584,f595,f106,f111,f116,f121,f184,f180,f150,f154])).

fof(f584,plain,
    ( spl7_61
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f593,plain,
    ( ! [X0] :
        ( v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_61 ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,
    ( ! [X0] :
        ( v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_61 ),
    inference(resolution,[],[f585,f265])).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f82,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f585,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | v2_struct_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f584])).

fof(f586,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_61
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f582,f578,f584,f106,f111,f116,f121,f184,f180,f150])).

fof(f578,plain,
    ( spl7_60
  <=> ! [X0] :
        ( ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0)) )
    | ~ spl7_60 ),
    inference(duplicate_literal_removal,[],[f581])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | r2_hidden(X0,o_0_0_xboole_0)
        | ~ l1_waybel_0(sK5(sK0,sK1,X0),sK0)
        | ~ v7_waybel_0(sK5(sK0,sK1,X0))
        | ~ v4_orders_2(sK5(sK0,sK1,X0))
        | v2_struct_0(sK5(sK0,sK1,X0)) )
    | ~ spl7_60 ),
    inference(resolution,[],[f579,f271])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(X2,o_0_0_xboole_0)
      | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,o_0_0_xboole_0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_yellow_6(sK5(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK5(X0,X1,X2))
      | ~ v4_orders_2(sK5(X0,X1,X2))
      | v2_struct_0(sK5(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f83,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k10_yellow_6(X0,X1) = o_0_0_xboole_0
      | v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f80,f69])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k10_yellow_6(X0,X1) = k1_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k10_yellow_6(X0,X1) = k1_xboole_0 )
            & ( k10_yellow_6(X0,X1) != k1_xboole_0
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f579,plain,
    ( ! [X0] :
        ( ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK1,X0) )
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f578])).

fof(f580,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | spl7_60
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f571,f102,f578,f106,f111,f116,f121,f184,f180,f150])).

fof(f102,plain,
    ( spl7_2
  <=> ! [X2] :
        ( ~ v3_yellow_6(X2,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f571,plain,
    ( ! [X0] :
        ( ~ v3_yellow_6(sK5(sK0,sK1,X0),sK0)
        | ~ r3_waybel_9(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f103,f82])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ m2_yellow_6(X2,sK0,sK1)
        | ~ v3_yellow_6(X2,sK0) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f536,plain,
    ( ~ spl7_32
    | ~ spl7_33
    | ~ spl7_24
    | ~ spl7_21
    | spl7_16
    | ~ spl7_15
    | ~ spl7_14
    | spl7_9
    | ~ spl7_22
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f534,f481,f237,f150,f180,f184,f188,f224,f254,f385,f381])).

fof(f381,plain,
    ( spl7_32
  <=> v3_yellow_6(sK2(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f385,plain,
    ( spl7_33
  <=> l1_waybel_0(sK2(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f254,plain,
    ( spl7_24
  <=> v7_waybel_0(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f188,plain,
    ( spl7_16
  <=> v2_struct_0(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f237,plain,
    ( spl7_22
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(k10_yellow_6(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v3_yellow_6(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f481,plain,
    ( spl7_46
  <=> v1_xboole_0(k10_yellow_6(sK0,sK2(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f534,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | ~ spl7_22
    | ~ spl7_46 ),
    inference(resolution,[],[f483,f238])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k10_yellow_6(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v3_yellow_6(X1,X0) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f237])).

fof(f483,plain,
    ( v1_xboole_0(k10_yellow_6(sK0,sK2(sK3(sK0))))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f481])).

fof(f533,plain,
    ( ~ spl7_24
    | spl7_46
    | ~ spl7_33
    | ~ spl7_21
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_16
    | spl7_45 ),
    inference(avatar_split_clause,[],[f528,f477,f188,f184,f180,f150,f224,f385,f481,f254])).

fof(f477,plain,
    ( spl7_45
  <=> m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f528,plain,
    ( v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | v1_xboole_0(k10_yellow_6(sK0,sK2(sK3(sK0))))
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | spl7_45 ),
    inference(resolution,[],[f352,f479])).

fof(f479,plain,
    ( ~ m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0)))),u1_struct_0(sK0))
    | spl7_45 ),
    inference(avatar_component_clause,[],[f477])).

fof(f352,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(k10_yellow_6(X1,X0)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X0)
      | ~ l1_waybel_0(X0,X1)
      | v1_xboole_0(k10_yellow_6(X1,X0))
      | ~ v7_waybel_0(X0) ) ),
    inference(resolution,[],[f307,f85])).

fof(f307,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k10_yellow_6(X4,X3))
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_waybel_0(X3,X4)
      | v1_xboole_0(k10_yellow_6(X4,X3))
      | ~ v7_waybel_0(X3) ) ),
    inference(resolution,[],[f216,f86])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X1,X0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f91,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f484,plain,
    ( ~ spl7_45
    | spl7_46
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_16
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_33
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f474,f367,f385,f254,f224,f188,f184,f180,f150,f481,f477])).

fof(f367,plain,
    ( spl7_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f474,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k10_yellow_6(sK0,sK2(sK3(sK0))))
    | ~ m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | ~ v7_waybel_0(sK2(sK3(sK0)))
    | ~ v4_orders_2(sK2(sK3(sK0)))
    | v2_struct_0(sK2(sK3(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(k10_yellow_6(sK0,sK2(sK3(sK0))))
    | ~ m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(k10_yellow_6(sK0,sK2(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(resolution,[],[f346,f368])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f367])).

fof(f346,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK6(k10_yellow_6(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(k10_yellow_6(X0,X1))
      | ~ m1_subset_1(sK6(k10_yellow_6(X0,X1)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f249,f85])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(resolution,[],[f81,f86])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

fof(f399,plain,
    ( ~ spl7_30
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_20
    | spl7_33 ),
    inference(avatar_split_clause,[],[f398,f385,f209,f200,f196,f192,f363])).

fof(f209,plain,
    ( spl7_20
  <=> ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f398,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ spl7_20
    | spl7_33 ),
    inference(resolution,[],[f387,f210])).

fof(f210,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f387,plain,
    ( ~ l1_waybel_0(sK2(sK3(sK0)),sK0)
    | spl7_33 ),
    inference(avatar_component_clause,[],[f385])).

fof(f397,plain,
    ( ~ spl7_30
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_7
    | spl7_32 ),
    inference(avatar_split_clause,[],[f396,f381,f126,f200,f196,f192,f363])).

fof(f126,plain,
    ( spl7_7
  <=> ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f396,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ l1_waybel_0(sK3(sK0),sK0)
    | ~ spl7_7
    | spl7_32 ),
    inference(resolution,[],[f382,f127])).

fof(f127,plain,
    ( ! [X3] :
        ( v3_yellow_6(sK2(X3),sK0)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f382,plain,
    ( ~ v3_yellow_6(sK2(sK3(sK0)),sK0)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f381])).

fof(f371,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | spl7_30 ),
    inference(avatar_split_clause,[],[f370,f363,f98,f184,f180,f150])).

fof(f370,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_30 ),
    inference(resolution,[],[f365,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f365,plain,
    ( ~ l1_waybel_0(sK3(sK0),sK0)
    | spl7_30 ),
    inference(avatar_component_clause,[],[f363])).

fof(f369,plain,
    ( spl7_1
    | spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_19
    | ~ spl7_18
    | ~ spl7_17
    | ~ spl7_30
    | spl7_31
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f361,f130,f367,f363,f192,f196,f200,f184,f180,f150,f98])).

fof(f130,plain,
    ( spl7_8
  <=> ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ v7_waybel_0(sK3(sK0))
        | ~ v4_orders_2(sK3(sK0))
        | v2_struct_0(sK3(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v1_compts_1(sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2(sK3(sK0)),X0)
        | ~ l1_waybel_0(sK3(sK0),sK0)
        | ~ v7_waybel_0(sK3(sK0))
        | ~ v4_orders_2(sK3(sK0))
        | v2_struct_0(sK3(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v1_compts_1(sK0)
        | v2_struct_0(sK3(sK0))
        | ~ v4_orders_2(sK3(sK0))
        | ~ v7_waybel_0(sK3(sK0))
        | ~ l1_waybel_0(sK3(sK0),sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f274,f131])).

fof(f131,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK2(X3),sK0,X3)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ l1_waybel_0(sK3(X0),X0)
      | ~ v7_waybel_0(sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m2_yellow_6(X1,X0,sK3(X0))
      | ~ l1_waybel_0(sK3(X0),X0)
      | ~ v7_waybel_0(sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f84,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK3(X0),X2)
      | v1_compts_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,X3)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f257,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | spl7_24
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f252,f175,f200,f196,f192,f254,f98,f184,f180,f150])).

fof(f175,plain,
    ( spl7_13
  <=> ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f252,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | v7_waybel_0(sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_13 ),
    inference(resolution,[],[f176,f77])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v7_waybel_0(sK2(X0)) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f248,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl7_23 ),
    inference(resolution,[],[f242,f68])).

fof(f242,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_23
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f244,plain,
    ( ~ spl7_23
    | spl7_22 ),
    inference(avatar_split_clause,[],[f233,f237,f240])).

fof(f233,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(k10_yellow_6(X2,X3))
      | ~ v1_xboole_0(o_0_0_xboole_0)
      | ~ v3_yellow_6(X3,X2)
      | ~ l1_waybel_0(X3,X2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(extensionality_resolution,[],[f133,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k10_yellow_6(X0,X1) != o_0_0_xboole_0
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f69])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k10_yellow_6(X0,X1) != k1_xboole_0
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f133,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f94,f94])).

fof(f231,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f230,f200,f98,f184,f180,f150])).

fof(f230,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_19 ),
    inference(resolution,[],[f202,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f202,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f219,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | spl7_18 ),
    inference(avatar_split_clause,[],[f218,f196,f98,f184,f180,f150])).

fof(f218,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_18 ),
    inference(resolution,[],[f198,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v4_orders_2(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f198,plain,
    ( ~ v4_orders_2(sK3(sK0))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f215,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | spl7_17 ),
    inference(avatar_split_clause,[],[f214,f192,f98,f184,f180,f150])).

fof(f214,plain,
    ( v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_17 ),
    inference(resolution,[],[f194,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v7_waybel_0(sK3(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f194,plain,
    ( ~ v7_waybel_0(sK3(sK0))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f213,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f186,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,sK1) )
        & l1_waybel_0(sK1,sK0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) )
      | ~ v1_compts_1(sK0) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK2(X3),sK0)
            & m2_yellow_6(sK2(X3),sK0,X3) )
          | ~ l1_waybel_0(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK0) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK0)
                | ~ m2_yellow_6(X2,sK0,X1) )
            & l1_waybel_0(X1,sK0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK0)
                & m2_yellow_6(X4,sK0,X3) )
            | ~ l1_waybel_0(X3,sK0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK0)
            | ~ m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ v3_yellow_6(X2,sK0)
          | ~ m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,sK0)
          & m2_yellow_6(X4,sK0,X3) )
     => ( v3_yellow_6(sK2(X3),sK0)
        & m2_yellow_6(sK2(X3),sK0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f211,plain,
    ( spl7_9
    | ~ spl7_10
    | spl7_20
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f207,f130,f209,f154,f150])).

fof(f207,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( ! [X0] :
        ( l1_waybel_0(sK2(X0),sK0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f90,f131])).

fof(f205,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f182,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f182,plain,
    ( ~ v2_pre_topc(sK0)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f203,plain,
    ( spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | spl7_1
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | spl7_19
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f178,f158,f200,f196,f192,f188,f98,f184,f180,f150])).

fof(f158,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f178,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ v4_orders_2(sK3(sK0))
    | ~ v7_waybel_0(sK3(sK0))
    | ~ v2_struct_0(sK2(sK3(sK0)))
    | v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_11 ),
    inference(resolution,[],[f159,f77])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v2_struct_0(sK2(X0)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f177,plain,
    ( spl7_9
    | ~ spl7_10
    | spl7_13
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f173,f130,f175,f154,f150])).

fof(f173,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f89,f131])).

fof(f171,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f152,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f152,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f169,plain,
    ( spl7_9
    | ~ spl7_10
    | spl7_12
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f165,f130,f167,f154,f150])).

fof(f165,plain,
    ( ! [X0] :
        ( v4_orders_2(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X0] :
        ( v4_orders_2(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f88,f131])).

fof(f163,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f161,f60])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_10 ),
    inference(resolution,[],[f156,f70])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f156,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f160,plain,
    ( spl7_9
    | ~ spl7_10
    | spl7_11
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f148,f130,f158,f154,f150])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK2(X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f87,f131])).

fof(f132,plain,
    ( spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f61,f130,f98])).

fof(f61,plain,(
    ! [X3] :
      ( m2_yellow_6(sK2(X3),sK0,X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,
    ( spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f62,f126,f98])).

fof(f62,plain,(
    ! [X3] :
      ( v3_yellow_6(sK2(X3),sK0)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,
    ( ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f63,f121,f98])).

fof(f63,plain,
    ( ~ v2_struct_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f64,f116,f98])).

fof(f64,plain,
    ( v4_orders_2(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f65,f111,f98])).

fof(f65,plain,
    ( v7_waybel_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f66,f106,f98])).

fof(f66,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f67,f102,f98])).

fof(f67,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK0)
      | ~ m2_yellow_6(X2,sK0,sK1)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f47])).

%------------------------------------------------------------------------------
