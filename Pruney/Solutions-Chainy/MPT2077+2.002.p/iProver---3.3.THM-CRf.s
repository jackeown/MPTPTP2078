%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:24 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_64)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f49])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK2(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f61,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK7(X3),X0)
        & m2_yellow_6(sK7(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v3_yellow_6(X2,X0)
            | ~ m2_yellow_6(X2,X0,sK6) )
        & l1_waybel_0(sK6,X0)
        & v7_waybel_0(sK6)
        & v4_orders_2(sK6)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
                ( ~ v3_yellow_6(X2,sK5)
                | ~ m2_yellow_6(X2,sK5,X1) )
            & l1_waybel_0(X1,sK5)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK5) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK5)
                & m2_yellow_6(X4,sK5,X3) )
            | ~ l1_waybel_0(X3,sK5)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK5) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK5)
            | ~ m2_yellow_6(X2,sK5,sK6) )
        & l1_waybel_0(sK6,sK5)
        & v7_waybel_0(sK6)
        & v4_orders_2(sK6)
        & ~ v2_struct_0(sK6) )
      | ~ v1_compts_1(sK5) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK7(X3),sK5)
            & m2_yellow_6(sK7(X3),sK5,X3) )
          | ~ l1_waybel_0(X3,sK5)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK5) )
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f58,f61,f60,f59])).

fof(f95,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
                & m2_yellow_6(sK1(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f47])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK1(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
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
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK5)
      | ~ m2_yellow_6(X2,sK5,sK6)
      | ~ v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f99,plain,
    ( ~ v2_struct_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,
    ( v4_orders_2(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,
    ( v7_waybel_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X3] :
      ( m2_yellow_6(sK7(X3),sK5,X3)
      | ~ l1_waybel_0(X3,sK5)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f81,plain,(
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

fof(f14,axiom,(
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
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_hidden(X1,k6_yellow_6(X0))
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f54,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK3(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK3(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK3(X0),X0)
            & v7_waybel_0(sK3(X0))
            & v4_orders_2(sK3(X0))
            & ~ v2_struct_0(sK3(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK4(X0,X3))
                & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).

fof(f93,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X3] :
      ( v3_yellow_6(sK7(X3),sK5)
      | ~ l1_waybel_0(X3,sK5)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6650,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_810,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_811,plain,
    ( r3_waybel_9(sK5,X0,sK2(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_815,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK5,X0,sK2(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_811,c_40,c_38])).

cnf(c_816,plain,
    ( r3_waybel_9(sK5,X0,sK2(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_815])).

cnf(c_6633,plain,
    ( r3_waybel_9(sK5,X0,sK2(sK5,X0)) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_840,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_841,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_845,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_40,c_38])).

cnf(c_846,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_845])).

cnf(c_6632,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_15,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ v3_yellow_6(X0,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_590,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK5)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_591,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5)
    | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK5)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m2_yellow_6(X0,sK5,sK6)
    | v2_struct_0(X0)
    | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_40,c_39,c_38])).

cnf(c_596,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_6641,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_35,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_50,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_51,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v4_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_52,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v7_waybel_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_53,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_597,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_525,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_526,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_1149,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_526,c_38])).

cnf(c_1150,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | l1_waybel_0(X0,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1149])).

cnf(c_1152,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1150,c_40])).

cnf(c_1153,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | l1_waybel_0(X0,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1152])).

cnf(c_6746,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_6747,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6746])).

cnf(c_12,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_497,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_498,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_1175,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_498,c_38])).

cnf(c_1176,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1175])).

cnf(c_1178,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1176,c_40])).

cnf(c_1179,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1178])).

cnf(c_6751,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_6752,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6751])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_469,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_470,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_1201,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_38])).

cnf(c_1202,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_1204,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_40])).

cnf(c_1205,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1204])).

cnf(c_6758,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_6759,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6758])).

cnf(c_7768,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | k10_yellow_6(sK5,X0) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6641,c_50,c_51,c_52,c_53,c_597,c_6747,c_6752,c_6759])).

cnf(c_7769,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7768])).

cnf(c_7913,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6632,c_7769])).

cnf(c_9254,plain,
    ( v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top
    | v1_compts_1(sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7913,c_50,c_51,c_52,c_53])).

cnf(c_9255,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9254])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_441,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_442,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1227,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_38])).

cnf(c_1228,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_1230,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_40])).

cnf(c_1231,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1230])).

cnf(c_6622,plain,
    ( m2_yellow_6(X0,sK5,X1) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_7917,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK5,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6632,c_6622])).

cnf(c_9260,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9255,c_7917])).

cnf(c_37,negated_conjecture,
    ( m2_yellow_6(sK7(X0),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6643,plain,
    ( m2_yellow_6(sK7(X0),sK5,X0) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6654,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1034,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_39])).

cnf(c_1035,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1034])).

cnf(c_1039,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1035,c_40,c_38])).

cnf(c_1040,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1039])).

cnf(c_6626,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6649,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7520,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6626,c_6649])).

cnf(c_8501,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) = iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6654,c_7520])).

cnf(c_17,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_938,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_939,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_943,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_939,c_40,c_38])).

cnf(c_944,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_943])).

cnf(c_6629,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_945,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_7802,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | r3_waybel_9(sK5,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6629,c_945,c_7520])).

cnf(c_7803,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7802])).

cnf(c_7808,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X0),X1)) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6654,c_7803])).

cnf(c_18,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_906,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_907,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | ~ m2_yellow_6(X0,sK5,X2)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_909,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | ~ m2_yellow_6(X0,sK5,X2)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_907,c_40,c_38])).

cnf(c_910,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | ~ m2_yellow_6(X0,sK5,X2)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_6630,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | r3_waybel_9(sK5,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK5,X2) != iProver_top
    | l1_waybel_0(X2,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_8510,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK5,X0) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7808,c_6630])).

cnf(c_9882,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK5,X0) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8501,c_8510])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_789,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_790,plain,
    ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_40,c_38])).

cnf(c_6634,plain,
    ( r3_waybel_9(sK5,sK3(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_10036,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9882,c_6634])).

cnf(c_28,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_719,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_720,plain,
    ( v1_compts_1(sK5)
    | ~ v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_722,plain,
    ( v1_compts_1(sK5)
    | ~ v2_struct_0(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_40,c_39,c_38,c_64])).

cnf(c_724,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_733,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_734,plain,
    ( v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | v4_orders_2(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_736,plain,
    ( v4_orders_2(sK3(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_40,c_38])).

cnf(c_737,plain,
    ( v1_compts_1(sK5)
    | v4_orders_2(sK3(sK5)) ),
    inference(renaming,[status(thm)],[c_736])).

cnf(c_738,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v4_orders_2(sK3(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_747,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_39])).

cnf(c_748,plain,
    ( v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | v7_waybel_0(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_750,plain,
    ( v7_waybel_0(sK3(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_748,c_40,c_38])).

cnf(c_751,plain,
    ( v1_compts_1(sK5)
    | v7_waybel_0(sK3(sK5)) ),
    inference(renaming,[status(thm)],[c_750])).

cnf(c_752,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v7_waybel_0(sK3(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_25,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_761,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_762,plain,
    ( l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_764,plain,
    ( l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_40,c_38])).

cnf(c_766,plain,
    ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_6864,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_6865,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(X0,sK5) = iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6864])).

cnf(c_6863,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_6869,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6863])).

cnf(c_6862,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_6873,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6862])).

cnf(c_10114,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10036,c_724,c_738,c_752,c_766,c_6865,c_6869,c_6873,c_8501])).

cnf(c_10115,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10114])).

cnf(c_10120,plain,
    ( l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6643,c_10115])).

cnf(c_6636,plain,
    ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_7005,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6643,c_6622])).

cnf(c_7294,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6636,c_7005])).

cnf(c_8129,plain,
    ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7294,c_724,c_738,c_752])).

cnf(c_8130,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8129])).

cnf(c_10126,plain,
    ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10120,c_724,c_738,c_752,c_766,c_8130])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6652,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7419,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6650,c_6652])).

cnf(c_10135,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10126,c_7419])).

cnf(c_1421,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | l1_waybel_0(X2,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK7(X1) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1153])).

cnf(c_1422,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1397,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(X2)
    | X0 != X1
    | sK7(X1) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1179])).

cnf(c_1398,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK7(X0)) ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_1373,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK7(X1) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1205])).

cnf(c_1374,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1373])).

cnf(c_1349,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | v1_compts_1(sK5)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK7(X1) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_1231])).

cnf(c_1350,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK7(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1349])).

cnf(c_16,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,negated_conjecture,
    ( v3_yellow_6(sK7(X0),sK5)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_623,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK5)
    | v1_compts_1(sK5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0
    | sK7(X2) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_624,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK7(X0))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | ~ l1_pre_topc(sK5)
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_628,plain,
    ( ~ v7_waybel_0(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK7(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | ~ l1_waybel_0(X0,sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_40,c_39,c_38])).

cnf(c_629,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK7(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_1604,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1350,c_629])).

cnf(c_1615,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1374,c_1604])).

cnf(c_1626,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1615])).

cnf(c_1632,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1422,c_1626])).

cnf(c_6998,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_6999,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6998])).

cnf(c_10330,plain,
    ( v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10135,c_724,c_738,c_752,c_766,c_6999])).

cnf(c_11517,plain,
    ( r3_waybel_9(sK5,sK6,X0) != iProver_top
    | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9260,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6999,c_10135])).

cnf(c_11518,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11517])).

cnf(c_11524,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6633,c_11518])).

cnf(c_22,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1004,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_1005,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1009,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_40,c_38])).

cnf(c_1010,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1009])).

cnf(c_6726,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_6727,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6726])).

cnf(c_11816,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11524,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6727,c_6999,c_10135])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_873,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_874,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_873])).

cnf(c_878,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_874,c_40,c_38])).

cnf(c_879,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_878])).

cnf(c_6631,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_11828,plain,
    ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_11816,c_6631])).

cnf(c_6737,plain,
    ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_6738,plain,
    ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6737])).

cnf(c_11924,plain,
    ( r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11828,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6727,c_6738,c_6999,c_10135])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6648,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11929,plain,
    ( r1_tarski(k1_xboole_0,sK2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11924,c_6648])).

cnf(c_12882,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_6650,c_11929])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.55/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/1.00  
% 3.55/1.00  ------  iProver source info
% 3.55/1.00  
% 3.55/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.55/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/1.00  git: non_committed_changes: false
% 3.55/1.00  git: last_make_outside_of_git: false
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    ""
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         true
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     num_symb
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       true
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.00  --demod_use_ground                      true
% 3.55/1.00  --sup_to_prop_solver                    passive
% 3.55/1.00  --sup_prop_simpl_new                    true
% 3.55/1.00  --sup_prop_simpl_given                  true
% 3.55/1.00  --sup_fun_splitting                     true
% 3.55/1.00  --sup_smt_interval                      50000
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Simplification Setup
% 3.55/1.00  
% 3.55/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_immed_triv                        [TrivRules]
% 3.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_bw_main                     []
% 3.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_input_bw                          []
% 3.55/1.00  
% 3.55/1.00  ------ Combination Options
% 3.55/1.00  
% 3.55/1.00  --comb_res_mult                         3
% 3.55/1.00  --comb_sup_mult                         2
% 3.55/1.00  --comb_inst_mult                        10
% 3.55/1.00  
% 3.55/1.00  ------ Debug Options
% 3.55/1.00  
% 3.55/1.00  --dbg_backtrace                         false
% 3.55/1.00  --dbg_dump_prop_clauses                 false
% 3.55/1.00  --dbg_dump_prop_clauses_file            -
% 3.55/1.00  --dbg_out_stat                          false
% 3.55/1.00  ------ Parsing...
% 3.55/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/1.00  ------ Proving...
% 3.55/1.00  ------ Problem Properties 
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  clauses                                 35
% 3.55/1.00  conjectures                             6
% 3.55/1.00  EPR                                     14
% 3.55/1.00  Horn                                    15
% 3.55/1.00  unary                                   3
% 3.55/1.00  binary                                  12
% 3.55/1.00  lits                                    142
% 3.55/1.00  lits eq                                 3
% 3.55/1.00  fd_pure                                 0
% 3.55/1.00  fd_pseudo                               0
% 3.55/1.00  fd_cond                                 0
% 3.55/1.00  fd_pseudo_cond                          1
% 3.55/1.00  AC symbols                              0
% 3.55/1.00  
% 3.55/1.00  ------ Schedule dynamic 5 is on 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  Current options:
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    ""
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         true
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     none
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       false
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.00  --demod_use_ground                      true
% 3.55/1.00  --sup_to_prop_solver                    passive
% 3.55/1.00  --sup_prop_simpl_new                    true
% 3.55/1.00  --sup_prop_simpl_given                  true
% 3.55/1.00  --sup_fun_splitting                     true
% 3.55/1.00  --sup_smt_interval                      50000
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Simplification Setup
% 3.55/1.00  
% 3.55/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_immed_triv                        [TrivRules]
% 3.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_bw_main                     []
% 3.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_input_bw                          []
% 3.55/1.00  
% 3.55/1.00  ------ Combination Options
% 3.55/1.00  
% 3.55/1.00  --comb_res_mult                         3
% 3.55/1.00  --comb_sup_mult                         2
% 3.55/1.00  --comb_inst_mult                        10
% 3.55/1.00  
% 3.55/1.00  ------ Debug Options
% 3.55/1.00  
% 3.55/1.00  --dbg_backtrace                         false
% 3.55/1.00  --dbg_dump_prop_clauses                 false
% 3.55/1.00  --dbg_dump_prop_clauses_file            -
% 3.55/1.00  --dbg_out_stat                          false
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  ------ Proving...
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS status Theorem for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00   Resolution empty clause
% 3.55/1.00  
% 3.55/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  fof(f3,axiom,(
% 3.55/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f69,plain,(
% 3.55/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f3])).
% 3.55/1.00  
% 3.55/1.00  fof(f13,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f34,plain,(
% 3.55/1.00    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f13])).
% 3.55/1.00  
% 3.55/1.00  fof(f35,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f34])).
% 3.55/1.00  
% 3.55/1.00  fof(f49,plain,(
% 3.55/1.00    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f50,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f49])).
% 3.55/1.00  
% 3.55/1.00  fof(f85,plain,(
% 3.55/1.00    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK2(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f50])).
% 3.55/1.00  
% 3.55/1.00  fof(f15,conjecture,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f16,negated_conjecture,(
% 3.55/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.55/1.00    inference(negated_conjecture,[],[f15])).
% 3.55/1.00  
% 3.55/1.00  fof(f38,plain,(
% 3.55/1.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f16])).
% 3.55/1.00  
% 3.55/1.00  fof(f39,plain,(
% 3.55/1.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f38])).
% 3.55/1.00  
% 3.55/1.00  fof(f56,plain,(
% 3.55/1.00    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/1.00    inference(nnf_transformation,[],[f39])).
% 3.55/1.00  
% 3.55/1.00  fof(f57,plain,(
% 3.55/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f56])).
% 3.55/1.00  
% 3.55/1.00  fof(f58,plain,(
% 3.55/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/1.00    inference(rectify,[],[f57])).
% 3.55/1.00  
% 3.55/1.00  fof(f61,plain,(
% 3.55/1.00    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK7(X3),X0) & m2_yellow_6(sK7(X3),X0,X3)))) )),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f60,plain,(
% 3.55/1.00    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK6)) & l1_waybel_0(sK6,X0) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))) )),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f59,plain,(
% 3.55/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,X1)) & l1_waybel_0(X1,sK5) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK5)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK5) & m2_yellow_6(X4,sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f62,plain,(
% 3.55/1.00    ((! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6)) & l1_waybel_0(sK6,sK5) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) | ~v1_compts_1(sK5)) & (! [X3] : ((v3_yellow_6(sK7(X3),sK5) & m2_yellow_6(sK7(X3),sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f58,f61,f60,f59])).
% 3.55/1.00  
% 3.55/1.00  fof(f95,plain,(
% 3.55/1.00    v2_pre_topc(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f94,plain,(
% 3.55/1.00    ~v2_struct_0(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f96,plain,(
% 3.55/1.00    l1_pre_topc(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f12,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f32,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f12])).
% 3.55/1.00  
% 3.55/1.00  fof(f33,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f32])).
% 3.55/1.00  
% 3.55/1.00  fof(f47,plain,(
% 3.55/1.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f48,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f47])).
% 3.55/1.00  
% 3.55/1.00  fof(f82,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (m2_yellow_6(sK1(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f48])).
% 3.55/1.00  
% 3.55/1.00  fof(f9,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f26,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f9])).
% 3.55/1.00  
% 3.55/1.00  fof(f27,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f26])).
% 3.55/1.00  
% 3.55/1.00  fof(f46,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(nnf_transformation,[],[f27])).
% 3.55/1.00  
% 3.55/1.00  fof(f79,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f46])).
% 3.55/1.00  
% 3.55/1.00  fof(f103,plain,(
% 3.55/1.00    ( ! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6) | ~v1_compts_1(sK5)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f99,plain,(
% 3.55/1.00    ~v2_struct_0(sK6) | ~v1_compts_1(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f100,plain,(
% 3.55/1.00    v4_orders_2(sK6) | ~v1_compts_1(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f101,plain,(
% 3.55/1.00    v7_waybel_0(sK6) | ~v1_compts_1(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f102,plain,(
% 3.55/1.00    l1_waybel_0(sK6,sK5) | ~v1_compts_1(sK5)),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f6,axiom,(
% 3.55/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f21,plain,(
% 3.55/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.55/1.00    inference(ennf_transformation,[],[f6])).
% 3.55/1.00  
% 3.55/1.00  fof(f72,plain,(
% 3.55/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f21])).
% 3.55/1.00  
% 3.55/1.00  fof(f8,axiom,(
% 3.55/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f24,plain,(
% 3.55/1.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f8])).
% 3.55/1.00  
% 3.55/1.00  fof(f25,plain,(
% 3.55/1.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f24])).
% 3.55/1.00  
% 3.55/1.00  fof(f77,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f25])).
% 3.55/1.00  
% 3.55/1.00  fof(f76,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f25])).
% 3.55/1.00  
% 3.55/1.00  fof(f75,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f25])).
% 3.55/1.00  
% 3.55/1.00  fof(f74,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f25])).
% 3.55/1.00  
% 3.55/1.00  fof(f97,plain,(
% 3.55/1.00    ( ! [X3] : (m2_yellow_6(sK7(X3),sK5,X3) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f1,axiom,(
% 3.55/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f17,plain,(
% 3.55/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f1])).
% 3.55/1.00  
% 3.55/1.00  fof(f40,plain,(
% 3.55/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/1.00    inference(nnf_transformation,[],[f17])).
% 3.55/1.00  
% 3.55/1.00  fof(f41,plain,(
% 3.55/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/1.00    inference(rectify,[],[f40])).
% 3.55/1.00  
% 3.55/1.00  fof(f42,plain,(
% 3.55/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f43,plain,(
% 3.55/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.55/1.00  
% 3.55/1.00  fof(f64,plain,(
% 3.55/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f43])).
% 3.55/1.00  
% 3.55/1.00  fof(f7,axiom,(
% 3.55/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f22,plain,(
% 3.55/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f7])).
% 3.55/1.00  
% 3.55/1.00  fof(f23,plain,(
% 3.55/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f22])).
% 3.55/1.00  
% 3.55/1.00  fof(f73,plain,(
% 3.55/1.00    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f23])).
% 3.55/1.00  
% 3.55/1.00  fof(f4,axiom,(
% 3.55/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f18,plain,(
% 3.55/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.55/1.00    inference(ennf_transformation,[],[f4])).
% 3.55/1.00  
% 3.55/1.00  fof(f19,plain,(
% 3.55/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/1.00    inference(flattening,[],[f18])).
% 3.55/1.00  
% 3.55/1.00  fof(f70,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f19])).
% 3.55/1.00  
% 3.55/1.00  fof(f10,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f28,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f10])).
% 3.55/1.00  
% 3.55/1.00  fof(f29,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f28])).
% 3.55/1.00  
% 3.55/1.00  fof(f80,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f29])).
% 3.55/1.00  
% 3.55/1.00  fof(f11,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f30,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f11])).
% 3.55/1.00  
% 3.55/1.00  fof(f31,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f30])).
% 3.55/1.00  
% 3.55/1.00  fof(f81,plain,(
% 3.55/1.00    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f31])).
% 3.55/1.00  
% 3.55/1.00  fof(f14,axiom,(
% 3.55/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f36,plain,(
% 3.55/1.00    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/1.00    inference(ennf_transformation,[],[f14])).
% 3.55/1.00  
% 3.55/1.00  fof(f37,plain,(
% 3.55/1.00    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(flattening,[],[f36])).
% 3.55/1.00  
% 3.55/1.00  fof(f51,plain,(
% 3.55/1.00    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(nnf_transformation,[],[f37])).
% 3.55/1.00  
% 3.55/1.00  fof(f52,plain,(
% 3.55/1.00    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(rectify,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f54,plain,(
% 3.55/1.00    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f53,plain,(
% 3.55/1.00    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f55,plain,(
% 3.55/1.00    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f54,f53])).
% 3.55/1.00  
% 3.55/1.00  fof(f93,plain,(
% 3.55/1.00    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f55])).
% 3.55/1.00  
% 3.55/1.00  fof(f88,plain,(
% 3.55/1.00    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f55])).
% 3.55/1.00  
% 3.55/1.00  fof(f89,plain,(
% 3.55/1.00    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f55])).
% 3.55/1.00  
% 3.55/1.00  fof(f90,plain,(
% 3.55/1.00    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f55])).
% 3.55/1.00  
% 3.55/1.00  fof(f91,plain,(
% 3.55/1.00    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f55])).
% 3.55/1.00  
% 3.55/1.00  fof(f2,axiom,(
% 3.55/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f44,plain,(
% 3.55/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/1.00    inference(nnf_transformation,[],[f2])).
% 3.55/1.00  
% 3.55/1.00  fof(f45,plain,(
% 3.55/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/1.00    inference(flattening,[],[f44])).
% 3.55/1.00  
% 3.55/1.00  fof(f68,plain,(
% 3.55/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f45])).
% 3.55/1.00  
% 3.55/1.00  fof(f78,plain,(
% 3.55/1.00    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f46])).
% 3.55/1.00  
% 3.55/1.00  fof(f98,plain,(
% 3.55/1.00    ( ! [X3] : (v3_yellow_6(sK7(X3),sK5) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f62])).
% 3.55/1.00  
% 3.55/1.00  fof(f84,plain,(
% 3.55/1.00    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f50])).
% 3.55/1.00  
% 3.55/1.00  fof(f83,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f48])).
% 3.55/1.00  
% 3.55/1.00  fof(f5,axiom,(
% 3.55/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f20,plain,(
% 3.55/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.55/1.00    inference(ennf_transformation,[],[f5])).
% 3.55/1.00  
% 3.55/1.00  fof(f71,plain,(
% 3.55/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f20])).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6,plain,
% 3.55/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6650,plain,
% 3.55/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_21,plain,
% 3.55/1.00      ( r3_waybel_9(X0,X1,sK2(X0,X1))
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_39,negated_conjecture,
% 3.55/1.00      ( v2_pre_topc(sK5) ),
% 3.55/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_810,plain,
% 3.55/1.00      ( r3_waybel_9(X0,X1,sK2(X0,X1))
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_811,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK2(sK5,X0))
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_810]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_40,negated_conjecture,
% 3.55/1.00      ( ~ v2_struct_0(sK5) ),
% 3.55/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_38,negated_conjecture,
% 3.55/1.00      ( l1_pre_topc(sK5) ),
% 3.55/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_815,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | r3_waybel_9(sK5,X0,sK2(sK5,X0))
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_811,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_816,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK2(sK5,X0))
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_815]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6633,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK2(sK5,X0)) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_20,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_840,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_841,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_840]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_845,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_841,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_846,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_845]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6632,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.55/1.00      | m2_yellow_6(sK1(sK5,X0,X1),sK5,X0) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_15,plain,
% 3.55/1.00      ( v3_yellow_6(X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | ~ v2_pre_topc(X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1)
% 3.55/1.00      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_31,negated_conjecture,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ v3_yellow_6(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5) ),
% 3.55/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_590,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ l1_waybel_0(X1,X2)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_pre_topc(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X2)
% 3.55/1.00      | X0 != X1
% 3.55/1.00      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.55/1.00      | sK5 != X2 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_591,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_pre_topc(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5)
% 3.55/1.00      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_590]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_595,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_591,c_40,c_39,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_596,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_595]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6641,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.55/1.00      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_35,negated_conjecture,
% 3.55/1.00      ( ~ v1_compts_1(sK5) | ~ v2_struct_0(sK6) ),
% 3.55/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_50,plain,
% 3.55/1.00      ( v1_compts_1(sK5) != iProver_top | v2_struct_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_34,negated_conjecture,
% 3.55/1.00      ( ~ v1_compts_1(sK5) | v4_orders_2(sK6) ),
% 3.55/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_51,plain,
% 3.55/1.00      ( v1_compts_1(sK5) != iProver_top | v4_orders_2(sK6) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_33,negated_conjecture,
% 3.55/1.00      ( ~ v1_compts_1(sK5) | v7_waybel_0(sK6) ),
% 3.55/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_52,plain,
% 3.55/1.00      ( v1_compts_1(sK5) != iProver_top | v7_waybel_0(sK6) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_32,negated_conjecture,
% 3.55/1.00      ( l1_waybel_0(sK6,sK5) | ~ v1_compts_1(sK5) ),
% 3.55/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_53,plain,
% 3.55/1.00      ( l1_waybel_0(sK6,sK5) = iProver_top | v1_compts_1(sK5) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_597,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.55/1.00      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9,plain,
% 3.55/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | l1_waybel_0(X0,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_struct_0(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_525,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | l1_waybel_0(X0,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X3)
% 3.55/1.00      | X1 != X3 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_526,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | l1_waybel_0(X0,X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1149,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | l1_waybel_0(X0,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_526,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1150,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | l1_waybel_0(X0,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1149]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1152,plain,
% 3.55/1.00      ( v2_struct_0(X1)
% 3.55/1.00      | l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1150,c_40]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1153,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | l1_waybel_0(X0,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1152]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6746,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK6,sK5)
% 3.55/1.00      | v2_struct_0(sK6)
% 3.55/1.00      | ~ v4_orders_2(sK6)
% 3.55/1.00      | ~ v7_waybel_0(sK6) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1153]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6747,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) = iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6746]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_12,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_struct_0(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_497,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X3)
% 3.55/1.00      | X1 != X3 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_498,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_497]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1175,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_498,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1176,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | v7_waybel_0(X0) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1175]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1178,plain,
% 3.55/1.00      ( v2_struct_0(X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | v7_waybel_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1176,c_40]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1179,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1178]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6751,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ l1_waybel_0(sK6,sK5)
% 3.55/1.00      | v2_struct_0(sK6)
% 3.55/1.00      | ~ v4_orders_2(sK6)
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK6) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1179]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6752,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) = iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6751]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_13,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_struct_0(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_469,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X3)
% 3.55/1.00      | X1 != X3 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_470,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_469]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1201,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_470,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1202,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1201]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1204,plain,
% 3.55/1.00      ( v2_struct_0(X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1202,c_40]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1205,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1204]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6758,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.55/1.00      | ~ l1_waybel_0(sK6,sK5)
% 3.55/1.00      | v2_struct_0(sK6)
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(sK6)
% 3.55/1.00      | ~ v7_waybel_0(sK6) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1205]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6759,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6758]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7768,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_6641,c_50,c_51,c_52,c_53,c_597,c_6747,c_6752,c_6759]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7769,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.55/1.00      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_7768]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7913,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6632,c_7769]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9254,plain,
% 3.55/1.00      ( v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_7913,c_50,c_51,c_52,c_53]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9255,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK1(sK5,sK6,X0)) = iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_9254]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_14,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_struct_0(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_441,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X3)
% 3.55/1.00      | X1 != X3 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_442,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1227,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,X1)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_442,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1228,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1227]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1230,plain,
% 3.55/1.00      ( v2_struct_0(X1)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1228,c_40]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1231,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | ~ v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1230]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6622,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,X1) != iProver_top
% 3.55/1.00      | l1_waybel_0(X1,sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) != iProver_top
% 3.55/1.00      | v2_struct_0(X1) = iProver_top
% 3.55/1.00      | v4_orders_2(X1) != iProver_top
% 3.55/1.00      | v7_waybel_0(X1) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1231]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7917,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v2_struct_0(sK1(sK5,X0,X1)) != iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6632,c_6622]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9260,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_9255,c_7917]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_37,negated_conjecture,
% 3.55/1.00      ( m2_yellow_6(sK7(X0),sK5,X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6643,plain,
% 3.55/1.00      ( m2_yellow_6(sK7(X0),sK5,X0) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1,plain,
% 3.55/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6654,plain,
% 3.55/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.55/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.00      | ~ v2_pre_topc(X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1034,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1035,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1034]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1039,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_1035,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1040,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1039]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6626,plain,
% 3.55/1.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7,plain,
% 3.55/1.00      ( m1_subset_1(X0,X1)
% 3.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.55/1.00      | ~ r2_hidden(X0,X2) ),
% 3.55/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6649,plain,
% 3.55/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.55/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7520,plain,
% 3.55/1.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) = iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6626,c_6649]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8501,plain,
% 3.55/1.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) = iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6654,c_7520]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_17,plain,
% 3.55/1.00      ( r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_938,plain,
% 3.55/1.00      ( r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_939,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_938]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_943,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_939,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_944,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_943]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6629,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_945,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7802,plain,
% 3.55/1.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_6629,c_945,c_7520]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7803,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_7802]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7808,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X0),X1)) = iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6654,c_7803]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_18,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | r3_waybel_9(X0,X3,X2)
% 3.55/1.00      | ~ m2_yellow_6(X1,X0,X3)
% 3.55/1.00      | ~ l1_waybel_0(X3,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X3)
% 3.55/1.00      | ~ v4_orders_2(X3)
% 3.55/1.00      | ~ v7_waybel_0(X3)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_906,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | r3_waybel_9(X0,X3,X2)
% 3.55/1.00      | ~ m2_yellow_6(X1,X0,X3)
% 3.55/1.00      | ~ l1_waybel_0(X3,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X3)
% 3.55/1.00      | ~ v4_orders_2(X3)
% 3.55/1.00      | ~ v7_waybel_0(X3)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_907,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | r3_waybel_9(sK5,X2,X1)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_906]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_909,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | r3_waybel_9(sK5,X2,X1)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X2) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_907,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_910,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | r3_waybel_9(sK5,X2,X1)
% 3.55/1.00      | ~ m2_yellow_6(X0,sK5,X2)
% 3.55/1.00      | ~ l1_waybel_0(X2,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X2) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_909]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6630,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.55/1.00      | r3_waybel_9(sK5,X2,X1) = iProver_top
% 3.55/1.00      | m2_yellow_6(X0,sK5,X2) != iProver_top
% 3.55/1.00      | l1_waybel_0(X2,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v2_struct_0(X2) = iProver_top
% 3.55/1.00      | v4_orders_2(X2) != iProver_top
% 3.55/1.00      | v7_waybel_0(X2) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8510,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
% 3.55/1.00      | m2_yellow_6(X1,sK5,X0) != iProver_top
% 3.55/1.00      | l1_waybel_0(X1,sK5) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
% 3.55/1.00      | v2_struct_0(X1) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X1) != iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X1) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_7808,c_6630]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9882,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
% 3.55/1.00      | m2_yellow_6(X1,sK5,X0) != iProver_top
% 3.55/1.00      | l1_waybel_0(X1,sK5) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
% 3.55/1.00      | v2_struct_0(X1) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X1) != iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X1) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_8501,c_8510]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_23,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,sK3(X0),X1)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.55/1.00      | v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_789,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,sK3(X0),X1)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.55/1.00      | v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_790,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
% 3.55/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_789]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_794,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
% 3.55/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.55/1.00      | v1_compts_1(sK5) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_790,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6634,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,sK3(sK5),X0) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10036,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_9882,c_6634]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_28,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v2_struct_0(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_719,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v2_struct_0(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_720,plain,
% 3.55/1.00      ( v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_struct_0(sK3(sK5))
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_719]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_722,plain,
% 3.55/1.00      ( v1_compts_1(sK5) | ~ v2_struct_0(sK3(sK5)) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_720,c_40,c_39,c_38,c_64]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_724,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top | v2_struct_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_27,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v4_orders_2(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_733,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v4_orders_2(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_734,plain,
% 3.55/1.00      ( v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | v4_orders_2(sK3(sK5))
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_733]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_736,plain,
% 3.55/1.00      ( v4_orders_2(sK3(sK5)) | v1_compts_1(sK5) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_734,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_737,plain,
% 3.55/1.00      ( v1_compts_1(sK5) | v4_orders_2(sK3(sK5)) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_736]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_738,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top | v4_orders_2(sK3(sK5)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_26,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v7_waybel_0(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_747,plain,
% 3.55/1.00      ( v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v7_waybel_0(sK3(X0))
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_748,plain,
% 3.55/1.00      ( v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | v7_waybel_0(sK3(sK5))
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_747]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_750,plain,
% 3.55/1.00      ( v7_waybel_0(sK3(sK5)) | v1_compts_1(sK5) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_748,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_751,plain,
% 3.55/1.00      ( v1_compts_1(sK5) | v7_waybel_0(sK3(sK5)) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_750]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_752,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top | v7_waybel_0(sK3(sK5)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_25,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(X0),X0)
% 3.55/1.00      | v1_compts_1(X0)
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_761,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(X0),X0)
% 3.55/1.00      | v1_compts_1(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_762,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(sK5),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_761]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_764,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(sK5),sK5) | v1_compts_1(sK5) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_762,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_766,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6864,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.55/1.00      | l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.55/1.00      | v2_struct_0(sK3(sK5))
% 3.55/1.00      | ~ v4_orders_2(sK3(sK5))
% 3.55/1.00      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1153]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6865,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) = iProver_top
% 3.55/1.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6864]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6863,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.55/1.00      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.55/1.00      | v2_struct_0(sK3(sK5))
% 3.55/1.00      | ~ v4_orders_2(sK3(sK5))
% 3.55/1.00      | v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1179]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6869,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) = iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6863]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6862,plain,
% 3.55/1.00      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.55/1.00      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.55/1.00      | v2_struct_0(sK3(sK5))
% 3.55/1.00      | v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(sK3(sK5))
% 3.55/1.00      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1205]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6873,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6862]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10114,plain,
% 3.55/1.00      ( v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.55/1.00      | m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_10036,c_724,c_738,c_752,c_766,c_6865,c_6869,c_6873,c_8501]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10115,plain,
% 3.55/1.00      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_10114]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10120,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(sK7(sK3(sK5))) = iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6643,c_10115]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6636,plain,
% 3.55/1.00      ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7005,plain,
% 3.55/1.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v2_struct_0(sK7(X0)) != iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6643,c_6622]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7294,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6636,c_7005]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8129,plain,
% 3.55/1.00      ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_7294,c_724,c_738,c_752]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8130,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_8129]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10126,plain,
% 3.55/1.00      ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_10120,c_724,c_738,c_752,c_766,c_8130]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3,plain,
% 3.55/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6652,plain,
% 3.55/1.00      ( X0 = X1
% 3.55/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.55/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7419,plain,
% 3.55/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6650,c_6652]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10135,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_10126,c_7419]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1421,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | l1_waybel_0(X2,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | X0 != X1
% 3.55/1.00      | sK7(X1) != X2
% 3.55/1.00      | sK5 != sK5 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_1153]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1422,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1421]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1397,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | v7_waybel_0(X2)
% 3.55/1.00      | X0 != X1
% 3.55/1.00      | sK7(X1) != X2
% 3.55/1.00      | sK5 != sK5 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_1179]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1398,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | v7_waybel_0(sK7(X0)) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1397]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1373,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | X0 != X1
% 3.55/1.00      | sK7(X1) != X2
% 3.55/1.00      | sK5 != sK5 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_1205]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1374,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | v4_orders_2(sK7(X0))
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1373]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1349,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(X1,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_struct_0(X2)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | X0 != X1
% 3.55/1.00      | sK7(X1) != X2
% 3.55/1.00      | sK5 != sK5 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_1231]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1350,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v2_struct_0(sK7(X0))
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1349]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_16,plain,
% 3.55/1.00      ( ~ v3_yellow_6(X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | ~ v2_pre_topc(X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1)
% 3.55/1.00      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_36,negated_conjecture,
% 3.55/1.00      ( v3_yellow_6(sK7(X0),sK5)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_623,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X2,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_pre_topc(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X2)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(X2)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(X2)
% 3.55/1.00      | ~ l1_pre_topc(X1)
% 3.55/1.00      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.55/1.00      | sK7(X2) != X0
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_624,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | ~ v2_pre_topc(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK7(X0))
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(sK7(X0))
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK7(X0))
% 3.55/1.00      | ~ l1_pre_topc(sK5)
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_623]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_628,plain,
% 3.55/1.00      ( ~ v7_waybel_0(sK7(X0))
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(sK7(X0))
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK7(X0))
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_624,c_40,c_39,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_629,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK7(X0))
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(sK7(X0))
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK7(X0))
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_628]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1604,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v4_orders_2(sK7(X0))
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK7(X0))
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1350,c_629]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1615,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v7_waybel_0(sK7(X0))
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1374,c_1604]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1626,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1615]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1632,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.55/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1422,c_1626]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6998,plain,
% 3.55/1.00      ( ~ l1_waybel_0(sK3(sK5),sK5)
% 3.55/1.00      | v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK3(sK5))
% 3.55/1.00      | ~ v4_orders_2(sK3(sK5))
% 3.55/1.00      | ~ v7_waybel_0(sK3(sK5))
% 3.55/1.00      | k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1632]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6999,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
% 3.55/1.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) = iProver_top
% 3.55/1.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.55/1.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6998]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10330,plain,
% 3.55/1.00      ( v1_compts_1(sK5) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_10135,c_724,c_738,c_752,c_766,c_6999]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11517,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.55/1.00      | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_9260,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6999,
% 3.55/1.00                 c_10135]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11518,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 3.55/1.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.55/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_11517]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11524,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6633,c_11518]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_22,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 3.55/1.00      | ~ v1_compts_1(X1)
% 3.55/1.00      | ~ v2_pre_topc(X1)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1004,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.55/1.00      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 3.55/1.00      | ~ v1_compts_1(X1)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(X1)
% 3.55/1.00      | sK5 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1005,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_1004]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1009,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_1005,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1010,plain,
% 3.55/1.00      ( ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | m1_subset_1(sK2(sK5,X0),u1_struct_0(sK5))
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_1009]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6726,plain,
% 3.55/1.00      ( ~ l1_waybel_0(sK6,sK5)
% 3.55/1.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK6)
% 3.55/1.00      | ~ v4_orders_2(sK6)
% 3.55/1.00      | ~ v7_waybel_0(sK6) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1010]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6727,plain,
% 3.55/1.00      ( l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) = iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6726]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11816,plain,
% 3.55/1.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0 ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_11524,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6727,
% 3.55/1.00                 c_6999,c_10135]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_19,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 3.55/1.00      | ~ v2_pre_topc(X0)
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_873,plain,
% 3.55/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.55/1.00      | ~ l1_waybel_0(X1,X0)
% 3.55/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.55/1.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(X1)
% 3.55/1.00      | ~ v4_orders_2(X1)
% 3.55/1.00      | ~ v7_waybel_0(X1)
% 3.55/1.00      | ~ l1_pre_topc(X0)
% 3.55/1.00      | sK5 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_874,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | v2_struct_0(sK5)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ l1_pre_topc(sK5) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_873]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_878,plain,
% 3.55/1.00      ( ~ v7_waybel_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
% 3.55/1.00      | v2_struct_0(X0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_874,c_40,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_879,plain,
% 3.55/1.00      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.55/1.00      | ~ l1_waybel_0(X0,sK5)
% 3.55/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1)))
% 3.55/1.00      | v2_struct_0(X0)
% 3.55/1.00      | ~ v4_orders_2(X0)
% 3.55/1.00      | ~ v7_waybel_0(X0) ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_878]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6631,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.55/1.00      | l1_waybel_0(X0,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r2_hidden(X1,k10_yellow_6(sK5,sK1(sK5,X0,X1))) = iProver_top
% 3.55/1.00      | v2_struct_0(X0) = iProver_top
% 3.55/1.00      | v4_orders_2(X0) != iProver_top
% 3.55/1.00      | v7_waybel_0(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11828,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) != iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 3.55/1.00      | r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_11816,c_6631]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6737,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6))
% 3.55/1.00      | ~ l1_waybel_0(sK6,sK5)
% 3.55/1.00      | ~ v1_compts_1(sK5)
% 3.55/1.00      | v2_struct_0(sK6)
% 3.55/1.00      | ~ v4_orders_2(sK6)
% 3.55/1.00      | ~ v7_waybel_0(sK6) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_816]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6738,plain,
% 3.55/1.00      ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) = iProver_top
% 3.55/1.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.55/1.00      | v1_compts_1(sK5) != iProver_top
% 3.55/1.00      | v2_struct_0(sK6) = iProver_top
% 3.55/1.00      | v4_orders_2(sK6) != iProver_top
% 3.55/1.00      | v7_waybel_0(sK6) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_6737]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11924,plain,
% 3.55/1.00      ( r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_11828,c_50,c_51,c_52,c_53,c_724,c_738,c_752,c_766,c_6727,
% 3.55/1.00                 c_6738,c_6999,c_10135]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8,plain,
% 3.55/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6648,plain,
% 3.55/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11929,plain,
% 3.55/1.00      ( r1_tarski(k1_xboole_0,sK2(sK5,sK6)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_11924,c_6648]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_12882,plain,
% 3.55/1.00      ( $false ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_6650,c_11929]) ).
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  ------                               Statistics
% 3.55/1.00  
% 3.55/1.00  ------ General
% 3.55/1.00  
% 3.55/1.00  abstr_ref_over_cycles:                  0
% 3.55/1.00  abstr_ref_under_cycles:                 0
% 3.55/1.00  gc_basic_clause_elim:                   0
% 3.55/1.00  forced_gc_time:                         0
% 3.55/1.00  parsing_time:                           0.011
% 3.55/1.00  unif_index_cands_time:                  0.
% 3.55/1.00  unif_index_add_time:                    0.
% 3.55/1.00  orderings_time:                         0.
% 3.55/1.00  out_proof_time:                         0.018
% 3.55/1.00  total_time:                             0.331
% 3.55/1.00  num_of_symbols:                         58
% 3.55/1.00  num_of_terms:                           6699
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing
% 3.55/1.00  
% 3.55/1.00  num_of_splits:                          0
% 3.55/1.00  num_of_split_atoms:                     0
% 3.55/1.00  num_of_reused_defs:                     0
% 3.55/1.00  num_eq_ax_congr_red:                    33
% 3.55/1.00  num_of_sem_filtered_clauses:            1
% 3.55/1.00  num_of_subtypes:                        0
% 3.55/1.00  monotx_restored_types:                  0
% 3.55/1.00  sat_num_of_epr_types:                   0
% 3.55/1.00  sat_num_of_non_cyclic_types:            0
% 3.55/1.00  sat_guarded_non_collapsed_types:        0
% 3.55/1.00  num_pure_diseq_elim:                    0
% 3.55/1.00  simp_replaced_by:                       0
% 3.55/1.00  res_preprocessed:                       186
% 3.55/1.00  prep_upred:                             0
% 3.55/1.00  prep_unflattend:                        76
% 3.55/1.00  smt_new_axioms:                         0
% 3.55/1.00  pred_elim_cands:                        10
% 3.55/1.00  pred_elim:                              4
% 3.55/1.00  pred_elim_cl:                           5
% 3.55/1.00  pred_elim_cycles:                       8
% 3.55/1.00  merged_defs:                            0
% 3.55/1.00  merged_defs_ncl:                        0
% 3.55/1.00  bin_hyper_res:                          0
% 3.55/1.00  prep_cycles:                            4
% 3.55/1.00  pred_elim_time:                         0.087
% 3.55/1.00  splitting_time:                         0.
% 3.55/1.00  sem_filter_time:                        0.
% 3.55/1.00  monotx_time:                            0.
% 3.55/1.00  subtype_inf_time:                       0.
% 3.55/1.00  
% 3.55/1.00  ------ Problem properties
% 3.55/1.00  
% 3.55/1.00  clauses:                                35
% 3.55/1.00  conjectures:                            6
% 3.55/1.00  epr:                                    14
% 3.55/1.00  horn:                                   15
% 3.55/1.00  ground:                                 10
% 3.55/1.00  unary:                                  3
% 3.55/1.00  binary:                                 12
% 3.55/1.00  lits:                                   142
% 3.55/1.00  lits_eq:                                3
% 3.55/1.00  fd_pure:                                0
% 3.55/1.00  fd_pseudo:                              0
% 3.55/1.00  fd_cond:                                0
% 3.55/1.00  fd_pseudo_cond:                         1
% 3.55/1.00  ac_symbols:                             0
% 3.55/1.00  
% 3.55/1.00  ------ Propositional Solver
% 3.55/1.00  
% 3.55/1.00  prop_solver_calls:                      31
% 3.55/1.00  prop_fast_solver_calls:                 3845
% 3.55/1.00  smt_solver_calls:                       0
% 3.55/1.00  smt_fast_solver_calls:                  0
% 3.55/1.00  prop_num_of_clauses:                    3641
% 3.55/1.00  prop_preprocess_simplified:             11009
% 3.55/1.00  prop_fo_subsumed:                       174
% 3.55/1.00  prop_solver_time:                       0.
% 3.55/1.00  smt_solver_time:                        0.
% 3.55/1.00  smt_fast_solver_time:                   0.
% 3.55/1.00  prop_fast_solver_time:                  0.
% 3.55/1.00  prop_unsat_core_time:                   0.
% 3.55/1.00  
% 3.55/1.00  ------ QBF
% 3.55/1.00  
% 3.55/1.00  qbf_q_res:                              0
% 3.55/1.00  qbf_num_tautologies:                    0
% 3.55/1.00  qbf_prep_cycles:                        0
% 3.55/1.00  
% 3.55/1.00  ------ BMC1
% 3.55/1.00  
% 3.55/1.00  bmc1_current_bound:                     -1
% 3.55/1.00  bmc1_last_solved_bound:                 -1
% 3.55/1.00  bmc1_unsat_core_size:                   -1
% 3.55/1.00  bmc1_unsat_core_parents_size:           -1
% 3.55/1.00  bmc1_merge_next_fun:                    0
% 3.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation
% 3.55/1.00  
% 3.55/1.00  inst_num_of_clauses:                    1001
% 3.55/1.00  inst_num_in_passive:                    524
% 3.55/1.00  inst_num_in_active:                     434
% 3.55/1.00  inst_num_in_unprocessed:                43
% 3.55/1.00  inst_num_of_loops:                      600
% 3.55/1.00  inst_num_of_learning_restarts:          0
% 3.55/1.00  inst_num_moves_active_passive:          161
% 3.55/1.00  inst_lit_activity:                      0
% 3.55/1.00  inst_lit_activity_moves:                0
% 3.55/1.00  inst_num_tautologies:                   0
% 3.55/1.00  inst_num_prop_implied:                  0
% 3.55/1.00  inst_num_existing_simplified:           0
% 3.55/1.00  inst_num_eq_res_simplified:             0
% 3.55/1.00  inst_num_child_elim:                    0
% 3.55/1.00  inst_num_of_dismatching_blockings:      119
% 3.55/1.00  inst_num_of_non_proper_insts:           954
% 3.55/1.00  inst_num_of_duplicates:                 0
% 3.55/1.00  inst_inst_num_from_inst_to_res:         0
% 3.55/1.00  inst_dismatching_checking_time:         0.
% 3.55/1.00  
% 3.55/1.00  ------ Resolution
% 3.55/1.00  
% 3.55/1.00  res_num_of_clauses:                     0
% 3.55/1.00  res_num_in_passive:                     0
% 3.55/1.00  res_num_in_active:                      0
% 3.55/1.00  res_num_of_loops:                       190
% 3.55/1.00  res_forward_subset_subsumed:            68
% 3.55/1.00  res_backward_subset_subsumed:           0
% 3.55/1.00  res_forward_subsumed:                   0
% 3.55/1.00  res_backward_subsumed:                  0
% 3.55/1.00  res_forward_subsumption_resolution:     0
% 3.55/1.00  res_backward_subsumption_resolution:    4
% 3.55/1.00  res_clause_to_clause_subsumption:       907
% 3.55/1.00  res_orphan_elimination:                 0
% 3.55/1.00  res_tautology_del:                      89
% 3.55/1.00  res_num_eq_res_simplified:              0
% 3.55/1.00  res_num_sel_changes:                    0
% 3.55/1.00  res_moves_from_active_to_pass:          0
% 3.55/1.00  
% 3.55/1.00  ------ Superposition
% 3.55/1.00  
% 3.55/1.00  sup_time_total:                         0.
% 3.55/1.00  sup_time_generating:                    0.
% 3.55/1.00  sup_time_sim_full:                      0.
% 3.55/1.00  sup_time_sim_immed:                     0.
% 3.55/1.00  
% 3.55/1.00  sup_num_of_clauses:                     110
% 3.55/1.00  sup_num_in_active:                      74
% 3.55/1.00  sup_num_in_passive:                     36
% 3.55/1.00  sup_num_of_loops:                       118
% 3.55/1.00  sup_fw_superposition:                   80
% 3.55/1.00  sup_bw_superposition:                   96
% 3.55/1.00  sup_immediate_simplified:               21
% 3.55/1.00  sup_given_eliminated:                   0
% 3.55/1.00  comparisons_done:                       0
% 3.55/1.00  comparisons_avoided:                    1
% 3.55/1.00  
% 3.55/1.00  ------ Simplifications
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  sim_fw_subset_subsumed:                 7
% 3.55/1.00  sim_bw_subset_subsumed:                 7
% 3.55/1.00  sim_fw_subsumed:                        12
% 3.55/1.00  sim_bw_subsumed:                        40
% 3.55/1.00  sim_fw_subsumption_res:                 0
% 3.55/1.00  sim_bw_subsumption_res:                 0
% 3.55/1.00  sim_tautology_del:                      10
% 3.55/1.00  sim_eq_tautology_del:                   6
% 3.55/1.00  sim_eq_res_simp:                        0
% 3.55/1.00  sim_fw_demodulated:                     0
% 3.55/1.00  sim_bw_demodulated:                     0
% 3.55/1.00  sim_light_normalised:                   4
% 3.55/1.00  sim_joinable_taut:                      0
% 3.55/1.00  sim_joinable_simp:                      0
% 3.55/1.00  sim_ac_normalised:                      0
% 3.55/1.00  sim_smt_subsumption:                    0
% 3.55/1.00  
%------------------------------------------------------------------------------
