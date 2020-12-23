%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:24 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_64)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X0,X3))
        & m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f57])).

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

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK7(X3),X0)
        & m2_yellow_6(sK7(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).

fof(f97,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f96,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
        & m2_yellow_6(sK2(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
                & m2_yellow_6(sK2(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f51])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK2(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f82,plain,(
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

fof(f105,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK5)
      | ~ m2_yellow_6(X2,sK5,sK6)
      | ~ v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,
    ( ~ v2_struct_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f102,plain,
    ( v4_orders_2(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,
    ( v7_waybel_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f74,plain,(
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

fof(f79,plain,(
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

fof(f78,plain,(
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

fof(f77,plain,(
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

fof(f76,plain,(
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

fof(f99,plain,(
    ! [X3] :
      ( m2_yellow_6(sK7(X3),sK5,X3)
      | ~ l1_waybel_0(X3,sK5)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f64])).

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

fof(f66,plain,(
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

fof(f75,plain,(
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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
                    & m1_connsp_2(sK1(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK1(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
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

fof(f100,plain,(
    ! [X3] :
      ( v3_yellow_6(sK7(X3),sK5)
      | ~ l1_waybel_0(X3,sK5)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5331,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_798,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_799,plain,
    ( r3_waybel_9(sK5,X0,sK4(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_803,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK5,X0,sK4(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_799,c_40,c_38])).

cnf(c_804,plain,
    ( r3_waybel_9(sK5,X0,sK4(sK5,X0))
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_803])).

cnf(c_5320,plain,
    ( r3_waybel_9(sK5,X0,sK4(sK5,X0)) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_905,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_906,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_910,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_40,c_38])).

cnf(c_911,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_910])).

cnf(c_5314,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_16,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ v3_yellow_6(X0,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_670,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_671,plain,
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
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_675,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK5)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m2_yellow_6(X0,sK5,sK6)
    | v2_struct_0(X0)
    | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_40,c_39,c_38])).

cnf(c_676,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(X0,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_675])).

cnf(c_5322,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_35,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_50,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_51,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v4_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v7_waybel_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_677,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_595,plain,
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

cnf(c_596,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1192,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_596,c_38])).

cnf(c_1193,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | l1_waybel_0(X0,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1192])).

cnf(c_1195,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1193,c_40])).

cnf(c_1196,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | l1_waybel_0(X0,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1195])).

cnf(c_5419,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_5420,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(X0,sK5) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5419])).

cnf(c_12,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_567,plain,
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

cnf(c_568,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_1218,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_568,c_38])).

cnf(c_1219,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1218])).

cnf(c_1221,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_40])).

cnf(c_1222,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1221])).

cnf(c_5424,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_5425,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5424])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_539,plain,
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

cnf(c_540,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1244,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_540,c_38])).

cnf(c_1245,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1247,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_40])).

cnf(c_1248,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1247])).

cnf(c_5429,plain,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_5430,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5429])).

cnf(c_6478,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | k10_yellow_6(sK5,X0) = k1_xboole_0
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5322,c_50,c_51,c_52,c_53,c_677,c_5420,c_5425,c_5430])).

cnf(c_6479,plain,
    ( k10_yellow_6(sK5,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK5,sK6) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6478])).

cnf(c_6691,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5314,c_6479])).

cnf(c_7521,plain,
    ( v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top
    | v1_compts_1(sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6691,c_50,c_51,c_52,c_53])).

cnf(c_7522,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7521])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_511,plain,
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

cnf(c_512,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1270,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_512,c_38])).

cnf(c_1271,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1270])).

cnf(c_1273,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK5)
    | ~ m2_yellow_6(X0,sK5,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1271,c_40])).

cnf(c_1274,plain,
    ( ~ m2_yellow_6(X0,sK5,X1)
    | ~ l1_waybel_0(X1,sK5)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1273])).

cnf(c_5304,plain,
    ( m2_yellow_6(X0,sK5,X1) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_6695,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK5,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5314,c_5304])).

cnf(c_7527,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7522,c_6695])).

cnf(c_37,negated_conjecture,
    ( m2_yellow_6(sK7(X0),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5324,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_5335,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_1061,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_39])).

cnf(c_1062,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_40,c_38])).

cnf(c_1067,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_5309,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5330,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6299,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_5330])).

cnf(c_7151,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) = iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5335,c_6299])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f86])).

cnf(c_971,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_972,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_40,c_38])).

cnf(c_977,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_5312,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_978,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_6535,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | r3_waybel_9(sK5,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5312,c_978,c_6299])).

cnf(c_6536,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6535])).

cnf(c_6541,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X0),X1)) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5335,c_6536])).

cnf(c_19,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ r3_waybel_9(X1,X3,X2)
    | r2_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_443,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X3,X4,X5)
    | r2_waybel_0(X0,X1,X6)
    | ~ l1_waybel_0(X4,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X2 != X5
    | X0 != X3
    | sK1(X3,X4,X5) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_444,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | r2_waybel_0(X0,X1,sK1(X0,X3,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_766,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | r2_waybel_0(X0,X1,sK1(X0,X3,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_444,c_39])).

cnf(c_767,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
    | ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_769,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
    | ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_40,c_38])).

cnf(c_770,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | r3_waybel_9(sK5,X2,X1)
    | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
    | ~ l1_waybel_0(X2,sK5)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_769])).

cnf(c_5321,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | r3_waybel_9(sK5,X2,X1) = iProver_top
    | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1)) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | l1_waybel_0(X2,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_15,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_481,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_15])).

cnf(c_1163,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_38])).

cnf(c_1164,plain,
    ( ~ r2_waybel_0(sK5,X0,X1)
    | r2_waybel_0(sK5,X2,X1)
    | ~ m2_yellow_6(X0,sK5,X2)
    | ~ l1_waybel_0(X2,sK5)
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_1163])).

cnf(c_1166,plain,
    ( v2_struct_0(X2)
    | ~ l1_waybel_0(X2,sK5)
    | ~ m2_yellow_6(X0,sK5,X2)
    | r2_waybel_0(sK5,X2,X1)
    | ~ r2_waybel_0(sK5,X0,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1164,c_40])).

cnf(c_1167,plain,
    ( ~ r2_waybel_0(sK5,X0,X1)
    | r2_waybel_0(sK5,X2,X1)
    | ~ m2_yellow_6(X0,sK5,X2)
    | ~ l1_waybel_0(X2,sK5)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1166])).

cnf(c_5308,plain,
    ( r2_waybel_0(sK5,X0,X1) != iProver_top
    | r2_waybel_0(sK5,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK5,X2) != iProver_top
    | l1_waybel_0(X2,sK5) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_6784,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | r3_waybel_9(sK5,X2,X1) = iProver_top
    | r2_waybel_0(sK5,X3,sK1(sK5,X2,X1)) = iProver_top
    | m2_yellow_6(X0,sK5,X3) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | l1_waybel_0(X2,sK5) != iProver_top
    | l1_waybel_0(X3,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5321,c_5308])).

cnf(c_7885,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
    | r2_waybel_0(sK5,X3,sK1(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2))) = iProver_top
    | m2_yellow_6(X1,sK5,X3) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | l1_waybel_0(X3,sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6541,c_6784])).

cnf(c_18,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1004,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_1005,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ r2_waybel_0(sK5,X0,sK1(sK5,X0,X1))
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1009,plain,
    ( r3_waybel_9(sK5,X0,X1)
    | ~ r2_waybel_0(sK5,X0,sK1(sK5,X0,X1))
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_40,c_38])).

cnf(c_5311,plain,
    ( r3_waybel_9(sK5,X0,X1) = iProver_top
    | r2_waybel_0(sK5,X0,sK1(sK5,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_8714,plain,
    ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK5,X0) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | l1_waybel_0(X1,sK5) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7885,c_5311])).

cnf(c_8834,plain,
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
    inference(superposition,[status(thm)],[c_7151,c_8714])).

cnf(c_24,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_884,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_885,plain,
    ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_889,plain,
    ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_40,c_38])).

cnf(c_5315,plain,
    ( r3_waybel_9(sK5,sK3(sK5),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_8840,plain,
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
    inference(superposition,[status(thm)],[c_8834,c_5315])).

cnf(c_28,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_828,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_829,plain,
    ( v1_compts_1(sK5)
    | ~ v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_831,plain,
    ( v1_compts_1(sK5)
    | ~ v2_struct_0(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_40,c_39,c_38,c_64])).

cnf(c_833,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_842,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_843,plain,
    ( v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | v4_orders_2(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_845,plain,
    ( v4_orders_2(sK3(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_40,c_38])).

cnf(c_846,plain,
    ( v1_compts_1(sK5)
    | v4_orders_2(sK3(sK5)) ),
    inference(renaming,[status(thm)],[c_845])).

cnf(c_847,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v4_orders_2(sK3(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_856,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_39])).

cnf(c_857,plain,
    ( v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | v7_waybel_0(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_859,plain,
    ( v7_waybel_0(sK3(sK5))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_857,c_40,c_38])).

cnf(c_860,plain,
    ( v1_compts_1(sK5)
    | v7_waybel_0(sK3(sK5)) ),
    inference(renaming,[status(thm)],[c_859])).

cnf(c_861,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v7_waybel_0(sK3(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_25,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_870,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_871,plain,
    ( l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_870])).

cnf(c_873,plain,
    ( l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_871,c_40,c_38])).

cnf(c_875,plain,
    ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_5558,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_5559,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(X0,sK5) = iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5558])).

cnf(c_5557,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_5563,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5557])).

cnf(c_5556,plain,
    ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_5567,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5556])).

cnf(c_8906,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8840,c_833,c_847,c_861,c_875,c_5559,c_5563,c_5567,c_7151])).

cnf(c_8907,plain,
    ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8906])).

cnf(c_8912,plain,
    ( l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5324,c_8907])).

cnf(c_5316,plain,
    ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_5730,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5324,c_5304])).

cnf(c_6037,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5316,c_5730])).

cnf(c_6999,plain,
    ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6037,c_833,c_847,c_861])).

cnf(c_7000,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6999])).

cnf(c_8918,plain,
    ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8912,c_833,c_847,c_861,c_875,c_7000])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5333,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6250,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5331,c_5333])).

cnf(c_8927,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_8918,c_6250])).

cnf(c_1469,plain,
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
    inference(resolution_lifted,[status(thm)],[c_37,c_1196])).

cnf(c_1470,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1469])).

cnf(c_1445,plain,
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
    inference(resolution_lifted,[status(thm)],[c_37,c_1222])).

cnf(c_1446,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK7(X0)) ),
    inference(unflattening,[status(thm)],[c_1445])).

cnf(c_1421,plain,
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
    inference(resolution_lifted,[status(thm)],[c_37,c_1248])).

cnf(c_1422,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_1397,plain,
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
    inference(resolution_lifted,[status(thm)],[c_37,c_1274])).

cnf(c_1398,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK7(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_17,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( v3_yellow_6(sK7(X0),sK5)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_703,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_704,plain,
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
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_708,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_40,c_39,c_38])).

cnf(c_709,plain,
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
    inference(renaming,[status(thm)],[c_708])).

cnf(c_1650,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_709])).

cnf(c_1661,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7(X0))
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1422,c_1650])).

cnf(c_1672,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | ~ l1_waybel_0(sK7(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1446,c_1661])).

cnf(c_1678,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1470,c_1672])).

cnf(c_5636,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_5637,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5636])).

cnf(c_8986,plain,
    ( v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8927,c_833,c_847,c_861,c_875,c_5637])).

cnf(c_9179,plain,
    ( r3_waybel_9(sK5,sK6,X0) != iProver_top
    | k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7527,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5637,c_8927])).

cnf(c_9180,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9179])).

cnf(c_9185,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,sK4(sK5,sK6))) = k1_xboole_0
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5320,c_9180])).

cnf(c_30,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1031,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_1032,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_1036,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1032,c_40,c_38])).

cnf(c_1037,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1036])).

cnf(c_5405,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5))
    | ~ v1_compts_1(sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_5406,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5405])).

cnf(c_9663,plain,
    ( k10_yellow_6(sK5,sK2(sK5,sK6,sK4(sK5,sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9185,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5406,c_5637,c_8927])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_938,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_39])).

cnf(c_939,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_943,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_939,c_40,c_38])).

cnf(c_944,plain,
    ( ~ r3_waybel_9(sK5,X0,X1)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_943])).

cnf(c_5313,plain,
    ( r3_waybel_9(sK5,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_9675,plain,
    ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6)) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,sK6),k1_xboole_0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9663,c_5313])).

cnf(c_5416,plain,
    ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6))
    | ~ l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_5417,plain,
    ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6)) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5416])).

cnf(c_9857,plain,
    ( r2_hidden(sK4(sK5,sK6),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9675,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5406,c_5417,c_5637,c_8927])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5329,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9862,plain,
    ( r1_tarski(k1_xboole_0,sK4(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9857,c_5329])).

cnf(c_10799,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5331,c_9862])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.67/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.01  
% 3.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.01  
% 3.67/1.01  ------  iProver source info
% 3.67/1.01  
% 3.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.01  git: non_committed_changes: false
% 3.67/1.01  git: last_make_outside_of_git: false
% 3.67/1.01  
% 3.67/1.01  ------ 
% 3.67/1.01  
% 3.67/1.01  ------ Input Options
% 3.67/1.01  
% 3.67/1.01  --out_options                           all
% 3.67/1.01  --tptp_safe_out                         true
% 3.67/1.01  --problem_path                          ""
% 3.67/1.01  --include_path                          ""
% 3.67/1.01  --clausifier                            res/vclausify_rel
% 3.67/1.01  --clausifier_options                    ""
% 3.67/1.01  --stdin                                 false
% 3.67/1.01  --stats_out                             all
% 3.67/1.01  
% 3.67/1.01  ------ General Options
% 3.67/1.01  
% 3.67/1.01  --fof                                   false
% 3.67/1.01  --time_out_real                         305.
% 3.67/1.01  --time_out_virtual                      -1.
% 3.67/1.01  --symbol_type_check                     false
% 3.67/1.01  --clausify_out                          false
% 3.67/1.01  --sig_cnt_out                           false
% 3.67/1.01  --trig_cnt_out                          false
% 3.67/1.01  --trig_cnt_out_tolerance                1.
% 3.67/1.01  --trig_cnt_out_sk_spl                   false
% 3.67/1.01  --abstr_cl_out                          false
% 3.67/1.01  
% 3.67/1.01  ------ Global Options
% 3.67/1.01  
% 3.67/1.01  --schedule                              default
% 3.67/1.01  --add_important_lit                     false
% 3.67/1.01  --prop_solver_per_cl                    1000
% 3.67/1.01  --min_unsat_core                        false
% 3.67/1.01  --soft_assumptions                      false
% 3.67/1.01  --soft_lemma_size                       3
% 3.67/1.01  --prop_impl_unit_size                   0
% 3.67/1.01  --prop_impl_unit                        []
% 3.67/1.01  --share_sel_clauses                     true
% 3.67/1.01  --reset_solvers                         false
% 3.67/1.01  --bc_imp_inh                            [conj_cone]
% 3.67/1.01  --conj_cone_tolerance                   3.
% 3.67/1.01  --extra_neg_conj                        none
% 3.67/1.01  --large_theory_mode                     true
% 3.67/1.01  --prolific_symb_bound                   200
% 3.67/1.01  --lt_threshold                          2000
% 3.67/1.01  --clause_weak_htbl                      true
% 3.67/1.01  --gc_record_bc_elim                     false
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing Options
% 3.67/1.01  
% 3.67/1.01  --preprocessing_flag                    true
% 3.67/1.01  --time_out_prep_mult                    0.1
% 3.67/1.01  --splitting_mode                        input
% 3.67/1.01  --splitting_grd                         true
% 3.67/1.01  --splitting_cvd                         false
% 3.67/1.01  --splitting_cvd_svl                     false
% 3.67/1.01  --splitting_nvd                         32
% 3.67/1.01  --sub_typing                            true
% 3.67/1.01  --prep_gs_sim                           true
% 3.67/1.01  --prep_unflatten                        true
% 3.67/1.01  --prep_res_sim                          true
% 3.67/1.01  --prep_upred                            true
% 3.67/1.01  --prep_sem_filter                       exhaustive
% 3.67/1.01  --prep_sem_filter_out                   false
% 3.67/1.01  --pred_elim                             true
% 3.67/1.01  --res_sim_input                         true
% 3.67/1.01  --eq_ax_congr_red                       true
% 3.67/1.01  --pure_diseq_elim                       true
% 3.67/1.01  --brand_transform                       false
% 3.67/1.01  --non_eq_to_eq                          false
% 3.67/1.01  --prep_def_merge                        true
% 3.67/1.01  --prep_def_merge_prop_impl              false
% 3.67/1.01  --prep_def_merge_mbd                    true
% 3.67/1.01  --prep_def_merge_tr_red                 false
% 3.67/1.01  --prep_def_merge_tr_cl                  false
% 3.67/1.01  --smt_preprocessing                     true
% 3.67/1.01  --smt_ac_axioms                         fast
% 3.67/1.01  --preprocessed_out                      false
% 3.67/1.01  --preprocessed_stats                    false
% 3.67/1.01  
% 3.67/1.01  ------ Abstraction refinement Options
% 3.67/1.01  
% 3.67/1.01  --abstr_ref                             []
% 3.67/1.01  --abstr_ref_prep                        false
% 3.67/1.01  --abstr_ref_until_sat                   false
% 3.67/1.01  --abstr_ref_sig_restrict                funpre
% 3.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.01  --abstr_ref_under                       []
% 3.67/1.01  
% 3.67/1.01  ------ SAT Options
% 3.67/1.01  
% 3.67/1.01  --sat_mode                              false
% 3.67/1.01  --sat_fm_restart_options                ""
% 3.67/1.01  --sat_gr_def                            false
% 3.67/1.01  --sat_epr_types                         true
% 3.67/1.01  --sat_non_cyclic_types                  false
% 3.67/1.01  --sat_finite_models                     false
% 3.67/1.01  --sat_fm_lemmas                         false
% 3.67/1.01  --sat_fm_prep                           false
% 3.67/1.01  --sat_fm_uc_incr                        true
% 3.67/1.01  --sat_out_model                         small
% 3.67/1.01  --sat_out_clauses                       false
% 3.67/1.01  
% 3.67/1.01  ------ QBF Options
% 3.67/1.01  
% 3.67/1.01  --qbf_mode                              false
% 3.67/1.01  --qbf_elim_univ                         false
% 3.67/1.01  --qbf_dom_inst                          none
% 3.67/1.01  --qbf_dom_pre_inst                      false
% 3.67/1.01  --qbf_sk_in                             false
% 3.67/1.01  --qbf_pred_elim                         true
% 3.67/1.01  --qbf_split                             512
% 3.67/1.01  
% 3.67/1.01  ------ BMC1 Options
% 3.67/1.01  
% 3.67/1.01  --bmc1_incremental                      false
% 3.67/1.01  --bmc1_axioms                           reachable_all
% 3.67/1.01  --bmc1_min_bound                        0
% 3.67/1.01  --bmc1_max_bound                        -1
% 3.67/1.01  --bmc1_max_bound_default                -1
% 3.67/1.01  --bmc1_symbol_reachability              true
% 3.67/1.01  --bmc1_property_lemmas                  false
% 3.67/1.01  --bmc1_k_induction                      false
% 3.67/1.01  --bmc1_non_equiv_states                 false
% 3.67/1.01  --bmc1_deadlock                         false
% 3.67/1.01  --bmc1_ucm                              false
% 3.67/1.01  --bmc1_add_unsat_core                   none
% 3.67/1.01  --bmc1_unsat_core_children              false
% 3.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.01  --bmc1_out_stat                         full
% 3.67/1.01  --bmc1_ground_init                      false
% 3.67/1.01  --bmc1_pre_inst_next_state              false
% 3.67/1.01  --bmc1_pre_inst_state                   false
% 3.67/1.01  --bmc1_pre_inst_reach_state             false
% 3.67/1.01  --bmc1_out_unsat_core                   false
% 3.67/1.01  --bmc1_aig_witness_out                  false
% 3.67/1.01  --bmc1_verbose                          false
% 3.67/1.01  --bmc1_dump_clauses_tptp                false
% 3.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.01  --bmc1_dump_file                        -
% 3.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.01  --bmc1_ucm_extend_mode                  1
% 3.67/1.01  --bmc1_ucm_init_mode                    2
% 3.67/1.01  --bmc1_ucm_cone_mode                    none
% 3.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.01  --bmc1_ucm_relax_model                  4
% 3.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.01  --bmc1_ucm_layered_model                none
% 3.67/1.01  --bmc1_ucm_max_lemma_size               10
% 3.67/1.01  
% 3.67/1.01  ------ AIG Options
% 3.67/1.01  
% 3.67/1.01  --aig_mode                              false
% 3.67/1.01  
% 3.67/1.01  ------ Instantiation Options
% 3.67/1.01  
% 3.67/1.01  --instantiation_flag                    true
% 3.67/1.01  --inst_sos_flag                         true
% 3.67/1.01  --inst_sos_phase                        true
% 3.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel_side                     num_symb
% 3.67/1.01  --inst_solver_per_active                1400
% 3.67/1.01  --inst_solver_calls_frac                1.
% 3.67/1.01  --inst_passive_queue_type               priority_queues
% 3.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.01  --inst_passive_queues_freq              [25;2]
% 3.67/1.01  --inst_dismatching                      true
% 3.67/1.01  --inst_eager_unprocessed_to_passive     true
% 3.67/1.01  --inst_prop_sim_given                   true
% 3.67/1.01  --inst_prop_sim_new                     false
% 3.67/1.01  --inst_subs_new                         false
% 3.67/1.01  --inst_eq_res_simp                      false
% 3.67/1.01  --inst_subs_given                       false
% 3.67/1.01  --inst_orphan_elimination               true
% 3.67/1.01  --inst_learning_loop_flag               true
% 3.67/1.01  --inst_learning_start                   3000
% 3.67/1.01  --inst_learning_factor                  2
% 3.67/1.01  --inst_start_prop_sim_after_learn       3
% 3.67/1.01  --inst_sel_renew                        solver
% 3.67/1.01  --inst_lit_activity_flag                true
% 3.67/1.01  --inst_restr_to_given                   false
% 3.67/1.01  --inst_activity_threshold               500
% 3.67/1.01  --inst_out_proof                        true
% 3.67/1.01  
% 3.67/1.01  ------ Resolution Options
% 3.67/1.01  
% 3.67/1.01  --resolution_flag                       true
% 3.67/1.01  --res_lit_sel                           adaptive
% 3.67/1.01  --res_lit_sel_side                      none
% 3.67/1.01  --res_ordering                          kbo
% 3.67/1.01  --res_to_prop_solver                    active
% 3.67/1.01  --res_prop_simpl_new                    false
% 3.67/1.01  --res_prop_simpl_given                  true
% 3.67/1.01  --res_passive_queue_type                priority_queues
% 3.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.01  --res_passive_queues_freq               [15;5]
% 3.67/1.01  --res_forward_subs                      full
% 3.67/1.01  --res_backward_subs                     full
% 3.67/1.01  --res_forward_subs_resolution           true
% 3.67/1.01  --res_backward_subs_resolution          true
% 3.67/1.01  --res_orphan_elimination                true
% 3.67/1.01  --res_time_limit                        2.
% 3.67/1.01  --res_out_proof                         true
% 3.67/1.01  
% 3.67/1.01  ------ Superposition Options
% 3.67/1.01  
% 3.67/1.01  --superposition_flag                    true
% 3.67/1.01  --sup_passive_queue_type                priority_queues
% 3.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.01  --demod_completeness_check              fast
% 3.67/1.01  --demod_use_ground                      true
% 3.67/1.01  --sup_to_prop_solver                    passive
% 3.67/1.01  --sup_prop_simpl_new                    true
% 3.67/1.01  --sup_prop_simpl_given                  true
% 3.67/1.01  --sup_fun_splitting                     true
% 3.67/1.01  --sup_smt_interval                      50000
% 3.67/1.01  
% 3.67/1.01  ------ Superposition Simplification Setup
% 3.67/1.01  
% 3.67/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/1.01  --sup_immed_triv                        [TrivRules]
% 3.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_immed_bw_main                     []
% 3.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_input_bw                          []
% 3.67/1.01  
% 3.67/1.01  ------ Combination Options
% 3.67/1.01  
% 3.67/1.01  --comb_res_mult                         3
% 3.67/1.01  --comb_sup_mult                         2
% 3.67/1.01  --comb_inst_mult                        10
% 3.67/1.01  
% 3.67/1.01  ------ Debug Options
% 3.67/1.01  
% 3.67/1.01  --dbg_backtrace                         false
% 3.67/1.01  --dbg_dump_prop_clauses                 false
% 3.67/1.01  --dbg_dump_prop_clauses_file            -
% 3.67/1.01  --dbg_out_stat                          false
% 3.67/1.01  ------ Parsing...
% 3.67/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/1.01  ------ Proving...
% 3.67/1.01  ------ Problem Properties 
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  clauses                                 34
% 3.67/1.01  conjectures                             6
% 3.67/1.01  EPR                                     15
% 3.67/1.01  Horn                                    15
% 3.67/1.01  unary                                   3
% 3.67/1.01  binary                                  11
% 3.67/1.01  lits                                    138
% 3.67/1.01  lits eq                                 3
% 3.67/1.01  fd_pure                                 0
% 3.67/1.01  fd_pseudo                               0
% 3.67/1.01  fd_cond                                 0
% 3.67/1.01  fd_pseudo_cond                          1
% 3.67/1.01  AC symbols                              0
% 3.67/1.01  
% 3.67/1.01  ------ Schedule dynamic 5 is on 
% 3.67/1.01  
% 3.67/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  ------ 
% 3.67/1.01  Current options:
% 3.67/1.01  ------ 
% 3.67/1.01  
% 3.67/1.01  ------ Input Options
% 3.67/1.01  
% 3.67/1.01  --out_options                           all
% 3.67/1.01  --tptp_safe_out                         true
% 3.67/1.01  --problem_path                          ""
% 3.67/1.01  --include_path                          ""
% 3.67/1.01  --clausifier                            res/vclausify_rel
% 3.67/1.01  --clausifier_options                    ""
% 3.67/1.01  --stdin                                 false
% 3.67/1.01  --stats_out                             all
% 3.67/1.01  
% 3.67/1.01  ------ General Options
% 3.67/1.01  
% 3.67/1.01  --fof                                   false
% 3.67/1.01  --time_out_real                         305.
% 3.67/1.01  --time_out_virtual                      -1.
% 3.67/1.01  --symbol_type_check                     false
% 3.67/1.01  --clausify_out                          false
% 3.67/1.01  --sig_cnt_out                           false
% 3.67/1.01  --trig_cnt_out                          false
% 3.67/1.01  --trig_cnt_out_tolerance                1.
% 3.67/1.01  --trig_cnt_out_sk_spl                   false
% 3.67/1.01  --abstr_cl_out                          false
% 3.67/1.01  
% 3.67/1.01  ------ Global Options
% 3.67/1.01  
% 3.67/1.01  --schedule                              default
% 3.67/1.01  --add_important_lit                     false
% 3.67/1.01  --prop_solver_per_cl                    1000
% 3.67/1.01  --min_unsat_core                        false
% 3.67/1.01  --soft_assumptions                      false
% 3.67/1.01  --soft_lemma_size                       3
% 3.67/1.01  --prop_impl_unit_size                   0
% 3.67/1.01  --prop_impl_unit                        []
% 3.67/1.01  --share_sel_clauses                     true
% 3.67/1.01  --reset_solvers                         false
% 3.67/1.01  --bc_imp_inh                            [conj_cone]
% 3.67/1.01  --conj_cone_tolerance                   3.
% 3.67/1.01  --extra_neg_conj                        none
% 3.67/1.01  --large_theory_mode                     true
% 3.67/1.01  --prolific_symb_bound                   200
% 3.67/1.01  --lt_threshold                          2000
% 3.67/1.01  --clause_weak_htbl                      true
% 3.67/1.01  --gc_record_bc_elim                     false
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing Options
% 3.67/1.01  
% 3.67/1.01  --preprocessing_flag                    true
% 3.67/1.01  --time_out_prep_mult                    0.1
% 3.67/1.01  --splitting_mode                        input
% 3.67/1.01  --splitting_grd                         true
% 3.67/1.01  --splitting_cvd                         false
% 3.67/1.01  --splitting_cvd_svl                     false
% 3.67/1.01  --splitting_nvd                         32
% 3.67/1.01  --sub_typing                            true
% 3.67/1.01  --prep_gs_sim                           true
% 3.67/1.01  --prep_unflatten                        true
% 3.67/1.01  --prep_res_sim                          true
% 3.67/1.01  --prep_upred                            true
% 3.67/1.01  --prep_sem_filter                       exhaustive
% 3.67/1.01  --prep_sem_filter_out                   false
% 3.67/1.01  --pred_elim                             true
% 3.67/1.01  --res_sim_input                         true
% 3.67/1.01  --eq_ax_congr_red                       true
% 3.67/1.01  --pure_diseq_elim                       true
% 3.67/1.01  --brand_transform                       false
% 3.67/1.01  --non_eq_to_eq                          false
% 3.67/1.01  --prep_def_merge                        true
% 3.67/1.01  --prep_def_merge_prop_impl              false
% 3.67/1.01  --prep_def_merge_mbd                    true
% 3.67/1.01  --prep_def_merge_tr_red                 false
% 3.67/1.01  --prep_def_merge_tr_cl                  false
% 3.67/1.01  --smt_preprocessing                     true
% 3.67/1.01  --smt_ac_axioms                         fast
% 3.67/1.01  --preprocessed_out                      false
% 3.67/1.01  --preprocessed_stats                    false
% 3.67/1.01  
% 3.67/1.01  ------ Abstraction refinement Options
% 3.67/1.01  
% 3.67/1.01  --abstr_ref                             []
% 3.67/1.01  --abstr_ref_prep                        false
% 3.67/1.01  --abstr_ref_until_sat                   false
% 3.67/1.01  --abstr_ref_sig_restrict                funpre
% 3.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.01  --abstr_ref_under                       []
% 3.67/1.01  
% 3.67/1.01  ------ SAT Options
% 3.67/1.01  
% 3.67/1.01  --sat_mode                              false
% 3.67/1.01  --sat_fm_restart_options                ""
% 3.67/1.01  --sat_gr_def                            false
% 3.67/1.01  --sat_epr_types                         true
% 3.67/1.01  --sat_non_cyclic_types                  false
% 3.67/1.01  --sat_finite_models                     false
% 3.67/1.01  --sat_fm_lemmas                         false
% 3.67/1.01  --sat_fm_prep                           false
% 3.67/1.01  --sat_fm_uc_incr                        true
% 3.67/1.01  --sat_out_model                         small
% 3.67/1.01  --sat_out_clauses                       false
% 3.67/1.01  
% 3.67/1.01  ------ QBF Options
% 3.67/1.01  
% 3.67/1.01  --qbf_mode                              false
% 3.67/1.01  --qbf_elim_univ                         false
% 3.67/1.01  --qbf_dom_inst                          none
% 3.67/1.01  --qbf_dom_pre_inst                      false
% 3.67/1.01  --qbf_sk_in                             false
% 3.67/1.01  --qbf_pred_elim                         true
% 3.67/1.01  --qbf_split                             512
% 3.67/1.01  
% 3.67/1.01  ------ BMC1 Options
% 3.67/1.01  
% 3.67/1.01  --bmc1_incremental                      false
% 3.67/1.01  --bmc1_axioms                           reachable_all
% 3.67/1.01  --bmc1_min_bound                        0
% 3.67/1.01  --bmc1_max_bound                        -1
% 3.67/1.01  --bmc1_max_bound_default                -1
% 3.67/1.01  --bmc1_symbol_reachability              true
% 3.67/1.01  --bmc1_property_lemmas                  false
% 3.67/1.01  --bmc1_k_induction                      false
% 3.67/1.01  --bmc1_non_equiv_states                 false
% 3.67/1.01  --bmc1_deadlock                         false
% 3.67/1.01  --bmc1_ucm                              false
% 3.67/1.01  --bmc1_add_unsat_core                   none
% 3.67/1.01  --bmc1_unsat_core_children              false
% 3.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.01  --bmc1_out_stat                         full
% 3.67/1.01  --bmc1_ground_init                      false
% 3.67/1.01  --bmc1_pre_inst_next_state              false
% 3.67/1.01  --bmc1_pre_inst_state                   false
% 3.67/1.01  --bmc1_pre_inst_reach_state             false
% 3.67/1.01  --bmc1_out_unsat_core                   false
% 3.67/1.01  --bmc1_aig_witness_out                  false
% 3.67/1.01  --bmc1_verbose                          false
% 3.67/1.01  --bmc1_dump_clauses_tptp                false
% 3.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.01  --bmc1_dump_file                        -
% 3.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.01  --bmc1_ucm_extend_mode                  1
% 3.67/1.01  --bmc1_ucm_init_mode                    2
% 3.67/1.01  --bmc1_ucm_cone_mode                    none
% 3.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.01  --bmc1_ucm_relax_model                  4
% 3.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.01  --bmc1_ucm_layered_model                none
% 3.67/1.01  --bmc1_ucm_max_lemma_size               10
% 3.67/1.01  
% 3.67/1.01  ------ AIG Options
% 3.67/1.01  
% 3.67/1.01  --aig_mode                              false
% 3.67/1.01  
% 3.67/1.01  ------ Instantiation Options
% 3.67/1.01  
% 3.67/1.01  --instantiation_flag                    true
% 3.67/1.01  --inst_sos_flag                         true
% 3.67/1.01  --inst_sos_phase                        true
% 3.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel_side                     none
% 3.67/1.01  --inst_solver_per_active                1400
% 3.67/1.01  --inst_solver_calls_frac                1.
% 3.67/1.01  --inst_passive_queue_type               priority_queues
% 3.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.01  --inst_passive_queues_freq              [25;2]
% 3.67/1.01  --inst_dismatching                      true
% 3.67/1.01  --inst_eager_unprocessed_to_passive     true
% 3.67/1.01  --inst_prop_sim_given                   true
% 3.67/1.01  --inst_prop_sim_new                     false
% 3.67/1.01  --inst_subs_new                         false
% 3.67/1.01  --inst_eq_res_simp                      false
% 3.67/1.01  --inst_subs_given                       false
% 3.67/1.01  --inst_orphan_elimination               true
% 3.67/1.01  --inst_learning_loop_flag               true
% 3.67/1.01  --inst_learning_start                   3000
% 3.67/1.01  --inst_learning_factor                  2
% 3.67/1.01  --inst_start_prop_sim_after_learn       3
% 3.67/1.01  --inst_sel_renew                        solver
% 3.67/1.01  --inst_lit_activity_flag                true
% 3.67/1.01  --inst_restr_to_given                   false
% 3.67/1.01  --inst_activity_threshold               500
% 3.67/1.01  --inst_out_proof                        true
% 3.67/1.01  
% 3.67/1.01  ------ Resolution Options
% 3.67/1.01  
% 3.67/1.01  --resolution_flag                       false
% 3.67/1.01  --res_lit_sel                           adaptive
% 3.67/1.01  --res_lit_sel_side                      none
% 3.67/1.01  --res_ordering                          kbo
% 3.67/1.01  --res_to_prop_solver                    active
% 3.67/1.01  --res_prop_simpl_new                    false
% 3.67/1.01  --res_prop_simpl_given                  true
% 3.67/1.01  --res_passive_queue_type                priority_queues
% 3.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.67/1.01  --res_passive_queues_freq               [15;5]
% 3.67/1.01  --res_forward_subs                      full
% 3.67/1.01  --res_backward_subs                     full
% 3.67/1.01  --res_forward_subs_resolution           true
% 3.67/1.01  --res_backward_subs_resolution          true
% 3.67/1.01  --res_orphan_elimination                true
% 3.67/1.01  --res_time_limit                        2.
% 3.67/1.01  --res_out_proof                         true
% 3.67/1.01  
% 3.67/1.01  ------ Superposition Options
% 3.67/1.01  
% 3.67/1.01  --superposition_flag                    true
% 3.67/1.01  --sup_passive_queue_type                priority_queues
% 3.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.67/1.01  --demod_completeness_check              fast
% 3.67/1.01  --demod_use_ground                      true
% 3.67/1.01  --sup_to_prop_solver                    passive
% 3.67/1.01  --sup_prop_simpl_new                    true
% 3.67/1.01  --sup_prop_simpl_given                  true
% 3.67/1.01  --sup_fun_splitting                     true
% 3.67/1.01  --sup_smt_interval                      50000
% 3.67/1.01  
% 3.67/1.01  ------ Superposition Simplification Setup
% 3.67/1.01  
% 3.67/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.67/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.67/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.67/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.67/1.01  --sup_immed_triv                        [TrivRules]
% 3.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_immed_bw_main                     []
% 3.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.67/1.01  --sup_input_bw                          []
% 3.67/1.01  
% 3.67/1.01  ------ Combination Options
% 3.67/1.01  
% 3.67/1.01  --comb_res_mult                         3
% 3.67/1.01  --comb_sup_mult                         2
% 3.67/1.01  --comb_inst_mult                        10
% 3.67/1.01  
% 3.67/1.01  ------ Debug Options
% 3.67/1.01  
% 3.67/1.01  --dbg_backtrace                         false
% 3.67/1.01  --dbg_dump_prop_clauses                 false
% 3.67/1.01  --dbg_dump_prop_clauses_file            -
% 3.67/1.01  --dbg_out_stat                          false
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  ------ Proving...
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  % SZS status Theorem for theBenchmark.p
% 3.67/1.01  
% 3.67/1.01   Resolution empty clause
% 3.67/1.01  
% 3.67/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.01  
% 3.67/1.01  fof(f3,axiom,(
% 3.67/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f71,plain,(
% 3.67/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f3])).
% 3.67/1.01  
% 3.67/1.01  fof(f14,axiom,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f36,plain,(
% 3.67/1.01    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f14])).
% 3.67/1.01  
% 3.67/1.01  fof(f37,plain,(
% 3.67/1.01    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f36])).
% 3.67/1.01  
% 3.67/1.01  fof(f53,plain,(
% 3.67/1.01    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(nnf_transformation,[],[f37])).
% 3.67/1.01  
% 3.67/1.01  fof(f54,plain,(
% 3.67/1.01    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(rectify,[],[f53])).
% 3.67/1.01  
% 3.67/1.01  fof(f56,plain,(
% 3.67/1.01    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f55,plain,(
% 3.67/1.01    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f57,plain,(
% 3.67/1.01    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 3.67/1.01  
% 3.67/1.01  fof(f90,plain,(
% 3.67/1.01    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK4(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f15,conjecture,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f16,negated_conjecture,(
% 3.67/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.67/1.01    inference(negated_conjecture,[],[f15])).
% 3.67/1.01  
% 3.67/1.01  fof(f38,plain,(
% 3.67/1.01    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f16])).
% 3.67/1.01  
% 3.67/1.01  fof(f39,plain,(
% 3.67/1.01    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f38])).
% 3.67/1.01  
% 3.67/1.01  fof(f58,plain,(
% 3.67/1.01    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/1.01    inference(nnf_transformation,[],[f39])).
% 3.67/1.01  
% 3.67/1.01  fof(f59,plain,(
% 3.67/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f58])).
% 3.67/1.01  
% 3.67/1.01  fof(f60,plain,(
% 3.67/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/1.01    inference(rectify,[],[f59])).
% 3.67/1.01  
% 3.67/1.01  fof(f63,plain,(
% 3.67/1.01    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK7(X3),X0) & m2_yellow_6(sK7(X3),X0,X3)))) )),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f62,plain,(
% 3.67/1.01    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK6)) & l1_waybel_0(sK6,X0) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))) )),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f61,plain,(
% 3.67/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,X1)) & l1_waybel_0(X1,sK5) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK5)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK5) & m2_yellow_6(X4,sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f64,plain,(
% 3.67/1.01    ((! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6)) & l1_waybel_0(sK6,sK5) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) | ~v1_compts_1(sK5)) & (! [X3] : ((v3_yellow_6(sK7(X3),sK5) & m2_yellow_6(sK7(X3),sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).
% 3.67/1.01  
% 3.67/1.01  fof(f97,plain,(
% 3.67/1.01    v2_pre_topc(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f96,plain,(
% 3.67/1.01    ~v2_struct_0(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f98,plain,(
% 3.67/1.01    l1_pre_topc(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f13,axiom,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f34,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f13])).
% 3.67/1.01  
% 3.67/1.01  fof(f35,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f34])).
% 3.67/1.01  
% 3.67/1.01  fof(f51,plain,(
% 3.67/1.01    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & m2_yellow_6(sK2(X0,X1,X2),X0,X1)))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f52,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & m2_yellow_6(sK2(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f51])).
% 3.67/1.01  
% 3.67/1.01  fof(f87,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (m2_yellow_6(sK2(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f52])).
% 3.67/1.01  
% 3.67/1.01  fof(f10,axiom,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f28,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f10])).
% 3.67/1.01  
% 3.67/1.01  fof(f29,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f28])).
% 3.67/1.01  
% 3.67/1.01  fof(f46,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(nnf_transformation,[],[f29])).
% 3.67/1.01  
% 3.67/1.01  fof(f82,plain,(
% 3.67/1.01    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f46])).
% 3.67/1.01  
% 3.67/1.01  fof(f105,plain,(
% 3.67/1.01    ( ! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6) | ~v1_compts_1(sK5)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f101,plain,(
% 3.67/1.01    ~v2_struct_0(sK6) | ~v1_compts_1(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f102,plain,(
% 3.67/1.01    v4_orders_2(sK6) | ~v1_compts_1(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f103,plain,(
% 3.67/1.01    v7_waybel_0(sK6) | ~v1_compts_1(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f104,plain,(
% 3.67/1.01    l1_waybel_0(sK6,sK5) | ~v1_compts_1(sK5)),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f6,axiom,(
% 3.67/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f21,plain,(
% 3.67/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.67/1.01    inference(ennf_transformation,[],[f6])).
% 3.67/1.01  
% 3.67/1.01  fof(f74,plain,(
% 3.67/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f21])).
% 3.67/1.01  
% 3.67/1.01  fof(f8,axiom,(
% 3.67/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f24,plain,(
% 3.67/1.01    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f8])).
% 3.67/1.01  
% 3.67/1.01  fof(f25,plain,(
% 3.67/1.01    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f24])).
% 3.67/1.01  
% 3.67/1.01  fof(f79,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f25])).
% 3.67/1.01  
% 3.67/1.01  fof(f78,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f25])).
% 3.67/1.01  
% 3.67/1.01  fof(f77,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f25])).
% 3.67/1.01  
% 3.67/1.01  fof(f76,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f25])).
% 3.67/1.01  
% 3.67/1.01  fof(f99,plain,(
% 3.67/1.01    ( ! [X3] : (m2_yellow_6(sK7(X3),sK5,X3) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f1,axiom,(
% 3.67/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f17,plain,(
% 3.67/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f1])).
% 3.67/1.01  
% 3.67/1.01  fof(f40,plain,(
% 3.67/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.01    inference(nnf_transformation,[],[f17])).
% 3.67/1.01  
% 3.67/1.01  fof(f41,plain,(
% 3.67/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.01    inference(rectify,[],[f40])).
% 3.67/1.01  
% 3.67/1.01  fof(f42,plain,(
% 3.67/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f43,plain,(
% 3.67/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 3.67/1.01  
% 3.67/1.01  fof(f66,plain,(
% 3.67/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f43])).
% 3.67/1.01  
% 3.67/1.01  fof(f7,axiom,(
% 3.67/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f22,plain,(
% 3.67/1.01    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f7])).
% 3.67/1.01  
% 3.67/1.01  fof(f23,plain,(
% 3.67/1.01    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f22])).
% 3.67/1.01  
% 3.67/1.01  fof(f75,plain,(
% 3.67/1.01    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f23])).
% 3.67/1.01  
% 3.67/1.01  fof(f4,axiom,(
% 3.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f18,plain,(
% 3.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.67/1.01    inference(ennf_transformation,[],[f4])).
% 3.67/1.01  
% 3.67/1.01  fof(f19,plain,(
% 3.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.67/1.01    inference(flattening,[],[f18])).
% 3.67/1.01  
% 3.67/1.01  fof(f72,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f19])).
% 3.67/1.01  
% 3.67/1.01  fof(f12,axiom,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f32,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f12])).
% 3.67/1.01  
% 3.67/1.01  fof(f33,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f32])).
% 3.67/1.01  
% 3.67/1.01  fof(f86,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f33])).
% 3.67/1.01  
% 3.67/1.01  fof(f11,axiom,(
% 3.67/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f30,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f11])).
% 3.67/1.01  
% 3.67/1.01  fof(f31,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f30])).
% 3.67/1.01  
% 3.67/1.01  fof(f47,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(nnf_transformation,[],[f31])).
% 3.67/1.01  
% 3.67/1.01  fof(f48,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(rectify,[],[f47])).
% 3.67/1.01  
% 3.67/1.01  fof(f49,plain,(
% 3.67/1.01    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X2)))),
% 3.67/1.01    introduced(choice_axiom,[])).
% 3.67/1.01  
% 3.67/1.01  fof(f50,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 3.67/1.01  
% 3.67/1.01  fof(f84,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK1(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f50])).
% 3.67/1.01  
% 3.67/1.01  fof(f83,plain,(
% 3.67/1.01    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f50])).
% 3.67/1.01  
% 3.67/1.01  fof(f9,axiom,(
% 3.67/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f26,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.67/1.01    inference(ennf_transformation,[],[f9])).
% 3.67/1.01  
% 3.67/1.01  fof(f27,plain,(
% 3.67/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.67/1.01    inference(flattening,[],[f26])).
% 3.67/1.01  
% 3.67/1.01  fof(f80,plain,(
% 3.67/1.01    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f27])).
% 3.67/1.01  
% 3.67/1.01  fof(f85,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f50])).
% 3.67/1.01  
% 3.67/1.01  fof(f95,plain,(
% 3.67/1.01    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f91,plain,(
% 3.67/1.01    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f92,plain,(
% 3.67/1.01    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f93,plain,(
% 3.67/1.01    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f94,plain,(
% 3.67/1.01    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f2,axiom,(
% 3.67/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f44,plain,(
% 3.67/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.01    inference(nnf_transformation,[],[f2])).
% 3.67/1.01  
% 3.67/1.01  fof(f45,plain,(
% 3.67/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.67/1.01    inference(flattening,[],[f44])).
% 3.67/1.01  
% 3.67/1.01  fof(f70,plain,(
% 3.67/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f45])).
% 3.67/1.01  
% 3.67/1.01  fof(f81,plain,(
% 3.67/1.01    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f46])).
% 3.67/1.01  
% 3.67/1.01  fof(f100,plain,(
% 3.67/1.01    ( ! [X3] : (v3_yellow_6(sK7(X3),sK5) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f64])).
% 3.67/1.01  
% 3.67/1.01  fof(f89,plain,(
% 3.67/1.01    ( ! [X0,X3] : (m1_subset_1(sK4(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f57])).
% 3.67/1.01  
% 3.67/1.01  fof(f88,plain,(
% 3.67/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f52])).
% 3.67/1.01  
% 3.67/1.01  fof(f5,axiom,(
% 3.67/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/1.01  
% 3.67/1.01  fof(f20,plain,(
% 3.67/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.67/1.01    inference(ennf_transformation,[],[f5])).
% 3.67/1.01  
% 3.67/1.01  fof(f73,plain,(
% 3.67/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.67/1.01    inference(cnf_transformation,[],[f20])).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6,plain,
% 3.67/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5331,plain,
% 3.67/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_29,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_39,negated_conjecture,
% 3.67/1.01      ( v2_pre_topc(sK5) ),
% 3.67/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_798,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_799,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK4(sK5,X0))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_798]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_40,negated_conjecture,
% 3.67/1.01      ( ~ v2_struct_0(sK5) ),
% 3.67/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_38,negated_conjecture,
% 3.67/1.01      ( l1_pre_topc(sK5) ),
% 3.67/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_803,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | r3_waybel_9(sK5,X0,sK4(sK5,X0))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_799,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_804,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK4(sK5,X0))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_803]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5320,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK4(sK5,X0)) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_23,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_905,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_906,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_905]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_910,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_906,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_911,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_910]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5314,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.67/1.01      | m2_yellow_6(sK2(sK5,X0,X1),sK5,X0) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_16,plain,
% 3.67/1.01      ( v3_yellow_6(X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1)
% 3.67/1.01      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.67/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_31,negated_conjecture,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ v3_yellow_6(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5) ),
% 3.67/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_670,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ l1_waybel_0(X1,X2)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_pre_topc(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X2)
% 3.67/1.01      | X0 != X1
% 3.67/1.01      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.67/1.01      | sK5 != X2 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_671,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_pre_topc(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5)
% 3.67/1.01      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_670]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_675,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_671,c_40,c_39,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_676,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | k10_yellow_6(sK5,X0) = k1_xboole_0 ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_675]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5322,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.67/1.01      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_35,negated_conjecture,
% 3.67/1.01      ( ~ v1_compts_1(sK5) | ~ v2_struct_0(sK6) ),
% 3.67/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_50,plain,
% 3.67/1.01      ( v1_compts_1(sK5) != iProver_top | v2_struct_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_34,negated_conjecture,
% 3.67/1.01      ( ~ v1_compts_1(sK5) | v4_orders_2(sK6) ),
% 3.67/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_51,plain,
% 3.67/1.01      ( v1_compts_1(sK5) != iProver_top | v4_orders_2(sK6) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_33,negated_conjecture,
% 3.67/1.01      ( ~ v1_compts_1(sK5) | v7_waybel_0(sK6) ),
% 3.67/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_52,plain,
% 3.67/1.01      ( v1_compts_1(sK5) != iProver_top | v7_waybel_0(sK6) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_32,negated_conjecture,
% 3.67/1.01      ( l1_waybel_0(sK6,sK5) | ~ v1_compts_1(sK5) ),
% 3.67/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_53,plain,
% 3.67/1.01      ( l1_waybel_0(sK6,sK5) = iProver_top | v1_compts_1(sK5) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_677,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.67/1.01      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9,plain,
% 3.67/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_11,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | l1_waybel_0(X0,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_struct_0(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_595,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | l1_waybel_0(X0,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X3)
% 3.67/1.01      | X1 != X3 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_596,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | l1_waybel_0(X0,X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_595]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1192,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | l1_waybel_0(X0,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_596,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1193,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | l1_waybel_0(X0,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1192]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1195,plain,
% 3.67/1.01      ( v2_struct_0(X1)
% 3.67/1.01      | l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1193,c_40]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1196,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | l1_waybel_0(X0,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1195]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5419,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK6,sK5)
% 3.67/1.01      | v2_struct_0(sK6)
% 3.67/1.01      | ~ v4_orders_2(sK6)
% 3.67/1.01      | ~ v7_waybel_0(sK6) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5420,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) = iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5419]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_12,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_struct_0(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_567,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X3)
% 3.67/1.01      | X1 != X3 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_568,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1218,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_568,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1219,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | v7_waybel_0(X0) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1218]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1221,plain,
% 3.67/1.01      ( v2_struct_0(X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | v7_waybel_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1219,c_40]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1222,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1221]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5424,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ l1_waybel_0(sK6,sK5)
% 3.67/1.01      | v2_struct_0(sK6)
% 3.67/1.01      | ~ v4_orders_2(sK6)
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK6) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1222]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5425,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) = iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5424]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_13,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_struct_0(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_539,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X3)
% 3.67/1.01      | X1 != X3 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_540,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_539]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1244,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_540,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1245,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1244]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1247,plain,
% 3.67/1.01      ( v2_struct_0(X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1245,c_40]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1248,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1247]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5429,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK6)
% 3.67/1.01      | ~ l1_waybel_0(sK6,sK5)
% 3.67/1.01      | v2_struct_0(sK6)
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(sK6)
% 3.67/1.01      | ~ v7_waybel_0(sK6) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1248]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5430,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5429]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6478,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_5322,c_50,c_51,c_52,c_53,c_677,c_5420,c_5425,c_5430]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6479,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,X0) = k1_xboole_0
% 3.67/1.01      | m2_yellow_6(X0,sK5,sK6) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_6478]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6691,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5314,c_6479]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7521,plain,
% 3.67/1.01      ( v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_6691,c_50,c_51,c_52,c_53]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7522,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK2(sK5,sK6,X0)) = iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_7521]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_14,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_struct_0(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_511,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X3)
% 3.67/1.01      | X1 != X3 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_512,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_511]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1270,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,X1)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_512,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1271,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1270]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1273,plain,
% 3.67/1.01      ( v2_struct_0(X1)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1271,c_40]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1274,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,X1)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | ~ v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1273]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5304,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,X1) != iProver_top
% 3.67/1.01      | l1_waybel_0(X1,sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) != iProver_top
% 3.67/1.01      | v2_struct_0(X1) = iProver_top
% 3.67/1.01      | v4_orders_2(X1) != iProver_top
% 3.67/1.01      | v7_waybel_0(X1) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6695,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(sK2(sK5,X0,X1)) != iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5314,c_5304]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7527,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_7522,c_6695]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_37,negated_conjecture,
% 3.67/1.01      ( m2_yellow_6(sK7(X0),sK5,X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5324,plain,
% 3.67/1.01      ( m2_yellow_6(sK7(X0),sK5,X0) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1,plain,
% 3.67/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5335,plain,
% 3.67/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.67/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_10,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1061,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1062,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1061]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1066,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_1062,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1067,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1066]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5309,plain,
% 3.67/1.01      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7,plain,
% 3.67/1.01      ( m1_subset_1(X0,X1)
% 3.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.67/1.01      | ~ r2_hidden(X0,X2) ),
% 3.67/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5330,plain,
% 3.67/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.67/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.67/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6299,plain,
% 3.67/1.01      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) = iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5309,c_5330]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7151,plain,
% 3.67/1.01      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) = iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5335,c_6299]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_21,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_971,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_972,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_971]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_976,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_972,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_977,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK5,X0))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_976]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5312,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_978,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6535,plain,
% 3.67/1.01      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_5312,c_978,c_6299]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6536,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,X0)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_6535]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6541,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X0),X1)) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5335,c_6536]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_19,plain,
% 3.67/1.01      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 3.67/1.01      | r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_20,plain,
% 3.67/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.67/1.01      | ~ r3_waybel_9(X1,X3,X2)
% 3.67/1.01      | r2_waybel_0(X1,X3,X0)
% 3.67/1.01      | ~ l1_waybel_0(X3,X1)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_443,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | r3_waybel_9(X3,X4,X5)
% 3.67/1.01      | r2_waybel_0(X0,X1,X6)
% 3.67/1.01      | ~ l1_waybel_0(X4,X3)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ v2_pre_topc(X3)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | v2_struct_0(X4)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X3)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | X2 != X5
% 3.67/1.01      | X0 != X3
% 3.67/1.01      | sK1(X3,X4,X5) != X6 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_444,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | r3_waybel_9(X0,X3,X2)
% 3.67/1.01      | r2_waybel_0(X0,X1,sK1(X0,X3,X2))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ l1_waybel_0(X3,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_443]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_766,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | r3_waybel_9(X0,X3,X2)
% 3.67/1.01      | r2_waybel_0(X0,X1,sK1(X0,X3,X2))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ l1_waybel_0(X3,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_444,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_767,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | r3_waybel_9(sK5,X2,X1)
% 3.67/1.01      | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_766]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_769,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | r3_waybel_9(sK5,X2,X1)
% 3.67/1.01      | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X2) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_767,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_770,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | r3_waybel_9(sK5,X2,X1)
% 3.67/1.01      | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1))
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X2) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_769]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5321,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.67/1.01      | r3_waybel_9(sK5,X2,X1) = iProver_top
% 3.67/1.01      | r2_waybel_0(sK5,X0,sK1(sK5,X2,X1)) = iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X2,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(X2) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_15,plain,
% 3.67/1.01      ( ~ r2_waybel_0(X0,X1,X2)
% 3.67/1.01      | r2_waybel_0(X0,X3,X2)
% 3.67/1.01      | ~ m2_yellow_6(X1,X0,X3)
% 3.67/1.01      | ~ l1_waybel_0(X3,X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ v4_orders_2(X3)
% 3.67/1.01      | ~ v7_waybel_0(X3)
% 3.67/1.01      | ~ l1_struct_0(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_481,plain,
% 3.67/1.01      ( ~ r2_waybel_0(X0,X1,X2)
% 3.67/1.01      | r2_waybel_0(X0,X3,X2)
% 3.67/1.01      | ~ m2_yellow_6(X1,X0,X3)
% 3.67/1.01      | ~ l1_waybel_0(X3,X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ v4_orders_2(X3)
% 3.67/1.01      | ~ v7_waybel_0(X3)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(resolution,[status(thm)],[c_9,c_15]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1163,plain,
% 3.67/1.01      ( ~ r2_waybel_0(X0,X1,X2)
% 3.67/1.01      | r2_waybel_0(X0,X3,X2)
% 3.67/1.01      | ~ m2_yellow_6(X1,X0,X3)
% 3.67/1.01      | ~ l1_waybel_0(X3,X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X3)
% 3.67/1.01      | ~ v4_orders_2(X3)
% 3.67/1.01      | ~ v7_waybel_0(X3)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_481,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1164,plain,
% 3.67/1.01      ( ~ r2_waybel_0(sK5,X0,X1)
% 3.67/1.01      | r2_waybel_0(sK5,X2,X1)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1163]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1166,plain,
% 3.67/1.01      ( v2_struct_0(X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X2)
% 3.67/1.01      | r2_waybel_0(sK5,X2,X1)
% 3.67/1.01      | ~ r2_waybel_0(sK5,X0,X1)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2) ),
% 3.67/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1164,c_40]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1167,plain,
% 3.67/1.01      ( ~ r2_waybel_0(sK5,X0,X1)
% 3.67/1.01      | r2_waybel_0(sK5,X2,X1)
% 3.67/1.01      | ~ m2_yellow_6(X0,sK5,X2)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X2) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1166]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5308,plain,
% 3.67/1.01      ( r2_waybel_0(sK5,X0,X1) != iProver_top
% 3.67/1.01      | r2_waybel_0(sK5,X2,X1) = iProver_top
% 3.67/1.01      | m2_yellow_6(X0,sK5,X2) != iProver_top
% 3.67/1.01      | l1_waybel_0(X2,sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(X2) = iProver_top
% 3.67/1.01      | v4_orders_2(X2) != iProver_top
% 3.67/1.01      | v7_waybel_0(X2) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6784,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.67/1.01      | r3_waybel_9(sK5,X2,X1) = iProver_top
% 3.67/1.01      | r2_waybel_0(sK5,X3,sK1(sK5,X2,X1)) = iProver_top
% 3.67/1.01      | m2_yellow_6(X0,sK5,X3) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X2,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X3,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(X3) = iProver_top
% 3.67/1.01      | v2_struct_0(X2) = iProver_top
% 3.67/1.01      | v4_orders_2(X3) != iProver_top
% 3.67/1.01      | v7_waybel_0(X3) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5321,c_5308]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7885,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
% 3.67/1.01      | r2_waybel_0(sK5,X3,sK1(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2))) = iProver_top
% 3.67/1.01      | m2_yellow_6(X1,sK5,X3) != iProver_top
% 3.67/1.01      | l1_waybel_0(X1,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X3,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
% 3.67/1.01      | v2_struct_0(X1) = iProver_top
% 3.67/1.01      | v2_struct_0(X3) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X1) != iProver_top
% 3.67/1.01      | v4_orders_2(X3) != iProver_top
% 3.67/1.01      | v7_waybel_0(X1) != iProver_top
% 3.67/1.01      | v7_waybel_0(X3) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_6541,c_6784]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_18,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1004,plain,
% 3.67/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ r2_waybel_0(X0,X1,sK1(X0,X1,X2))
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1005,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ r2_waybel_0(sK5,X0,sK1(sK5,X0,X1))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1004]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1009,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ r2_waybel_0(sK5,X0,sK1(sK5,X0,X1))
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_1005,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5311,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) = iProver_top
% 3.67/1.01      | r2_waybel_0(sK5,X0,sK1(sK5,X0,X1)) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8714,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
% 3.67/1.01      | m2_yellow_6(X1,sK5,X0) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X1,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK0(k10_yellow_6(sK5,X1),X2),u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(X1) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v4_orders_2(X1) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X1) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_7885,c_5311]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8834,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,sK0(k10_yellow_6(sK5,X1),X2)) = iProver_top
% 3.67/1.01      | m2_yellow_6(X1,sK5,X0) != iProver_top
% 3.67/1.01      | l1_waybel_0(X1,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X1),X2) = iProver_top
% 3.67/1.01      | v2_struct_0(X1) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X1) != iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X1) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_7151,c_8714]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_24,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,sK3(X0),X1)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.67/1.01      | v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_884,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,sK3(X0),X1)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.67/1.01      | v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_885,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
% 3.67/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_884]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_889,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,sK3(sK5),X0)
% 3.67/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.67/1.01      | v1_compts_1(sK5) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_885,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5315,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,sK3(sK5),X0) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8840,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK0(k10_yellow_6(sK5,X0),X1),u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_8834,c_5315]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_28,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v2_struct_0(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_828,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v2_struct_0(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_829,plain,
% 3.67/1.01      ( v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_struct_0(sK3(sK5))
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_828]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_831,plain,
% 3.67/1.01      ( v1_compts_1(sK5) | ~ v2_struct_0(sK3(sK5)) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_829,c_40,c_39,c_38,c_64]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_833,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top | v2_struct_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_27,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v4_orders_2(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_842,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v4_orders_2(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_843,plain,
% 3.67/1.01      ( v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | v4_orders_2(sK3(sK5))
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_842]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_845,plain,
% 3.67/1.01      ( v4_orders_2(sK3(sK5)) | v1_compts_1(sK5) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_843,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_846,plain,
% 3.67/1.01      ( v1_compts_1(sK5) | v4_orders_2(sK3(sK5)) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_845]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_847,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top | v4_orders_2(sK3(sK5)) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_26,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v7_waybel_0(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_856,plain,
% 3.67/1.01      ( v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v7_waybel_0(sK3(X0))
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_857,plain,
% 3.67/1.01      ( v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | v7_waybel_0(sK3(sK5))
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_856]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_859,plain,
% 3.67/1.01      ( v7_waybel_0(sK3(sK5)) | v1_compts_1(sK5) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_857,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_860,plain,
% 3.67/1.01      ( v1_compts_1(sK5) | v7_waybel_0(sK3(sK5)) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_859]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_861,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top | v7_waybel_0(sK3(sK5)) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_25,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(X0),X0)
% 3.67/1.01      | v1_compts_1(X0)
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_870,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(X0),X0)
% 3.67/1.01      | v1_compts_1(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_871,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(sK5),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_870]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_873,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(sK5),sK5) | v1_compts_1(sK5) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_871,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_875,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5558,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.67/1.01      | l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.67/1.01      | v2_struct_0(sK3(sK5))
% 3.67/1.01      | ~ v4_orders_2(sK3(sK5))
% 3.67/1.01      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5559,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) = iProver_top
% 3.67/1.01      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5558]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5557,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.67/1.01      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.67/1.01      | v2_struct_0(sK3(sK5))
% 3.67/1.01      | ~ v4_orders_2(sK3(sK5))
% 3.67/1.01      | v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1222]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5563,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) = iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5557]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5556,plain,
% 3.67/1.01      ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
% 3.67/1.01      | ~ l1_waybel_0(sK3(sK5),sK5)
% 3.67/1.01      | v2_struct_0(sK3(sK5))
% 3.67/1.01      | v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(sK3(sK5))
% 3.67/1.01      | ~ v7_waybel_0(sK3(sK5)) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1248]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5567,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5556]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8906,plain,
% 3.67/1.01      ( v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.67/1.01      | m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_8840,c_833,c_847,c_861,c_875,c_5559,c_5563,c_5567,c_7151]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8907,plain,
% 3.67/1.01      ( m2_yellow_6(X0,sK5,sK3(sK5)) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,X0),X1) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_8906]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8912,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(sK7(sK3(sK5))) = iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5324,c_8907]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5316,plain,
% 3.67/1.01      ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5730,plain,
% 3.67/1.01      ( l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v2_struct_0(sK7(X0)) != iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5324,c_5304]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6037,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5316,c_5730]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6999,plain,
% 3.67/1.01      ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_6037,c_833,c_847,c_861]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_7000,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_6999]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8918,plain,
% 3.67/1.01      ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_8912,c_833,c_847,c_861,c_875,c_7000]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_3,plain,
% 3.67/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.67/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5333,plain,
% 3.67/1.01      ( X0 = X1
% 3.67/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.67/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_6250,plain,
% 3.67/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5331,c_5333]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8927,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_8918,c_6250]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1469,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | l1_waybel_0(X2,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | X0 != X1
% 3.67/1.01      | sK7(X1) != X2
% 3.67/1.01      | sK5 != sK5 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_37,c_1196]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1470,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1469]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1445,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | v7_waybel_0(X2)
% 3.67/1.01      | X0 != X1
% 3.67/1.01      | sK7(X1) != X2
% 3.67/1.01      | sK5 != sK5 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_37,c_1222]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1446,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | v7_waybel_0(sK7(X0)) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1445]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1421,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | X0 != X1
% 3.67/1.01      | sK7(X1) != X2
% 3.67/1.01      | sK5 != sK5 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_37,c_1248]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1422,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | v4_orders_2(sK7(X0))
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1421]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1397,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(X1,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_struct_0(X2)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | X0 != X1
% 3.67/1.01      | sK7(X1) != X2
% 3.67/1.01      | sK5 != sK5 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_37,c_1274]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1398,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v2_struct_0(sK7(X0))
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1397]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_17,plain,
% 3.67/1.01      ( ~ v3_yellow_6(X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1)
% 3.67/1.01      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.67/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_36,negated_conjecture,
% 3.67/1.01      ( v3_yellow_6(sK7(X0),sK5)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_703,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X2,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X2)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(X2)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(X2)
% 3.67/1.01      | ~ l1_pre_topc(X1)
% 3.67/1.01      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.67/1.01      | sK7(X2) != X0
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_704,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | ~ v2_pre_topc(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK7(X0))
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(sK7(X0))
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK7(X0))
% 3.67/1.01      | ~ l1_pre_topc(sK5)
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_703]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_708,plain,
% 3.67/1.01      ( ~ v7_waybel_0(sK7(X0))
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(sK7(X0))
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK7(X0))
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_704,c_40,c_39,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_709,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK7(X0))
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(sK7(X0))
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK7(X0))
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_708]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1650,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v4_orders_2(sK7(X0))
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK7(X0))
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_709]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1661,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v7_waybel_0(sK7(X0))
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1422,c_1650]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1672,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ l1_waybel_0(sK7(X0),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1446,c_1661]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1678,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | k10_yellow_6(sK5,sK7(X0)) != k1_xboole_0 ),
% 3.67/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1470,c_1672]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5636,plain,
% 3.67/1.01      ( ~ l1_waybel_0(sK3(sK5),sK5)
% 3.67/1.01      | v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK3(sK5))
% 3.67/1.01      | ~ v4_orders_2(sK3(sK5))
% 3.67/1.01      | ~ v7_waybel_0(sK3(sK5))
% 3.67/1.01      | k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0 ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5637,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
% 3.67/1.01      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) = iProver_top
% 3.67/1.01      | v2_struct_0(sK3(sK5)) = iProver_top
% 3.67/1.01      | v4_orders_2(sK3(sK5)) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5636]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8986,plain,
% 3.67/1.01      ( v1_compts_1(sK5) = iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_8927,c_833,c_847,c_861,c_875,c_5637]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9179,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.67/1.01      | k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_7527,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5637,
% 3.67/1.01                 c_8927]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9180,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,X0)) = k1_xboole_0
% 3.67/1.01      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 3.67/1.01      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_9179]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9185,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,sK4(sK5,sK6))) = k1_xboole_0
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5320,c_9180]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_30,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 3.67/1.01      | ~ v1_compts_1(X1)
% 3.67/1.01      | ~ v2_pre_topc(X1)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1) ),
% 3.67/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1031,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.67/1.01      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 3.67/1.01      | ~ v1_compts_1(X1)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(X1)
% 3.67/1.01      | sK5 != X1 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1032,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_1031]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1036,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_1032,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_1037,plain,
% 3.67/1.01      ( ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | m1_subset_1(sK4(sK5,X0),u1_struct_0(sK5))
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_1036]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5405,plain,
% 3.67/1.01      ( ~ l1_waybel_0(sK6,sK5)
% 3.67/1.01      | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5))
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK6)
% 3.67/1.01      | ~ v4_orders_2(sK6)
% 3.67/1.01      | ~ v7_waybel_0(sK6) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_1037]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5406,plain,
% 3.67/1.01      ( l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) = iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5405]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9663,plain,
% 3.67/1.01      ( k10_yellow_6(sK5,sK2(sK5,sK6,sK4(sK5,sK6))) = k1_xboole_0 ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_9185,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5406,
% 3.67/1.01                 c_5637,c_8927]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_22,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
% 3.67/1.01      | ~ v2_pre_topc(X0)
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_938,plain,
% 3.67/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.67/1.01      | ~ l1_waybel_0(X1,X0)
% 3.67/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.67/1.01      | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(X1)
% 3.67/1.01      | ~ v4_orders_2(X1)
% 3.67/1.01      | ~ v7_waybel_0(X1)
% 3.67/1.01      | ~ l1_pre_topc(X0)
% 3.67/1.01      | sK5 != X0 ),
% 3.67/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_39]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_939,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | v2_struct_0(sK5)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ l1_pre_topc(sK5) ),
% 3.67/1.01      inference(unflattening,[status(thm)],[c_938]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_943,plain,
% 3.67/1.01      ( ~ v7_waybel_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
% 3.67/1.01      | v2_struct_0(X0) ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_939,c_40,c_38]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_944,plain,
% 3.67/1.01      ( ~ r3_waybel_9(sK5,X0,X1)
% 3.67/1.01      | ~ l1_waybel_0(X0,sK5)
% 3.67/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1)))
% 3.67/1.01      | v2_struct_0(X0)
% 3.67/1.01      | ~ v4_orders_2(X0)
% 3.67/1.01      | ~ v7_waybel_0(X0) ),
% 3.67/1.01      inference(renaming,[status(thm)],[c_943]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5313,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,X0,X1) != iProver_top
% 3.67/1.01      | l1_waybel_0(X0,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r2_hidden(X1,k10_yellow_6(sK5,sK2(sK5,X0,X1))) = iProver_top
% 3.67/1.01      | v2_struct_0(X0) = iProver_top
% 3.67/1.01      | v4_orders_2(X0) != iProver_top
% 3.67/1.01      | v7_waybel_0(X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9675,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6)) != iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | m1_subset_1(sK4(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 3.67/1.01      | r2_hidden(sK4(sK5,sK6),k1_xboole_0) = iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_9663,c_5313]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5416,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6))
% 3.67/1.01      | ~ l1_waybel_0(sK6,sK5)
% 3.67/1.01      | ~ v1_compts_1(sK5)
% 3.67/1.01      | v2_struct_0(sK6)
% 3.67/1.01      | ~ v4_orders_2(sK6)
% 3.67/1.01      | ~ v7_waybel_0(sK6) ),
% 3.67/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5417,plain,
% 3.67/1.01      ( r3_waybel_9(sK5,sK6,sK4(sK5,sK6)) = iProver_top
% 3.67/1.01      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.67/1.01      | v1_compts_1(sK5) != iProver_top
% 3.67/1.01      | v2_struct_0(sK6) = iProver_top
% 3.67/1.01      | v4_orders_2(sK6) != iProver_top
% 3.67/1.01      | v7_waybel_0(sK6) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_5416]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9857,plain,
% 3.67/1.01      ( r2_hidden(sK4(sK5,sK6),k1_xboole_0) = iProver_top ),
% 3.67/1.01      inference(global_propositional_subsumption,
% 3.67/1.01                [status(thm)],
% 3.67/1.01                [c_9675,c_50,c_51,c_52,c_53,c_833,c_847,c_861,c_875,c_5406,
% 3.67/1.01                 c_5417,c_5637,c_8927]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_8,plain,
% 3.67/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.67/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_5329,plain,
% 3.67/1.01      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.67/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_9862,plain,
% 3.67/1.01      ( r1_tarski(k1_xboole_0,sK4(sK5,sK6)) != iProver_top ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_9857,c_5329]) ).
% 3.67/1.01  
% 3.67/1.01  cnf(c_10799,plain,
% 3.67/1.01      ( $false ),
% 3.67/1.01      inference(superposition,[status(thm)],[c_5331,c_9862]) ).
% 3.67/1.01  
% 3.67/1.01  
% 3.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.01  
% 3.67/1.01  ------                               Statistics
% 3.67/1.01  
% 3.67/1.01  ------ General
% 3.67/1.01  
% 3.67/1.01  abstr_ref_over_cycles:                  0
% 3.67/1.01  abstr_ref_under_cycles:                 0
% 3.67/1.01  gc_basic_clause_elim:                   0
% 3.67/1.01  forced_gc_time:                         0
% 3.67/1.01  parsing_time:                           0.019
% 3.67/1.01  unif_index_cands_time:                  0.
% 3.67/1.01  unif_index_add_time:                    0.
% 3.67/1.01  orderings_time:                         0.
% 3.67/1.01  out_proof_time:                         0.022
% 3.67/1.01  total_time:                             0.465
% 3.67/1.01  num_of_symbols:                         59
% 3.67/1.01  num_of_terms:                           6558
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing
% 3.67/1.01  
% 3.67/1.01  num_of_splits:                          0
% 3.67/1.01  num_of_split_atoms:                     0
% 3.67/1.01  num_of_reused_defs:                     0
% 3.67/1.01  num_eq_ax_congr_red:                    41
% 3.67/1.01  num_of_sem_filtered_clauses:            1
% 3.67/1.01  num_of_subtypes:                        0
% 3.67/1.01  monotx_restored_types:                  0
% 3.67/1.01  sat_num_of_epr_types:                   0
% 3.67/1.01  sat_num_of_non_cyclic_types:            0
% 3.67/1.01  sat_guarded_non_collapsed_types:        0
% 3.67/1.01  num_pure_diseq_elim:                    0
% 3.67/1.01  simp_replaced_by:                       0
% 3.67/1.01  res_preprocessed:                       183
% 3.67/1.01  prep_upred:                             0
% 3.67/1.01  prep_unflattend:                        78
% 3.67/1.01  smt_new_axioms:                         0
% 3.67/1.01  pred_elim_cands:                        11
% 3.67/1.01  pred_elim:                              5
% 3.67/1.01  pred_elim_cl:                           6
% 3.67/1.01  pred_elim_cycles:                       9
% 3.67/1.01  merged_defs:                            0
% 3.67/1.01  merged_defs_ncl:                        0
% 3.67/1.01  bin_hyper_res:                          0
% 3.67/1.01  prep_cycles:                            4
% 3.67/1.01  pred_elim_time:                         0.084
% 3.67/1.01  splitting_time:                         0.
% 3.67/1.01  sem_filter_time:                        0.
% 3.67/1.01  monotx_time:                            0.001
% 3.67/1.01  subtype_inf_time:                       0.
% 3.67/1.01  
% 3.67/1.01  ------ Problem properties
% 3.67/1.01  
% 3.67/1.01  clauses:                                34
% 3.67/1.01  conjectures:                            6
% 3.67/1.01  epr:                                    15
% 3.67/1.01  horn:                                   15
% 3.67/1.01  ground:                                 9
% 3.67/1.01  unary:                                  3
% 3.67/1.01  binary:                                 11
% 3.67/1.01  lits:                                   138
% 3.67/1.01  lits_eq:                                3
% 3.67/1.01  fd_pure:                                0
% 3.67/1.01  fd_pseudo:                              0
% 3.67/1.01  fd_cond:                                0
% 3.67/1.01  fd_pseudo_cond:                         1
% 3.67/1.01  ac_symbols:                             0
% 3.67/1.01  
% 3.67/1.01  ------ Propositional Solver
% 3.67/1.01  
% 3.67/1.01  prop_solver_calls:                      29
% 3.67/1.01  prop_fast_solver_calls:                 3319
% 3.67/1.01  smt_solver_calls:                       0
% 3.67/1.01  smt_fast_solver_calls:                  0
% 3.67/1.01  prop_num_of_clauses:                    3305
% 3.67/1.01  prop_preprocess_simplified:             10950
% 3.67/1.01  prop_fo_subsumed:                       153
% 3.67/1.01  prop_solver_time:                       0.
% 3.67/1.01  smt_solver_time:                        0.
% 3.67/1.01  smt_fast_solver_time:                   0.
% 3.67/1.01  prop_fast_solver_time:                  0.
% 3.67/1.01  prop_unsat_core_time:                   0.
% 3.67/1.01  
% 3.67/1.01  ------ QBF
% 3.67/1.01  
% 3.67/1.01  qbf_q_res:                              0
% 3.67/1.01  qbf_num_tautologies:                    0
% 3.67/1.01  qbf_prep_cycles:                        0
% 3.67/1.01  
% 3.67/1.01  ------ BMC1
% 3.67/1.01  
% 3.67/1.01  bmc1_current_bound:                     -1
% 3.67/1.01  bmc1_last_solved_bound:                 -1
% 3.67/1.01  bmc1_unsat_core_size:                   -1
% 3.67/1.01  bmc1_unsat_core_parents_size:           -1
% 3.67/1.01  bmc1_merge_next_fun:                    0
% 3.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.67/1.01  
% 3.67/1.01  ------ Instantiation
% 3.67/1.01  
% 3.67/1.01  inst_num_of_clauses:                    966
% 3.67/1.01  inst_num_in_passive:                    511
% 3.67/1.01  inst_num_in_active:                     395
% 3.67/1.01  inst_num_in_unprocessed:                60
% 3.67/1.01  inst_num_of_loops:                      540
% 3.67/1.01  inst_num_of_learning_restarts:          0
% 3.67/1.01  inst_num_moves_active_passive:          141
% 3.67/1.01  inst_lit_activity:                      0
% 3.67/1.01  inst_lit_activity_moves:                0
% 3.67/1.01  inst_num_tautologies:                   0
% 3.67/1.01  inst_num_prop_implied:                  0
% 3.67/1.01  inst_num_existing_simplified:           0
% 3.67/1.01  inst_num_eq_res_simplified:             0
% 3.67/1.01  inst_num_child_elim:                    0
% 3.67/1.01  inst_num_of_dismatching_blockings:      87
% 3.67/1.01  inst_num_of_non_proper_insts:           786
% 3.67/1.01  inst_num_of_duplicates:                 0
% 3.67/1.01  inst_inst_num_from_inst_to_res:         0
% 3.67/1.01  inst_dismatching_checking_time:         0.
% 3.67/1.01  
% 3.67/1.01  ------ Resolution
% 3.67/1.01  
% 3.67/1.01  res_num_of_clauses:                     0
% 3.67/1.01  res_num_in_passive:                     0
% 3.67/1.01  res_num_in_active:                      0
% 3.67/1.01  res_num_of_loops:                       187
% 3.67/1.01  res_forward_subset_subsumed:            25
% 3.67/1.01  res_backward_subset_subsumed:           0
% 3.67/1.01  res_forward_subsumed:                   0
% 3.67/1.01  res_backward_subsumed:                  0
% 3.67/1.01  res_forward_subsumption_resolution:     0
% 3.67/1.01  res_backward_subsumption_resolution:    4
% 3.67/1.01  res_clause_to_clause_subsumption:       825
% 3.67/1.01  res_orphan_elimination:                 0
% 3.67/1.01  res_tautology_del:                      59
% 3.67/1.01  res_num_eq_res_simplified:              0
% 3.67/1.01  res_num_sel_changes:                    0
% 3.67/1.01  res_moves_from_active_to_pass:          0
% 3.67/1.01  
% 3.67/1.01  ------ Superposition
% 3.67/1.01  
% 3.67/1.01  sup_time_total:                         0.
% 3.67/1.01  sup_time_generating:                    0.
% 3.67/1.01  sup_time_sim_full:                      0.
% 3.67/1.01  sup_time_sim_immed:                     0.
% 3.67/1.01  
% 3.67/1.01  sup_num_of_clauses:                     104
% 3.67/1.01  sup_num_in_active:                      69
% 3.67/1.01  sup_num_in_passive:                     35
% 3.67/1.01  sup_num_of_loops:                       106
% 3.67/1.01  sup_fw_superposition:                   73
% 3.67/1.01  sup_bw_superposition:                   92
% 3.67/1.01  sup_immediate_simplified:               20
% 3.67/1.01  sup_given_eliminated:                   0
% 3.67/1.01  comparisons_done:                       0
% 3.67/1.01  comparisons_avoided:                    1
% 3.67/1.01  
% 3.67/1.01  ------ Simplifications
% 3.67/1.02  
% 3.67/1.02  
% 3.67/1.02  sim_fw_subset_subsumed:                 6
% 3.67/1.02  sim_bw_subset_subsumed:                 7
% 3.67/1.02  sim_fw_subsumed:                        12
% 3.67/1.02  sim_bw_subsumed:                        33
% 3.67/1.02  sim_fw_subsumption_res:                 0
% 3.67/1.02  sim_bw_subsumption_res:                 0
% 3.67/1.02  sim_tautology_del:                      12
% 3.67/1.02  sim_eq_tautology_del:                   6
% 3.67/1.02  sim_eq_res_simp:                        0
% 3.67/1.02  sim_fw_demodulated:                     0
% 3.67/1.02  sim_bw_demodulated:                     0
% 3.67/1.02  sim_light_normalised:                   4
% 3.67/1.02  sim_joinable_taut:                      0
% 3.67/1.02  sim_joinable_simp:                      0
% 3.67/1.02  sim_ac_normalised:                      0
% 3.67/1.02  sim_smt_subsumption:                    0
% 3.67/1.02  
%------------------------------------------------------------------------------
