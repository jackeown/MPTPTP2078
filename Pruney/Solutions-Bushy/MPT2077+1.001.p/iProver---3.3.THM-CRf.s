%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_70)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK6(X3),X0)
        & m2_yellow_6(sK6(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
            | ~ m2_yellow_6(X2,X0,sK5) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
                ( ~ v3_yellow_6(X2,sK4)
                | ~ m2_yellow_6(X2,sK4,X1) )
            & l1_waybel_0(X1,sK4)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK4) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK4)
                & m2_yellow_6(X4,sK4,X3) )
            | ~ l1_waybel_0(X3,sK4)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK4)
            | ~ m2_yellow_6(X2,sK4,sK5) )
        & l1_waybel_0(sK5,sK4)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) )
      | ~ v1_compts_1(sK4) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK6(X3),sK4)
            & m2_yellow_6(sK6(X3),sK4,X3) )
          | ~ l1_waybel_0(X3,sK4)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK4) )
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).

fof(f86,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f44])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ! [X3] :
      ( m2_yellow_6(sK6(X3),sK4,X3)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK3(X0,X3))
        & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
            ( ~ r3_waybel_9(X0,sK2(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK2(X0),X0)
        & v7_waybel_0(sK2(X0))
        & v4_orders_2(sK2(X0))
        & ~ v2_struct_0(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK2(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK2(X0),X0)
            & v7_waybel_0(sK2(X0))
            & v4_orders_2(sK2(X0))
            & ~ v2_struct_0(sK2(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK3(X0,X3))
                & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).

fof(f79,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f42])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f83,f60])).

fof(f76,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
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
    inference(definition_unfolding,[],[f58,f60])).

fof(f88,plain,(
    ! [X3] :
      ( v3_yellow_6(sK6(X3),sK4)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k10_yellow_6(X0,X1) = o_0_0_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f93,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK4)
      | ~ m2_yellow_6(X2,sK4,sK5)
      | ~ v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,
    ( ~ v2_struct_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,
    ( v4_orders_2(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,
    ( v7_waybel_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK3(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK3(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_437,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_3])).

cnf(c_438,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1340,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_438,c_32])).

cnf(c_1341,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1340])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1343,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_34])).

cnf(c_1344,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1343])).

cnf(c_14,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1035,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_1036,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1035])).

cnf(c_1040,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1036,c_34,c_32])).

cnf(c_1041,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1040])).

cnf(c_29950,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(sK4,X0,X1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1344,c_1041])).

cnf(c_5127,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | m2_yellow_6(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_5125,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_9499,plain,
    ( ~ m2_yellow_6(X0,X1,k1_zfmisc_1(X2))
    | m2_yellow_6(X3,X4,k1_zfmisc_1(X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_5127,c_5125])).

cnf(c_31,negated_conjecture,
    ( m2_yellow_6(sK6(X0),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23222,plain,
    ( m2_yellow_6(X0,X1,k1_zfmisc_1(X2))
    | ~ l1_waybel_0(k1_zfmisc_1(X3),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(k1_zfmisc_1(X3))
    | ~ v4_orders_2(k1_zfmisc_1(X3))
    | ~ v7_waybel_0(k1_zfmisc_1(X3))
    | X2 != X3
    | X0 != sK6(k1_zfmisc_1(X3))
    | X1 != sK4 ),
    inference(resolution,[status(thm)],[c_9499,c_31])).

cnf(c_16,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1000,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_1001,plain,
    ( l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1000])).

cnf(c_1003,plain,
    ( l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1001,c_34,c_32])).

cnf(c_5772,plain,
    ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_9,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5789,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5788,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6127,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_5788])).

cnf(c_2,plain,
    ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1166,plain,
    ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_33])).

cnf(c_1167,plain,
    ( m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1166])).

cnf(c_1171,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1167,c_34,c_32])).

cnf(c_1172,plain,
    ( m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1171])).

cnf(c_5766,plain,
    ( m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5786,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6767,plain,
    ( r2_hidden(X0,k10_yellow_6(sK4,X1)) != iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5766,c_5786])).

cnf(c_6997,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_xboole_0(k10_yellow_6(sK4,X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6127,c_6767])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5785,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12181,plain,
    ( k10_yellow_6(sK4,X0) = o_0_0_xboole_0
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6997,c_5785])).

cnf(c_12199,plain,
    ( k10_yellow_6(sK4,sK2(sK4)) = o_0_0_xboole_0
    | v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5772,c_12181])).

cnf(c_19,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_958,plain,
    ( v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_959,plain,
    ( v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_961,plain,
    ( ~ v2_struct_0(sK2(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_34,c_32])).

cnf(c_962,plain,
    ( v1_compts_1(sK4)
    | ~ v2_struct_0(sK2(sK4)) ),
    inference(renaming,[status(thm)],[c_961])).

cnf(c_963,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_18,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK2(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_972,plain,
    ( v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_973,plain,
    ( v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v4_orders_2(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_975,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_973,c_34,c_33,c_32,c_70])).

cnf(c_977,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v4_orders_2(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_17,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_986,plain,
    ( v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_987,plain,
    ( v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v7_waybel_0(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_986])).

cnf(c_73,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_989,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_34,c_33,c_32,c_73])).

cnf(c_991,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v7_waybel_0(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_1005,plain,
    ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1003])).

cnf(c_5117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5152,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_5117])).

cnf(c_6166,plain,
    ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_6167,plain,
    ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6166])).

cnf(c_4,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_521,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_3])).

cnf(c_522,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_1262,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_522,c_32])).

cnf(c_1263,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X0,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1262])).

cnf(c_1265,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1263,c_34])).

cnf(c_1266,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X0,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1265])).

cnf(c_6286,plain,
    ( ~ m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4))
    | l1_waybel_0(sK6(sK2(sK4)),sK4)
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_6287,plain,
    ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6286])).

cnf(c_6398,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4)))
    | ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_6399,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4))) = iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6398])).

cnf(c_5,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_493,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_3])).

cnf(c_494,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_1288,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_32])).

cnf(c_1289,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1288])).

cnf(c_1291,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1289,c_34])).

cnf(c_1292,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1291])).

cnf(c_6029,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0)) ),
    inference(resolution,[status(thm)],[c_1292,c_31])).

cnf(c_6045,plain,
    ( v1_compts_1(sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v7_waybel_0(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(resolution,[status(thm)],[c_6029,c_1003])).

cnf(c_6555,plain,
    ( v7_waybel_0(sK6(sK2(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6045,c_34,c_33,c_32,c_73,c_962,c_973])).

cnf(c_6556,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK6(sK2(sK4))) ),
    inference(renaming,[status(thm)],[c_6555])).

cnf(c_6557,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6556])).

cnf(c_6,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_465,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_3])).

cnf(c_466,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_1314,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_466,c_32])).

cnf(c_1315,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1314])).

cnf(c_1317,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1315,c_34])).

cnf(c_1318,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1317])).

cnf(c_6159,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1318,c_31])).

cnf(c_6234,plain,
    ( v1_compts_1(sK4)
    | v2_struct_0(sK2(sK4))
    | v4_orders_2(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(resolution,[status(thm)],[c_6159,c_1003])).

cnf(c_6667,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK6(sK2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6234,c_34,c_33,c_32,c_67,c_70,c_73])).

cnf(c_6669,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6667])).

cnf(c_8124,plain,
    ( ~ m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4)))
    | l1_waybel_0(sK6(sK6(sK2(sK4))),sK4)
    | ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | v2_struct_0(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_8125,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4))) != iProver_top
    | l1_waybel_0(sK6(sK6(sK2(sK4))),sK4) = iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8124])).

cnf(c_8123,plain,
    ( ~ m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4)))
    | ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | v2_struct_0(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | v7_waybel_0(sK6(sK6(sK2(sK4))))
    | ~ v7_waybel_0(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_8127,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4))) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK6(sK2(sK4)))) = iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8123])).

cnf(c_8122,plain,
    ( ~ m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4)))
    | ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | v2_struct_0(sK6(sK2(sK4)))
    | v4_orders_2(sK6(sK6(sK2(sK4))))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_8129,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4))) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK6(sK2(sK4)))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8122])).

cnf(c_12,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X3,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1101,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X3,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_1102,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X2,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_1104,plain,
    ( v2_struct_0(X2)
    | ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X2,sK4)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_34,c_32])).

cnf(c_1105,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X2,sK4)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_7389,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ r3_waybel_9(sK4,sK6(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1105,c_31])).

cnf(c_10,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1133,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_1134,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1133])).

cnf(c_1138,plain,
    ( v2_struct_0(X0)
    | r3_waybel_9(sK4,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1134,c_34,c_32])).

cnf(c_1139,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1138])).

cnf(c_6439,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,k10_yellow_6(sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1139,c_11])).

cnf(c_7187,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0)))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,X0)),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_6439,c_9])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5787,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6766,plain,
    ( r2_hidden(X0,k10_yellow_6(sK4,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5766,c_5787])).

cnf(c_6875,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,X0)),u1_struct_0(sK4)) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_xboole_0(k10_yellow_6(sK4,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6127,c_6766])).

cnf(c_6876,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,X0)),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6875])).

cnf(c_5767,plain,
    ( r3_waybel_9(sK4,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_6992,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0))) = iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,X0)),u1_struct_0(sK4)) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_xboole_0(k10_yellow_6(sK4,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6127,c_5767])).

cnf(c_6993,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0)))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,X0)),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6992])).

cnf(c_7190,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0)))
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7187,c_6876,c_6993])).

cnf(c_7411,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(X0))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(X0))),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v1_xboole_0(k10_yellow_6(sK4,sK6(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0)) ),
    inference(resolution,[status(thm)],[c_7389,c_7190])).

cnf(c_1654,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X1 != X0
    | sK6(X0) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1344])).

cnf(c_1655,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1654])).

cnf(c_1678,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X1 != X0
    | sK6(X0) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1318])).

cnf(c_1679,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1678])).

cnf(c_1702,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X2)
    | X1 != X0
    | sK6(X0) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1292])).

cnf(c_1703,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0)) ),
    inference(unflattening,[status(thm)],[c_1702])).

cnf(c_1726,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X2,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X1 != X0
    | sK6(X0) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1266])).

cnf(c_1727,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1726])).

cnf(c_1,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v3_yellow_6(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(X1,X0) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_30,negated_conjecture,
    ( ~ l1_waybel_0(X0,sK4)
    | v3_yellow_6(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_619,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK4)
    | v1_compts_1(sK4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | k10_yellow_6(X1,X0) != o_0_0_xboole_0
    | sK6(X2) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_620,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_624,plain,
    ( v2_struct_0(sK6(X0))
    | v2_struct_0(X0)
    | v1_compts_1(sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_34,c_33,c_32])).

cnf(c_625,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_624])).

cnf(c_1909,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1655,c_625])).

cnf(c_1920,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1679,c_1909])).

cnf(c_1931,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1703,c_1920])).

cnf(c_1937,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,sK6(X0)) != o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1727,c_1931])).

cnf(c_5118,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6047,plain,
    ( k10_yellow_6(sK4,sK6(X0)) != X1
    | k10_yellow_6(sK4,sK6(X0)) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_5118])).

cnf(c_6175,plain,
    ( k10_yellow_6(sK4,sK6(X0)) != k10_yellow_6(sK4,sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k10_yellow_6(sK4,sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_6047])).

cnf(c_6176,plain,
    ( k10_yellow_6(sK4,sK6(X0)) = k10_yellow_6(sK4,sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_5117])).

cnf(c_6604,plain,
    ( ~ v1_xboole_0(k10_yellow_6(sK4,sK6(X0)))
    | o_0_0_xboole_0 = k10_yellow_6(sK4,sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_8288,plain,
    ( ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(X0))),u1_struct_0(sK4))
    | r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(X0))))
    | v1_compts_1(sK4)
    | ~ v4_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7411,c_1655,c_1679,c_1703,c_1727,c_1937,c_6175,c_6176,c_6604])).

cnf(c_8289,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(X0))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(X0))),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_8288])).

cnf(c_8328,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(sK6(X0)))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(X0)))),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0)) ),
    inference(resolution,[status(thm)],[c_8289,c_7389])).

cnf(c_8649,plain,
    ( ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v1_compts_1(sK4)
    | r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(sK6(X0)))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(X0)))),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8328,c_1655,c_1679,c_1703,c_1727])).

cnf(c_8650,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,sK6(sK6(X0)))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(X0)))),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_8649])).

cnf(c_15,plain,
    ( ~ r3_waybel_9(X0,sK2(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1014,plain,
    ( ~ r3_waybel_9(X0,sK2(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_1015,plain,
    ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1014])).

cnf(c_1019,plain,
    ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_34,c_32])).

cnf(c_8687,plain,
    ( ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(resolution,[status(thm)],[c_8650,c_1019])).

cnf(c_76,plain,
    ( l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_8698,plain,
    ( v1_compts_1(sK4)
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8687,c_34,c_33,c_32,c_67,c_70,c_73,c_76])).

cnf(c_8699,plain,
    ( ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_8698])).

cnf(c_8700,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8699])).

cnf(c_9383,plain,
    ( m1_subset_1(k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_waybel_0(sK6(sK6(sK2(sK4))),sK4)
    | v2_struct_0(sK6(sK6(sK2(sK4))))
    | ~ v4_orders_2(sK6(sK6(sK2(sK4))))
    | ~ v7_waybel_0(sK6(sK6(sK2(sK4)))) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_9387,plain,
    ( m1_subset_1(k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_waybel_0(sK6(sK6(sK2(sK4))),sK4) != iProver_top
    | v2_struct_0(sK6(sK6(sK2(sK4)))) = iProver_top
    | v4_orders_2(sK6(sK6(sK2(sK4)))) != iProver_top
    | v7_waybel_0(sK6(sK6(sK2(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9383])).

cnf(c_6626,plain,
    ( sK6(X0) = sK6(X0) ),
    inference(instantiation,[status(thm)],[c_5117])).

cnf(c_9431,plain,
    ( sK6(sK6(sK2(sK4))) = sK6(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_6626])).

cnf(c_10958,plain,
    ( ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK6(sK2(sK4)))
    | k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_10959,plain,
    ( k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) != o_0_0_xboole_0
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10958])).

cnf(c_11589,plain,
    ( k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) != k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))
    | k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) ),
    inference(instantiation,[status(thm)],[c_6175])).

cnf(c_11441,plain,
    ( ~ m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(sK6(sK2(sK4))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_14074,plain,
    ( ~ m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4)))
    | ~ l1_waybel_0(sK6(sK2(sK4)),sK4)
    | ~ v2_struct_0(sK6(sK6(sK2(sK4))))
    | v2_struct_0(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_11441])).

cnf(c_14075,plain,
    ( m2_yellow_6(sK6(sK6(sK2(sK4))),sK4,sK6(sK2(sK4))) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v2_struct_0(sK6(sK6(sK2(sK4)))) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14074])).

cnf(c_14457,plain,
    ( ~ v1_xboole_0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))))
    | o_0_0_xboole_0 = k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) ),
    inference(instantiation,[status(thm)],[c_6604])).

cnf(c_14459,plain,
    ( o_0_0_xboole_0 = k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))
    | v1_xboole_0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14457])).

cnf(c_5119,plain,
    ( X0 != X1
    | X2 != X3
    | k10_yellow_6(X0,X2) = k10_yellow_6(X1,X3) ),
    theory(equality)).

cnf(c_7832,plain,
    ( X0 != sK6(X1)
    | X2 != sK4
    | k10_yellow_6(X2,X0) = k10_yellow_6(sK4,sK6(X1)) ),
    inference(instantiation,[status(thm)],[c_5119])).

cnf(c_10915,plain,
    ( X0 != sK4
    | k10_yellow_6(X0,sK6(X1)) = k10_yellow_6(sK4,sK6(X1))
    | sK6(X1) != sK6(X1) ),
    inference(instantiation,[status(thm)],[c_7832])).

cnf(c_15051,plain,
    ( X0 != sK4
    | k10_yellow_6(X0,sK6(sK6(sK2(sK4)))) = k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))
    | sK6(sK6(sK2(sK4))) != sK6(sK6(sK2(sK4))) ),
    inference(instantiation,[status(thm)],[c_10915])).

cnf(c_15054,plain,
    ( k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))) = k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))
    | sK6(sK6(sK2(sK4))) != sK6(sK6(sK2(sK4)))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_15051])).

cnf(c_5996,plain,
    ( r2_hidden(sK0(X0),X0)
    | ~ m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7683,plain,
    ( r2_hidden(sK0(k10_yellow_6(sK4,sK6(X0))),k10_yellow_6(sK4,sK6(X0)))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(X0))),k10_yellow_6(sK4,sK6(X0)))
    | v1_xboole_0(k10_yellow_6(sK4,sK6(X0))) ),
    inference(instantiation,[status(thm)],[c_5996])).

cnf(c_15776,plain,
    ( r2_hidden(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))))
    | ~ m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))))
    | v1_xboole_0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) ),
    inference(instantiation,[status(thm)],[c_7683])).

cnf(c_15780,plain,
    ( r2_hidden(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) = iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) != iProver_top
    | v1_xboole_0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15776])).

cnf(c_5780,plain,
    ( m2_yellow_6(sK6(X0),sK4,X0) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5762,plain,
    ( m2_yellow_6(X0,sK4,X1) != iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_6295,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5780,c_5762])).

cnf(c_8415,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5772,c_6295])).

cnf(c_16773,plain,
    ( v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8415,c_963,c_977,c_991])).

cnf(c_16774,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16773])).

cnf(c_9984,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_12267,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(X0),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9984])).

cnf(c_18032,plain,
    ( ~ r2_hidden(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))))
    | ~ m1_subset_1(k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12267])).

cnf(c_18033,plain,
    ( r2_hidden(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,sK6(sK6(sK2(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18032])).

cnf(c_9185,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,sK6(X0))),k10_yellow_6(sK4,sK6(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_23478,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) ),
    inference(instantiation,[status(thm)],[c_9185])).

cnf(c_23479,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))),k10_yellow_6(sK4,sK6(sK6(sK2(sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23478])).

cnf(c_23515,plain,
    ( v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12199,c_963,c_977,c_991,c_1005,c_5152,c_6167,c_6287,c_6399,c_6557,c_6669,c_8125,c_8127,c_8129,c_8700,c_9387,c_9431,c_10959,c_11589,c_14075,c_14459,c_15054,c_15780,c_16774,c_18033,c_23479])).

cnf(c_23517,plain,
    ( v1_compts_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23515])).

cnf(c_23526,plain,
    ( v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23222,c_23517])).

cnf(c_0,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v3_yellow_6(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(X1,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_25,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ v3_yellow_6(X0,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_586,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | k10_yellow_6(X2,X1) = o_0_0_xboole_0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_587,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,X0) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( v2_struct_0(X0)
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m2_yellow_6(X0,sK4,sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_34,c_33,c_32])).

cnf(c_592,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,X0) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_23540,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,X0) = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_23526,c_592])).

cnf(c_5128,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_23826,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_23540,c_5128])).

cnf(c_8,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24916,plain,
    ( v1_xboole_0(k10_yellow_6(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ m2_yellow_6(X0,sK4,sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23826,c_8])).

cnf(c_24917,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_24916])).

cnf(c_24952,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | v1_xboole_0(k10_yellow_6(sK4,sK1(sK4,sK5,X0)))
    | v2_struct_0(sK1(sK4,sK5,X0))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_24917,c_1041])).

cnf(c_29,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_28,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_24957,plain,
    ( ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | v2_struct_0(sK1(sK4,sK5,X0))
    | v1_xboole_0(k10_yellow_6(sK4,sK1(sK4,sK5,X0)))
    | ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | ~ v4_orders_2(sK1(sK4,sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24952,c_29,c_28,c_27,c_26,c_23517])).

cnf(c_24958,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | v1_xboole_0(k10_yellow_6(sK4,sK1(sK4,sK5,X0)))
    | v2_struct_0(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0)) ),
    inference(renaming,[status(thm)],[c_24957])).

cnf(c_5121,plain,
    ( ~ v7_waybel_0(X0)
    | v7_waybel_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6685,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_5121,c_24])).

cnf(c_25140,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | v2_struct_0(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(k10_yellow_6(sK4,sK1(sK4,sK5,X0)))
    | v7_waybel_0(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_24958,c_6685])).

cnf(c_5130,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_8429,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,o_0_0_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_5130,c_24])).

cnf(c_5790,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6211,plain,
    ( r2_hidden(X0,sK0(k1_zfmisc_1(X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_5786])).

cnf(c_6403,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6127,c_6211])).

cnf(c_7151,plain,
    ( sK0(k1_zfmisc_1(X0)) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6403,c_5785])).

cnf(c_7246,plain,
    ( sK0(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_5790,c_7151])).

cnf(c_7339,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7246,c_6211])).

cnf(c_7346,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7339])).

cnf(c_10302,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8429,c_8,c_7346])).

cnf(c_13,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1068,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_1069,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1068])).

cnf(c_1073,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK4,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1069,c_34,c_32])).

cnf(c_1074,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1073])).

cnf(c_28762,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_xboole_0(k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_10302,c_1074])).

cnf(c_28804,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK1(sK4,sK5,X0))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_28762,c_24958])).

cnf(c_29544,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK1(sK4,sK5,X0),sK4)
    | v2_struct_0(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25140,c_29,c_28,c_27,c_26,c_23517,c_28804])).

cnf(c_7292,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | l1_waybel_0(sK1(sK4,X0,X1),sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1041,c_1266])).

cnf(c_29578,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK1(sK4,sK5,X0))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_29544,c_7292])).

cnf(c_29907,plain,
    ( ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | v2_struct_0(sK1(sK4,sK5,X0))
    | ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v4_orders_2(sK1(sK4,sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29578,c_29,c_28,c_27,c_26,c_23517])).

cnf(c_29908,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0)) ),
    inference(renaming,[status(thm)],[c_29907])).

cnf(c_30281,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_29950,c_29908])).

cnf(c_30286,plain,
    ( ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v4_orders_2(sK1(sK4,sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30281,c_29,c_28,c_27,c_26,c_23517])).

cnf(c_30287,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v4_orders_2(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0)) ),
    inference(renaming,[status(thm)],[c_30286])).

cnf(c_7291,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK1(sK4,X0,X1))
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1041,c_1318])).

cnf(c_30312,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_30287,c_7291])).

cnf(c_31119,plain,
    ( ~ v7_waybel_0(sK1(sK4,sK5,X0))
    | ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30312,c_29,c_28,c_27,c_26,c_23517])).

cnf(c_31120,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v7_waybel_0(sK1(sK4,sK5,X0)) ),
    inference(renaming,[status(thm)],[c_31119])).

cnf(c_7290,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK1(sK4,X0,X1)) ),
    inference(resolution,[status(thm)],[c_1041,c_1292])).

cnf(c_31141,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_31120,c_7290])).

cnf(c_31147,plain,
    ( ~ r3_waybel_9(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31141,c_29,c_28,c_27,c_26,c_23517])).

cnf(c_20,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_928,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_929,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_933,plain,
    ( v2_struct_0(X0)
    | r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_34,c_32])).

cnf(c_934,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_933])).

cnf(c_23539,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_23526,c_934])).

cnf(c_31408,plain,
    ( ~ m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(resolution,[status(thm)],[c_31147,c_23539])).

cnf(c_21,plain,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_898,plain,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_899,plain,
    ( m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_903,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_899,c_34,c_32])).

cnf(c_904,plain,
    ( m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_903])).

cnf(c_5905,plain,
    ( m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_904])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31408,c_23517,c_5905,c_26,c_27,c_28,c_29])).


%------------------------------------------------------------------------------
