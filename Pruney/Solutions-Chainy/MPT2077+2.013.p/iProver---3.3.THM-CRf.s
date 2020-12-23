%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:27 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_63)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
                & m2_yellow_6(sK3(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f46])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK3(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK8(X3),X0)
        & m2_yellow_6(sK8(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
            | ~ m2_yellow_6(X2,X0,sK7) )
        & l1_waybel_0(sK7,X0)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                ( ~ v3_yellow_6(X2,sK6)
                | ~ m2_yellow_6(X2,sK6,X1) )
            & l1_waybel_0(X1,sK6)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK6) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK6)
                & m2_yellow_6(X4,sK6,X3) )
            | ~ l1_waybel_0(X3,sK6)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK6) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK6)
            | ~ m2_yellow_6(X2,sK6,sK7) )
        & l1_waybel_0(sK7,sK6)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) )
      | ~ v1_compts_1(sK6) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK8(X3),sK6)
            & m2_yellow_6(sK8(X3),sK6,X3) )
          | ~ l1_waybel_0(X3,sK6)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK6) )
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f55,f58,f57,f56])).

fof(f91,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f51,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK4(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK4(X0),X0)
            & v7_waybel_0(sK4(X0))
            & v4_orders_2(sK4(X0))
            & ~ v2_struct_0(sK4(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f49,f51,f50])).

fof(f84,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK5(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f80,plain,(
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

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f75,plain,(
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

fof(f74,plain,(
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

fof(f73,plain,(
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

fof(f76,plain,(
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

fof(f85,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f93,plain,(
    ! [X3] :
      ( m2_yellow_6(sK8(X3),sK6,X3)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X3] :
      ( v3_yellow_6(sK8(X3),sK6)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK0(X0,X1,X2)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
                        & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2)) )
                      | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
                      | r2_hidden(sK0(X0,X1,X2),X2) )
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
                            & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f79,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f72,plain,(
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

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f69,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK6)
      | ~ m2_yellow_6(X2,sK6,sK7)
      | ~ v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,
    ( ~ v2_struct_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,
    ( v4_orders_2(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,
    ( v7_waybel_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1228,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_1229,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1228])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1233,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_39,c_37])).

cnf(c_1234,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1233])).

cnf(c_8003,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1234])).

cnf(c_8754,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8003])).

cnf(c_28,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1121,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_38])).

cnf(c_1122,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_1126,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1122,c_39,c_37])).

cnf(c_1127,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1126])).

cnf(c_8009,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57))
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1127])).

cnf(c_8748,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57)) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8009])).

cnf(c_29,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1503,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_1504,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1503])).

cnf(c_1508,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_39,c_37])).

cnf(c_1509,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1508])).

cnf(c_7997,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1509])).

cnf(c_8760,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6)) = iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7997])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_1294,plain,
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
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_1295,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1294])).

cnf(c_1297,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1295,c_39,c_37])).

cnf(c_1298,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1297])).

cnf(c_8001,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | r3_waybel_9(sK6,X1_57,X0_58)
    | ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1298])).

cnf(c_8756,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | r3_waybel_9(sK6,X1_57,X0_58) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8001])).

cnf(c_10723,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) != iProver_top
    | r3_waybel_9(sK6,X2_57,sK5(sK6,X1_57)) = iProver_top
    | m2_yellow_6(X0_57,sK6,X2_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X2_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X2_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X2_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8760,c_8756])).

cnf(c_11259,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
    | m2_yellow_6(X1_57,sK6,X0_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8748,c_10723])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_509,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_510,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_1836,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_510,c_37])).

cnf(c_1837,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1836])).

cnf(c_1839,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_39])).

cnf(c_1840,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1839])).

cnf(c_7989,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57)
    | v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1840])).

cnf(c_8768,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7989])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_481,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_482,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1862,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_482,c_37])).

cnf(c_1863,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1862])).

cnf(c_1865,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1863,c_39])).

cnf(c_1866,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1865])).

cnf(c_7988,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | v4_orders_2(X0_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1866])).

cnf(c_8769,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7988])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_453,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_454,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_1888,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_37])).

cnf(c_1889,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1888])).

cnf(c_1891,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1889,c_39])).

cnf(c_1892,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1891])).

cnf(c_7987,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | ~ v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1892])).

cnf(c_8770,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7987])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_537,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_538,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1810,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_538,c_37])).

cnf(c_1811,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1810])).

cnf(c_1813,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1811,c_39])).

cnf(c_1814,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1813])).

cnf(c_7990,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | l1_waybel_0(X0_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1814])).

cnf(c_8767,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7990])).

cnf(c_11273,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
    | m2_yellow_6(X1_57,sK6,X0_57) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11259,c_8768,c_8769,c_8770,c_8767])).

cnf(c_11276,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
    | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
    | m2_yellow_6(X2_57,sK6,X0_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X2_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X2_57) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X2_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_11273,c_10723])).

cnf(c_12477,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
    | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
    | m2_yellow_6(X2_57,sK6,X0_57) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11276,c_8768,c_8769,c_8770,c_8767,c_8767])).

cnf(c_12479,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK3(sK6,X0_57,X0_58)) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(sK3(sK6,X0_57,X0_58)) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(sK3(sK6,X0_57,X0_58)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8754,c_12477])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1151,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_1152,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1151])).

cnf(c_1154,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1152,c_39,c_38,c_37,c_63])).

cnf(c_1156,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1165,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_1166,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v4_orders_2(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1165])).

cnf(c_1168,plain,
    ( v4_orders_2(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_39,c_37])).

cnf(c_1169,plain,
    ( v1_compts_1(sK6)
    | v4_orders_2(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1168])).

cnf(c_1170,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v4_orders_2(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_25,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1179,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_1180,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v7_waybel_0(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1179])).

cnf(c_1182,plain,
    ( v7_waybel_0(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_39,c_37])).

cnf(c_1183,plain,
    ( v1_compts_1(sK6)
    | v7_waybel_0(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1182])).

cnf(c_1184,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v7_waybel_0(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_24,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1193,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_1194,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1193])).

cnf(c_1196,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1194,c_39,c_37])).

cnf(c_1198,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1196])).

cnf(c_8130,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7990])).

cnf(c_8131,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7989])).

cnf(c_8132,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7988])).

cnf(c_8133,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7987])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8019,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_60)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_9357,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8019])).

cnf(c_9360,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9357])).

cnf(c_36,negated_conjecture,
    ( m2_yellow_6(sK8(X0),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_8013,negated_conjecture,
    ( m2_yellow_6(sK8(X0_57),sK6,X0_57)
    | ~ l1_waybel_0(X0_57,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_9390,plain,
    ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_8013])).

cnf(c_9458,plain,
    ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) = iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9390])).

cnf(c_2443,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X2,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1814])).

cnf(c_2444,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2443])).

cnf(c_2419,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(X2)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1840])).

cnf(c_2420,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK8(X0)) ),
    inference(unflattening,[status(thm)],[c_2419])).

cnf(c_2395,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1866])).

cnf(c_2396,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2395])).

cnf(c_2371,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1892])).

cnf(c_2372,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK8(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2371])).

cnf(c_18,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( v3_yellow_6(sK8(X0),sK6)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_635,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK6)
    | v1_compts_1(sK6)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0
    | sK8(X2) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_636,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( ~ v7_waybel_0(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | ~ l1_waybel_0(X0,sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_39,c_38,c_37])).

cnf(c_641,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_640])).

cnf(c_2626,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2372,c_641])).

cnf(c_2637,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2396,c_2626])).

cnf(c_2648,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2420,c_2637])).

cnf(c_2654,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2444,c_2648])).

cnf(c_7986,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,sK8(X0_57)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2654])).

cnf(c_9540,plain,
    ( ~ l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7986])).

cnf(c_9541,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9540])).

cnf(c_9461,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | l1_waybel_0(X0_57,sK6)
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_7990])).

cnf(c_9680,plain,
    ( ~ m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
    | l1_waybel_0(sK8(sK4(sK6)),sK6)
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_9461])).

cnf(c_9681,plain,
    ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) = iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9680])).

cnf(c_8005,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6) ),
    inference(subtyping,[status(esa)],[c_1196])).

cnf(c_8752,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8005])).

cnf(c_8744,plain,
    ( m2_yellow_6(sK8(X0_57),sK6,X0_57) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8013])).

cnf(c_9621,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(sK8(X0_57)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8744,c_8768])).

cnf(c_9631,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) = iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8752,c_9621])).

cnf(c_9690,plain,
    ( v7_waybel_0(sK8(sK4(sK6))) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9631,c_1156,c_1170,c_1184])).

cnf(c_9691,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9690])).

cnf(c_9372,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK8(X0_57)) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8744,c_8770])).

cnf(c_9525,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8752,c_9372])).

cnf(c_9697,plain,
    ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9525,c_1156,c_1170,c_1184])).

cnf(c_9698,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9697])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1608,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_38])).

cnf(c_1609,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1608])).

cnf(c_1613,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_39,c_37])).

cnf(c_1614,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1613])).

cnf(c_7992,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1614])).

cnf(c_9898,plain,
    ( ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6)))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
    inference(instantiation,[status(thm)],[c_7992])).

cnf(c_9911,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9898])).

cnf(c_9913,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9911])).

cnf(c_10239,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(sK3(sK6,X0_57,X0_58)) = iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8754,c_8769])).

cnf(c_10240,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(sK3(sK6,X0_57,X0_58)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8754,c_8768])).

cnf(c_10241,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK3(sK6,X0_57,X0_58)) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8754,c_8770])).

cnf(c_9731,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(sK8(X0_57)) = iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8744,c_8769])).

cnf(c_9855,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8752,c_9731])).

cnf(c_10406,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9855,c_1156,c_1170,c_1184])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1207,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_1208,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1207])).

cnf(c_1212,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_39,c_37])).

cnf(c_8004,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0_58)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(subtyping,[status(esa)],[c_1212])).

cnf(c_10438,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8004])).

cnf(c_10444,plain,
    ( r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10438])).

cnf(c_10446,plain,
    ( r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10444])).

cnf(c_19,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1326,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_1327,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1326])).

cnf(c_1331,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_39,c_37])).

cnf(c_1332,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1331])).

cnf(c_8000,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1332])).

cnf(c_9897,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),X0_58)
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | ~ r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_8000])).

cnf(c_10425,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | ~ r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_9897])).

cnf(c_10496,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10425])).

cnf(c_10498,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10496])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1533,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_1534,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1533])).

cnf(c_1538,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_39,c_37])).

cnf(c_1539,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1538])).

cnf(c_9,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1395,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_38])).

cnf(c_1396,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1395])).

cnf(c_1400,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1396,c_39,c_37])).

cnf(c_1401,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1400])).

cnf(c_1557,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1539,c_1401])).

cnf(c_7994,plain,
    ( ~ r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58))
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1557])).

cnf(c_9891,plain,
    ( ~ r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),X0_58))
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_7994])).

cnf(c_11051,plain,
    ( ~ r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)))
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_9891])).

cnf(c_11052,plain,
    ( r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))) != iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11051])).

cnf(c_11054,plain,
    ( r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0))) != iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11052])).

cnf(c_10,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1359,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_38])).

cnf(c_1360,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1359])).

cnf(c_1364,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_39,c_37])).

cnf(c_1365,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1364])).

cnf(c_1556,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1539,c_1365])).

cnf(c_7995,plain,
    ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1556])).

cnf(c_9890,plain,
    ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),X0_58),sK6,X0_58)
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_7995])).

cnf(c_11095,plain,
    ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6))) ),
    inference(instantiation,[status(thm)],[c_9890])).

cnf(c_11096,plain,
    ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11095])).

cnf(c_11098,plain,
    ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)),sK6,sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11096])).

cnf(c_9460,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | r3_waybel_9(sK6,sK4(sK6),X0_58)
    | ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_8001])).

cnf(c_10428,plain,
    ( ~ r3_waybel_9(sK6,X0_57,sK0(sK6,sK8(sK4(sK6)),X0_58))
    | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
    | ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_9460])).

cnf(c_11168,plain,
    ( ~ r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))
    | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
    | ~ m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_10428])).

cnf(c_11169,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
    | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
    | m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11168])).

cnf(c_11171,plain,
    ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
    | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
    | m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11169])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | r2_hidden(sK0(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1641,plain,
    ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | r2_hidden(sK0(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_38])).

cnf(c_1642,plain,
    ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_1641])).

cnf(c_1646,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1642,c_39,c_37])).

cnf(c_1647,plain,
    ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(renaming,[status(thm)],[c_1646])).

cnf(c_7991,plain,
    ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58))
    | r1_waybel_0(sK6,X0_57,X0_59)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1647])).

cnf(c_9892,plain,
    ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
    | r1_waybel_0(sK6,sK8(sK4(sK6)),X0_59)
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6)))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
    inference(instantiation,[status(thm)],[c_7991])).

cnf(c_12415,plain,
    ( ~ m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
    | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)))
    | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK8(sK4(sK6)))
    | ~ v4_orders_2(sK8(sK4(sK6)))
    | ~ v7_waybel_0(sK8(sK4(sK6)))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
    inference(instantiation,[status(thm)],[c_9892])).

cnf(c_12421,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58
    | m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
    | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12415])).

cnf(c_12423,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
    | m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)),sK6,sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
    | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0))) = iProver_top
    | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
    | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v4_orders_2(sK8(sK4(sK6))) != iProver_top
    | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12421])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_8011,plain,
    ( ~ r2_hidden(X0_58,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_12538,plain,
    ( ~ r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8011])).

cnf(c_12541,plain,
    ( r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12538])).

cnf(c_12623,plain,
    ( v7_waybel_0(X1_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12479,c_1156,c_1170,c_1184,c_1198,c_8130,c_8131,c_8132,c_8133,c_9360,c_9458,c_9541,c_9681,c_9691,c_9698,c_9913,c_10239,c_10240,c_10241,c_10406,c_10446,c_10498,c_11054,c_11098,c_11171,c_12423,c_12541])).

cnf(c_12624,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_12623])).

cnf(c_8753,plain,
    ( r3_waybel_9(sK6,sK4(sK6),X0_58) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8004])).

cnf(c_12637,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK5(sK6,sK3(sK6,X0_57,X0_58)),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12624,c_8753])).

cnf(c_12724,plain,
    ( v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12637,c_1156,c_1170,c_1184,c_1198,c_9360,c_9458,c_9541,c_9681,c_9691,c_9698,c_9913,c_10406,c_10446,c_10498,c_11054,c_11098,c_11171,c_12423,c_12541])).

cnf(c_17,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ v3_yellow_6(X0,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_602,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK6)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_603,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_607,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK6)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m2_yellow_6(X0,sK6,sK7)
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_39,c_38,c_37])).

cnf(c_608,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_607])).

cnf(c_8010,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_8747,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8010])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_50,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v4_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_51,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v7_waybel_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( l1_waybel_0(sK7,sK6) = iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8086,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8010])).

cnf(c_9204,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | v4_orders_2(X0_57)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7988])).

cnf(c_9205,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9204])).

cnf(c_9209,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | v7_waybel_0(X0_57)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7989])).

cnf(c_9210,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9209])).

cnf(c_9214,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | l1_waybel_0(X0_57,sK6)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7990])).

cnf(c_9215,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9214])).

cnf(c_9318,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8747,c_49,c_50,c_51,c_52,c_8086,c_9205,c_9210,c_9215])).

cnf(c_9319,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_9318])).

cnf(c_10242,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8754,c_9319])).

cnf(c_10273,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10241,c_10242])).

cnf(c_11472,plain,
    ( v1_compts_1(sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10273,c_49,c_50,c_51,c_52])).

cnf(c_11473,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11472])).

cnf(c_11482,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8748,c_11473])).

cnf(c_9195,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_7997])).

cnf(c_9196,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9195])).

cnf(c_11655,plain,
    ( v1_compts_1(sK6) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11482,c_49,c_50,c_51,c_52,c_9196])).

cnf(c_11656,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11655])).

cnf(c_12729,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12724,c_11656])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1261,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_1262,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1261])).

cnf(c_1266,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_39,c_37])).

cnf(c_1267,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1266])).

cnf(c_8002,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1267])).

cnf(c_8755,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8002])).

cnf(c_13074,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_12729,c_8755])).

cnf(c_9198,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8009])).

cnf(c_9199,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9198])).

cnf(c_13158,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13074,c_49,c_50,c_51,c_52,c_1156,c_1170,c_1184,c_1198,c_9196,c_9199,c_9360,c_9458,c_9541,c_9681,c_9691,c_9698,c_9913,c_10406,c_10446,c_10498,c_11054,c_11098,c_11171,c_12423,c_12541])).

cnf(c_8746,plain,
    ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8011])).

cnf(c_13163,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13158,c_8746])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:33:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.76/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.99  
% 3.76/0.99  ------  iProver source info
% 3.76/0.99  
% 3.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.99  git: non_committed_changes: false
% 3.76/0.99  git: last_make_outside_of_git: false
% 3.76/0.99  
% 3.76/0.99  ------ 
% 3.76/0.99  
% 3.76/0.99  ------ Input Options
% 3.76/0.99  
% 3.76/0.99  --out_options                           all
% 3.76/0.99  --tptp_safe_out                         true
% 3.76/0.99  --problem_path                          ""
% 3.76/0.99  --include_path                          ""
% 3.76/0.99  --clausifier                            res/vclausify_rel
% 3.76/0.99  --clausifier_options                    --mode clausify
% 3.76/0.99  --stdin                                 false
% 3.76/0.99  --stats_out                             all
% 3.76/0.99  
% 3.76/0.99  ------ General Options
% 3.76/0.99  
% 3.76/0.99  --fof                                   false
% 3.76/0.99  --time_out_real                         305.
% 3.76/0.99  --time_out_virtual                      -1.
% 3.76/0.99  --symbol_type_check                     false
% 3.76/0.99  --clausify_out                          false
% 3.76/0.99  --sig_cnt_out                           false
% 3.76/0.99  --trig_cnt_out                          false
% 3.76/0.99  --trig_cnt_out_tolerance                1.
% 3.76/0.99  --trig_cnt_out_sk_spl                   false
% 3.76/0.99  --abstr_cl_out                          false
% 3.76/0.99  
% 3.76/0.99  ------ Global Options
% 3.76/0.99  
% 3.76/0.99  --schedule                              default
% 3.76/0.99  --add_important_lit                     false
% 3.76/0.99  --prop_solver_per_cl                    1000
% 3.76/0.99  --min_unsat_core                        false
% 3.76/0.99  --soft_assumptions                      false
% 3.76/0.99  --soft_lemma_size                       3
% 3.76/0.99  --prop_impl_unit_size                   0
% 3.76/0.99  --prop_impl_unit                        []
% 3.76/0.99  --share_sel_clauses                     true
% 3.76/0.99  --reset_solvers                         false
% 3.76/0.99  --bc_imp_inh                            [conj_cone]
% 3.76/0.99  --conj_cone_tolerance                   3.
% 3.76/0.99  --extra_neg_conj                        none
% 3.76/0.99  --large_theory_mode                     true
% 3.76/0.99  --prolific_symb_bound                   200
% 3.76/0.99  --lt_threshold                          2000
% 3.76/0.99  --clause_weak_htbl                      true
% 3.76/0.99  --gc_record_bc_elim                     false
% 3.76/0.99  
% 3.76/0.99  ------ Preprocessing Options
% 3.76/0.99  
% 3.76/0.99  --preprocessing_flag                    true
% 3.76/0.99  --time_out_prep_mult                    0.1
% 3.76/0.99  --splitting_mode                        input
% 3.76/0.99  --splitting_grd                         true
% 3.76/0.99  --splitting_cvd                         false
% 3.76/0.99  --splitting_cvd_svl                     false
% 3.76/0.99  --splitting_nvd                         32
% 3.76/0.99  --sub_typing                            true
% 3.76/0.99  --prep_gs_sim                           true
% 3.76/0.99  --prep_unflatten                        true
% 3.76/0.99  --prep_res_sim                          true
% 3.76/0.99  --prep_upred                            true
% 3.76/0.99  --prep_sem_filter                       exhaustive
% 3.76/0.99  --prep_sem_filter_out                   false
% 3.76/0.99  --pred_elim                             true
% 3.76/0.99  --res_sim_input                         true
% 3.76/0.99  --eq_ax_congr_red                       true
% 3.76/0.99  --pure_diseq_elim                       true
% 3.76/0.99  --brand_transform                       false
% 3.76/0.99  --non_eq_to_eq                          false
% 3.76/0.99  --prep_def_merge                        true
% 3.76/0.99  --prep_def_merge_prop_impl              false
% 3.76/0.99  --prep_def_merge_mbd                    true
% 3.76/0.99  --prep_def_merge_tr_red                 false
% 3.76/0.99  --prep_def_merge_tr_cl                  false
% 3.76/0.99  --smt_preprocessing                     true
% 3.76/0.99  --smt_ac_axioms                         fast
% 3.76/0.99  --preprocessed_out                      false
% 3.76/0.99  --preprocessed_stats                    false
% 3.76/0.99  
% 3.76/0.99  ------ Abstraction refinement Options
% 3.76/0.99  
% 3.76/0.99  --abstr_ref                             []
% 3.76/0.99  --abstr_ref_prep                        false
% 3.76/0.99  --abstr_ref_until_sat                   false
% 3.76/0.99  --abstr_ref_sig_restrict                funpre
% 3.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/0.99  --abstr_ref_under                       []
% 3.76/0.99  
% 3.76/0.99  ------ SAT Options
% 3.76/0.99  
% 3.76/0.99  --sat_mode                              false
% 3.76/0.99  --sat_fm_restart_options                ""
% 3.76/0.99  --sat_gr_def                            false
% 3.76/0.99  --sat_epr_types                         true
% 3.76/0.99  --sat_non_cyclic_types                  false
% 3.76/0.99  --sat_finite_models                     false
% 3.76/0.99  --sat_fm_lemmas                         false
% 3.76/0.99  --sat_fm_prep                           false
% 3.76/0.99  --sat_fm_uc_incr                        true
% 3.76/0.99  --sat_out_model                         small
% 3.76/0.99  --sat_out_clauses                       false
% 3.76/0.99  
% 3.76/0.99  ------ QBF Options
% 3.76/0.99  
% 3.76/0.99  --qbf_mode                              false
% 3.76/0.99  --qbf_elim_univ                         false
% 3.76/0.99  --qbf_dom_inst                          none
% 3.76/0.99  --qbf_dom_pre_inst                      false
% 3.76/0.99  --qbf_sk_in                             false
% 3.76/0.99  --qbf_pred_elim                         true
% 3.76/0.99  --qbf_split                             512
% 3.76/0.99  
% 3.76/0.99  ------ BMC1 Options
% 3.76/0.99  
% 3.76/0.99  --bmc1_incremental                      false
% 3.76/0.99  --bmc1_axioms                           reachable_all
% 3.76/0.99  --bmc1_min_bound                        0
% 3.76/0.99  --bmc1_max_bound                        -1
% 3.76/0.99  --bmc1_max_bound_default                -1
% 3.76/0.99  --bmc1_symbol_reachability              true
% 3.76/0.99  --bmc1_property_lemmas                  false
% 3.76/0.99  --bmc1_k_induction                      false
% 3.76/0.99  --bmc1_non_equiv_states                 false
% 3.76/0.99  --bmc1_deadlock                         false
% 3.76/0.99  --bmc1_ucm                              false
% 3.76/0.99  --bmc1_add_unsat_core                   none
% 3.76/0.99  --bmc1_unsat_core_children              false
% 3.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/0.99  --bmc1_out_stat                         full
% 3.76/0.99  --bmc1_ground_init                      false
% 3.76/0.99  --bmc1_pre_inst_next_state              false
% 3.76/0.99  --bmc1_pre_inst_state                   false
% 3.76/0.99  --bmc1_pre_inst_reach_state             false
% 3.76/0.99  --bmc1_out_unsat_core                   false
% 3.76/0.99  --bmc1_aig_witness_out                  false
% 3.76/0.99  --bmc1_verbose                          false
% 3.76/0.99  --bmc1_dump_clauses_tptp                false
% 3.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.76/0.99  --bmc1_dump_file                        -
% 3.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.76/0.99  --bmc1_ucm_extend_mode                  1
% 3.76/0.99  --bmc1_ucm_init_mode                    2
% 3.76/0.99  --bmc1_ucm_cone_mode                    none
% 3.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.76/0.99  --bmc1_ucm_relax_model                  4
% 3.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/0.99  --bmc1_ucm_layered_model                none
% 3.76/0.99  --bmc1_ucm_max_lemma_size               10
% 3.76/0.99  
% 3.76/0.99  ------ AIG Options
% 3.76/0.99  
% 3.76/0.99  --aig_mode                              false
% 3.76/0.99  
% 3.76/0.99  ------ Instantiation Options
% 3.76/0.99  
% 3.76/0.99  --instantiation_flag                    true
% 3.76/0.99  --inst_sos_flag                         false
% 3.76/0.99  --inst_sos_phase                        true
% 3.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/0.99  --inst_lit_sel_side                     num_symb
% 3.76/0.99  --inst_solver_per_active                1400
% 3.76/0.99  --inst_solver_calls_frac                1.
% 3.76/0.99  --inst_passive_queue_type               priority_queues
% 3.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/0.99  --inst_passive_queues_freq              [25;2]
% 3.76/0.99  --inst_dismatching                      true
% 3.76/0.99  --inst_eager_unprocessed_to_passive     true
% 3.76/0.99  --inst_prop_sim_given                   true
% 3.76/0.99  --inst_prop_sim_new                     false
% 3.76/0.99  --inst_subs_new                         false
% 3.76/0.99  --inst_eq_res_simp                      false
% 3.76/0.99  --inst_subs_given                       false
% 3.76/0.99  --inst_orphan_elimination               true
% 3.76/0.99  --inst_learning_loop_flag               true
% 3.76/0.99  --inst_learning_start                   3000
% 3.76/0.99  --inst_learning_factor                  2
% 3.76/0.99  --inst_start_prop_sim_after_learn       3
% 3.76/0.99  --inst_sel_renew                        solver
% 3.76/0.99  --inst_lit_activity_flag                true
% 3.76/0.99  --inst_restr_to_given                   false
% 3.76/0.99  --inst_activity_threshold               500
% 3.76/0.99  --inst_out_proof                        true
% 3.76/0.99  
% 3.76/0.99  ------ Resolution Options
% 3.76/0.99  
% 3.76/0.99  --resolution_flag                       true
% 3.76/0.99  --res_lit_sel                           adaptive
% 3.76/0.99  --res_lit_sel_side                      none
% 3.76/0.99  --res_ordering                          kbo
% 3.76/0.99  --res_to_prop_solver                    active
% 3.76/0.99  --res_prop_simpl_new                    false
% 3.76/0.99  --res_prop_simpl_given                  true
% 3.76/0.99  --res_passive_queue_type                priority_queues
% 3.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/0.99  --res_passive_queues_freq               [15;5]
% 3.76/0.99  --res_forward_subs                      full
% 3.76/0.99  --res_backward_subs                     full
% 3.76/0.99  --res_forward_subs_resolution           true
% 3.76/0.99  --res_backward_subs_resolution          true
% 3.76/0.99  --res_orphan_elimination                true
% 3.76/0.99  --res_time_limit                        2.
% 3.76/0.99  --res_out_proof                         true
% 3.76/0.99  
% 3.76/0.99  ------ Superposition Options
% 3.76/0.99  
% 3.76/0.99  --superposition_flag                    true
% 3.76/0.99  --sup_passive_queue_type                priority_queues
% 3.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.76/0.99  --demod_completeness_check              fast
% 3.76/0.99  --demod_use_ground                      true
% 3.76/0.99  --sup_to_prop_solver                    passive
% 3.76/0.99  --sup_prop_simpl_new                    true
% 3.76/0.99  --sup_prop_simpl_given                  true
% 3.76/0.99  --sup_fun_splitting                     false
% 3.76/0.99  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   []
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_full_bw                           [BwDemod]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  ------ Parsing...
% 3.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.00  ------ Proving...
% 3.76/1.00  ------ Problem Properties 
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  clauses                                 34
% 3.76/1.00  conjectures                             6
% 3.76/1.00  EPR                                     10
% 3.76/1.00  Horn                                    11
% 3.76/1.00  unary                                   3
% 3.76/1.00  binary                                  8
% 3.76/1.00  lits                                    168
% 3.76/1.00  lits eq                                 6
% 3.76/1.00  fd_pure                                 0
% 3.76/1.00  fd_pseudo                               0
% 3.76/1.00  fd_cond                                 0
% 3.76/1.00  fd_pseudo_cond                          4
% 3.76/1.00  AC symbols                              0
% 3.76/1.00  
% 3.76/1.00  ------ Schedule dynamic 5 is on 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  Current options:
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  ------ Input Options
% 3.76/1.00  
% 3.76/1.00  --out_options                           all
% 3.76/1.00  --tptp_safe_out                         true
% 3.76/1.00  --problem_path                          ""
% 3.76/1.00  --include_path                          ""
% 3.76/1.00  --clausifier                            res/vclausify_rel
% 3.76/1.00  --clausifier_options                    --mode clausify
% 3.76/1.00  --stdin                                 false
% 3.76/1.00  --stats_out                             all
% 3.76/1.00  
% 3.76/1.00  ------ General Options
% 3.76/1.00  
% 3.76/1.00  --fof                                   false
% 3.76/1.00  --time_out_real                         305.
% 3.76/1.00  --time_out_virtual                      -1.
% 3.76/1.00  --symbol_type_check                     false
% 3.76/1.00  --clausify_out                          false
% 3.76/1.00  --sig_cnt_out                           false
% 3.76/1.00  --trig_cnt_out                          false
% 3.76/1.00  --trig_cnt_out_tolerance                1.
% 3.76/1.00  --trig_cnt_out_sk_spl                   false
% 3.76/1.00  --abstr_cl_out                          false
% 3.76/1.00  
% 3.76/1.00  ------ Global Options
% 3.76/1.00  
% 3.76/1.00  --schedule                              default
% 3.76/1.00  --add_important_lit                     false
% 3.76/1.00  --prop_solver_per_cl                    1000
% 3.76/1.00  --min_unsat_core                        false
% 3.76/1.00  --soft_assumptions                      false
% 3.76/1.00  --soft_lemma_size                       3
% 3.76/1.00  --prop_impl_unit_size                   0
% 3.76/1.00  --prop_impl_unit                        []
% 3.76/1.00  --share_sel_clauses                     true
% 3.76/1.00  --reset_solvers                         false
% 3.76/1.00  --bc_imp_inh                            [conj_cone]
% 3.76/1.00  --conj_cone_tolerance                   3.
% 3.76/1.00  --extra_neg_conj                        none
% 3.76/1.00  --large_theory_mode                     true
% 3.76/1.00  --prolific_symb_bound                   200
% 3.76/1.00  --lt_threshold                          2000
% 3.76/1.00  --clause_weak_htbl                      true
% 3.76/1.00  --gc_record_bc_elim                     false
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing Options
% 3.76/1.00  
% 3.76/1.00  --preprocessing_flag                    true
% 3.76/1.00  --time_out_prep_mult                    0.1
% 3.76/1.00  --splitting_mode                        input
% 3.76/1.00  --splitting_grd                         true
% 3.76/1.00  --splitting_cvd                         false
% 3.76/1.00  --splitting_cvd_svl                     false
% 3.76/1.00  --splitting_nvd                         32
% 3.76/1.00  --sub_typing                            true
% 3.76/1.00  --prep_gs_sim                           true
% 3.76/1.00  --prep_unflatten                        true
% 3.76/1.00  --prep_res_sim                          true
% 3.76/1.00  --prep_upred                            true
% 3.76/1.00  --prep_sem_filter                       exhaustive
% 3.76/1.00  --prep_sem_filter_out                   false
% 3.76/1.00  --pred_elim                             true
% 3.76/1.00  --res_sim_input                         true
% 3.76/1.00  --eq_ax_congr_red                       true
% 3.76/1.00  --pure_diseq_elim                       true
% 3.76/1.00  --brand_transform                       false
% 3.76/1.00  --non_eq_to_eq                          false
% 3.76/1.00  --prep_def_merge                        true
% 3.76/1.00  --prep_def_merge_prop_impl              false
% 3.76/1.00  --prep_def_merge_mbd                    true
% 3.76/1.00  --prep_def_merge_tr_red                 false
% 3.76/1.00  --prep_def_merge_tr_cl                  false
% 3.76/1.00  --smt_preprocessing                     true
% 3.76/1.00  --smt_ac_axioms                         fast
% 3.76/1.00  --preprocessed_out                      false
% 3.76/1.00  --preprocessed_stats                    false
% 3.76/1.00  
% 3.76/1.00  ------ Abstraction refinement Options
% 3.76/1.00  
% 3.76/1.00  --abstr_ref                             []
% 3.76/1.00  --abstr_ref_prep                        false
% 3.76/1.00  --abstr_ref_until_sat                   false
% 3.76/1.00  --abstr_ref_sig_restrict                funpre
% 3.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.00  --abstr_ref_under                       []
% 3.76/1.00  
% 3.76/1.00  ------ SAT Options
% 3.76/1.00  
% 3.76/1.00  --sat_mode                              false
% 3.76/1.00  --sat_fm_restart_options                ""
% 3.76/1.00  --sat_gr_def                            false
% 3.76/1.00  --sat_epr_types                         true
% 3.76/1.00  --sat_non_cyclic_types                  false
% 3.76/1.00  --sat_finite_models                     false
% 3.76/1.00  --sat_fm_lemmas                         false
% 3.76/1.00  --sat_fm_prep                           false
% 3.76/1.00  --sat_fm_uc_incr                        true
% 3.76/1.00  --sat_out_model                         small
% 3.76/1.00  --sat_out_clauses                       false
% 3.76/1.00  
% 3.76/1.00  ------ QBF Options
% 3.76/1.00  
% 3.76/1.00  --qbf_mode                              false
% 3.76/1.00  --qbf_elim_univ                         false
% 3.76/1.00  --qbf_dom_inst                          none
% 3.76/1.00  --qbf_dom_pre_inst                      false
% 3.76/1.00  --qbf_sk_in                             false
% 3.76/1.00  --qbf_pred_elim                         true
% 3.76/1.00  --qbf_split                             512
% 3.76/1.00  
% 3.76/1.00  ------ BMC1 Options
% 3.76/1.00  
% 3.76/1.00  --bmc1_incremental                      false
% 3.76/1.00  --bmc1_axioms                           reachable_all
% 3.76/1.00  --bmc1_min_bound                        0
% 3.76/1.00  --bmc1_max_bound                        -1
% 3.76/1.00  --bmc1_max_bound_default                -1
% 3.76/1.00  --bmc1_symbol_reachability              true
% 3.76/1.00  --bmc1_property_lemmas                  false
% 3.76/1.00  --bmc1_k_induction                      false
% 3.76/1.00  --bmc1_non_equiv_states                 false
% 3.76/1.00  --bmc1_deadlock                         false
% 3.76/1.00  --bmc1_ucm                              false
% 3.76/1.00  --bmc1_add_unsat_core                   none
% 3.76/1.00  --bmc1_unsat_core_children              false
% 3.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.00  --bmc1_out_stat                         full
% 3.76/1.00  --bmc1_ground_init                      false
% 3.76/1.00  --bmc1_pre_inst_next_state              false
% 3.76/1.00  --bmc1_pre_inst_state                   false
% 3.76/1.00  --bmc1_pre_inst_reach_state             false
% 3.76/1.00  --bmc1_out_unsat_core                   false
% 3.76/1.00  --bmc1_aig_witness_out                  false
% 3.76/1.00  --bmc1_verbose                          false
% 3.76/1.00  --bmc1_dump_clauses_tptp                false
% 3.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.00  --bmc1_dump_file                        -
% 3.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.00  --bmc1_ucm_extend_mode                  1
% 3.76/1.00  --bmc1_ucm_init_mode                    2
% 3.76/1.00  --bmc1_ucm_cone_mode                    none
% 3.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.00  --bmc1_ucm_relax_model                  4
% 3.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.00  --bmc1_ucm_layered_model                none
% 3.76/1.00  --bmc1_ucm_max_lemma_size               10
% 3.76/1.00  
% 3.76/1.00  ------ AIG Options
% 3.76/1.00  
% 3.76/1.00  --aig_mode                              false
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation Options
% 3.76/1.00  
% 3.76/1.00  --instantiation_flag                    true
% 3.76/1.00  --inst_sos_flag                         false
% 3.76/1.00  --inst_sos_phase                        true
% 3.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.00  --inst_lit_sel_side                     none
% 3.76/1.00  --inst_solver_per_active                1400
% 3.76/1.00  --inst_solver_calls_frac                1.
% 3.76/1.00  --inst_passive_queue_type               priority_queues
% 3.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.00  --inst_passive_queues_freq              [25;2]
% 3.76/1.00  --inst_dismatching                      true
% 3.76/1.00  --inst_eager_unprocessed_to_passive     true
% 3.76/1.00  --inst_prop_sim_given                   true
% 3.76/1.00  --inst_prop_sim_new                     false
% 3.76/1.00  --inst_subs_new                         false
% 3.76/1.00  --inst_eq_res_simp                      false
% 3.76/1.00  --inst_subs_given                       false
% 3.76/1.00  --inst_orphan_elimination               true
% 3.76/1.00  --inst_learning_loop_flag               true
% 3.76/1.00  --inst_learning_start                   3000
% 3.76/1.00  --inst_learning_factor                  2
% 3.76/1.00  --inst_start_prop_sim_after_learn       3
% 3.76/1.00  --inst_sel_renew                        solver
% 3.76/1.00  --inst_lit_activity_flag                true
% 3.76/1.00  --inst_restr_to_given                   false
% 3.76/1.00  --inst_activity_threshold               500
% 3.76/1.00  --inst_out_proof                        true
% 3.76/1.00  
% 3.76/1.00  ------ Resolution Options
% 3.76/1.00  
% 3.76/1.00  --resolution_flag                       false
% 3.76/1.00  --res_lit_sel                           adaptive
% 3.76/1.00  --res_lit_sel_side                      none
% 3.76/1.00  --res_ordering                          kbo
% 3.76/1.00  --res_to_prop_solver                    active
% 3.76/1.00  --res_prop_simpl_new                    false
% 3.76/1.00  --res_prop_simpl_given                  true
% 3.76/1.00  --res_passive_queue_type                priority_queues
% 3.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.00  --res_passive_queues_freq               [15;5]
% 3.76/1.00  --res_forward_subs                      full
% 3.76/1.00  --res_backward_subs                     full
% 3.76/1.00  --res_forward_subs_resolution           true
% 3.76/1.00  --res_backward_subs_resolution          true
% 3.76/1.00  --res_orphan_elimination                true
% 3.76/1.00  --res_time_limit                        2.
% 3.76/1.00  --res_out_proof                         true
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Options
% 3.76/1.00  
% 3.76/1.00  --superposition_flag                    true
% 3.76/1.00  --sup_passive_queue_type                priority_queues
% 3.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.00  --demod_completeness_check              fast
% 3.76/1.00  --demod_use_ground                      true
% 3.76/1.00  --sup_to_prop_solver                    passive
% 3.76/1.00  --sup_prop_simpl_new                    true
% 3.76/1.00  --sup_prop_simpl_given                  true
% 3.76/1.00  --sup_fun_splitting                     false
% 3.76/1.00  --sup_smt_interval                      50000
% 3.76/1.00  
% 3.76/1.00  ------ Superposition Simplification Setup
% 3.76/1.00  
% 3.76/1.00  --sup_indices_passive                   []
% 3.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_full_bw                           [BwDemod]
% 3.76/1.00  --sup_immed_triv                        [TrivRules]
% 3.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_immed_bw_main                     []
% 3.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.00  
% 3.76/1.00  ------ Combination Options
% 3.76/1.00  
% 3.76/1.00  --comb_res_mult                         3
% 3.76/1.00  --comb_sup_mult                         2
% 3.76/1.00  --comb_inst_mult                        10
% 3.76/1.00  
% 3.76/1.00  ------ Debug Options
% 3.76/1.00  
% 3.76/1.00  --dbg_backtrace                         false
% 3.76/1.00  --dbg_dump_prop_clauses                 false
% 3.76/1.00  --dbg_dump_prop_clauses_file            -
% 3.76/1.00  --dbg_out_stat                          false
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ Proving...
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS status Theorem for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00   Resolution empty clause
% 3.76/1.00  
% 3.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  fof(f12,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f32,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f12])).
% 3.76/1.00  
% 3.76/1.00  fof(f33,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f32])).
% 3.76/1.00  
% 3.76/1.00  fof(f46,plain,(
% 3.76/1.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f47,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f46])).
% 3.76/1.00  
% 3.76/1.00  fof(f81,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f47])).
% 3.76/1.00  
% 3.76/1.00  fof(f14,conjecture,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f15,negated_conjecture,(
% 3.76/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.76/1.00    inference(negated_conjecture,[],[f14])).
% 3.76/1.00  
% 3.76/1.00  fof(f36,plain,(
% 3.76/1.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f37,plain,(
% 3.76/1.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f36])).
% 3.76/1.00  
% 3.76/1.00  fof(f53,plain,(
% 3.76/1.00    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f37])).
% 3.76/1.00  
% 3.76/1.00  fof(f54,plain,(
% 3.76/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f53])).
% 3.76/1.00  
% 3.76/1.00  fof(f55,plain,(
% 3.76/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/1.00    inference(rectify,[],[f54])).
% 3.76/1.00  
% 3.76/1.00  fof(f58,plain,(
% 3.76/1.00    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK8(X3),X0) & m2_yellow_6(sK8(X3),X0,X3)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f57,plain,(
% 3.76/1.00    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK7)) & l1_waybel_0(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f56,plain,(
% 3.76/1.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,X1)) & l1_waybel_0(X1,sK6) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK6)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK6) & m2_yellow_6(X4,sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f59,plain,(
% 3.76/1.00    ((! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7)) & l1_waybel_0(sK7,sK6) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) | ~v1_compts_1(sK6)) & (! [X3] : ((v3_yellow_6(sK8(X3),sK6) & m2_yellow_6(sK8(X3),sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f55,f58,f57,f56])).
% 3.76/1.00  
% 3.76/1.00  fof(f91,plain,(
% 3.76/1.00    v2_pre_topc(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f90,plain,(
% 3.76/1.00    ~v2_struct_0(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f92,plain,(
% 3.76/1.00    l1_pre_topc(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f13,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f34,plain,(
% 3.76/1.00    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f13])).
% 3.76/1.00  
% 3.76/1.00  fof(f35,plain,(
% 3.76/1.00    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f48,plain,(
% 3.76/1.00    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f35])).
% 3.76/1.00  
% 3.76/1.00  fof(f49,plain,(
% 3.76/1.00    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(rectify,[],[f48])).
% 3.76/1.00  
% 3.76/1.00  fof(f51,plain,(
% 3.76/1.00    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f50,plain,(
% 3.76/1.00    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f52,plain,(
% 3.76/1.00    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f49,f51,f50])).
% 3.76/1.00  
% 3.76/1.00  fof(f84,plain,(
% 3.76/1.00    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK5(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f83,plain,(
% 3.76/1.00    ( ! [X0,X3] : (m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f11,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f30,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f11])).
% 3.76/1.00  
% 3.76/1.00  fof(f31,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f30])).
% 3.76/1.00  
% 3.76/1.00  fof(f80,plain,(
% 3.76/1.00    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f5,axiom,(
% 3.76/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f19,plain,(
% 3.76/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.76/1.00    inference(ennf_transformation,[],[f5])).
% 3.76/1.00  
% 3.76/1.00  fof(f64,plain,(
% 3.76/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f19])).
% 3.76/1.00  
% 3.76/1.00  fof(f8,axiom,(
% 3.76/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f24,plain,(
% 3.76/1.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f8])).
% 3.76/1.00  
% 3.76/1.00  fof(f25,plain,(
% 3.76/1.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f24])).
% 3.76/1.00  
% 3.76/1.00  fof(f75,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f74,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f73,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f76,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f25])).
% 3.76/1.00  
% 3.76/1.00  fof(f85,plain,(
% 3.76/1.00    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f86,plain,(
% 3.76/1.00    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f87,plain,(
% 3.76/1.00    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f88,plain,(
% 3.76/1.00    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK4(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f2,axiom,(
% 3.76/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f61,plain,(
% 3.76/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f2])).
% 3.76/1.00  
% 3.76/1.00  fof(f93,plain,(
% 3.76/1.00    ( ! [X3] : (m2_yellow_6(sK8(X3),sK6,X3) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f9,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f26,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f9])).
% 3.76/1.00  
% 3.76/1.00  fof(f27,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f26])).
% 3.76/1.00  
% 3.76/1.00  fof(f45,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f77,plain,(
% 3.76/1.00    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f45])).
% 3.76/1.00  
% 3.76/1.00  fof(f94,plain,(
% 3.76/1.00    ( ! [X3] : (v3_yellow_6(sK8(X3),sK6) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f6,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f20,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f6])).
% 3.76/1.00  
% 3.76/1.00  fof(f21,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f20])).
% 3.76/1.00  
% 3.76/1.00  fof(f38,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(nnf_transformation,[],[f21])).
% 3.76/1.00  
% 3.76/1.00  fof(f39,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f38])).
% 3.76/1.00  
% 3.76/1.00  fof(f40,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(rectify,[],[f39])).
% 3.76/1.00  
% 3.76/1.00  fof(f43,plain,(
% 3.76/1.00    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f42,plain,(
% 3.76/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f41,plain,(
% 3.76/1.00    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f44,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 3.76/1.00  
% 3.76/1.00  fof(f68,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f44])).
% 3.76/1.00  
% 3.76/1.00  fof(f89,plain,(
% 3.76/1.00    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f52])).
% 3.76/1.00  
% 3.76/1.00  fof(f10,axiom,(
% 3.76/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f28,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f10])).
% 3.76/1.00  
% 3.76/1.00  fof(f29,plain,(
% 3.76/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f28])).
% 3.76/1.00  
% 3.76/1.00  fof(f79,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f29])).
% 3.76/1.00  
% 3.76/1.00  fof(f7,axiom,(
% 3.76/1.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f22,plain,(
% 3.76/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f7])).
% 3.76/1.00  
% 3.76/1.00  fof(f23,plain,(
% 3.76/1.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.00    inference(flattening,[],[f22])).
% 3.76/1.00  
% 3.76/1.00  fof(f72,plain,(
% 3.76/1.00    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f23])).
% 3.76/1.00  
% 3.76/1.00  fof(f67,plain,(
% 3.76/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f44])).
% 3.76/1.00  
% 3.76/1.00  fof(f100,plain,(
% 3.76/1.00    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(equality_resolution,[],[f67])).
% 3.76/1.00  
% 3.76/1.00  fof(f66,plain,(
% 3.76/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f44])).
% 3.76/1.00  
% 3.76/1.00  fof(f101,plain,(
% 3.76/1.00    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(equality_resolution,[],[f66])).
% 3.76/1.00  
% 3.76/1.00  fof(f69,plain,(
% 3.76/1.00    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f44])).
% 3.76/1.00  
% 3.76/1.00  fof(f1,axiom,(
% 3.76/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f60,plain,(
% 3.76/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f1])).
% 3.76/1.00  
% 3.76/1.00  fof(f4,axiom,(
% 3.76/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f18,plain,(
% 3.76/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.76/1.00    inference(ennf_transformation,[],[f4])).
% 3.76/1.00  
% 3.76/1.00  fof(f63,plain,(
% 3.76/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f18])).
% 3.76/1.00  
% 3.76/1.00  fof(f78,plain,(
% 3.76/1.00    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f45])).
% 3.76/1.00  
% 3.76/1.00  fof(f99,plain,(
% 3.76/1.00    ( ! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7) | ~v1_compts_1(sK6)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f95,plain,(
% 3.76/1.00    ~v2_struct_0(sK7) | ~v1_compts_1(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f96,plain,(
% 3.76/1.00    v4_orders_2(sK7) | ~v1_compts_1(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f97,plain,(
% 3.76/1.00    v7_waybel_0(sK7) | ~v1_compts_1(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f98,plain,(
% 3.76/1.00    l1_waybel_0(sK7,sK6) | ~v1_compts_1(sK6)),
% 3.76/1.00    inference(cnf_transformation,[],[f59])).
% 3.76/1.00  
% 3.76/1.00  fof(f82,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f47])).
% 3.76/1.00  
% 3.76/1.00  cnf(c_22,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_38,negated_conjecture,
% 3.76/1.00      ( v2_pre_topc(sK6) ),
% 3.76/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1228,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1229,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1228]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_39,negated_conjecture,
% 3.76/1.00      ( ~ v2_struct_0(sK6) ),
% 3.76/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_37,negated_conjecture,
% 3.76/1.00      ( l1_pre_topc(sK6) ),
% 3.76/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1233,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1229,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1234,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1233]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8003,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.76/1.00      | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1234]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8754,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57) = iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8003]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_28,plain,
% 3.76/1.00      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1121,plain,
% 3.76/1.00      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1122,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1121]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1126,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1122,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1127,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1126]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8009,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57))
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1127]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8748,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57)) = iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8009]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_29,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.76/1.00      | ~ v1_compts_1(X1)
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1503,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.76/1.00      | ~ v1_compts_1(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1504,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1503]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1508,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1504,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1509,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1508]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7997,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6))
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1509]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8760,plain,
% 3.76/1.00      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6)) = iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7997]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_20,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | r3_waybel_9(X0,X3,X2)
% 3.76/1.00      | ~ m2_yellow_6(X1,X0,X3)
% 3.76/1.00      | ~ l1_waybel_0(X3,X0)
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X3)
% 3.76/1.00      | ~ v4_orders_2(X3)
% 3.76/1.00      | ~ v7_waybel_0(X3)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1294,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | r3_waybel_9(X0,X3,X2)
% 3.76/1.00      | ~ m2_yellow_6(X1,X0,X3)
% 3.76/1.00      | ~ l1_waybel_0(X3,X0)
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X3)
% 3.76/1.00      | ~ v4_orders_2(X3)
% 3.76/1.00      | ~ v7_waybel_0(X3)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1295,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | r3_waybel_9(sK6,X2,X1)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1294]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1297,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | r3_waybel_9(sK6,X2,X1)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X2) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1295,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1298,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | r3_waybel_9(sK6,X2,X1)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1297]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8001,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.76/1.00      | r3_waybel_9(sK6,X1_57,X0_58)
% 3.76/1.00      | ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.76/1.00      | ~ l1_waybel_0(X1_57,sK6)
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X1_57)
% 3.76/1.00      | ~ v4_orders_2(X1_57)
% 3.76/1.00      | ~ v7_waybel_0(X1_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1298]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8756,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X1_57,X0_58) = iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8001]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10723,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X2_57,sK5(sK6,X1_57)) = iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,X2_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X2_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X2_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X2_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X2_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8760,c_8756]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11259,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
% 3.76/1.00      | m2_yellow_6(X1_57,sK6,X0_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8748,c_10723]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4,plain,
% 3.76/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_struct_0(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_509,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X3)
% 3.76/1.00      | X1 != X3 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_510,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_509]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1836,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | v7_waybel_0(X0)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_510,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1837,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | v7_waybel_0(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1836]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1839,plain,
% 3.76/1.00      ( v2_struct_0(X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | v7_waybel_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1837,c_39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1840,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1839]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7989,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.76/1.00      | ~ l1_waybel_0(X1_57,sK6)
% 3.76/1.00      | v2_struct_0(X1_57)
% 3.76/1.00      | ~ v4_orders_2(X1_57)
% 3.76/1.00      | ~ v7_waybel_0(X1_57)
% 3.76/1.00      | v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1840]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8768,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7989]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_15,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_struct_0(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_481,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X3)
% 3.76/1.00      | X1 != X3 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_482,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_481]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1862,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_482,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1863,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1862]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1865,plain,
% 3.76/1.00      ( v2_struct_0(X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1863,c_39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1866,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1865]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7988,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.76/1.00      | ~ l1_waybel_0(X1_57,sK6)
% 3.76/1.00      | v2_struct_0(X1_57)
% 3.76/1.00      | ~ v4_orders_2(X1_57)
% 3.76/1.00      | v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X1_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1866]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8769,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) = iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7988]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_struct_0(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_453,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X3)
% 3.76/1.00      | X1 != X3 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_454,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1888,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_454,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1889,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1888]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1891,plain,
% 3.76/1.00      ( v2_struct_0(X1)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1889,c_39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1892,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1891]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7987,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.76/1.00      | ~ l1_waybel_0(X1_57,sK6)
% 3.76/1.00      | ~ v2_struct_0(X0_57)
% 3.76/1.00      | v2_struct_0(X1_57)
% 3.76/1.00      | ~ v4_orders_2(X1_57)
% 3.76/1.00      | ~ v7_waybel_0(X1_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1892]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8770,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7987]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | l1_waybel_0(X0,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_struct_0(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_537,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | l1_waybel_0(X0,X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X3)
% 3.76/1.00      | X1 != X3 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_538,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | l1_waybel_0(X0,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1810,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | l1_waybel_0(X0,X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_538,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1811,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | l1_waybel_0(X0,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1810]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1813,plain,
% 3.76/1.00      ( v2_struct_0(X1)
% 3.76/1.00      | l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1811,c_39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1814,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | l1_waybel_0(X0,sK6)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1813]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7990,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.76/1.00      | ~ l1_waybel_0(X1_57,sK6)
% 3.76/1.00      | l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | v2_struct_0(X1_57)
% 3.76/1.00      | ~ v4_orders_2(X1_57)
% 3.76/1.00      | ~ v7_waybel_0(X1_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1814]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8767,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7990]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11273,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
% 3.76/1.00      | m2_yellow_6(X1_57,sK6,X0_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(forward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_11259,c_8768,c_8769,c_8770,c_8767]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11276,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
% 3.76/1.00      | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
% 3.76/1.00      | m2_yellow_6(X2_57,sK6,X0_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X2_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X2_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X2_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X2_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_11273,c_10723]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12477,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X1_57)) = iProver_top
% 3.76/1.00      | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
% 3.76/1.00      | m2_yellow_6(X2_57,sK6,X0_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(forward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_11276,c_8768,c_8769,c_8770,c_8767,c_8767]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12479,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v2_struct_0(sK3(sK6,X0_57,X0_58)) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(sK3(sK6,X0_57,X0_58)) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK3(sK6,X0_57,X0_58)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8754,c_12477]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_27,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v2_struct_0(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1151,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v2_struct_0(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1152,plain,
% 3.76/1.00      ( v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_struct_0(sK4(sK6))
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1151]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1154,plain,
% 3.76/1.00      ( v1_compts_1(sK6) | ~ v2_struct_0(sK4(sK6)) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1152,c_39,c_38,c_37,c_63]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1156,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top | v2_struct_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_26,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v4_orders_2(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1165,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v4_orders_2(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1166,plain,
% 3.76/1.00      ( v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1165]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1168,plain,
% 3.76/1.00      ( v4_orders_2(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1166,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1169,plain,
% 3.76/1.00      ( v1_compts_1(sK6) | v4_orders_2(sK4(sK6)) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1168]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1170,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top | v4_orders_2(sK4(sK6)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_25,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v7_waybel_0(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1179,plain,
% 3.76/1.00      ( v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v7_waybel_0(sK4(X0))
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1180,plain,
% 3.76/1.00      ( v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | v7_waybel_0(sK4(sK6))
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1179]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1182,plain,
% 3.76/1.00      ( v7_waybel_0(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1180,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1183,plain,
% 3.76/1.00      ( v1_compts_1(sK6) | v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1182]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1184,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top | v7_waybel_0(sK4(sK6)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_24,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(X0),X0)
% 3.76/1.00      | v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1193,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(X0),X0)
% 3.76/1.00      | v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1194,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1193]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1196,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(sK6),sK6) | v1_compts_1(sK6) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1194,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1198,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1196]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8130,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7990]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8131,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7989]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8132,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) = iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7988]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8133,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7987]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.76/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8019,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_60)) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9357,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8019]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9360,plain,
% 3.76/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9357]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_36,negated_conjecture,
% 3.76/1.00      ( m2_yellow_6(sK8(X0),sK6,X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8013,negated_conjecture,
% 3.76/1.00      ( m2_yellow_6(sK8(X0_57),sK6,X0_57)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_36]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9390,plain,
% 3.76/1.00      ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8013]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9458,plain,
% 3.76/1.00      ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9390]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2443,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | l1_waybel_0(X2,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | X1 != X0
% 3.76/1.00      | sK8(X0) != X2
% 3.76/1.00      | sK6 != sK6 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_1814]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2444,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_2443]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2419,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | v7_waybel_0(X2)
% 3.76/1.00      | X1 != X0
% 3.76/1.00      | sK8(X0) != X2
% 3.76/1.00      | sK6 != sK6 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_1840]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2420,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | v7_waybel_0(sK8(X0)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_2419]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2395,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | X1 != X0
% 3.76/1.00      | sK8(X0) != X2
% 3.76/1.00      | sK6 != sK6 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_1866]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2396,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | v4_orders_2(sK8(X0))
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_2395]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2371,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | X1 != X0
% 3.76/1.00      | sK8(X0) != X2
% 3.76/1.00      | sK6 != sK6 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_1892]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2372,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v2_struct_0(sK8(X0))
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_2371]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_18,plain,
% 3.76/1.00      ( ~ v3_yellow_6(X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_35,negated_conjecture,
% 3.76/1.00      ( v3_yellow_6(sK8(X0),sK6)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_635,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X2,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.76/1.00      | sK8(X2) != X0
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_636,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_pre_topc(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK8(X0))
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v4_orders_2(sK8(X0))
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v7_waybel_0(sK8(X0))
% 3.76/1.00      | ~ l1_pre_topc(sK6)
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_635]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_640,plain,
% 3.76/1.00      ( ~ v7_waybel_0(sK8(X0))
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(sK8(X0))
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK8(X0))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_636,c_39,c_38,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_641,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK8(X0))
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v4_orders_2(sK8(X0))
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v7_waybel_0(sK8(X0))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_640]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2626,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v4_orders_2(sK8(X0))
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v7_waybel_0(sK8(X0))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2372,c_641]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2637,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v7_waybel_0(sK8(X0))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2396,c_2626]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2648,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2420,c_2637]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2654,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2444,c_2648]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7986,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57)
% 3.76/1.00      | k10_yellow_6(sK6,sK8(X0_57)) != k1_xboole_0 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_2654]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9540,plain,
% 3.76/1.00      ( ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7986]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9541,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9540]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9461,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.76/1.00      | l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7990]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9680,plain,
% 3.76/1.00      ( ~ m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9461]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9681,plain,
% 3.76/1.00      ( m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9680]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8005,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(sK6),sK6) | v1_compts_1(sK6) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1196]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8752,plain,
% 3.76/1.00      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8005]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8744,plain,
% 3.76/1.00      ( m2_yellow_6(sK8(X0_57),sK6,X0_57) = iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8013]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9621,plain,
% 3.76/1.00      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(X0_57)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8744,c_8768]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9631,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8752,c_9621]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9690,plain,
% 3.76/1.00      ( v7_waybel_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_9631,c_1156,c_1170,c_1184]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9691,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) = iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_9690]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9372,plain,
% 3.76/1.00      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v2_struct_0(sK8(X0_57)) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8744,c_8770]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9525,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8752,c_9372]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9697,plain,
% 3.76/1.00      ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_9525,c_1156,c_1170,c_1184]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9698,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_9697]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X0) = X2 ),
% 3.76/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1608,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X0) = X2
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1609,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = X1 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1608]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1613,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = X1 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1609,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1614,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = X1 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1613]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7992,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57)
% 3.76/1.00      | k10_yellow_6(sK6,X0_57) = X0_58 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1614]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9898,plain,
% 3.76/1.00      ( ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6)))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7992]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9911,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) = iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9898]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9913,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) = iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9911]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10239,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v4_orders_2(sK3(sK6,X0_57,X0_58)) = iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8754,c_8769]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10240,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK3(sK6,X0_57,X0_58)) = iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8754,c_8768]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10241,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v2_struct_0(sK3(sK6,X0_57,X0_58)) != iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8754,c_8770]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9731,plain,
% 3.76/1.00      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v4_orders_2(sK8(X0_57)) = iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8744,c_8769]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9855,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8752,c_9731]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10406,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_9855,c_1156,c_1170,c_1184]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_23,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.76/1.00      | v1_compts_1(X0)
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1207,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.76/1.00      | v1_compts_1(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1208,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.76/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.76/1.00      | v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1207]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1212,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.76/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.76/1.00      | v1_compts_1(sK6) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1208,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8004,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,sK4(sK6),X0_58)
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v1_compts_1(sK6) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1212]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10438,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v1_compts_1(sK6) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8004]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10444,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_10438]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10446,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_10444]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_19,plain,
% 3.76/1.00      ( r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1326,plain,
% 3.76/1.00      ( r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1327,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1326]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1331,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1327,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1332,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1331]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8000,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1332]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9897,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),X0_58)
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | ~ r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8000]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10425,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | ~ r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9897]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10496,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_10425]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10498,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_10496]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1533,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1534,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1533]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1538,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1534,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1539,plain,
% 3.76/1.00      ( ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1538]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9,plain,
% 3.76/1.00      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1395,plain,
% 3.76/1.00      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1396,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1395]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1400,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1396,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1401,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1400]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1557,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1539,c_1401]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7994,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58))
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1557]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9891,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7994]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11051,plain,
% 3.76/1.00      ( ~ r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)))
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9891]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11052,plain,
% 3.76/1.00      ( r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_11051]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11054,plain,
% 3.76/1.00      ( r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0))) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_11052]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1359,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1360,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1359]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1364,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1360,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1365,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1364]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1556,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1539,c_1365]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7995,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1556]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9890,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),X0_58),sK6,X0_58)
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7995]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11095,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6))))
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9890]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11096,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_11095]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11098,plain,
% 3.76/1.00      ( m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)),sK6,sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k10_yellow_6(sK6,sK8(sK4(sK6)))) = iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_11096]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9460,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.76/1.00      | r3_waybel_9(sK6,sK4(sK6),X0_58)
% 3.76/1.00      | ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8001]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10428,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0_57,sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9460]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11168,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | ~ m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6))
% 3.76/1.00      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.76/1.00      | ~ m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(sK4(sK6))
% 3.76/1.00      | ~ v4_orders_2(sK4(sK6))
% 3.76/1.00      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_10428]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11169,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),X0_58)) = iProver_top
% 3.76/1.00      | m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),X0_58),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_11168]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11171,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,sK4(sK6),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) = iProver_top
% 3.76/1.00      | m2_yellow_6(sK8(sK4(sK6)),sK6,sK4(sK6)) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_11169]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.76/1.00      | r1_waybel_0(X1,X2,X0)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X2) = X3 ),
% 3.76/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1641,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.76/1.00      | r1_waybel_0(X1,X2,X0)
% 3.76/1.00      | ~ l1_waybel_0(X2,X1)
% 3.76/1.00      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.76/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X2)
% 3.76/1.00      | ~ v7_waybel_0(X2)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X2) = X3
% 3.76/1.00      | sK6 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1642,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.76/1.00      | r1_waybel_0(sK6,X1,X0)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(sK6)
% 3.76/1.00      | k10_yellow_6(sK6,X1) = X2 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1641]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1646,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.76/1.00      | r1_waybel_0(sK6,X1,X0)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | k10_yellow_6(sK6,X1) = X2 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1642,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1647,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.76/1.00      | r1_waybel_0(sK6,X1,X0)
% 3.76/1.00      | ~ l1_waybel_0(X1,sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.76/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | k10_yellow_6(sK6,X1) = X2 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1646]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7991,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58))
% 3.76/1.00      | r1_waybel_0(sK6,X0_57,X0_59)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58)
% 3.76/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57)
% 3.76/1.00      | k10_yellow_6(sK6,X0_57) = X0_58 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1647]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9892,plain,
% 3.76/1.00      ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | r1_waybel_0(sK6,sK8(sK4(sK6)),X0_59)
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58)
% 3.76/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6)))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7991]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12415,plain,
% 3.76/1.00      ( ~ m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58))
% 3.76/1.00      | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)))
% 3.76/1.00      | ~ l1_waybel_0(sK8(sK4(sK6)),sK6)
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58)
% 3.76/1.00      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v4_orders_2(sK8(sK4(sK6)))
% 3.76/1.00      | ~ v7_waybel_0(sK8(sK4(sK6)))
% 3.76/1.00      | k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_9892]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12421,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = X0_58
% 3.76/1.00      | m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58)),sK6,sK0(sK6,sK8(sK4(sK6)),X0_58)) != iProver_top
% 3.76/1.00      | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),X0_58))) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),X0_58),X0_58) = iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_12415]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12423,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
% 3.76/1.00      | m1_connsp_2(sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)),sK6,sK0(sK6,sK8(sK4(sK6)),k1_xboole_0)) != iProver_top
% 3.76/1.00      | r1_waybel_0(sK6,sK8(sK4(sK6)),sK2(sK6,sK8(sK4(sK6)),sK0(sK6,sK8(sK4(sK6)),k1_xboole_0))) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK8(sK4(sK6)),sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) = iProver_top
% 3.76/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.76/1.00      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.76/1.00      | v4_orders_2(sK8(sK4(sK6))) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK8(sK4(sK6))) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_12421]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_0,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_442,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_443,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_442]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8011,plain,
% 3.76/1.00      ( ~ r2_hidden(X0_58,k1_xboole_0) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_443]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12538,plain,
% 3.76/1.00      ( ~ r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8011]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12541,plain,
% 3.76/1.00      ( r2_hidden(sK0(sK6,sK8(sK4(sK6)),k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_12538]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12623,plain,
% 3.76/1.00      ( v7_waybel_0(X1_57) != iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_12479,c_1156,c_1170,c_1184,c_1198,c_8130,c_8131,c_8132,
% 3.76/1.00                 c_8133,c_9360,c_9458,c_9541,c_9681,c_9691,c_9698,c_9913,
% 3.76/1.00                 c_10239,c_10240,c_10241,c_10406,c_10446,c_10498,c_11054,
% 3.76/1.00                 c_11098,c_11171,c_12423,c_12541]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12624,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | r3_waybel_9(sK6,X1_57,sK5(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.76/1.00      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X1_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X1_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X1_57) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_12623]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8753,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK4(sK6),X0_58) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8004]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12637,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | m1_subset_1(sK5(sK6,sK3(sK6,X0_57,X0_58)),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) = iProver_top
% 3.76/1.00      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.76/1.00      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_12624,c_8753]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12724,plain,
% 3.76/1.00      ( v1_compts_1(sK6) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_12637,c_1156,c_1170,c_1184,c_1198,c_9360,c_9458,c_9541,
% 3.76/1.00                 c_9681,c_9691,c_9698,c_9913,c_10406,c_10446,c_10498,c_11054,
% 3.76/1.00                 c_11098,c_11171,c_12423,c_12541]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_17,plain,
% 3.76/1.00      ( v3_yellow_6(X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,X1)
% 3.76/1.00      | ~ v2_pre_topc(X1)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(X1)
% 3.76/1.00      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_30,negated_conjecture,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.76/1.00      | ~ v3_yellow_6(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6) ),
% 3.76/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_602,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(X1,X2)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_pre_topc(X2)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | v2_struct_0(X2)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X2)
% 3.76/1.00      | X0 != X1
% 3.76/1.00      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.76/1.00      | sK6 != X2 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_603,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | ~ v2_pre_topc(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_602]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_607,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ m2_yellow_6(X0,sK6,sK7)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_603,c_39,c_38,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_608,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_607]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8010,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57)
% 3.76/1.00      | k10_yellow_6(sK6,X0_57) = k1_xboole_0 ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_608]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8747,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8010]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_34,negated_conjecture,
% 3.76/1.00      ( ~ v1_compts_1(sK6) | ~ v2_struct_0(sK7) ),
% 3.76/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_49,plain,
% 3.76/1.00      ( v1_compts_1(sK6) != iProver_top | v2_struct_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_33,negated_conjecture,
% 3.76/1.00      ( ~ v1_compts_1(sK6) | v4_orders_2(sK7) ),
% 3.76/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_50,plain,
% 3.76/1.00      ( v1_compts_1(sK6) != iProver_top | v4_orders_2(sK7) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_32,negated_conjecture,
% 3.76/1.00      ( ~ v1_compts_1(sK6) | v7_waybel_0(sK7) ),
% 3.76/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_51,plain,
% 3.76/1.00      ( v1_compts_1(sK6) != iProver_top | v7_waybel_0(sK7) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_31,negated_conjecture,
% 3.76/1.00      ( l1_waybel_0(sK7,sK6) | ~ v1_compts_1(sK6) ),
% 3.76/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_52,plain,
% 3.76/1.00      ( l1_waybel_0(sK7,sK6) = iProver_top | v1_compts_1(sK6) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8086,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8010]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9204,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.76/1.00      | v2_struct_0(sK7)
% 3.76/1.00      | v4_orders_2(X0_57)
% 3.76/1.00      | ~ v4_orders_2(sK7)
% 3.76/1.00      | ~ v7_waybel_0(sK7) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7988]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9205,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9204]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9209,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.76/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.76/1.00      | v2_struct_0(sK7)
% 3.76/1.00      | ~ v4_orders_2(sK7)
% 3.76/1.00      | v7_waybel_0(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(sK7) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7989]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9210,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) = iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9209]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9214,plain,
% 3.76/1.00      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.76/1.00      | l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.76/1.00      | v2_struct_0(sK7)
% 3.76/1.00      | ~ v4_orders_2(sK7)
% 3.76/1.00      | ~ v7_waybel_0(sK7) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7990]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9215,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9214]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9318,plain,
% 3.76/1.00      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_8747,c_49,c_50,c_51,c_52,c_8086,c_9205,c_9210,c_9215]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9319,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.76/1.00      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_9318]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10242,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.76/1.00      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8754,c_9319]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10273,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.76/1.00      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(backward_subsumption_resolution,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_10241,c_10242]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11472,plain,
% 3.76/1.00      ( v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.76/1.00      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_10273,c_49,c_50,c_51,c_52]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11473,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.76/1.00      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_11472]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11482,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_8748,c_11473]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9195,plain,
% 3.76/1.00      ( ~ l1_waybel_0(sK7,sK6)
% 3.76/1.00      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK7)
% 3.76/1.00      | ~ v4_orders_2(sK7)
% 3.76/1.00      | ~ v7_waybel_0(sK7) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_7997]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9196,plain,
% 3.76/1.00      ( l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9195]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11655,plain,
% 3.76/1.00      ( v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_11482,c_49,c_50,c_51,c_52,c_9196]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11656,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_11655]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12729,plain,
% 3.76/1.00      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_12724,c_11656]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_21,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | ~ v2_pre_topc(X0)
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1261,plain,
% 3.76/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 3.76/1.00      | ~ l1_waybel_0(X1,X0)
% 3.76/1.00      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.76/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(X1)
% 3.76/1.00      | ~ v4_orders_2(X1)
% 3.76/1.00      | ~ v7_waybel_0(X1)
% 3.76/1.00      | ~ l1_pre_topc(X0)
% 3.76/1.00      | sK6 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1262,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | v2_struct_0(sK6)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ l1_pre_topc(sK6) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_1261]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1266,plain,
% 3.76/1.00      ( ~ v7_waybel_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0) ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_1262,c_39,c_37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1267,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.76/1.00      | ~ l1_waybel_0(X0,sK6)
% 3.76/1.00      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.76/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0)
% 3.76/1.00      | ~ v4_orders_2(X0)
% 3.76/1.00      | ~ v7_waybel_0(X0) ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_1266]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8002,plain,
% 3.76/1.00      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.76/1.00      | ~ l1_waybel_0(X0_57,sK6)
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58)))
% 3.76/1.00      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.76/1.00      | v2_struct_0(X0_57)
% 3.76/1.00      | ~ v4_orders_2(X0_57)
% 3.76/1.00      | ~ v7_waybel_0(X0_57) ),
% 3.76/1.00      inference(subtyping,[status(esa)],[c_1267]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8755,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.76/1.00      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.76/1.00      | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
% 3.76/1.00      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(X0_57) = iProver_top
% 3.76/1.00      | v4_orders_2(X0_57) != iProver_top
% 3.76/1.00      | v7_waybel_0(X0_57) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8002]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13074,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
% 3.76/1.00      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(superposition,[status(thm)],[c_12729,c_8755]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9198,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
% 3.76/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.76/1.00      | ~ v1_compts_1(sK6)
% 3.76/1.00      | v2_struct_0(sK7)
% 3.76/1.00      | ~ v4_orders_2(sK7)
% 3.76/1.00      | ~ v7_waybel_0(sK7) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8009]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9199,plain,
% 3.76/1.00      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
% 3.76/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.76/1.00      | v1_compts_1(sK6) != iProver_top
% 3.76/1.00      | v2_struct_0(sK7) = iProver_top
% 3.76/1.00      | v4_orders_2(sK7) != iProver_top
% 3.76/1.00      | v7_waybel_0(sK7) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_9198]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13158,plain,
% 3.76/1.00      ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_13074,c_49,c_50,c_51,c_52,c_1156,c_1170,c_1184,c_1198,
% 3.76/1.00                 c_9196,c_9199,c_9360,c_9458,c_9541,c_9681,c_9691,c_9698,
% 3.76/1.00                 c_9913,c_10406,c_10446,c_10498,c_11054,c_11098,c_11171,
% 3.76/1.00                 c_12423,c_12541]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8746,plain,
% 3.76/1.00      ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8011]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13163,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_13158,c_8746]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ General
% 3.76/1.00  
% 3.76/1.00  abstr_ref_over_cycles:                  0
% 3.76/1.00  abstr_ref_under_cycles:                 0
% 3.76/1.00  gc_basic_clause_elim:                   0
% 3.76/1.00  forced_gc_time:                         0
% 3.76/1.00  parsing_time:                           0.01
% 3.76/1.00  unif_index_cands_time:                  0.
% 3.76/1.00  unif_index_add_time:                    0.
% 3.76/1.00  orderings_time:                         0.
% 3.76/1.00  out_proof_time:                         0.022
% 3.76/1.00  total_time:                             0.337
% 3.76/1.00  num_of_symbols:                         61
% 3.76/1.00  num_of_terms:                           6608
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing
% 3.76/1.00  
% 3.76/1.00  num_of_splits:                          0
% 3.76/1.00  num_of_split_atoms:                     0
% 3.76/1.00  num_of_reused_defs:                     0
% 3.76/1.00  num_eq_ax_congr_red:                    46
% 3.76/1.00  num_of_sem_filtered_clauses:            1
% 3.76/1.00  num_of_subtypes:                        4
% 3.76/1.00  monotx_restored_types:                  1
% 3.76/1.00  sat_num_of_epr_types:                   0
% 3.76/1.00  sat_num_of_non_cyclic_types:            0
% 3.76/1.00  sat_guarded_non_collapsed_types:        0
% 3.76/1.00  num_pure_diseq_elim:                    0
% 3.76/1.00  simp_replaced_by:                       0
% 3.76/1.00  res_preprocessed:                       193
% 3.76/1.00  prep_upred:                             0
% 3.76/1.00  prep_unflattend:                        201
% 3.76/1.00  smt_new_axioms:                         0
% 3.76/1.00  pred_elim_cands:                        11
% 3.76/1.00  pred_elim:                              5
% 3.76/1.00  pred_elim_cl:                           6
% 3.76/1.00  pred_elim_cycles:                       17
% 3.76/1.00  merged_defs:                            0
% 3.76/1.00  merged_defs_ncl:                        0
% 3.76/1.00  bin_hyper_res:                          0
% 3.76/1.00  prep_cycles:                            4
% 3.76/1.00  pred_elim_time:                         0.123
% 3.76/1.00  splitting_time:                         0.
% 3.76/1.00  sem_filter_time:                        0.
% 3.76/1.00  monotx_time:                            0.001
% 3.76/1.00  subtype_inf_time:                       0.001
% 3.76/1.00  
% 3.76/1.00  ------ Problem properties
% 3.76/1.00  
% 3.76/1.00  clauses:                                34
% 3.76/1.00  conjectures:                            6
% 3.76/1.00  epr:                                    10
% 3.76/1.00  horn:                                   11
% 3.76/1.00  ground:                                 9
% 3.76/1.00  unary:                                  3
% 3.76/1.00  binary:                                 8
% 3.76/1.00  lits:                                   168
% 3.76/1.00  lits_eq:                                6
% 3.76/1.00  fd_pure:                                0
% 3.76/1.00  fd_pseudo:                              0
% 3.76/1.00  fd_cond:                                0
% 3.76/1.00  fd_pseudo_cond:                         4
% 3.76/1.00  ac_symbols:                             0
% 3.76/1.00  
% 3.76/1.00  ------ Propositional Solver
% 3.76/1.00  
% 3.76/1.00  prop_solver_calls:                      29
% 3.76/1.00  prop_fast_solver_calls:                 4625
% 3.76/1.00  smt_solver_calls:                       0
% 3.76/1.00  smt_fast_solver_calls:                  0
% 3.76/1.00  prop_num_of_clauses:                    2475
% 3.76/1.00  prop_preprocess_simplified:             8620
% 3.76/1.00  prop_fo_subsumed:                       160
% 3.76/1.00  prop_solver_time:                       0.
% 3.76/1.00  smt_solver_time:                        0.
% 3.76/1.00  smt_fast_solver_time:                   0.
% 3.76/1.00  prop_fast_solver_time:                  0.
% 3.76/1.00  prop_unsat_core_time:                   0.
% 3.76/1.00  
% 3.76/1.00  ------ QBF
% 3.76/1.00  
% 3.76/1.00  qbf_q_res:                              0
% 3.76/1.00  qbf_num_tautologies:                    0
% 3.76/1.00  qbf_prep_cycles:                        0
% 3.76/1.00  
% 3.76/1.00  ------ BMC1
% 3.76/1.00  
% 3.76/1.00  bmc1_current_bound:                     -1
% 3.76/1.00  bmc1_last_solved_bound:                 -1
% 3.76/1.00  bmc1_unsat_core_size:                   -1
% 3.76/1.00  bmc1_unsat_core_parents_size:           -1
% 3.76/1.00  bmc1_merge_next_fun:                    0
% 3.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.00  
% 3.76/1.00  ------ Instantiation
% 3.76/1.00  
% 3.76/1.00  inst_num_of_clauses:                    518
% 3.76/1.00  inst_num_in_passive:                    181
% 3.76/1.00  inst_num_in_active:                     331
% 3.76/1.00  inst_num_in_unprocessed:                6
% 3.76/1.00  inst_num_of_loops:                      400
% 3.76/1.00  inst_num_of_learning_restarts:          0
% 3.76/1.00  inst_num_moves_active_passive:          64
% 3.76/1.00  inst_lit_activity:                      0
% 3.76/1.00  inst_lit_activity_moves:                0
% 3.76/1.00  inst_num_tautologies:                   0
% 3.76/1.00  inst_num_prop_implied:                  0
% 3.76/1.00  inst_num_existing_simplified:           0
% 3.76/1.00  inst_num_eq_res_simplified:             0
% 3.76/1.00  inst_num_child_elim:                    0
% 3.76/1.00  inst_num_of_dismatching_blockings:      28
% 3.76/1.00  inst_num_of_non_proper_insts:           281
% 3.76/1.00  inst_num_of_duplicates:                 0
% 3.76/1.00  inst_inst_num_from_inst_to_res:         0
% 3.76/1.00  inst_dismatching_checking_time:         0.
% 3.76/1.00  
% 3.76/1.00  ------ Resolution
% 3.76/1.00  
% 3.76/1.00  res_num_of_clauses:                     0
% 3.76/1.00  res_num_in_passive:                     0
% 3.76/1.00  res_num_in_active:                      0
% 3.76/1.00  res_num_of_loops:                       197
% 3.76/1.00  res_forward_subset_subsumed:            6
% 3.76/1.00  res_backward_subset_subsumed:           0
% 3.76/1.00  res_forward_subsumed:                   0
% 3.76/1.00  res_backward_subsumed:                  0
% 3.76/1.00  res_forward_subsumption_resolution:     22
% 3.76/1.00  res_backward_subsumption_resolution:    6
% 3.76/1.00  res_clause_to_clause_subsumption:       913
% 3.76/1.00  res_orphan_elimination:                 0
% 3.76/1.00  res_tautology_del:                      37
% 3.76/1.00  res_num_eq_res_simplified:              0
% 3.76/1.00  res_num_sel_changes:                    0
% 3.76/1.00  res_moves_from_active_to_pass:          0
% 3.76/1.00  
% 3.76/1.00  ------ Superposition
% 3.76/1.00  
% 3.76/1.00  sup_time_total:                         0.
% 3.76/1.00  sup_time_generating:                    0.
% 3.76/1.00  sup_time_sim_full:                      0.
% 3.76/1.00  sup_time_sim_immed:                     0.
% 3.76/1.00  
% 3.76/1.00  sup_num_of_clauses:                     89
% 3.76/1.00  sup_num_in_active:                      71
% 3.76/1.00  sup_num_in_passive:                     18
% 3.76/1.00  sup_num_of_loops:                       78
% 3.76/1.00  sup_fw_superposition:                   23
% 3.76/1.00  sup_bw_superposition:                   57
% 3.76/1.00  sup_immediate_simplified:               10
% 3.76/1.00  sup_given_eliminated:                   0
% 3.76/1.00  comparisons_done:                       0
% 3.76/1.00  comparisons_avoided:                    0
% 3.76/1.00  
% 3.76/1.00  ------ Simplifications
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  sim_fw_subset_subsumed:                 5
% 3.76/1.00  sim_bw_subset_subsumed:                 8
% 3.76/1.00  sim_fw_subsumed:                        4
% 3.76/1.00  sim_bw_subsumed:                        0
% 3.76/1.00  sim_fw_subsumption_res:                 11
% 3.76/1.00  sim_bw_subsumption_res:                 1
% 3.76/1.00  sim_tautology_del:                      10
% 3.76/1.00  sim_eq_tautology_del:                   0
% 3.76/1.00  sim_eq_res_simp:                        0
% 3.76/1.00  sim_fw_demodulated:                     0
% 3.76/1.00  sim_bw_demodulated:                     0
% 3.76/1.00  sim_light_normalised:                   2
% 3.76/1.00  sim_joinable_taut:                      0
% 3.76/1.00  sim_joinable_simp:                      0
% 3.76/1.00  sim_ac_normalised:                      0
% 3.76/1.00  sim_smt_subsumption:                    0
% 3.76/1.00  
%------------------------------------------------------------------------------
