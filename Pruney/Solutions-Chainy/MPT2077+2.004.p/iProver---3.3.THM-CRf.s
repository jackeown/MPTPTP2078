%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:25 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_61)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f80,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f87,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f77,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK4)
      | ~ m2_yellow_6(X2,sK4,sK5)
      | ~ v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,
    ( ~ v2_struct_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,
    ( v4_orders_2(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,
    ( v7_waybel_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f72,plain,(
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

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f89,plain,(
    ! [X3] :
      ( m2_yellow_6(sK6(X3),sK4,X3)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f27])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f76,plain,(
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

fof(f85,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X3] :
      ( v3_yellow_6(sK6(X3),sK4)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
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

fof(f78,plain,(
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

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5102,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_653,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_654,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_658,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_37,c_35])).

cnf(c_659,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_5092,plain,
    ( r3_waybel_9(sK4,X0,sK3(sK4,X0)) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_760,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_761,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_765,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_37,c_35])).

cnf(c_766,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_765])).

cnf(c_5086,plain,
    ( r3_waybel_9(sK4,X0,X1) != iProver_top
    | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

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
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ v3_yellow_6(X0,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_557,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_558,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4)
    | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_562,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m2_yellow_6(X0,sK4,sK5)
    | v2_struct_0(X0)
    | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_37,c_36,c_35])).

cnf(c_563,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_562])).

cnf(c_5093,plain,
    ( k10_yellow_6(sK4,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK4,sK5) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_32,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_47,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_48,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v4_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v7_waybel_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_50,plain,
    ( l1_waybel_0(sK5,sK4) = iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_564,plain,
    ( k10_yellow_6(sK4,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK4,sK5) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_492,plain,
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

cnf(c_493,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1017,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_493,c_35])).

cnf(c_1018,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X0,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_1020,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_37])).

cnf(c_1021,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X0,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1020])).

cnf(c_5186,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_5187,plain,
    ( m2_yellow_6(X0,sK4,sK5) != iProver_top
    | l1_waybel_0(X0,sK4) = iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5186])).

cnf(c_12,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_464,plain,
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

cnf(c_465,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1043,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_35])).

cnf(c_1044,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1046,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_37])).

cnf(c_1047,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1046])).

cnf(c_5191,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_5192,plain,
    ( m2_yellow_6(X0,sK4,sK5) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5191])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_436,plain,
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

cnf(c_437,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_1069,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_437,c_35])).

cnf(c_1070,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_1072,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1070,c_37])).

cnf(c_1073,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1072])).

cnf(c_5196,plain,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ l1_waybel_0(sK5,sK4)
    | v2_struct_0(sK5)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_5197,plain,
    ( m2_yellow_6(X0,sK4,sK5) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5196])).

cnf(c_6142,plain,
    ( m2_yellow_6(X0,sK4,sK5) != iProver_top
    | k10_yellow_6(sK4,X0) = k1_xboole_0
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5093,c_47,c_48,c_49,c_50,c_564,c_5187,c_5192,c_5197])).

cnf(c_6143,plain,
    ( k10_yellow_6(sK4,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK4,sK5) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6142])).

cnf(c_6262,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5086,c_6143])).

cnf(c_7479,plain,
    ( v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top
    | v1_compts_1(sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6262,c_47,c_48,c_49,c_50])).

cnf(c_7480,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7479])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_408,plain,
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

cnf(c_409,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1095,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_409,c_35])).

cnf(c_1096,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1098,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK4)
    | ~ m2_yellow_6(X0,sK4,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_37])).

cnf(c_1099,plain,
    ( ~ m2_yellow_6(X0,sK4,X1)
    | ~ l1_waybel_0(X1,sK4)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1098])).

cnf(c_5077,plain,
    ( m2_yellow_6(X0,sK4,X1) != iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_6266,plain,
    ( r3_waybel_9(sK4,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK4,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5086,c_5077])).

cnf(c_7485,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7480,c_6266])).

cnf(c_34,negated_conjecture,
    ( m2_yellow_6(sK6(X0),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5095,plain,
    ( m2_yellow_6(sK6(X0),sK4,X0) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5106,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_921,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_36])).

cnf(c_922,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_926,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_37,c_35])).

cnf(c_927,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_926])).

cnf(c_5081,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5101,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6021,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5081,c_5101])).

cnf(c_6556,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,X0),X1),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5106,c_6021])).

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
    inference(cnf_transformation,[],[f75])).

cnf(c_858,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_859,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_863,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_37,c_35])).

cnf(c_864,plain,
    ( r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_863])).

cnf(c_5083,plain,
    ( r3_waybel_9(sK4,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_865,plain,
    ( r3_waybel_9(sK4,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_6171,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | r3_waybel_9(sK4,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5083,c_865,c_6021])).

cnf(c_6172,plain,
    ( r3_waybel_9(sK4,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6171])).

cnf(c_6177,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0),X1)) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5106,c_6172])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_826,plain,
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
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_827,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_829,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_37,c_35])).

cnf(c_830,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | r3_waybel_9(sK4,X2,X1)
    | ~ m2_yellow_6(X0,sK4,X2)
    | ~ l1_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_829])).

cnf(c_5084,plain,
    ( r3_waybel_9(sK4,X0,X1) != iProver_top
    | r3_waybel_9(sK4,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK4,X2) != iProver_top
    | l1_waybel_0(X2,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_6764,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK4,X0) != iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,X1),X2),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6177,c_5084])).

cnf(c_8008,plain,
    ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK4,X0) != iProver_top
    | l1_waybel_0(X1,sK4) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6556,c_6764])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,sK2(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_739,plain,
    ( ~ r3_waybel_9(X0,sK2(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_740,plain,
    ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_744,plain,
    ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_37,c_35])).

cnf(c_5087,plain,
    ( r3_waybel_9(sK4,sK2(sK4),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_8337,plain,
    ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK4,X0),X1),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8008,c_5087])).

cnf(c_25,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_683,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_684,plain,
    ( v1_compts_1(sK4)
    | ~ v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_686,plain,
    ( v1_compts_1(sK4)
    | ~ v2_struct_0(sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_37,c_36,c_35,c_61])).

cnf(c_688,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_24,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_697,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK2(X0))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_698,plain,
    ( v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | v4_orders_2(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_700,plain,
    ( v4_orders_2(sK2(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_37,c_35])).

cnf(c_701,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK2(sK4)) ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_702,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v4_orders_2(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_23,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_711,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK2(X0))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_712,plain,
    ( v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | v7_waybel_0(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_714,plain,
    ( v7_waybel_0(sK2(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_37,c_35])).

cnf(c_715,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK2(sK4)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_716,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v7_waybel_0(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_22,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_725,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_726,plain,
    ( l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_725])).

cnf(c_728,plain,
    ( l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_726,c_37,c_35])).

cnf(c_730,plain,
    ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_5299,plain,
    ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
    | l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_5300,plain,
    ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(X0,sK4) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5299])).

cnf(c_5298,plain,
    ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_5304,plain,
    ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5298])).

cnf(c_5297,plain,
    ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
    | ~ l1_waybel_0(sK2(sK4),sK4)
    | v2_struct_0(sK2(sK4))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_5308,plain,
    ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5297])).

cnf(c_8405,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
    | m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8337,c_688,c_702,c_716,c_730,c_5300,c_5304,c_5308,c_6556])).

cnf(c_8406,plain,
    ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8405])).

cnf(c_8411,plain,
    ( l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_8406])).

cnf(c_5088,plain,
    ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_5469,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5095,c_5077])).

cnf(c_5753,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5088,c_5469])).

cnf(c_6509,plain,
    ( v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5753,c_688,c_702,c_716])).

cnf(c_6510,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6509])).

cnf(c_8417,plain,
    ( r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8411,c_688,c_702,c_716,c_730,c_6510])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5104,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5952,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5102,c_5104])).

cnf(c_8426,plain,
    ( k10_yellow_6(sK4,sK6(sK2(sK4))) = k1_xboole_0
    | v1_compts_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_8417,c_5952])).

cnf(c_1289,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | l1_waybel_0(X2,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK6(X1) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1021])).

cnf(c_1290,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1289])).

cnf(c_1265,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(X2)
    | X0 != X1
    | sK6(X1) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1047])).

cnf(c_1266,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0)) ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1241,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK6(X1) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1073])).

cnf(c_1242,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1241])).

cnf(c_1217,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(X1,sK4)
    | v1_compts_1(sK4)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | sK6(X1) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1099])).

cnf(c_1218,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1217])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( v3_yellow_6(sK6(X0),sK4)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_590,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK4)
    | v1_compts_1(sK4)
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
    | sK6(X2) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_591,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | ~ l1_pre_topc(sK4)
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( ~ v7_waybel_0(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_37,c_36,c_35])).

cnf(c_596,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_1472,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1218,c_596])).

cnf(c_1483,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(X0))
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1242,c_1472])).

cnf(c_1494,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ l1_waybel_0(sK6(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1266,c_1483])).

cnf(c_1500,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1290,c_1494])).

cnf(c_5422,plain,
    ( ~ l1_waybel_0(sK2(sK4),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK2(sK4))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4))
    | k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_5423,plain,
    ( k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5422])).

cnf(c_8482,plain,
    ( v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8426,c_688,c_702,c_716,c_730,c_5423])).

cnf(c_8652,plain,
    ( r3_waybel_9(sK4,sK5,X0) != iProver_top
    | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7485,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5423,c_8426])).

cnf(c_8653,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8652])).

cnf(c_8658,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5092,c_8653])).

cnf(c_27,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_891,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_892,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_896,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_37,c_35])).

cnf(c_897,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_896])).

cnf(c_5172,plain,
    ( ~ l1_waybel_0(sK5,sK4)
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_5173,plain,
    ( l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5172])).

cnf(c_9391,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8658,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5173,c_5423,c_8426])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_793,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_794,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_798,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_37,c_35])).

cnf(c_799,plain,
    ( ~ r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_798])).

cnf(c_5085,plain,
    ( r3_waybel_9(sK4,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_9404,plain,
    ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9391,c_5085])).

cnf(c_5183,plain,
    ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5))
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_5184,plain,
    ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) = iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5183])).

cnf(c_9476,plain,
    ( r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9404,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5173,c_5184,c_5423,c_8426])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5100,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9481,plain,
    ( r1_tarski(k1_xboole_0,sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9476,c_5100])).

cnf(c_9905,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5102,c_9481])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.80/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/0.96  
% 3.80/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/0.96  
% 3.80/0.96  ------  iProver source info
% 3.80/0.96  
% 3.80/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.80/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/0.96  git: non_committed_changes: false
% 3.80/0.96  git: last_make_outside_of_git: false
% 3.80/0.96  
% 3.80/0.96  ------ 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options
% 3.80/0.96  
% 3.80/0.96  --out_options                           all
% 3.80/0.96  --tptp_safe_out                         true
% 3.80/0.96  --problem_path                          ""
% 3.80/0.96  --include_path                          ""
% 3.80/0.96  --clausifier                            res/vclausify_rel
% 3.80/0.96  --clausifier_options                    ""
% 3.80/0.96  --stdin                                 false
% 3.80/0.96  --stats_out                             all
% 3.80/0.96  
% 3.80/0.96  ------ General Options
% 3.80/0.96  
% 3.80/0.96  --fof                                   false
% 3.80/0.96  --time_out_real                         305.
% 3.80/0.96  --time_out_virtual                      -1.
% 3.80/0.96  --symbol_type_check                     false
% 3.80/0.96  --clausify_out                          false
% 3.80/0.96  --sig_cnt_out                           false
% 3.80/0.96  --trig_cnt_out                          false
% 3.80/0.96  --trig_cnt_out_tolerance                1.
% 3.80/0.96  --trig_cnt_out_sk_spl                   false
% 3.80/0.96  --abstr_cl_out                          false
% 3.80/0.96  
% 3.80/0.96  ------ Global Options
% 3.80/0.96  
% 3.80/0.96  --schedule                              default
% 3.80/0.96  --add_important_lit                     false
% 3.80/0.96  --prop_solver_per_cl                    1000
% 3.80/0.96  --min_unsat_core                        false
% 3.80/0.96  --soft_assumptions                      false
% 3.80/0.96  --soft_lemma_size                       3
% 3.80/0.96  --prop_impl_unit_size                   0
% 3.80/0.96  --prop_impl_unit                        []
% 3.80/0.96  --share_sel_clauses                     true
% 3.80/0.96  --reset_solvers                         false
% 3.80/0.96  --bc_imp_inh                            [conj_cone]
% 3.80/0.96  --conj_cone_tolerance                   3.
% 3.80/0.96  --extra_neg_conj                        none
% 3.80/0.96  --large_theory_mode                     true
% 3.80/0.96  --prolific_symb_bound                   200
% 3.80/0.96  --lt_threshold                          2000
% 3.80/0.96  --clause_weak_htbl                      true
% 3.80/0.96  --gc_record_bc_elim                     false
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing Options
% 3.80/0.96  
% 3.80/0.96  --preprocessing_flag                    true
% 3.80/0.96  --time_out_prep_mult                    0.1
% 3.80/0.96  --splitting_mode                        input
% 3.80/0.96  --splitting_grd                         true
% 3.80/0.96  --splitting_cvd                         false
% 3.80/0.96  --splitting_cvd_svl                     false
% 3.80/0.96  --splitting_nvd                         32
% 3.80/0.96  --sub_typing                            true
% 3.80/0.96  --prep_gs_sim                           true
% 3.80/0.96  --prep_unflatten                        true
% 3.80/0.96  --prep_res_sim                          true
% 3.80/0.96  --prep_upred                            true
% 3.80/0.96  --prep_sem_filter                       exhaustive
% 3.80/0.96  --prep_sem_filter_out                   false
% 3.80/0.96  --pred_elim                             true
% 3.80/0.96  --res_sim_input                         true
% 3.80/0.96  --eq_ax_congr_red                       true
% 3.80/0.96  --pure_diseq_elim                       true
% 3.80/0.96  --brand_transform                       false
% 3.80/0.96  --non_eq_to_eq                          false
% 3.80/0.96  --prep_def_merge                        true
% 3.80/0.96  --prep_def_merge_prop_impl              false
% 3.80/0.96  --prep_def_merge_mbd                    true
% 3.80/0.96  --prep_def_merge_tr_red                 false
% 3.80/0.96  --prep_def_merge_tr_cl                  false
% 3.80/0.96  --smt_preprocessing                     true
% 3.80/0.96  --smt_ac_axioms                         fast
% 3.80/0.96  --preprocessed_out                      false
% 3.80/0.96  --preprocessed_stats                    false
% 3.80/0.96  
% 3.80/0.96  ------ Abstraction refinement Options
% 3.80/0.96  
% 3.80/0.96  --abstr_ref                             []
% 3.80/0.96  --abstr_ref_prep                        false
% 3.80/0.96  --abstr_ref_until_sat                   false
% 3.80/0.96  --abstr_ref_sig_restrict                funpre
% 3.80/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.96  --abstr_ref_under                       []
% 3.80/0.96  
% 3.80/0.96  ------ SAT Options
% 3.80/0.96  
% 3.80/0.96  --sat_mode                              false
% 3.80/0.96  --sat_fm_restart_options                ""
% 3.80/0.96  --sat_gr_def                            false
% 3.80/0.96  --sat_epr_types                         true
% 3.80/0.96  --sat_non_cyclic_types                  false
% 3.80/0.96  --sat_finite_models                     false
% 3.80/0.96  --sat_fm_lemmas                         false
% 3.80/0.96  --sat_fm_prep                           false
% 3.80/0.96  --sat_fm_uc_incr                        true
% 3.80/0.96  --sat_out_model                         small
% 3.80/0.96  --sat_out_clauses                       false
% 3.80/0.96  
% 3.80/0.96  ------ QBF Options
% 3.80/0.96  
% 3.80/0.96  --qbf_mode                              false
% 3.80/0.96  --qbf_elim_univ                         false
% 3.80/0.96  --qbf_dom_inst                          none
% 3.80/0.96  --qbf_dom_pre_inst                      false
% 3.80/0.96  --qbf_sk_in                             false
% 3.80/0.96  --qbf_pred_elim                         true
% 3.80/0.96  --qbf_split                             512
% 3.80/0.96  
% 3.80/0.96  ------ BMC1 Options
% 3.80/0.96  
% 3.80/0.96  --bmc1_incremental                      false
% 3.80/0.96  --bmc1_axioms                           reachable_all
% 3.80/0.96  --bmc1_min_bound                        0
% 3.80/0.96  --bmc1_max_bound                        -1
% 3.80/0.96  --bmc1_max_bound_default                -1
% 3.80/0.96  --bmc1_symbol_reachability              true
% 3.80/0.96  --bmc1_property_lemmas                  false
% 3.80/0.96  --bmc1_k_induction                      false
% 3.80/0.96  --bmc1_non_equiv_states                 false
% 3.80/0.96  --bmc1_deadlock                         false
% 3.80/0.96  --bmc1_ucm                              false
% 3.80/0.96  --bmc1_add_unsat_core                   none
% 3.80/0.96  --bmc1_unsat_core_children              false
% 3.80/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.96  --bmc1_out_stat                         full
% 3.80/0.96  --bmc1_ground_init                      false
% 3.80/0.96  --bmc1_pre_inst_next_state              false
% 3.80/0.96  --bmc1_pre_inst_state                   false
% 3.80/0.96  --bmc1_pre_inst_reach_state             false
% 3.80/0.96  --bmc1_out_unsat_core                   false
% 3.80/0.96  --bmc1_aig_witness_out                  false
% 3.80/0.96  --bmc1_verbose                          false
% 3.80/0.96  --bmc1_dump_clauses_tptp                false
% 3.80/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.96  --bmc1_dump_file                        -
% 3.80/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.96  --bmc1_ucm_extend_mode                  1
% 3.80/0.96  --bmc1_ucm_init_mode                    2
% 3.80/0.96  --bmc1_ucm_cone_mode                    none
% 3.80/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.96  --bmc1_ucm_relax_model                  4
% 3.80/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.96  --bmc1_ucm_layered_model                none
% 3.80/0.96  --bmc1_ucm_max_lemma_size               10
% 3.80/0.96  
% 3.80/0.96  ------ AIG Options
% 3.80/0.96  
% 3.80/0.96  --aig_mode                              false
% 3.80/0.96  
% 3.80/0.96  ------ Instantiation Options
% 3.80/0.96  
% 3.80/0.96  --instantiation_flag                    true
% 3.80/0.96  --inst_sos_flag                         true
% 3.80/0.96  --inst_sos_phase                        true
% 3.80/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel_side                     num_symb
% 3.80/0.96  --inst_solver_per_active                1400
% 3.80/0.96  --inst_solver_calls_frac                1.
% 3.80/0.96  --inst_passive_queue_type               priority_queues
% 3.80/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.96  --inst_passive_queues_freq              [25;2]
% 3.80/0.96  --inst_dismatching                      true
% 3.80/0.96  --inst_eager_unprocessed_to_passive     true
% 3.80/0.96  --inst_prop_sim_given                   true
% 3.80/0.96  --inst_prop_sim_new                     false
% 3.80/0.96  --inst_subs_new                         false
% 3.80/0.96  --inst_eq_res_simp                      false
% 3.80/0.96  --inst_subs_given                       false
% 3.80/0.96  --inst_orphan_elimination               true
% 3.80/0.96  --inst_learning_loop_flag               true
% 3.80/0.96  --inst_learning_start                   3000
% 3.80/0.96  --inst_learning_factor                  2
% 3.80/0.96  --inst_start_prop_sim_after_learn       3
% 3.80/0.96  --inst_sel_renew                        solver
% 3.80/0.96  --inst_lit_activity_flag                true
% 3.80/0.96  --inst_restr_to_given                   false
% 3.80/0.96  --inst_activity_threshold               500
% 3.80/0.96  --inst_out_proof                        true
% 3.80/0.96  
% 3.80/0.96  ------ Resolution Options
% 3.80/0.96  
% 3.80/0.96  --resolution_flag                       true
% 3.80/0.96  --res_lit_sel                           adaptive
% 3.80/0.96  --res_lit_sel_side                      none
% 3.80/0.96  --res_ordering                          kbo
% 3.80/0.96  --res_to_prop_solver                    active
% 3.80/0.96  --res_prop_simpl_new                    false
% 3.80/0.96  --res_prop_simpl_given                  true
% 3.80/0.96  --res_passive_queue_type                priority_queues
% 3.80/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.96  --res_passive_queues_freq               [15;5]
% 3.80/0.96  --res_forward_subs                      full
% 3.80/0.96  --res_backward_subs                     full
% 3.80/0.96  --res_forward_subs_resolution           true
% 3.80/0.96  --res_backward_subs_resolution          true
% 3.80/0.96  --res_orphan_elimination                true
% 3.80/0.96  --res_time_limit                        2.
% 3.80/0.96  --res_out_proof                         true
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Options
% 3.80/0.96  
% 3.80/0.96  --superposition_flag                    true
% 3.80/0.96  --sup_passive_queue_type                priority_queues
% 3.80/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.96  --demod_completeness_check              fast
% 3.80/0.96  --demod_use_ground                      true
% 3.80/0.96  --sup_to_prop_solver                    passive
% 3.80/0.96  --sup_prop_simpl_new                    true
% 3.80/0.96  --sup_prop_simpl_given                  true
% 3.80/0.96  --sup_fun_splitting                     true
% 3.80/0.96  --sup_smt_interval                      50000
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Simplification Setup
% 3.80/0.96  
% 3.80/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_immed_triv                        [TrivRules]
% 3.80/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_bw_main                     []
% 3.80/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_input_bw                          []
% 3.80/0.96  
% 3.80/0.96  ------ Combination Options
% 3.80/0.96  
% 3.80/0.96  --comb_res_mult                         3
% 3.80/0.96  --comb_sup_mult                         2
% 3.80/0.96  --comb_inst_mult                        10
% 3.80/0.96  
% 3.80/0.96  ------ Debug Options
% 3.80/0.96  
% 3.80/0.96  --dbg_backtrace                         false
% 3.80/0.96  --dbg_dump_prop_clauses                 false
% 3.80/0.96  --dbg_dump_prop_clauses_file            -
% 3.80/0.96  --dbg_out_stat                          false
% 3.80/0.96  ------ Parsing...
% 3.80/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/0.96  ------ Proving...
% 3.80/0.96  ------ Problem Properties 
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  clauses                                 32
% 3.80/0.96  conjectures                             6
% 3.80/0.96  EPR                                     14
% 3.80/0.96  Horn                                    15
% 3.80/0.96  unary                                   3
% 3.80/0.96  binary                                  11
% 3.80/0.96  lits                                    126
% 3.80/0.96  lits eq                                 3
% 3.80/0.96  fd_pure                                 0
% 3.80/0.96  fd_pseudo                               0
% 3.80/0.96  fd_cond                                 0
% 3.80/0.96  fd_pseudo_cond                          1
% 3.80/0.96  AC symbols                              0
% 3.80/0.96  
% 3.80/0.96  ------ Schedule dynamic 5 is on 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  ------ 
% 3.80/0.96  Current options:
% 3.80/0.96  ------ 
% 3.80/0.96  
% 3.80/0.96  ------ Input Options
% 3.80/0.96  
% 3.80/0.96  --out_options                           all
% 3.80/0.96  --tptp_safe_out                         true
% 3.80/0.96  --problem_path                          ""
% 3.80/0.96  --include_path                          ""
% 3.80/0.96  --clausifier                            res/vclausify_rel
% 3.80/0.96  --clausifier_options                    ""
% 3.80/0.96  --stdin                                 false
% 3.80/0.96  --stats_out                             all
% 3.80/0.96  
% 3.80/0.96  ------ General Options
% 3.80/0.96  
% 3.80/0.96  --fof                                   false
% 3.80/0.96  --time_out_real                         305.
% 3.80/0.96  --time_out_virtual                      -1.
% 3.80/0.96  --symbol_type_check                     false
% 3.80/0.96  --clausify_out                          false
% 3.80/0.96  --sig_cnt_out                           false
% 3.80/0.96  --trig_cnt_out                          false
% 3.80/0.96  --trig_cnt_out_tolerance                1.
% 3.80/0.96  --trig_cnt_out_sk_spl                   false
% 3.80/0.96  --abstr_cl_out                          false
% 3.80/0.96  
% 3.80/0.96  ------ Global Options
% 3.80/0.96  
% 3.80/0.96  --schedule                              default
% 3.80/0.96  --add_important_lit                     false
% 3.80/0.96  --prop_solver_per_cl                    1000
% 3.80/0.96  --min_unsat_core                        false
% 3.80/0.96  --soft_assumptions                      false
% 3.80/0.96  --soft_lemma_size                       3
% 3.80/0.96  --prop_impl_unit_size                   0
% 3.80/0.96  --prop_impl_unit                        []
% 3.80/0.96  --share_sel_clauses                     true
% 3.80/0.96  --reset_solvers                         false
% 3.80/0.96  --bc_imp_inh                            [conj_cone]
% 3.80/0.96  --conj_cone_tolerance                   3.
% 3.80/0.96  --extra_neg_conj                        none
% 3.80/0.96  --large_theory_mode                     true
% 3.80/0.96  --prolific_symb_bound                   200
% 3.80/0.96  --lt_threshold                          2000
% 3.80/0.96  --clause_weak_htbl                      true
% 3.80/0.96  --gc_record_bc_elim                     false
% 3.80/0.96  
% 3.80/0.96  ------ Preprocessing Options
% 3.80/0.96  
% 3.80/0.96  --preprocessing_flag                    true
% 3.80/0.96  --time_out_prep_mult                    0.1
% 3.80/0.96  --splitting_mode                        input
% 3.80/0.96  --splitting_grd                         true
% 3.80/0.96  --splitting_cvd                         false
% 3.80/0.96  --splitting_cvd_svl                     false
% 3.80/0.96  --splitting_nvd                         32
% 3.80/0.96  --sub_typing                            true
% 3.80/0.96  --prep_gs_sim                           true
% 3.80/0.96  --prep_unflatten                        true
% 3.80/0.96  --prep_res_sim                          true
% 3.80/0.96  --prep_upred                            true
% 3.80/0.96  --prep_sem_filter                       exhaustive
% 3.80/0.96  --prep_sem_filter_out                   false
% 3.80/0.96  --pred_elim                             true
% 3.80/0.96  --res_sim_input                         true
% 3.80/0.96  --eq_ax_congr_red                       true
% 3.80/0.96  --pure_diseq_elim                       true
% 3.80/0.96  --brand_transform                       false
% 3.80/0.96  --non_eq_to_eq                          false
% 3.80/0.96  --prep_def_merge                        true
% 3.80/0.96  --prep_def_merge_prop_impl              false
% 3.80/0.96  --prep_def_merge_mbd                    true
% 3.80/0.96  --prep_def_merge_tr_red                 false
% 3.80/0.96  --prep_def_merge_tr_cl                  false
% 3.80/0.96  --smt_preprocessing                     true
% 3.80/0.96  --smt_ac_axioms                         fast
% 3.80/0.96  --preprocessed_out                      false
% 3.80/0.96  --preprocessed_stats                    false
% 3.80/0.96  
% 3.80/0.96  ------ Abstraction refinement Options
% 3.80/0.96  
% 3.80/0.96  --abstr_ref                             []
% 3.80/0.96  --abstr_ref_prep                        false
% 3.80/0.96  --abstr_ref_until_sat                   false
% 3.80/0.96  --abstr_ref_sig_restrict                funpre
% 3.80/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/0.96  --abstr_ref_under                       []
% 3.80/0.96  
% 3.80/0.96  ------ SAT Options
% 3.80/0.96  
% 3.80/0.96  --sat_mode                              false
% 3.80/0.96  --sat_fm_restart_options                ""
% 3.80/0.96  --sat_gr_def                            false
% 3.80/0.96  --sat_epr_types                         true
% 3.80/0.96  --sat_non_cyclic_types                  false
% 3.80/0.96  --sat_finite_models                     false
% 3.80/0.96  --sat_fm_lemmas                         false
% 3.80/0.96  --sat_fm_prep                           false
% 3.80/0.96  --sat_fm_uc_incr                        true
% 3.80/0.96  --sat_out_model                         small
% 3.80/0.96  --sat_out_clauses                       false
% 3.80/0.96  
% 3.80/0.96  ------ QBF Options
% 3.80/0.96  
% 3.80/0.96  --qbf_mode                              false
% 3.80/0.96  --qbf_elim_univ                         false
% 3.80/0.96  --qbf_dom_inst                          none
% 3.80/0.96  --qbf_dom_pre_inst                      false
% 3.80/0.96  --qbf_sk_in                             false
% 3.80/0.96  --qbf_pred_elim                         true
% 3.80/0.96  --qbf_split                             512
% 3.80/0.96  
% 3.80/0.96  ------ BMC1 Options
% 3.80/0.96  
% 3.80/0.96  --bmc1_incremental                      false
% 3.80/0.96  --bmc1_axioms                           reachable_all
% 3.80/0.96  --bmc1_min_bound                        0
% 3.80/0.96  --bmc1_max_bound                        -1
% 3.80/0.96  --bmc1_max_bound_default                -1
% 3.80/0.96  --bmc1_symbol_reachability              true
% 3.80/0.96  --bmc1_property_lemmas                  false
% 3.80/0.96  --bmc1_k_induction                      false
% 3.80/0.96  --bmc1_non_equiv_states                 false
% 3.80/0.96  --bmc1_deadlock                         false
% 3.80/0.96  --bmc1_ucm                              false
% 3.80/0.96  --bmc1_add_unsat_core                   none
% 3.80/0.96  --bmc1_unsat_core_children              false
% 3.80/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/0.96  --bmc1_out_stat                         full
% 3.80/0.96  --bmc1_ground_init                      false
% 3.80/0.96  --bmc1_pre_inst_next_state              false
% 3.80/0.96  --bmc1_pre_inst_state                   false
% 3.80/0.96  --bmc1_pre_inst_reach_state             false
% 3.80/0.96  --bmc1_out_unsat_core                   false
% 3.80/0.96  --bmc1_aig_witness_out                  false
% 3.80/0.96  --bmc1_verbose                          false
% 3.80/0.96  --bmc1_dump_clauses_tptp                false
% 3.80/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.80/0.96  --bmc1_dump_file                        -
% 3.80/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.80/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.80/0.96  --bmc1_ucm_extend_mode                  1
% 3.80/0.96  --bmc1_ucm_init_mode                    2
% 3.80/0.96  --bmc1_ucm_cone_mode                    none
% 3.80/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.80/0.96  --bmc1_ucm_relax_model                  4
% 3.80/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.80/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/0.96  --bmc1_ucm_layered_model                none
% 3.80/0.96  --bmc1_ucm_max_lemma_size               10
% 3.80/0.96  
% 3.80/0.96  ------ AIG Options
% 3.80/0.96  
% 3.80/0.96  --aig_mode                              false
% 3.80/0.96  
% 3.80/0.96  ------ Instantiation Options
% 3.80/0.96  
% 3.80/0.96  --instantiation_flag                    true
% 3.80/0.96  --inst_sos_flag                         true
% 3.80/0.96  --inst_sos_phase                        true
% 3.80/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/0.96  --inst_lit_sel_side                     none
% 3.80/0.96  --inst_solver_per_active                1400
% 3.80/0.96  --inst_solver_calls_frac                1.
% 3.80/0.96  --inst_passive_queue_type               priority_queues
% 3.80/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/0.96  --inst_passive_queues_freq              [25;2]
% 3.80/0.96  --inst_dismatching                      true
% 3.80/0.96  --inst_eager_unprocessed_to_passive     true
% 3.80/0.96  --inst_prop_sim_given                   true
% 3.80/0.96  --inst_prop_sim_new                     false
% 3.80/0.96  --inst_subs_new                         false
% 3.80/0.96  --inst_eq_res_simp                      false
% 3.80/0.96  --inst_subs_given                       false
% 3.80/0.96  --inst_orphan_elimination               true
% 3.80/0.96  --inst_learning_loop_flag               true
% 3.80/0.96  --inst_learning_start                   3000
% 3.80/0.96  --inst_learning_factor                  2
% 3.80/0.96  --inst_start_prop_sim_after_learn       3
% 3.80/0.96  --inst_sel_renew                        solver
% 3.80/0.96  --inst_lit_activity_flag                true
% 3.80/0.96  --inst_restr_to_given                   false
% 3.80/0.96  --inst_activity_threshold               500
% 3.80/0.96  --inst_out_proof                        true
% 3.80/0.96  
% 3.80/0.96  ------ Resolution Options
% 3.80/0.96  
% 3.80/0.96  --resolution_flag                       false
% 3.80/0.96  --res_lit_sel                           adaptive
% 3.80/0.96  --res_lit_sel_side                      none
% 3.80/0.96  --res_ordering                          kbo
% 3.80/0.96  --res_to_prop_solver                    active
% 3.80/0.96  --res_prop_simpl_new                    false
% 3.80/0.96  --res_prop_simpl_given                  true
% 3.80/0.96  --res_passive_queue_type                priority_queues
% 3.80/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/0.96  --res_passive_queues_freq               [15;5]
% 3.80/0.96  --res_forward_subs                      full
% 3.80/0.96  --res_backward_subs                     full
% 3.80/0.96  --res_forward_subs_resolution           true
% 3.80/0.96  --res_backward_subs_resolution          true
% 3.80/0.96  --res_orphan_elimination                true
% 3.80/0.96  --res_time_limit                        2.
% 3.80/0.96  --res_out_proof                         true
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Options
% 3.80/0.96  
% 3.80/0.96  --superposition_flag                    true
% 3.80/0.96  --sup_passive_queue_type                priority_queues
% 3.80/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.80/0.96  --demod_completeness_check              fast
% 3.80/0.96  --demod_use_ground                      true
% 3.80/0.96  --sup_to_prop_solver                    passive
% 3.80/0.96  --sup_prop_simpl_new                    true
% 3.80/0.96  --sup_prop_simpl_given                  true
% 3.80/0.96  --sup_fun_splitting                     true
% 3.80/0.96  --sup_smt_interval                      50000
% 3.80/0.96  
% 3.80/0.96  ------ Superposition Simplification Setup
% 3.80/0.96  
% 3.80/0.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.80/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.80/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.80/0.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_immed_triv                        [TrivRules]
% 3.80/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_immed_bw_main                     []
% 3.80/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.80/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/0.96  --sup_input_bw                          []
% 3.80/0.96  
% 3.80/0.96  ------ Combination Options
% 3.80/0.96  
% 3.80/0.96  --comb_res_mult                         3
% 3.80/0.96  --comb_sup_mult                         2
% 3.80/0.96  --comb_inst_mult                        10
% 3.80/0.96  
% 3.80/0.96  ------ Debug Options
% 3.80/0.96  
% 3.80/0.96  --dbg_backtrace                         false
% 3.80/0.96  --dbg_dump_prop_clauses                 false
% 3.80/0.96  --dbg_dump_prop_clauses_file            -
% 3.80/0.96  --dbg_out_stat                          false
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  ------ Proving...
% 3.80/0.96  
% 3.80/0.96  
% 3.80/0.96  % SZS status Theorem for theBenchmark.p
% 3.80/0.96  
% 3.80/0.96   Resolution empty clause
% 3.80/0.96  
% 3.80/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/0.96  
% 3.80/0.96  fof(f3,axiom,(
% 3.80/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f64,plain,(
% 3.80/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f3])).
% 3.80/0.96  
% 3.80/0.96  fof(f13,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f33,plain,(
% 3.80/0.96    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f13])).
% 3.80/0.96  
% 3.80/0.96  fof(f34,plain,(
% 3.80/0.96    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f33])).
% 3.80/0.96  
% 3.80/0.96  fof(f46,plain,(
% 3.80/0.96    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f34])).
% 3.80/0.96  
% 3.80/0.96  fof(f47,plain,(
% 3.80/0.96    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(rectify,[],[f46])).
% 3.80/0.96  
% 3.80/0.96  fof(f49,plain,(
% 3.80/0.96    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK3(X0,X3)) & m1_subset_1(sK3(X0,X3),u1_struct_0(X0))))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f48,plain,(
% 3.80/0.96    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2(X0),X0) & v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0))))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f50,plain,(
% 3.80/0.96    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2(X0),X0) & v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK3(X0,X3)) & m1_subset_1(sK3(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).
% 3.80/0.96  
% 3.80/0.96  fof(f80,plain,(
% 3.80/0.96    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK3(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f14,conjecture,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f15,negated_conjecture,(
% 3.80/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.80/0.96    inference(negated_conjecture,[],[f14])).
% 3.80/0.96  
% 3.80/0.96  fof(f35,plain,(
% 3.80/0.96    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f15])).
% 3.80/0.96  
% 3.80/0.96  fof(f36,plain,(
% 3.80/0.96    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f35])).
% 3.80/0.96  
% 3.80/0.96  fof(f51,plain,(
% 3.80/0.96    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f36])).
% 3.80/0.96  
% 3.80/0.96  fof(f52,plain,(
% 3.80/0.96    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f51])).
% 3.80/0.96  
% 3.80/0.96  fof(f53,plain,(
% 3.80/0.96    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.80/0.96    inference(rectify,[],[f52])).
% 3.80/0.96  
% 3.80/0.96  fof(f56,plain,(
% 3.80/0.96    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK6(X3),X0) & m2_yellow_6(sK6(X3),X0,X3)))) )),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f55,plain,(
% 3.80/0.96    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK5)) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f54,plain,(
% 3.80/0.96    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,X1)) & l1_waybel_0(X1,sK4) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK4)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK4) & m2_yellow_6(X4,sK4,X3)) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f57,plain,(
% 3.80/0.96    ((! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,sK5)) & l1_waybel_0(sK5,sK4) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) | ~v1_compts_1(sK4)) & (! [X3] : ((v3_yellow_6(sK6(X3),sK4) & m2_yellow_6(sK6(X3),sK4,X3)) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.80/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).
% 3.80/0.96  
% 3.80/0.96  fof(f87,plain,(
% 3.80/0.96    v2_pre_topc(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f86,plain,(
% 3.80/0.96    ~v2_struct_0(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f88,plain,(
% 3.80/0.96    l1_pre_topc(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f12,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f31,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f12])).
% 3.80/0.96  
% 3.80/0.96  fof(f32,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f31])).
% 3.80/0.96  
% 3.80/0.96  fof(f44,plain,(
% 3.80/0.96    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f45,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f44])).
% 3.80/0.96  
% 3.80/0.96  fof(f77,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (m2_yellow_6(sK1(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f45])).
% 3.80/0.96  
% 3.80/0.96  fof(f9,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f25,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f9])).
% 3.80/0.96  
% 3.80/0.96  fof(f26,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f25])).
% 3.80/0.96  
% 3.80/0.96  fof(f43,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(nnf_transformation,[],[f26])).
% 3.80/0.96  
% 3.80/0.96  fof(f74,plain,(
% 3.80/0.96    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f43])).
% 3.80/0.96  
% 3.80/0.96  fof(f95,plain,(
% 3.80/0.96    ( ! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,sK5) | ~v1_compts_1(sK4)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f91,plain,(
% 3.80/0.96    ~v2_struct_0(sK5) | ~v1_compts_1(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f92,plain,(
% 3.80/0.96    v4_orders_2(sK5) | ~v1_compts_1(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f93,plain,(
% 3.80/0.96    v7_waybel_0(sK5) | ~v1_compts_1(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f94,plain,(
% 3.80/0.96    l1_waybel_0(sK5,sK4) | ~v1_compts_1(sK4)),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f6,axiom,(
% 3.80/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f20,plain,(
% 3.80/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.80/0.96    inference(ennf_transformation,[],[f6])).
% 3.80/0.96  
% 3.80/0.96  fof(f67,plain,(
% 3.80/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f20])).
% 3.80/0.96  
% 3.80/0.96  fof(f8,axiom,(
% 3.80/0.96    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f23,plain,(
% 3.80/0.96    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f8])).
% 3.80/0.96  
% 3.80/0.96  fof(f24,plain,(
% 3.80/0.96    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f23])).
% 3.80/0.96  
% 3.80/0.96  fof(f72,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f24])).
% 3.80/0.96  
% 3.80/0.96  fof(f71,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f24])).
% 3.80/0.96  
% 3.80/0.96  fof(f70,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f24])).
% 3.80/0.96  
% 3.80/0.96  fof(f69,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f24])).
% 3.80/0.96  
% 3.80/0.96  fof(f89,plain,(
% 3.80/0.96    ( ! [X3] : (m2_yellow_6(sK6(X3),sK4,X3) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK4)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f1,axiom,(
% 3.80/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f16,plain,(
% 3.80/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f1])).
% 3.80/0.96  
% 3.80/0.96  fof(f37,plain,(
% 3.80/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/0.96    inference(nnf_transformation,[],[f16])).
% 3.80/0.96  
% 3.80/0.96  fof(f38,plain,(
% 3.80/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/0.96    inference(rectify,[],[f37])).
% 3.80/0.96  
% 3.80/0.96  fof(f39,plain,(
% 3.80/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.80/0.96    introduced(choice_axiom,[])).
% 3.80/0.96  
% 3.80/0.96  fof(f40,plain,(
% 3.80/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.80/0.96  
% 3.80/0.96  fof(f59,plain,(
% 3.80/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f40])).
% 3.80/0.96  
% 3.80/0.96  fof(f7,axiom,(
% 3.80/0.96    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f21,plain,(
% 3.80/0.96    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f7])).
% 3.80/0.96  
% 3.80/0.96  fof(f22,plain,(
% 3.80/0.96    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f21])).
% 3.80/0.96  
% 3.80/0.96  fof(f68,plain,(
% 3.80/0.96    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f22])).
% 3.80/0.96  
% 3.80/0.96  fof(f4,axiom,(
% 3.80/0.96    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f17,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.80/0.96    inference(ennf_transformation,[],[f4])).
% 3.80/0.96  
% 3.80/0.96  fof(f18,plain,(
% 3.80/0.96    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.80/0.96    inference(flattening,[],[f17])).
% 3.80/0.96  
% 3.80/0.96  fof(f65,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f18])).
% 3.80/0.96  
% 3.80/0.96  fof(f10,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f27,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f10])).
% 3.80/0.96  
% 3.80/0.96  fof(f28,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f27])).
% 3.80/0.96  
% 3.80/0.96  fof(f75,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f28])).
% 3.80/0.96  
% 3.80/0.96  fof(f11,axiom,(
% 3.80/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f29,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.80/0.96    inference(ennf_transformation,[],[f11])).
% 3.80/0.96  
% 3.80/0.96  fof(f30,plain,(
% 3.80/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.80/0.96    inference(flattening,[],[f29])).
% 3.80/0.96  
% 3.80/0.96  fof(f76,plain,(
% 3.80/0.96    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f30])).
% 3.80/0.96  
% 3.80/0.96  fof(f85,plain,(
% 3.80/0.96    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f81,plain,(
% 3.80/0.96    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f82,plain,(
% 3.80/0.96    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f83,plain,(
% 3.80/0.96    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f84,plain,(
% 3.80/0.96    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f2,axiom,(
% 3.80/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f41,plain,(
% 3.80/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.96    inference(nnf_transformation,[],[f2])).
% 3.80/0.96  
% 3.80/0.96  fof(f42,plain,(
% 3.80/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.80/0.96    inference(flattening,[],[f41])).
% 3.80/0.96  
% 3.80/0.96  fof(f63,plain,(
% 3.80/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f42])).
% 3.80/0.96  
% 3.80/0.96  fof(f73,plain,(
% 3.80/0.96    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f43])).
% 3.80/0.96  
% 3.80/0.96  fof(f90,plain,(
% 3.80/0.96    ( ! [X3] : (v3_yellow_6(sK6(X3),sK4) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK4)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f57])).
% 3.80/0.96  
% 3.80/0.96  fof(f79,plain,(
% 3.80/0.96    ( ! [X0,X3] : (m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f50])).
% 3.80/0.96  
% 3.80/0.96  fof(f78,plain,(
% 3.80/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f45])).
% 3.80/0.96  
% 3.80/0.96  fof(f5,axiom,(
% 3.80/0.96    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.80/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/0.96  
% 3.80/0.96  fof(f19,plain,(
% 3.80/0.96    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.80/0.96    inference(ennf_transformation,[],[f5])).
% 3.80/0.96  
% 3.80/0.96  fof(f66,plain,(
% 3.80/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.80/0.96    inference(cnf_transformation,[],[f19])).
% 3.80/0.96  
% 3.80/0.96  cnf(c_6,plain,
% 3.80/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5102,plain,
% 3.80/0.96      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_26,plain,
% 3.80/0.96      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 3.80/0.96      | ~ l1_waybel_0(X1,X0)
% 3.80/0.96      | ~ v1_compts_1(X0)
% 3.80/0.96      | ~ v2_pre_topc(X0)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | ~ v4_orders_2(X1)
% 3.80/0.96      | ~ v7_waybel_0(X1)
% 3.80/0.96      | ~ l1_pre_topc(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_36,negated_conjecture,
% 3.80/0.96      ( v2_pre_topc(sK4) ),
% 3.80/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_653,plain,
% 3.80/0.96      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 3.80/0.96      | ~ l1_waybel_0(X1,X0)
% 3.80/0.96      | ~ v1_compts_1(X0)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | ~ v4_orders_2(X1)
% 3.80/0.96      | ~ v7_waybel_0(X1)
% 3.80/0.96      | ~ l1_pre_topc(X0)
% 3.80/0.96      | sK4 != X0 ),
% 3.80/0.96      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_654,plain,
% 3.80/0.96      ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ v1_compts_1(sK4)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(sK4)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ v7_waybel_0(X0)
% 3.80/0.96      | ~ l1_pre_topc(sK4) ),
% 3.80/0.96      inference(unflattening,[status(thm)],[c_653]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_37,negated_conjecture,
% 3.80/0.96      ( ~ v2_struct_0(sK4) ),
% 3.80/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_35,negated_conjecture,
% 3.80/0.96      ( l1_pre_topc(sK4) ),
% 3.80/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_658,plain,
% 3.80/0.96      ( ~ v7_waybel_0(X0)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | r3_waybel_9(sK4,X0,sK3(sK4,X0))
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ v1_compts_1(sK4)
% 3.80/0.96      | v2_struct_0(X0) ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_654,c_37,c_35]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_659,plain,
% 3.80/0.96      ( r3_waybel_9(sK4,X0,sK3(sK4,X0))
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ v1_compts_1(sK4)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ v7_waybel_0(X0) ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_658]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5092,plain,
% 3.80/0.96      ( r3_waybel_9(sK4,X0,sK3(sK4,X0)) = iProver_top
% 3.80/0.96      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.96      | v1_compts_1(sK4) != iProver_top
% 3.80/0.96      | v2_struct_0(X0) = iProver_top
% 3.80/0.96      | v4_orders_2(X0) != iProver_top
% 3.80/0.96      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_20,plain,
% 3.80/0.96      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.96      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 3.80/0.96      | ~ l1_waybel_0(X1,X0)
% 3.80/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.96      | ~ v2_pre_topc(X0)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | ~ v4_orders_2(X1)
% 3.80/0.96      | ~ v7_waybel_0(X1)
% 3.80/0.96      | ~ l1_pre_topc(X0) ),
% 3.80/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_760,plain,
% 3.80/0.96      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.96      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 3.80/0.96      | ~ l1_waybel_0(X1,X0)
% 3.80/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | ~ v4_orders_2(X1)
% 3.80/0.96      | ~ v7_waybel_0(X1)
% 3.80/0.96      | ~ l1_pre_topc(X0)
% 3.80/0.96      | sK4 != X0 ),
% 3.80/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_761,plain,
% 3.80/0.96      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.96      | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | v2_struct_0(sK4)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ v7_waybel_0(X0)
% 3.80/0.96      | ~ l1_pre_topc(sK4) ),
% 3.80/0.96      inference(unflattening,[status(thm)],[c_760]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_765,plain,
% 3.80/0.96      ( ~ v7_waybel_0(X0)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.96      | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.96      | v2_struct_0(X0) ),
% 3.80/0.96      inference(global_propositional_subsumption,
% 3.80/0.96                [status(thm)],
% 3.80/0.96                [c_761,c_37,c_35]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_766,plain,
% 3.80/0.96      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.96      | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0)
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ v7_waybel_0(X0) ),
% 3.80/0.96      inference(renaming,[status(thm)],[c_765]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_5086,plain,
% 3.80/0.96      ( r3_waybel_9(sK4,X0,X1) != iProver_top
% 3.80/0.96      | m2_yellow_6(sK1(sK4,X0,X1),sK4,X0) = iProver_top
% 3.80/0.96      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.96      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.96      | v2_struct_0(X0) = iProver_top
% 3.80/0.96      | v4_orders_2(X0) != iProver_top
% 3.80/0.96      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.96      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_15,plain,
% 3.80/0.96      ( v3_yellow_6(X0,X1)
% 3.80/0.96      | ~ l1_waybel_0(X0,X1)
% 3.80/0.96      | ~ v2_pre_topc(X1)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | v2_struct_0(X0)
% 3.80/0.96      | ~ v4_orders_2(X0)
% 3.80/0.96      | ~ v7_waybel_0(X0)
% 3.80/0.96      | ~ l1_pre_topc(X1)
% 3.80/0.96      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.80/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_28,negated_conjecture,
% 3.80/0.96      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.96      | ~ v3_yellow_6(X0,sK4)
% 3.80/0.96      | ~ v1_compts_1(sK4) ),
% 3.80/0.96      inference(cnf_transformation,[],[f95]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_557,plain,
% 3.80/0.96      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.96      | ~ l1_waybel_0(X1,X2)
% 3.80/0.96      | ~ v1_compts_1(sK4)
% 3.80/0.96      | ~ v2_pre_topc(X2)
% 3.80/0.96      | v2_struct_0(X1)
% 3.80/0.96      | v2_struct_0(X2)
% 3.80/0.96      | ~ v4_orders_2(X1)
% 3.80/0.96      | ~ v7_waybel_0(X1)
% 3.80/0.96      | ~ l1_pre_topc(X2)
% 3.80/0.96      | X0 != X1
% 3.80/0.96      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.80/0.96      | sK4 != X2 ),
% 3.80/0.96      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.80/0.96  
% 3.80/0.96  cnf(c_558,plain,
% 3.80/0.96      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.96      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.96      | ~ v1_compts_1(sK4)
% 3.80/0.96      | ~ v2_pre_topc(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(sK4)
% 3.80/0.97      | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_557]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_562,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_558,c_37,c_36,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_563,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | k10_yellow_6(sK4,X0) = k1_xboole_0 ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_562]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5093,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,X0) = k1_xboole_0
% 3.80/0.97      | m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_32,negated_conjecture,
% 3.80/0.97      ( ~ v1_compts_1(sK4) | ~ v2_struct_0(sK5) ),
% 3.80/0.97      inference(cnf_transformation,[],[f91]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_47,plain,
% 3.80/0.97      ( v1_compts_1(sK4) != iProver_top | v2_struct_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_31,negated_conjecture,
% 3.80/0.97      ( ~ v1_compts_1(sK4) | v4_orders_2(sK5) ),
% 3.80/0.97      inference(cnf_transformation,[],[f92]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_48,plain,
% 3.80/0.97      ( v1_compts_1(sK4) != iProver_top | v4_orders_2(sK5) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_30,negated_conjecture,
% 3.80/0.97      ( ~ v1_compts_1(sK4) | v7_waybel_0(sK5) ),
% 3.80/0.97      inference(cnf_transformation,[],[f93]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_49,plain,
% 3.80/0.97      ( v1_compts_1(sK4) != iProver_top | v7_waybel_0(sK5) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_29,negated_conjecture,
% 3.80/0.97      ( l1_waybel_0(sK5,sK4) | ~ v1_compts_1(sK4) ),
% 3.80/0.97      inference(cnf_transformation,[],[f94]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_50,plain,
% 3.80/0.97      ( l1_waybel_0(sK5,sK4) = iProver_top | v1_compts_1(sK4) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_564,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,X0) = k1_xboole_0
% 3.80/0.97      | m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9,plain,
% 3.80/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_11,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | l1_waybel_0(X0,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_struct_0(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_492,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | l1_waybel_0(X0,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X3)
% 3.80/0.97      | X1 != X3 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_493,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | l1_waybel_0(X0,X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_492]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1017,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | l1_waybel_0(X0,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_493,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1018,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | l1_waybel_0(X0,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1017]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1020,plain,
% 3.80/0.97      ( v2_struct_0(X1)
% 3.80/0.97      | l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1018,c_37]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1021,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | l1_waybel_0(X0,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_1020]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5186,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.97      | l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK5,sK4)
% 3.80/0.97      | v2_struct_0(sK5)
% 3.80/0.97      | ~ v4_orders_2(sK5)
% 3.80/0.97      | ~ v7_waybel_0(sK5) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1021]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5187,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) = iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5186]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_12,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_struct_0(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_464,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X3)
% 3.80/0.97      | X1 != X3 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_465,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_464]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1043,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_465,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1044,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | v7_waybel_0(X0) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1043]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1046,plain,
% 3.80/0.97      ( v2_struct_0(X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | v7_waybel_0(X0) ),
% 3.80/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1044,c_37]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1047,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | v7_waybel_0(X0) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_1046]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5191,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.97      | ~ l1_waybel_0(sK5,sK4)
% 3.80/0.97      | v2_struct_0(sK5)
% 3.80/0.97      | ~ v4_orders_2(sK5)
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK5) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5192,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) = iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5191]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_13,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_struct_0(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_436,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X3)
% 3.80/0.97      | X1 != X3 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_437,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_436]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1069,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_437,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1070,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1069]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1072,plain,
% 3.80/0.97      ( v2_struct_0(X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1070,c_37]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1073,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_1072]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5196,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK5)
% 3.80/0.97      | ~ l1_waybel_0(sK5,sK4)
% 3.80/0.97      | v2_struct_0(sK5)
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(sK5)
% 3.80/0.97      | ~ v7_waybel_0(sK5) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1073]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5197,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5196]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6142,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | k10_yellow_6(sK4,X0) = k1_xboole_0
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_5093,c_47,c_48,c_49,c_50,c_564,c_5187,c_5192,c_5197]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6143,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,X0) = k1_xboole_0
% 3.80/0.97      | m2_yellow_6(X0,sK4,sK5) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_6142]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6262,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5086,c_6143]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_7479,plain,
% 3.80/0.97      ( v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | r3_waybel_9(sK4,sK5,X0) != iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_6262,c_47,c_48,c_49,c_50]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_7480,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK1(sK4,sK5,X0)) = iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_7479]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_14,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_struct_0(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_408,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X3)
% 3.80/0.97      | X1 != X3 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_409,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_408]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1095,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,X1)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_409,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1096,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1095]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1098,plain,
% 3.80/0.97      ( v2_struct_0(X1)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1096,c_37]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1099,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,X1)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | ~ v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_1098]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5077,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,X1) != iProver_top
% 3.80/0.97      | l1_waybel_0(X1,sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) != iProver_top
% 3.80/0.97      | v2_struct_0(X1) = iProver_top
% 3.80/0.97      | v4_orders_2(X1) != iProver_top
% 3.80/0.97      | v7_waybel_0(X1) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6266,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v2_struct_0(sK1(sK4,X0,X1)) != iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5086,c_5077]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_7485,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_7480,c_6266]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_34,negated_conjecture,
% 3.80/0.97      ( m2_yellow_6(sK6(X0),sK4,X0)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5095,plain,
% 3.80/0.97      ( m2_yellow_6(sK6(X0),sK4,X0) = iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1,plain,
% 3.80/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5106,plain,
% 3.80/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.80/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_10,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.97      | ~ v2_pre_topc(X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_921,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_922,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_921]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_926,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.80/0.97      | v2_struct_0(X0) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_922,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_927,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_926]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5081,plain,
% 3.80/0.97      ( l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(k10_yellow_6(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_7,plain,
% 3.80/0.97      ( m1_subset_1(X0,X1)
% 3.80/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.80/0.97      | ~ r2_hidden(X0,X2) ),
% 3.80/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5101,plain,
% 3.80/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 3.80/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.80/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6021,plain,
% 3.80/0.97      ( l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) = iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5081,c_5101]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6556,plain,
% 3.80/0.97      ( l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK0(k10_yellow_6(sK4,X0),X1),u1_struct_0(sK4)) = iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5106,c_6021]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_17,plain,
% 3.80/0.97      ( r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X1,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_858,plain,
% 3.80/0.97      ( r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X1,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_859,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_858]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_863,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
% 3.80/0.97      | v2_struct_0(X0) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_859,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_864,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | ~ r2_hidden(X1,k10_yellow_6(sK4,X0))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_863]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5083,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) = iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_865,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) = iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6171,plain,
% 3.80/0.97      ( l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | r3_waybel_9(sK4,X0,X1) = iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_5083,c_865,c_6021]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6172,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) = iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,X0)) != iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_6171]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6177,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X0),X1)) = iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5106,c_6172]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_18,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | r3_waybel_9(X0,X3,X2)
% 3.80/0.97      | ~ m2_yellow_6(X1,X0,X3)
% 3.80/0.97      | ~ l1_waybel_0(X3,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X3)
% 3.80/0.97      | ~ v4_orders_2(X3)
% 3.80/0.97      | ~ v7_waybel_0(X3)
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_826,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | r3_waybel_9(X0,X3,X2)
% 3.80/0.97      | ~ m2_yellow_6(X1,X0,X3)
% 3.80/0.97      | ~ l1_waybel_0(X3,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X3)
% 3.80/0.97      | ~ v4_orders_2(X3)
% 3.80/0.97      | ~ v7_waybel_0(X3)
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_827,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | r3_waybel_9(sK4,X2,X1)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_826]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_829,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | r3_waybel_9(sK4,X2,X1)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | v2_struct_0(X2) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_827,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_830,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | r3_waybel_9(sK4,X2,X1)
% 3.80/0.97      | ~ m2_yellow_6(X0,sK4,X2)
% 3.80/0.97      | ~ l1_waybel_0(X2,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X2) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_829]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5084,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) != iProver_top
% 3.80/0.97      | r3_waybel_9(sK4,X2,X1) = iProver_top
% 3.80/0.97      | m2_yellow_6(X0,sK4,X2) != iProver_top
% 3.80/0.97      | l1_waybel_0(X2,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v2_struct_0(X2) = iProver_top
% 3.80/0.97      | v4_orders_2(X2) != iProver_top
% 3.80/0.97      | v7_waybel_0(X2) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6764,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X1),X2)) = iProver_top
% 3.80/0.97      | m2_yellow_6(X1,sK4,X0) != iProver_top
% 3.80/0.97      | l1_waybel_0(X1,sK4) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK0(k10_yellow_6(sK4,X1),X2),u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X1),X2) = iProver_top
% 3.80/0.97      | v2_struct_0(X1) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X1) != iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X1) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_6177,c_5084]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8008,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,sK0(k10_yellow_6(sK4,X1),X2)) = iProver_top
% 3.80/0.97      | m2_yellow_6(X1,sK4,X0) != iProver_top
% 3.80/0.97      | l1_waybel_0(X1,sK4) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X1),X2) = iProver_top
% 3.80/0.97      | v2_struct_0(X1) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X1) != iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X1) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_6556,c_6764]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_21,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,sK2(X0),X1)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.80/0.97      | v1_compts_1(X0)
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_739,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,sK2(X0),X1)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.80/0.97      | v1_compts_1(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_740,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
% 3.80/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_739]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_744,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,sK2(sK4),X0)
% 3.80/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.80/0.97      | v1_compts_1(sK4) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_740,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5087,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,sK2(sK4),X0) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8337,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK0(k10_yellow_6(sK4,X0),X1),u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_8008,c_5087]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_25,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v2_struct_0(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_683,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v2_struct_0(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_684,plain,
% 3.80/0.97      ( v1_compts_1(sK4)
% 3.80/0.97      | ~ v2_struct_0(sK2(sK4))
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_683]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_686,plain,
% 3.80/0.97      ( v1_compts_1(sK4) | ~ v2_struct_0(sK2(sK4)) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_684,c_37,c_36,c_35,c_61]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_688,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top | v2_struct_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_24,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v4_orders_2(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_697,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v4_orders_2(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_698,plain,
% 3.80/0.97      ( v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | v4_orders_2(sK2(sK4))
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_697]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_700,plain,
% 3.80/0.97      ( v4_orders_2(sK2(sK4)) | v1_compts_1(sK4) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_698,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_701,plain,
% 3.80/0.97      ( v1_compts_1(sK4) | v4_orders_2(sK2(sK4)) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_700]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_702,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top | v4_orders_2(sK2(sK4)) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_23,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v7_waybel_0(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_711,plain,
% 3.80/0.97      ( v1_compts_1(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v7_waybel_0(sK2(X0))
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_712,plain,
% 3.80/0.97      ( v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | v7_waybel_0(sK2(sK4))
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_711]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_714,plain,
% 3.80/0.97      ( v7_waybel_0(sK2(sK4)) | v1_compts_1(sK4) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_712,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_715,plain,
% 3.80/0.97      ( v1_compts_1(sK4) | v7_waybel_0(sK2(sK4)) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_714]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_716,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top | v7_waybel_0(sK2(sK4)) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_22,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(X0),X0)
% 3.80/0.97      | v1_compts_1(X0)
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_725,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(X0),X0)
% 3.80/0.97      | v1_compts_1(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_726,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(sK4),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_725]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_728,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(sK4),sK4) | v1_compts_1(sK4) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_726,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_730,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5299,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
% 3.80/0.97      | l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK2(sK4),sK4)
% 3.80/0.97      | v2_struct_0(sK2(sK4))
% 3.80/0.97      | ~ v4_orders_2(sK2(sK4))
% 3.80/0.97      | ~ v7_waybel_0(sK2(sK4)) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1021]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5300,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) = iProver_top
% 3.80/0.97      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5299]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5298,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
% 3.80/0.97      | ~ l1_waybel_0(sK2(sK4),sK4)
% 3.80/0.97      | v2_struct_0(sK2(sK4))
% 3.80/0.97      | ~ v4_orders_2(sK2(sK4))
% 3.80/0.97      | v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK2(sK4)) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5304,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) = iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5298]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5297,plain,
% 3.80/0.97      ( ~ m2_yellow_6(X0,sK4,sK2(sK4))
% 3.80/0.97      | ~ l1_waybel_0(sK2(sK4),sK4)
% 3.80/0.97      | v2_struct_0(sK2(sK4))
% 3.80/0.97      | v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(sK2(sK4))
% 3.80/0.97      | ~ v7_waybel_0(sK2(sK4)) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1073]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5308,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5297]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8405,plain,
% 3.80/0.97      ( v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
% 3.80/0.97      | m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_8337,c_688,c_702,c_716,c_730,c_5300,c_5304,c_5308,c_6556]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8406,plain,
% 3.80/0.97      ( m2_yellow_6(X0,sK4,sK2(sK4)) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,X0),X1) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_8405]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8411,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(sK6(sK2(sK4))) = iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5095,c_8406]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5088,plain,
% 3.80/0.97      ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5469,plain,
% 3.80/0.97      ( l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v2_struct_0(sK6(X0)) != iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5095,c_5077]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5753,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(sK6(sK2(sK4))) != iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5088,c_5469]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6509,plain,
% 3.80/0.97      ( v2_struct_0(sK6(sK2(sK4))) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_5753,c_688,c_702,c_716]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_6510,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(sK6(sK2(sK4))) != iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_6509]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8417,plain,
% 3.80/0.97      ( r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_8411,c_688,c_702,c_716,c_730,c_6510]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_3,plain,
% 3.80/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.80/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5104,plain,
% 3.80/0.97      ( X0 = X1
% 3.80/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.80/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5952,plain,
% 3.80/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5102,c_5104]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8426,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK6(sK2(sK4))) = k1_xboole_0
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_8417,c_5952]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1289,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | l1_waybel_0(X2,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | X0 != X1
% 3.80/0.97      | sK6(X1) != X2
% 3.80/0.97      | sK4 != sK4 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_34,c_1021]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1290,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1289]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1265,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | v7_waybel_0(X2)
% 3.80/0.97      | X0 != X1
% 3.80/0.97      | sK6(X1) != X2
% 3.80/0.97      | sK4 != sK4 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_34,c_1047]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1266,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | v7_waybel_0(sK6(X0)) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1265]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1241,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | X0 != X1
% 3.80/0.97      | sK6(X1) != X2
% 3.80/0.97      | sK4 != sK4 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_34,c_1073]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1242,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | v4_orders_2(sK6(X0))
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1241]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1217,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(X1,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | ~ v2_struct_0(X2)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | X0 != X1
% 3.80/0.97      | sK6(X1) != X2
% 3.80/0.97      | sK4 != sK4 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_34,c_1099]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1218,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v2_struct_0(sK6(X0))
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_1217]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_16,plain,
% 3.80/0.97      ( ~ v3_yellow_6(X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | ~ v2_pre_topc(X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1)
% 3.80/0.97      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.80/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_33,negated_conjecture,
% 3.80/0.97      ( v3_yellow_6(sK6(X0),sK4)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_590,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X2,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | ~ v2_pre_topc(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X2)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(X2)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(X2)
% 3.80/0.97      | ~ l1_pre_topc(X1)
% 3.80/0.97      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.80/0.97      | sK6(X2) != X0
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_591,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | ~ v2_pre_topc(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK6(X0))
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(sK6(X0))
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK6(X0))
% 3.80/0.97      | ~ l1_pre_topc(sK4)
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_590]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_595,plain,
% 3.80/0.97      ( ~ v7_waybel_0(sK6(X0))
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(sK6(X0))
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK6(X0))
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_591,c_37,c_36,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_596,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK6(X0))
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(sK6(X0))
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK6(X0))
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_595]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1472,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v4_orders_2(sK6(X0))
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK6(X0))
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(backward_subsumption_resolution,[status(thm)],[c_1218,c_596]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1483,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v7_waybel_0(sK6(X0))
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(backward_subsumption_resolution,[status(thm)],[c_1242,c_1472]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1494,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ l1_waybel_0(sK6(X0),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(backward_subsumption_resolution,[status(thm)],[c_1266,c_1483]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_1500,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | k10_yellow_6(sK4,sK6(X0)) != k1_xboole_0 ),
% 3.80/0.97      inference(backward_subsumption_resolution,[status(thm)],[c_1290,c_1494]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5422,plain,
% 3.80/0.97      ( ~ l1_waybel_0(sK2(sK4),sK4)
% 3.80/0.97      | v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK2(sK4))
% 3.80/0.97      | ~ v4_orders_2(sK2(sK4))
% 3.80/0.97      | ~ v7_waybel_0(sK2(sK4))
% 3.80/0.97      | k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0 ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_1500]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5423,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0
% 3.80/0.97      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) = iProver_top
% 3.80/0.97      | v2_struct_0(sK2(sK4)) = iProver_top
% 3.80/0.97      | v4_orders_2(sK2(sK4)) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5422]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8482,plain,
% 3.80/0.97      ( v1_compts_1(sK4) = iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_8426,c_688,c_702,c_716,c_730,c_5423]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8652,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,sK5,X0) != iProver_top
% 3.80/0.97      | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_7485,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5423,
% 3.80/0.97                 c_8426]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8653,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 3.80/0.97      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 3.80/0.97      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_8652]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8658,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5092,c_8653]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_27,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.80/0.97      | ~ v1_compts_1(X1)
% 3.80/0.97      | ~ v2_pre_topc(X1)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1) ),
% 3.80/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_891,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,X1)
% 3.80/0.97      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 3.80/0.97      | ~ v1_compts_1(X1)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(X1)
% 3.80/0.97      | sK4 != X1 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_892,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_891]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_896,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_892,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_897,plain,
% 3.80/0.97      ( ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4))
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_896]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5172,plain,
% 3.80/0.97      ( ~ l1_waybel_0(sK5,sK4)
% 3.80/0.97      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4))
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK5)
% 3.80/0.97      | ~ v4_orders_2(sK5)
% 3.80/0.97      | ~ v7_waybel_0(sK5) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_897]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5173,plain,
% 3.80/0.97      ( l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) = iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5172]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9391,plain,
% 3.80/0.97      ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0 ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_8658,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5173,
% 3.80/0.97                 c_5423,c_8426]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_19,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X1,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 3.80/0.97      | ~ v2_pre_topc(X0)
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ l1_pre_topc(X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_793,plain,
% 3.80/0.97      ( ~ r3_waybel_9(X0,X1,X2)
% 3.80/0.97      | ~ l1_waybel_0(X1,X0)
% 3.80/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.80/0.97      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(X1)
% 3.80/0.97      | ~ v4_orders_2(X1)
% 3.80/0.97      | ~ v7_waybel_0(X1)
% 3.80/0.97      | ~ l1_pre_topc(X0)
% 3.80/0.97      | sK4 != X0 ),
% 3.80/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_794,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | v2_struct_0(sK4)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ l1_pre_topc(sK4) ),
% 3.80/0.97      inference(unflattening,[status(thm)],[c_793]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_798,plain,
% 3.80/0.97      ( ~ v7_waybel_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
% 3.80/0.97      | v2_struct_0(X0) ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_794,c_37,c_35]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_799,plain,
% 3.80/0.97      ( ~ r3_waybel_9(sK4,X0,X1)
% 3.80/0.97      | ~ l1_waybel_0(X0,sK4)
% 3.80/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1)))
% 3.80/0.97      | v2_struct_0(X0)
% 3.80/0.97      | ~ v4_orders_2(X0)
% 3.80/0.97      | ~ v7_waybel_0(X0) ),
% 3.80/0.97      inference(renaming,[status(thm)],[c_798]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5085,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,X0,X1) != iProver_top
% 3.80/0.97      | l1_waybel_0(X0,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r2_hidden(X1,k10_yellow_6(sK4,sK1(sK4,X0,X1))) = iProver_top
% 3.80/0.97      | v2_struct_0(X0) = iProver_top
% 3.80/0.97      | v4_orders_2(X0) != iProver_top
% 3.80/0.97      | v7_waybel_0(X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9404,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) != iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 3.80/0.97      | r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_9391,c_5085]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5183,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5))
% 3.80/0.97      | ~ l1_waybel_0(sK5,sK4)
% 3.80/0.97      | ~ v1_compts_1(sK4)
% 3.80/0.97      | v2_struct_0(sK5)
% 3.80/0.97      | ~ v4_orders_2(sK5)
% 3.80/0.97      | ~ v7_waybel_0(sK5) ),
% 3.80/0.97      inference(instantiation,[status(thm)],[c_659]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5184,plain,
% 3.80/0.97      ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) = iProver_top
% 3.80/0.97      | l1_waybel_0(sK5,sK4) != iProver_top
% 3.80/0.97      | v1_compts_1(sK4) != iProver_top
% 3.80/0.97      | v2_struct_0(sK5) = iProver_top
% 3.80/0.97      | v4_orders_2(sK5) != iProver_top
% 3.80/0.97      | v7_waybel_0(sK5) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_5183]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9476,plain,
% 3.80/0.97      ( r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top ),
% 3.80/0.97      inference(global_propositional_subsumption,
% 3.80/0.97                [status(thm)],
% 3.80/0.97                [c_9404,c_47,c_48,c_49,c_50,c_688,c_702,c_716,c_730,c_5173,
% 3.80/0.97                 c_5184,c_5423,c_8426]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_8,plain,
% 3.80/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.80/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_5100,plain,
% 3.80/0.97      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.80/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9481,plain,
% 3.80/0.97      ( r1_tarski(k1_xboole_0,sK3(sK4,sK5)) != iProver_top ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_9476,c_5100]) ).
% 3.80/0.97  
% 3.80/0.97  cnf(c_9905,plain,
% 3.80/0.97      ( $false ),
% 3.80/0.97      inference(superposition,[status(thm)],[c_5102,c_9481]) ).
% 3.80/0.97  
% 3.80/0.97  
% 3.80/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/0.97  
% 3.80/0.97  ------                               Statistics
% 3.80/0.97  
% 3.80/0.97  ------ General
% 3.80/0.97  
% 3.80/0.97  abstr_ref_over_cycles:                  0
% 3.80/0.97  abstr_ref_under_cycles:                 0
% 3.80/0.97  gc_basic_clause_elim:                   0
% 3.80/0.97  forced_gc_time:                         0
% 3.80/0.97  parsing_time:                           0.01
% 3.80/0.97  unif_index_cands_time:                  0.
% 3.80/0.97  unif_index_add_time:                    0.
% 3.80/0.97  orderings_time:                         0.
% 3.80/0.97  out_proof_time:                         0.018
% 3.80/0.97  total_time:                             0.278
% 3.80/0.97  num_of_symbols:                         56
% 3.80/0.97  num_of_terms:                           5794
% 3.80/0.97  
% 3.80/0.97  ------ Preprocessing
% 3.80/0.97  
% 3.80/0.97  num_of_splits:                          0
% 3.80/0.97  num_of_split_atoms:                     0
% 3.80/0.97  num_of_reused_defs:                     0
% 3.80/0.97  num_eq_ax_congr_red:                    28
% 3.80/0.97  num_of_sem_filtered_clauses:            1
% 3.80/0.97  num_of_subtypes:                        0
% 3.80/0.97  monotx_restored_types:                  0
% 3.80/0.97  sat_num_of_epr_types:                   0
% 3.80/0.97  sat_num_of_non_cyclic_types:            0
% 3.80/0.97  sat_guarded_non_collapsed_types:        0
% 3.80/0.97  num_pure_diseq_elim:                    0
% 3.80/0.97  simp_replaced_by:                       0
% 3.80/0.97  res_preprocessed:                       170
% 3.80/0.97  prep_upred:                             0
% 3.80/0.97  prep_unflattend:                        73
% 3.80/0.97  smt_new_axioms:                         0
% 3.80/0.97  pred_elim_cands:                        10
% 3.80/0.97  pred_elim:                              4
% 3.80/0.97  pred_elim_cl:                           5
% 3.80/0.97  pred_elim_cycles:                       8
% 3.80/0.97  merged_defs:                            0
% 3.80/0.97  merged_defs_ncl:                        0
% 3.80/0.97  bin_hyper_res:                          0
% 3.80/0.97  prep_cycles:                            4
% 3.80/0.97  pred_elim_time:                         0.064
% 3.80/0.97  splitting_time:                         0.
% 3.80/0.97  sem_filter_time:                        0.
% 3.80/0.97  monotx_time:                            0.001
% 3.80/0.97  subtype_inf_time:                       0.
% 3.80/0.97  
% 3.80/0.97  ------ Problem properties
% 3.80/0.97  
% 3.80/0.97  clauses:                                32
% 3.80/0.97  conjectures:                            6
% 3.80/0.97  epr:                                    14
% 3.80/0.97  horn:                                   15
% 3.80/0.97  ground:                                 9
% 3.80/0.97  unary:                                  3
% 3.80/0.97  binary:                                 11
% 3.80/0.97  lits:                                   126
% 3.80/0.97  lits_eq:                                3
% 3.80/0.97  fd_pure:                                0
% 3.80/0.97  fd_pseudo:                              0
% 3.80/0.97  fd_cond:                                0
% 3.80/0.97  fd_pseudo_cond:                         1
% 3.80/0.97  ac_symbols:                             0
% 3.80/0.97  
% 3.80/0.97  ------ Propositional Solver
% 3.80/0.97  
% 3.80/0.97  prop_solver_calls:                      29
% 3.80/0.97  prop_fast_solver_calls:                 3144
% 3.80/0.97  smt_solver_calls:                       0
% 3.80/0.97  smt_fast_solver_calls:                  0
% 3.80/0.97  prop_num_of_clauses:                    2970
% 3.80/0.97  prop_preprocess_simplified:             8609
% 3.80/0.97  prop_fo_subsumed:                       155
% 3.80/0.97  prop_solver_time:                       0.
% 3.80/0.97  smt_solver_time:                        0.
% 3.80/0.97  smt_fast_solver_time:                   0.
% 3.80/0.97  prop_fast_solver_time:                  0.
% 3.80/0.97  prop_unsat_core_time:                   0.
% 3.80/0.97  
% 3.80/0.97  ------ QBF
% 3.80/0.97  
% 3.80/0.97  qbf_q_res:                              0
% 3.80/0.97  qbf_num_tautologies:                    0
% 3.80/0.97  qbf_prep_cycles:                        0
% 3.80/0.97  
% 3.80/0.97  ------ BMC1
% 3.80/0.97  
% 3.80/0.97  bmc1_current_bound:                     -1
% 3.80/0.97  bmc1_last_solved_bound:                 -1
% 3.80/0.97  bmc1_unsat_core_size:                   -1
% 3.80/0.97  bmc1_unsat_core_parents_size:           -1
% 3.80/0.97  bmc1_merge_next_fun:                    0
% 3.80/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.80/0.97  
% 3.80/0.97  ------ Instantiation
% 3.80/0.97  
% 3.80/0.97  inst_num_of_clauses:                    842
% 3.80/0.97  inst_num_in_passive:                    11
% 3.80/0.97  inst_num_in_active:                     415
% 3.80/0.97  inst_num_in_unprocessed:                416
% 3.80/0.97  inst_num_of_loops:                      530
% 3.80/0.97  inst_num_of_learning_restarts:          0
% 3.80/0.97  inst_num_moves_active_passive:          110
% 3.80/0.97  inst_lit_activity:                      0
% 3.80/0.97  inst_lit_activity_moves:                0
% 3.80/0.97  inst_num_tautologies:                   0
% 3.80/0.97  inst_num_prop_implied:                  0
% 3.80/0.97  inst_num_existing_simplified:           0
% 3.80/0.97  inst_num_eq_res_simplified:             0
% 3.80/0.97  inst_num_child_elim:                    0
% 3.80/0.97  inst_num_of_dismatching_blockings:      83
% 3.80/0.97  inst_num_of_non_proper_insts:           817
% 3.80/0.97  inst_num_of_duplicates:                 0
% 3.80/0.97  inst_inst_num_from_inst_to_res:         0
% 3.80/0.97  inst_dismatching_checking_time:         0.
% 3.80/0.97  
% 3.80/0.97  ------ Resolution
% 3.80/0.97  
% 3.80/0.97  res_num_of_clauses:                     0
% 3.80/0.97  res_num_in_passive:                     0
% 3.80/0.97  res_num_in_active:                      0
% 3.80/0.97  res_num_of_loops:                       174
% 3.80/0.97  res_forward_subset_subsumed:            28
% 3.80/0.97  res_backward_subset_subsumed:           0
% 3.80/0.97  res_forward_subsumed:                   0
% 3.80/0.97  res_backward_subsumed:                  0
% 3.80/0.97  res_forward_subsumption_resolution:     0
% 3.80/0.97  res_backward_subsumption_resolution:    4
% 3.80/0.97  res_clause_to_clause_subsumption:       789
% 3.80/0.97  res_orphan_elimination:                 0
% 3.80/0.97  res_tautology_del:                      65
% 3.80/0.97  res_num_eq_res_simplified:              0
% 3.80/0.97  res_num_sel_changes:                    0
% 3.80/0.97  res_moves_from_active_to_pass:          0
% 3.80/0.97  
% 3.80/0.97  ------ Superposition
% 3.80/0.97  
% 3.80/0.97  sup_time_total:                         0.
% 3.80/0.97  sup_time_generating:                    0.
% 3.80/0.97  sup_time_sim_full:                      0.
% 3.80/0.97  sup_time_sim_immed:                     0.
% 3.80/0.97  
% 3.80/0.97  sup_num_of_clauses:                     101
% 3.80/0.97  sup_num_in_active:                      67
% 3.80/0.97  sup_num_in_passive:                     34
% 3.80/0.97  sup_num_of_loops:                       105
% 3.80/0.97  sup_fw_superposition:                   71
% 3.80/0.97  sup_bw_superposition:                   95
% 3.80/0.97  sup_immediate_simplified:               22
% 3.80/0.97  sup_given_eliminated:                   0
% 3.80/0.97  comparisons_done:                       0
% 3.80/0.97  comparisons_avoided:                    1
% 3.80/0.97  
% 3.80/0.97  ------ Simplifications
% 3.80/0.97  
% 3.80/0.97  
% 3.80/0.97  sim_fw_subset_subsumed:                 6
% 3.80/0.97  sim_bw_subset_subsumed:                 7
% 3.80/0.97  sim_fw_subsumed:                        14
% 3.80/0.97  sim_bw_subsumed:                        34
% 3.80/0.97  sim_fw_subsumption_res:                 0
% 3.80/0.97  sim_bw_subsumption_res:                 0
% 3.80/0.97  sim_tautology_del:                      12
% 3.80/0.97  sim_eq_tautology_del:                   6
% 3.80/0.97  sim_eq_res_simp:                        0
% 3.80/0.97  sim_fw_demodulated:                     0
% 3.80/0.97  sim_bw_demodulated:                     0
% 3.80/0.97  sim_light_normalised:                   5
% 3.80/0.97  sim_joinable_taut:                      0
% 3.80/0.97  sim_joinable_simp:                      0
% 3.80/0.97  sim_ac_normalised:                      0
% 3.80/0.97  sim_smt_subsumption:                    0
% 3.80/0.97  
%------------------------------------------------------------------------------
