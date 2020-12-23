%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:25 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3445)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f14])).

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
     => ( r3_waybel_9(X0,X3,sK3(X0,X3))
        & m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) ) ) ),
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
            ( ~ r3_waybel_9(X0,sK2(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK2(X0),X0)
        & v7_waybel_0(sK2(X0))
        & v4_orders_2(sK2(X0))
        & ~ v2_struct_0(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f52])).

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
    inference(ennf_transformation,[],[f13])).

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
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f46])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f10])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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
     => ( v3_yellow_6(sK6(X3),X0)
        & m2_yellow_6(sK6(X3),X0,X3) ) ) ),
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
            | ~ m2_yellow_6(X2,X0,sK5) )
        & l1_waybel_0(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).

fof(f99,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK4)
      | ~ m2_yellow_6(X2,sK4,sK5)
      | ~ v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,
    ( ~ v2_struct_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,
    ( v4_orders_2(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,
    ( v7_waybel_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    ! [X3] :
      ( m2_yellow_6(sK6(X3),sK4,X3)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X3] :
      ( v3_yellow_6(sK6(X3),sK4)
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f59])).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f89,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_28,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1649,plain,
    ( r3_waybel_9(X0,X1,sK3(X0,X1)) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_1655,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

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

cnf(c_1664,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | l1_waybel_0(X0,X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3855,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1664])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_100,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7860,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r3_waybel_9(X0,X1,X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3855,c_100])).

cnf(c_7861,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7860])).

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

cnf(c_1660,plain,
    ( k10_yellow_6(X0,X1) = k1_xboole_0
    | v3_yellow_6(X1,X0) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7876,plain,
    ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
    | r3_waybel_9(X0,X1,X2) != iProver_top
    | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X0,X1,X2)) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK1(X0,X1,X2)) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK1(X0,X1,X2)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7861,c_1660])).

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

cnf(c_1663,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3540,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1663])).

cnf(c_5920,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r3_waybel_9(X0,X1,X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3540,c_100])).

cnf(c_5921,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5920])).

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

cnf(c_1662,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3541,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1662])).

cnf(c_6444,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r3_waybel_9(X0,X1,X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_100])).

cnf(c_6445,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6444])).

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

cnf(c_1661,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3627,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1661])).

cnf(c_7450,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r3_waybel_9(X0,X1,X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3627,c_100])).

cnf(c_7451,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7450])).

cnf(c_11267,plain,
    ( v7_waybel_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
    | r3_waybel_9(X0,X1,X2) != iProver_top
    | k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
    | v4_orders_2(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7876,c_5921,c_6445,c_7451])).

cnf(c_11268,plain,
    ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
    | r3_waybel_9(X0,X1,X2) != iProver_top
    | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11267])).

cnf(c_30,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK4,sK5)
    | ~ v3_yellow_6(X0,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1647,plain,
    ( m2_yellow_6(X0,sK4,sK5) != iProver_top
    | v3_yellow_6(X0,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3542,plain,
    ( r3_waybel_9(sK4,sK5,X0) != iProver_top
    | v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1647])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_50,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v4_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_51,plain,
    ( v1_compts_1(sK4) != iProver_top
    | v7_waybel_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( l1_waybel_0(sK5,sK4) = iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6981,plain,
    ( v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3542,c_40,c_41,c_42,c_49,c_50,c_51,c_52])).

cnf(c_6982,plain,
    ( r3_waybel_9(sK4,sK5,X0) != iProver_top
    | v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_6981])).

cnf(c_11284,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11268,c_6982])).

cnf(c_36,negated_conjecture,
    ( m2_yellow_6(sK6(X0),sK4,X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1641,plain,
    ( m2_yellow_6(sK6(X0),sK4,X0) = iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3856,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | l1_waybel_0(sK6(X0),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1664])).

cnf(c_102,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_struct_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_6678,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | l1_waybel_0(sK6(X0),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3856,c_40,c_42,c_102])).

cnf(c_6679,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | l1_waybel_0(sK6(X0),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6678])).

cnf(c_3444,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK6(X0)) = iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1662])).

cnf(c_4926,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v4_orders_2(sK6(X0)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_40,c_42,c_102])).

cnf(c_4927,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK6(X0)) = iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4926])).

cnf(c_6691,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK6(X0)) != iProver_top
    | v4_orders_2(sK6(sK6(X0))) = iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6679,c_4927])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_62,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_64,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_65,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(sK2(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_67,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_25,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK2(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_68,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_waybel_0(sK2(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_70,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v7_waybel_0(sK2(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_24,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_71,plain,
    ( l1_waybel_0(sK2(X0),X0) = iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_73,plain,
    ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_35,negated_conjecture,
    ( v3_yellow_6(sK6(X0),sK4)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2421,plain,
    ( v3_yellow_6(sK6(sK2(X0)),sK4)
    | ~ l1_waybel_0(sK2(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK2(X0))
    | ~ v4_orders_2(sK2(X0))
    | ~ v7_waybel_0(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2442,plain,
    ( v3_yellow_6(sK6(sK2(X0)),sK4) = iProver_top
    | l1_waybel_0(sK2(X0),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(X0)) = iProver_top
    | v4_orders_2(sK2(X0)) != iProver_top
    | v7_waybel_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2421])).

cnf(c_2444,plain,
    ( v3_yellow_6(sK6(sK2(sK4)),sK4) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_2420,plain,
    ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0))
    | ~ l1_waybel_0(sK2(X0),sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(sK2(X0))
    | ~ v4_orders_2(sK2(X0))
    | ~ v7_waybel_0(sK2(X0)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_2446,plain,
    ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0)) = iProver_top
    | l1_waybel_0(sK2(X0),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(X0)) = iProver_top
    | v4_orders_2(sK2(X0)) != iProver_top
    | v7_waybel_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2420])).

cnf(c_2448,plain,
    ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2446])).

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

cnf(c_2551,plain,
    ( ~ v3_yellow_6(sK6(sK2(X0)),sK4)
    | ~ l1_waybel_0(sK6(sK2(X0)),sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK6(sK2(X0)))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK6(sK2(X0)))
    | ~ v7_waybel_0(sK6(sK2(X0)))
    | ~ l1_pre_topc(sK4)
    | k10_yellow_6(sK4,sK6(sK2(X0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2557,plain,
    ( k10_yellow_6(sK4,sK6(sK2(X0))) != k1_xboole_0
    | v3_yellow_6(sK6(sK2(X0)),sK4) != iProver_top
    | l1_waybel_0(sK6(sK2(X0)),sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK6(sK2(X0))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(X0))) != iProver_top
    | v7_waybel_0(sK6(sK2(X0))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2551])).

cnf(c_2559,plain,
    ( k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0
    | v3_yellow_6(sK6(sK2(sK4)),sK4) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2557])).

cnf(c_2567,plain,
    ( ~ m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0))
    | l1_waybel_0(sK6(sK2(X0)),sK4)
    | ~ l1_waybel_0(sK2(X0),sK4)
    | v2_struct_0(sK2(X0))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK2(X0))
    | ~ v7_waybel_0(sK2(X0))
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2578,plain,
    ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0)) != iProver_top
    | l1_waybel_0(sK6(sK2(X0)),sK4) = iProver_top
    | l1_waybel_0(sK2(X0),sK4) != iProver_top
    | v2_struct_0(sK2(X0)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(X0)) != iProver_top
    | v7_waybel_0(sK2(X0)) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_2580,plain,
    ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) != iProver_top
    | l1_waybel_0(sK6(sK2(sK4)),sK4) = iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_3998,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_14,c_36])).

cnf(c_101,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3457,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK6(X0)) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1663])).

cnf(c_3458,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3457])).

cnf(c_4120,plain,
    ( v7_waybel_0(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3998,c_39,c_37,c_101,c_3458])).

cnf(c_4121,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK6(X0)) ),
    inference(renaming,[status(thm)],[c_4120])).

cnf(c_4488,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK2(sK4))
    | v7_waybel_0(sK6(sK2(sK4)))
    | ~ v7_waybel_0(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_4121,c_24])).

cnf(c_63,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_66,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v4_orders_2(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_69,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v7_waybel_0(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_4491,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK6(sK2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4488,c_39,c_38,c_37,c_63,c_66,c_69])).

cnf(c_4493,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4491])).

cnf(c_5532,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_15,c_36])).

cnf(c_4928,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4927])).

cnf(c_5697,plain,
    ( ~ v7_waybel_0(X0)
    | v4_orders_2(sK6(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5532,c_39,c_37,c_101,c_3445])).

cnf(c_5698,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_5697])).

cnf(c_5822,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | v4_orders_2(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_5698,c_24])).

cnf(c_1653,plain,
    ( l1_waybel_0(sK2(X0),X0) = iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4938,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_4927])).

cnf(c_4956,plain,
    ( v1_compts_1(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK2(sK4))
    | v2_struct_0(sK4)
    | v4_orders_2(sK6(sK2(sK4)))
    | ~ v4_orders_2(sK2(sK4))
    | ~ v7_waybel_0(sK2(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4938])).

cnf(c_5937,plain,
    ( v4_orders_2(sK6(sK2(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5822,c_39,c_38,c_37,c_63,c_66,c_69,c_4956])).

cnf(c_5938,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK6(sK2(sK4))) ),
    inference(renaming,[status(thm)],[c_5937])).

cnf(c_5939,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5938])).

cnf(c_3628,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1661])).

cnf(c_6646,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3628,c_40,c_42,c_102])).

cnf(c_6647,plain,
    ( l1_waybel_0(X0,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6646])).

cnf(c_6658,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_6647])).

cnf(c_7241,plain,
    ( v2_struct_0(sK6(sK2(sK4))) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6658,c_40,c_41,c_42,c_64,c_67,c_70])).

cnf(c_7242,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK6(sK2(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7241])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1675,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_1658,plain,
    ( r3_waybel_9(X0,X1,X2) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k10_yellow_6(X0,X1)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4262,plain,
    ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X0,X1),X2),u1_struct_0(X0)) != iProver_top
    | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1658])).

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

cnf(c_1665,plain,
    ( l1_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1668,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3911,plain,
    ( l1_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,k10_yellow_6(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1668])).

cnf(c_7600,plain,
    ( l1_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) = iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_3911])).

cnf(c_8906,plain,
    ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4262,c_7600])).

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

cnf(c_1657,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | r3_waybel_9(X0,X3,X2) = iProver_top
    | m2_yellow_6(X1,X0,X3) != iProver_top
    | l1_waybel_0(X3,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8910,plain,
    ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
    | m2_yellow_6(X2,X0,X1) != iProver_top
    | l1_waybel_0(X2,X0) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X0,X2),X3),u1_struct_0(X0)) != iProver_top
    | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8906,c_1657])).

cnf(c_11304,plain,
    ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
    | m2_yellow_6(X2,X0,X1) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_waybel_0(X2,X0) != iProver_top
    | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8910,c_7600])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,sK2(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1654,plain,
    ( r3_waybel_9(X0,sK2(X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11309,plain,
    ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | l1_waybel_0(sK2(X1),X1) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK2(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK2(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11304,c_1654])).

cnf(c_11546,plain,
    ( l1_waybel_0(sK2(X1),X1) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK2(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK2(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11309,c_7600])).

cnf(c_11547,plain,
    ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | l1_waybel_0(sK2(X1),X1) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK2(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK2(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11546])).

cnf(c_1652,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_waybel_0(sK2(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1651,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(sK2(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1650,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11566,plain,
    ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11547,c_1652,c_1651,c_1650,c_1653])).

cnf(c_11571,plain,
    ( l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
    | l1_waybel_0(sK2(sK4),sK4) != iProver_top
    | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK6(sK2(sK4))) = iProver_top
    | v2_struct_0(sK2(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK6(sK2(sK4))) != iProver_top
    | v4_orders_2(sK2(sK4)) != iProver_top
    | v7_waybel_0(sK6(sK2(sK4))) != iProver_top
    | v7_waybel_0(sK2(sK4)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_11566])).

cnf(c_11617,plain,
    ( v1_compts_1(sK4) = iProver_top
    | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11571,c_40,c_41,c_42,c_64,c_67,c_70,c_73,c_102,c_2448,c_2580,c_4493,c_5939,c_6658])).

cnf(c_11618,plain,
    ( r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_11617])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1671,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1669,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2466,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1669])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1673,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4610,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_1673])).

cnf(c_11626,plain,
    ( k10_yellow_6(sK4,sK6(sK2(sK4))) = k1_xboole_0
    | v1_compts_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_11618,c_4610])).

cnf(c_11838,plain,
    ( v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6691,c_40,c_41,c_42,c_64,c_67,c_70,c_73,c_102,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,c_11626])).

cnf(c_36586,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11284,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,c_73,c_102,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,c_11626])).

cnf(c_36587,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
    | r3_waybel_9(sK4,sK5,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36586])).

cnf(c_36595,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_36587])).

cnf(c_29,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2277,plain,
    ( ~ l1_waybel_0(sK5,X0)
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2278,plain,
    ( l1_waybel_0(sK5,X0) != iProver_top
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0)) = iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2280,plain,
    ( l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_37263,plain,
    ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36595,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,c_73,c_102,c_2280,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,c_11626])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_1656,plain,
    ( r3_waybel_9(X0,X1,X2) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_37290,plain,
    ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) != iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_37263,c_1656])).

cnf(c_2282,plain,
    ( r3_waybel_9(X0,sK5,sK3(X0,sK5))
    | ~ l1_waybel_0(sK5,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2283,plain,
    ( r3_waybel_9(X0,sK5,sK3(X0,sK5)) = iProver_top
    | l1_waybel_0(sK5,X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_2285,plain,
    ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) = iProver_top
    | l1_waybel_0(sK5,sK4) != iProver_top
    | v1_compts_1(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_37930,plain,
    ( r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37290,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,c_73,c_102,c_2280,c_2285,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,c_11626])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1667,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_37936,plain,
    ( r1_tarski(k1_xboole_0,sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37930,c_1667])).

cnf(c_38074,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37936,c_2466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:54:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.54/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/1.99  
% 11.54/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.54/1.99  
% 11.54/1.99  ------  iProver source info
% 11.54/1.99  
% 11.54/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.54/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.54/1.99  git: non_committed_changes: false
% 11.54/1.99  git: last_make_outside_of_git: false
% 11.54/1.99  
% 11.54/1.99  ------ 
% 11.54/1.99  
% 11.54/1.99  ------ Input Options
% 11.54/1.99  
% 11.54/1.99  --out_options                           all
% 11.54/1.99  --tptp_safe_out                         true
% 11.54/1.99  --problem_path                          ""
% 11.54/1.99  --include_path                          ""
% 11.54/1.99  --clausifier                            res/vclausify_rel
% 11.54/1.99  --clausifier_options                    --mode clausify
% 11.54/1.99  --stdin                                 false
% 11.54/1.99  --stats_out                             sel
% 11.54/1.99  
% 11.54/1.99  ------ General Options
% 11.54/1.99  
% 11.54/1.99  --fof                                   false
% 11.54/1.99  --time_out_real                         604.99
% 11.54/1.99  --time_out_virtual                      -1.
% 11.54/1.99  --symbol_type_check                     false
% 11.54/1.99  --clausify_out                          false
% 11.54/1.99  --sig_cnt_out                           false
% 11.54/1.99  --trig_cnt_out                          false
% 11.54/1.99  --trig_cnt_out_tolerance                1.
% 11.54/1.99  --trig_cnt_out_sk_spl                   false
% 11.54/1.99  --abstr_cl_out                          false
% 11.54/1.99  
% 11.54/1.99  ------ Global Options
% 11.54/1.99  
% 11.54/1.99  --schedule                              none
% 11.54/1.99  --add_important_lit                     false
% 11.54/1.99  --prop_solver_per_cl                    1000
% 11.54/1.99  --min_unsat_core                        false
% 11.54/1.99  --soft_assumptions                      false
% 11.54/1.99  --soft_lemma_size                       3
% 11.54/1.99  --prop_impl_unit_size                   0
% 11.54/1.99  --prop_impl_unit                        []
% 11.54/1.99  --share_sel_clauses                     true
% 11.54/1.99  --reset_solvers                         false
% 11.54/1.99  --bc_imp_inh                            [conj_cone]
% 11.54/1.99  --conj_cone_tolerance                   3.
% 11.54/1.99  --extra_neg_conj                        none
% 11.54/1.99  --large_theory_mode                     true
% 11.54/1.99  --prolific_symb_bound                   200
% 11.54/1.99  --lt_threshold                          2000
% 11.54/1.99  --clause_weak_htbl                      true
% 11.54/1.99  --gc_record_bc_elim                     false
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing Options
% 11.54/1.99  
% 11.54/1.99  --preprocessing_flag                    true
% 11.54/1.99  --time_out_prep_mult                    0.1
% 11.54/1.99  --splitting_mode                        input
% 11.54/1.99  --splitting_grd                         true
% 11.54/1.99  --splitting_cvd                         false
% 11.54/1.99  --splitting_cvd_svl                     false
% 11.54/1.99  --splitting_nvd                         32
% 11.54/1.99  --sub_typing                            true
% 11.54/1.99  --prep_gs_sim                           false
% 11.54/1.99  --prep_unflatten                        true
% 11.54/1.99  --prep_res_sim                          true
% 11.54/1.99  --prep_upred                            true
% 11.54/1.99  --prep_sem_filter                       exhaustive
% 11.54/1.99  --prep_sem_filter_out                   false
% 11.54/1.99  --pred_elim                             false
% 11.54/1.99  --res_sim_input                         true
% 11.54/1.99  --eq_ax_congr_red                       true
% 11.54/1.99  --pure_diseq_elim                       true
% 11.54/1.99  --brand_transform                       false
% 11.54/1.99  --non_eq_to_eq                          false
% 11.54/1.99  --prep_def_merge                        true
% 11.54/1.99  --prep_def_merge_prop_impl              false
% 11.54/1.99  --prep_def_merge_mbd                    true
% 11.54/1.99  --prep_def_merge_tr_red                 false
% 11.54/1.99  --prep_def_merge_tr_cl                  false
% 11.54/1.99  --smt_preprocessing                     true
% 11.54/1.99  --smt_ac_axioms                         fast
% 11.54/1.99  --preprocessed_out                      false
% 11.54/1.99  --preprocessed_stats                    false
% 11.54/1.99  
% 11.54/1.99  ------ Abstraction refinement Options
% 11.54/1.99  
% 11.54/1.99  --abstr_ref                             []
% 11.54/1.99  --abstr_ref_prep                        false
% 11.54/1.99  --abstr_ref_until_sat                   false
% 11.54/1.99  --abstr_ref_sig_restrict                funpre
% 11.54/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.99  --abstr_ref_under                       []
% 11.54/1.99  
% 11.54/1.99  ------ SAT Options
% 11.54/1.99  
% 11.54/1.99  --sat_mode                              false
% 11.54/1.99  --sat_fm_restart_options                ""
% 11.54/1.99  --sat_gr_def                            false
% 11.54/1.99  --sat_epr_types                         true
% 11.54/1.99  --sat_non_cyclic_types                  false
% 11.54/1.99  --sat_finite_models                     false
% 11.54/1.99  --sat_fm_lemmas                         false
% 11.54/1.99  --sat_fm_prep                           false
% 11.54/1.99  --sat_fm_uc_incr                        true
% 11.54/1.99  --sat_out_model                         small
% 11.54/1.99  --sat_out_clauses                       false
% 11.54/1.99  
% 11.54/1.99  ------ QBF Options
% 11.54/1.99  
% 11.54/1.99  --qbf_mode                              false
% 11.54/1.99  --qbf_elim_univ                         false
% 11.54/1.99  --qbf_dom_inst                          none
% 11.54/1.99  --qbf_dom_pre_inst                      false
% 11.54/1.99  --qbf_sk_in                             false
% 11.54/1.99  --qbf_pred_elim                         true
% 11.54/1.99  --qbf_split                             512
% 11.54/1.99  
% 11.54/1.99  ------ BMC1 Options
% 11.54/1.99  
% 11.54/1.99  --bmc1_incremental                      false
% 11.54/1.99  --bmc1_axioms                           reachable_all
% 11.54/1.99  --bmc1_min_bound                        0
% 11.54/1.99  --bmc1_max_bound                        -1
% 11.54/1.99  --bmc1_max_bound_default                -1
% 11.54/1.99  --bmc1_symbol_reachability              true
% 11.54/1.99  --bmc1_property_lemmas                  false
% 11.54/1.99  --bmc1_k_induction                      false
% 11.54/1.99  --bmc1_non_equiv_states                 false
% 11.54/1.99  --bmc1_deadlock                         false
% 11.54/1.99  --bmc1_ucm                              false
% 11.54/1.99  --bmc1_add_unsat_core                   none
% 11.54/1.99  --bmc1_unsat_core_children              false
% 11.54/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.99  --bmc1_out_stat                         full
% 11.54/1.99  --bmc1_ground_init                      false
% 11.54/1.99  --bmc1_pre_inst_next_state              false
% 11.54/1.99  --bmc1_pre_inst_state                   false
% 11.54/1.99  --bmc1_pre_inst_reach_state             false
% 11.54/1.99  --bmc1_out_unsat_core                   false
% 11.54/1.99  --bmc1_aig_witness_out                  false
% 11.54/1.99  --bmc1_verbose                          false
% 11.54/1.99  --bmc1_dump_clauses_tptp                false
% 11.54/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.99  --bmc1_dump_file                        -
% 11.54/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.99  --bmc1_ucm_extend_mode                  1
% 11.54/1.99  --bmc1_ucm_init_mode                    2
% 11.54/1.99  --bmc1_ucm_cone_mode                    none
% 11.54/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.99  --bmc1_ucm_relax_model                  4
% 11.54/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.99  --bmc1_ucm_layered_model                none
% 11.54/1.99  --bmc1_ucm_max_lemma_size               10
% 11.54/1.99  
% 11.54/1.99  ------ AIG Options
% 11.54/1.99  
% 11.54/1.99  --aig_mode                              false
% 11.54/1.99  
% 11.54/1.99  ------ Instantiation Options
% 11.54/1.99  
% 11.54/1.99  --instantiation_flag                    true
% 11.54/1.99  --inst_sos_flag                         false
% 11.54/1.99  --inst_sos_phase                        true
% 11.54/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel_side                     num_symb
% 11.54/1.99  --inst_solver_per_active                1400
% 11.54/1.99  --inst_solver_calls_frac                1.
% 11.54/1.99  --inst_passive_queue_type               priority_queues
% 11.54/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.99  --inst_passive_queues_freq              [25;2]
% 11.54/1.99  --inst_dismatching                      true
% 11.54/1.99  --inst_eager_unprocessed_to_passive     true
% 11.54/1.99  --inst_prop_sim_given                   true
% 11.54/1.99  --inst_prop_sim_new                     false
% 11.54/1.99  --inst_subs_new                         false
% 11.54/1.99  --inst_eq_res_simp                      false
% 11.54/1.99  --inst_subs_given                       false
% 11.54/1.99  --inst_orphan_elimination               true
% 11.54/1.99  --inst_learning_loop_flag               true
% 11.54/1.99  --inst_learning_start                   3000
% 11.54/1.99  --inst_learning_factor                  2
% 11.54/1.99  --inst_start_prop_sim_after_learn       3
% 11.54/1.99  --inst_sel_renew                        solver
% 11.54/1.99  --inst_lit_activity_flag                true
% 11.54/1.99  --inst_restr_to_given                   false
% 11.54/1.99  --inst_activity_threshold               500
% 11.54/1.99  --inst_out_proof                        true
% 11.54/1.99  
% 11.54/1.99  ------ Resolution Options
% 11.54/1.99  
% 11.54/1.99  --resolution_flag                       true
% 11.54/1.99  --res_lit_sel                           adaptive
% 11.54/1.99  --res_lit_sel_side                      none
% 11.54/1.99  --res_ordering                          kbo
% 11.54/1.99  --res_to_prop_solver                    active
% 11.54/1.99  --res_prop_simpl_new                    false
% 11.54/1.99  --res_prop_simpl_given                  true
% 11.54/1.99  --res_passive_queue_type                priority_queues
% 11.54/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/1.99  --res_passive_queues_freq               [15;5]
% 11.54/1.99  --res_forward_subs                      full
% 11.54/1.99  --res_backward_subs                     full
% 11.54/1.99  --res_forward_subs_resolution           true
% 11.54/1.99  --res_backward_subs_resolution          true
% 11.54/1.99  --res_orphan_elimination                true
% 11.54/1.99  --res_time_limit                        2.
% 11.54/1.99  --res_out_proof                         true
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Options
% 11.54/1.99  
% 11.54/1.99  --superposition_flag                    true
% 11.54/1.99  --sup_passive_queue_type                priority_queues
% 11.54/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/1.99  --sup_passive_queues_freq               [1;4]
% 11.54/1.99  --demod_completeness_check              fast
% 11.54/1.99  --demod_use_ground                      true
% 11.54/1.99  --sup_to_prop_solver                    passive
% 11.54/1.99  --sup_prop_simpl_new                    true
% 11.54/1.99  --sup_prop_simpl_given                  true
% 11.54/1.99  --sup_fun_splitting                     false
% 11.54/1.99  --sup_smt_interval                      50000
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Simplification Setup
% 11.54/1.99  
% 11.54/1.99  --sup_indices_passive                   []
% 11.54/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_full_bw                           [BwDemod]
% 11.54/1.99  --sup_immed_triv                        [TrivRules]
% 11.54/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_immed_bw_main                     []
% 11.54/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/1.99  
% 11.54/1.99  ------ Combination Options
% 11.54/1.99  
% 11.54/1.99  --comb_res_mult                         3
% 11.54/1.99  --comb_sup_mult                         2
% 11.54/1.99  --comb_inst_mult                        10
% 11.54/1.99  
% 11.54/1.99  ------ Debug Options
% 11.54/1.99  
% 11.54/1.99  --dbg_backtrace                         false
% 11.54/1.99  --dbg_dump_prop_clauses                 false
% 11.54/1.99  --dbg_dump_prop_clauses_file            -
% 11.54/1.99  --dbg_out_stat                          false
% 11.54/1.99  ------ Parsing...
% 11.54/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.54/1.99  ------ Proving...
% 11.54/1.99  ------ Problem Properties 
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  clauses                                 39
% 11.54/1.99  conjectures                             10
% 11.54/1.99  EPR                                     17
% 11.54/1.99  Horn                                    18
% 11.54/1.99  unary                                   5
% 11.54/1.99  binary                                  10
% 11.54/1.99  lits                                    192
% 11.54/1.99  lits eq                                 3
% 11.54/1.99  fd_pure                                 0
% 11.54/1.99  fd_pseudo                               0
% 11.54/1.99  fd_cond                                 0
% 11.54/1.99  fd_pseudo_cond                          1
% 11.54/1.99  AC symbols                              0
% 11.54/1.99  
% 11.54/1.99  ------ Input Options Time Limit: Unbounded
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  ------ 
% 11.54/1.99  Current options:
% 11.54/1.99  ------ 
% 11.54/1.99  
% 11.54/1.99  ------ Input Options
% 11.54/1.99  
% 11.54/1.99  --out_options                           all
% 11.54/1.99  --tptp_safe_out                         true
% 11.54/1.99  --problem_path                          ""
% 11.54/1.99  --include_path                          ""
% 11.54/1.99  --clausifier                            res/vclausify_rel
% 11.54/1.99  --clausifier_options                    --mode clausify
% 11.54/1.99  --stdin                                 false
% 11.54/1.99  --stats_out                             sel
% 11.54/1.99  
% 11.54/1.99  ------ General Options
% 11.54/1.99  
% 11.54/1.99  --fof                                   false
% 11.54/1.99  --time_out_real                         604.99
% 11.54/1.99  --time_out_virtual                      -1.
% 11.54/1.99  --symbol_type_check                     false
% 11.54/1.99  --clausify_out                          false
% 11.54/1.99  --sig_cnt_out                           false
% 11.54/1.99  --trig_cnt_out                          false
% 11.54/1.99  --trig_cnt_out_tolerance                1.
% 11.54/1.99  --trig_cnt_out_sk_spl                   false
% 11.54/1.99  --abstr_cl_out                          false
% 11.54/1.99  
% 11.54/1.99  ------ Global Options
% 11.54/1.99  
% 11.54/1.99  --schedule                              none
% 11.54/1.99  --add_important_lit                     false
% 11.54/1.99  --prop_solver_per_cl                    1000
% 11.54/1.99  --min_unsat_core                        false
% 11.54/1.99  --soft_assumptions                      false
% 11.54/1.99  --soft_lemma_size                       3
% 11.54/1.99  --prop_impl_unit_size                   0
% 11.54/1.99  --prop_impl_unit                        []
% 11.54/1.99  --share_sel_clauses                     true
% 11.54/1.99  --reset_solvers                         false
% 11.54/1.99  --bc_imp_inh                            [conj_cone]
% 11.54/1.99  --conj_cone_tolerance                   3.
% 11.54/1.99  --extra_neg_conj                        none
% 11.54/1.99  --large_theory_mode                     true
% 11.54/1.99  --prolific_symb_bound                   200
% 11.54/1.99  --lt_threshold                          2000
% 11.54/1.99  --clause_weak_htbl                      true
% 11.54/1.99  --gc_record_bc_elim                     false
% 11.54/1.99  
% 11.54/1.99  ------ Preprocessing Options
% 11.54/1.99  
% 11.54/1.99  --preprocessing_flag                    true
% 11.54/1.99  --time_out_prep_mult                    0.1
% 11.54/1.99  --splitting_mode                        input
% 11.54/1.99  --splitting_grd                         true
% 11.54/1.99  --splitting_cvd                         false
% 11.54/1.99  --splitting_cvd_svl                     false
% 11.54/1.99  --splitting_nvd                         32
% 11.54/1.99  --sub_typing                            true
% 11.54/1.99  --prep_gs_sim                           false
% 11.54/1.99  --prep_unflatten                        true
% 11.54/1.99  --prep_res_sim                          true
% 11.54/1.99  --prep_upred                            true
% 11.54/1.99  --prep_sem_filter                       exhaustive
% 11.54/1.99  --prep_sem_filter_out                   false
% 11.54/1.99  --pred_elim                             false
% 11.54/1.99  --res_sim_input                         true
% 11.54/1.99  --eq_ax_congr_red                       true
% 11.54/1.99  --pure_diseq_elim                       true
% 11.54/1.99  --brand_transform                       false
% 11.54/1.99  --non_eq_to_eq                          false
% 11.54/1.99  --prep_def_merge                        true
% 11.54/1.99  --prep_def_merge_prop_impl              false
% 11.54/1.99  --prep_def_merge_mbd                    true
% 11.54/1.99  --prep_def_merge_tr_red                 false
% 11.54/1.99  --prep_def_merge_tr_cl                  false
% 11.54/1.99  --smt_preprocessing                     true
% 11.54/1.99  --smt_ac_axioms                         fast
% 11.54/1.99  --preprocessed_out                      false
% 11.54/1.99  --preprocessed_stats                    false
% 11.54/1.99  
% 11.54/1.99  ------ Abstraction refinement Options
% 11.54/1.99  
% 11.54/1.99  --abstr_ref                             []
% 11.54/1.99  --abstr_ref_prep                        false
% 11.54/1.99  --abstr_ref_until_sat                   false
% 11.54/1.99  --abstr_ref_sig_restrict                funpre
% 11.54/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/1.99  --abstr_ref_under                       []
% 11.54/1.99  
% 11.54/1.99  ------ SAT Options
% 11.54/1.99  
% 11.54/1.99  --sat_mode                              false
% 11.54/1.99  --sat_fm_restart_options                ""
% 11.54/1.99  --sat_gr_def                            false
% 11.54/1.99  --sat_epr_types                         true
% 11.54/1.99  --sat_non_cyclic_types                  false
% 11.54/1.99  --sat_finite_models                     false
% 11.54/1.99  --sat_fm_lemmas                         false
% 11.54/1.99  --sat_fm_prep                           false
% 11.54/1.99  --sat_fm_uc_incr                        true
% 11.54/1.99  --sat_out_model                         small
% 11.54/1.99  --sat_out_clauses                       false
% 11.54/1.99  
% 11.54/1.99  ------ QBF Options
% 11.54/1.99  
% 11.54/1.99  --qbf_mode                              false
% 11.54/1.99  --qbf_elim_univ                         false
% 11.54/1.99  --qbf_dom_inst                          none
% 11.54/1.99  --qbf_dom_pre_inst                      false
% 11.54/1.99  --qbf_sk_in                             false
% 11.54/1.99  --qbf_pred_elim                         true
% 11.54/1.99  --qbf_split                             512
% 11.54/1.99  
% 11.54/1.99  ------ BMC1 Options
% 11.54/1.99  
% 11.54/1.99  --bmc1_incremental                      false
% 11.54/1.99  --bmc1_axioms                           reachable_all
% 11.54/1.99  --bmc1_min_bound                        0
% 11.54/1.99  --bmc1_max_bound                        -1
% 11.54/1.99  --bmc1_max_bound_default                -1
% 11.54/1.99  --bmc1_symbol_reachability              true
% 11.54/1.99  --bmc1_property_lemmas                  false
% 11.54/1.99  --bmc1_k_induction                      false
% 11.54/1.99  --bmc1_non_equiv_states                 false
% 11.54/1.99  --bmc1_deadlock                         false
% 11.54/1.99  --bmc1_ucm                              false
% 11.54/1.99  --bmc1_add_unsat_core                   none
% 11.54/1.99  --bmc1_unsat_core_children              false
% 11.54/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/1.99  --bmc1_out_stat                         full
% 11.54/1.99  --bmc1_ground_init                      false
% 11.54/1.99  --bmc1_pre_inst_next_state              false
% 11.54/1.99  --bmc1_pre_inst_state                   false
% 11.54/1.99  --bmc1_pre_inst_reach_state             false
% 11.54/1.99  --bmc1_out_unsat_core                   false
% 11.54/1.99  --bmc1_aig_witness_out                  false
% 11.54/1.99  --bmc1_verbose                          false
% 11.54/1.99  --bmc1_dump_clauses_tptp                false
% 11.54/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.54/1.99  --bmc1_dump_file                        -
% 11.54/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.54/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.54/1.99  --bmc1_ucm_extend_mode                  1
% 11.54/1.99  --bmc1_ucm_init_mode                    2
% 11.54/1.99  --bmc1_ucm_cone_mode                    none
% 11.54/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.54/1.99  --bmc1_ucm_relax_model                  4
% 11.54/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.54/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/1.99  --bmc1_ucm_layered_model                none
% 11.54/1.99  --bmc1_ucm_max_lemma_size               10
% 11.54/1.99  
% 11.54/1.99  ------ AIG Options
% 11.54/1.99  
% 11.54/1.99  --aig_mode                              false
% 11.54/1.99  
% 11.54/1.99  ------ Instantiation Options
% 11.54/1.99  
% 11.54/1.99  --instantiation_flag                    true
% 11.54/1.99  --inst_sos_flag                         false
% 11.54/1.99  --inst_sos_phase                        true
% 11.54/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/1.99  --inst_lit_sel_side                     num_symb
% 11.54/1.99  --inst_solver_per_active                1400
% 11.54/1.99  --inst_solver_calls_frac                1.
% 11.54/1.99  --inst_passive_queue_type               priority_queues
% 11.54/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/1.99  --inst_passive_queues_freq              [25;2]
% 11.54/1.99  --inst_dismatching                      true
% 11.54/1.99  --inst_eager_unprocessed_to_passive     true
% 11.54/1.99  --inst_prop_sim_given                   true
% 11.54/1.99  --inst_prop_sim_new                     false
% 11.54/1.99  --inst_subs_new                         false
% 11.54/1.99  --inst_eq_res_simp                      false
% 11.54/1.99  --inst_subs_given                       false
% 11.54/1.99  --inst_orphan_elimination               true
% 11.54/1.99  --inst_learning_loop_flag               true
% 11.54/1.99  --inst_learning_start                   3000
% 11.54/1.99  --inst_learning_factor                  2
% 11.54/1.99  --inst_start_prop_sim_after_learn       3
% 11.54/1.99  --inst_sel_renew                        solver
% 11.54/1.99  --inst_lit_activity_flag                true
% 11.54/1.99  --inst_restr_to_given                   false
% 11.54/1.99  --inst_activity_threshold               500
% 11.54/1.99  --inst_out_proof                        true
% 11.54/1.99  
% 11.54/1.99  ------ Resolution Options
% 11.54/1.99  
% 11.54/1.99  --resolution_flag                       true
% 11.54/1.99  --res_lit_sel                           adaptive
% 11.54/1.99  --res_lit_sel_side                      none
% 11.54/1.99  --res_ordering                          kbo
% 11.54/1.99  --res_to_prop_solver                    active
% 11.54/1.99  --res_prop_simpl_new                    false
% 11.54/1.99  --res_prop_simpl_given                  true
% 11.54/1.99  --res_passive_queue_type                priority_queues
% 11.54/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/1.99  --res_passive_queues_freq               [15;5]
% 11.54/1.99  --res_forward_subs                      full
% 11.54/1.99  --res_backward_subs                     full
% 11.54/1.99  --res_forward_subs_resolution           true
% 11.54/1.99  --res_backward_subs_resolution          true
% 11.54/1.99  --res_orphan_elimination                true
% 11.54/1.99  --res_time_limit                        2.
% 11.54/1.99  --res_out_proof                         true
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Options
% 11.54/1.99  
% 11.54/1.99  --superposition_flag                    true
% 11.54/1.99  --sup_passive_queue_type                priority_queues
% 11.54/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/1.99  --sup_passive_queues_freq               [1;4]
% 11.54/1.99  --demod_completeness_check              fast
% 11.54/1.99  --demod_use_ground                      true
% 11.54/1.99  --sup_to_prop_solver                    passive
% 11.54/1.99  --sup_prop_simpl_new                    true
% 11.54/1.99  --sup_prop_simpl_given                  true
% 11.54/1.99  --sup_fun_splitting                     false
% 11.54/1.99  --sup_smt_interval                      50000
% 11.54/1.99  
% 11.54/1.99  ------ Superposition Simplification Setup
% 11.54/1.99  
% 11.54/1.99  --sup_indices_passive                   []
% 11.54/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_full_bw                           [BwDemod]
% 11.54/1.99  --sup_immed_triv                        [TrivRules]
% 11.54/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_immed_bw_main                     []
% 11.54/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/1.99  
% 11.54/1.99  ------ Combination Options
% 11.54/1.99  
% 11.54/1.99  --comb_res_mult                         3
% 11.54/1.99  --comb_sup_mult                         2
% 11.54/1.99  --comb_inst_mult                        10
% 11.54/1.99  
% 11.54/1.99  ------ Debug Options
% 11.54/1.99  
% 11.54/1.99  --dbg_backtrace                         false
% 11.54/1.99  --dbg_dump_prop_clauses                 false
% 11.54/1.99  --dbg_dump_prop_clauses_file            -
% 11.54/1.99  --dbg_out_stat                          false
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  ------ Proving...
% 11.54/1.99  
% 11.54/1.99  
% 11.54/1.99  % SZS status Theorem for theBenchmark.p
% 11.54/1.99  
% 11.54/1.99   Resolution empty clause
% 11.54/1.99  
% 11.54/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.54/1.99  
% 11.54/1.99  fof(f14,axiom,(
% 11.54/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 11.54/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/1.99  
% 11.54/1.99  fof(f34,plain,(
% 11.54/1.99    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/1.99    inference(ennf_transformation,[],[f14])).
% 11.54/1.99  
% 11.54/1.99  fof(f35,plain,(
% 11.54/1.99    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/1.99    inference(flattening,[],[f34])).
% 11.54/1.99  
% 11.54/1.99  fof(f48,plain,(
% 11.54/1.99    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(nnf_transformation,[],[f35])).
% 11.54/2.00  
% 11.54/2.00  fof(f49,plain,(
% 11.54/2.00    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(rectify,[],[f48])).
% 11.54/2.00  
% 11.54/2.00  fof(f51,plain,(
% 11.54/2.00    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK3(X0,X3)) & m1_subset_1(sK3(X0,X3),u1_struct_0(X0))))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f50,plain,(
% 11.54/2.00    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2(X0),X0) & v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0))))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f52,plain,(
% 11.54/2.00    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK2(X0),X0) & v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK3(X0,X3)) & m1_subset_1(sK3(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).
% 11.54/2.00  
% 11.54/2.00  fof(f84,plain,(
% 11.54/2.00    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK3(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f13,axiom,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f32,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f13])).
% 11.54/2.00  
% 11.54/2.00  fof(f33,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f32])).
% 11.54/2.00  
% 11.54/2.00  fof(f46,plain,(
% 11.54/2.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f47,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f46])).
% 11.54/2.00  
% 11.54/2.00  fof(f81,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (m2_yellow_6(sK1(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f47])).
% 11.54/2.00  
% 11.54/2.00  fof(f9,axiom,(
% 11.54/2.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f24,plain,(
% 11.54/2.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f9])).
% 11.54/2.00  
% 11.54/2.00  fof(f25,plain,(
% 11.54/2.00    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f24])).
% 11.54/2.00  
% 11.54/2.00  fof(f76,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f25])).
% 11.54/2.00  
% 11.54/2.00  fof(f7,axiom,(
% 11.54/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f21,plain,(
% 11.54/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.54/2.00    inference(ennf_transformation,[],[f7])).
% 11.54/2.00  
% 11.54/2.00  fof(f71,plain,(
% 11.54/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f21])).
% 11.54/2.00  
% 11.54/2.00  fof(f10,axiom,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f26,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f10])).
% 11.54/2.00  
% 11.54/2.00  fof(f27,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f26])).
% 11.54/2.00  
% 11.54/2.00  fof(f45,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(nnf_transformation,[],[f27])).
% 11.54/2.00  
% 11.54/2.00  fof(f78,plain,(
% 11.54/2.00    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f45])).
% 11.54/2.00  
% 11.54/2.00  fof(f75,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f25])).
% 11.54/2.00  
% 11.54/2.00  fof(f74,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f25])).
% 11.54/2.00  
% 11.54/2.00  fof(f73,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f25])).
% 11.54/2.00  
% 11.54/2.00  fof(f15,conjecture,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f16,negated_conjecture,(
% 11.54/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 11.54/2.00    inference(negated_conjecture,[],[f15])).
% 11.54/2.00  
% 11.54/2.00  fof(f36,plain,(
% 11.54/2.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f16])).
% 11.54/2.00  
% 11.54/2.00  fof(f37,plain,(
% 11.54/2.00    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f36])).
% 11.54/2.00  
% 11.54/2.00  fof(f53,plain,(
% 11.54/2.00    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.54/2.00    inference(nnf_transformation,[],[f37])).
% 11.54/2.00  
% 11.54/2.00  fof(f54,plain,(
% 11.54/2.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f53])).
% 11.54/2.00  
% 11.54/2.00  fof(f55,plain,(
% 11.54/2.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.54/2.00    inference(rectify,[],[f54])).
% 11.54/2.00  
% 11.54/2.00  fof(f58,plain,(
% 11.54/2.00    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK6(X3),X0) & m2_yellow_6(sK6(X3),X0,X3)))) )),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f57,plain,(
% 11.54/2.00    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK5)) & l1_waybel_0(sK5,X0) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5))) )),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f56,plain,(
% 11.54/2.00    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,X1)) & l1_waybel_0(X1,sK4) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK4)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK4) & m2_yellow_6(X4,sK4,X3)) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f59,plain,(
% 11.54/2.00    ((! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,sK5)) & l1_waybel_0(sK5,sK4) & v7_waybel_0(sK5) & v4_orders_2(sK5) & ~v2_struct_0(sK5)) | ~v1_compts_1(sK4)) & (! [X3] : ((v3_yellow_6(sK6(X3),sK4) & m2_yellow_6(sK6(X3),sK4,X3)) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK4)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.54/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f55,f58,f57,f56])).
% 11.54/2.00  
% 11.54/2.00  fof(f99,plain,(
% 11.54/2.00    ( ! [X2] : (~v3_yellow_6(X2,sK4) | ~m2_yellow_6(X2,sK4,sK5) | ~v1_compts_1(sK4)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f90,plain,(
% 11.54/2.00    ~v2_struct_0(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f91,plain,(
% 11.54/2.00    v2_pre_topc(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f92,plain,(
% 11.54/2.00    l1_pre_topc(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f95,plain,(
% 11.54/2.00    ~v2_struct_0(sK5) | ~v1_compts_1(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f96,plain,(
% 11.54/2.00    v4_orders_2(sK5) | ~v1_compts_1(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f97,plain,(
% 11.54/2.00    v7_waybel_0(sK5) | ~v1_compts_1(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f98,plain,(
% 11.54/2.00    l1_waybel_0(sK5,sK4) | ~v1_compts_1(sK4)),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f93,plain,(
% 11.54/2.00    ( ! [X3] : (m2_yellow_6(sK6(X3),sK4,X3) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK4)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f85,plain,(
% 11.54/2.00    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f86,plain,(
% 11.54/2.00    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f87,plain,(
% 11.54/2.00    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f88,plain,(
% 11.54/2.00    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f94,plain,(
% 11.54/2.00    ( ! [X3] : (v3_yellow_6(sK6(X3),sK4) | ~l1_waybel_0(X3,sK4) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK4)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f59])).
% 11.54/2.00  
% 11.54/2.00  fof(f77,plain,(
% 11.54/2.00    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f45])).
% 11.54/2.00  
% 11.54/2.00  fof(f1,axiom,(
% 11.54/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f17,plain,(
% 11.54/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f1])).
% 11.54/2.00  
% 11.54/2.00  fof(f38,plain,(
% 11.54/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.54/2.00    inference(nnf_transformation,[],[f17])).
% 11.54/2.00  
% 11.54/2.00  fof(f39,plain,(
% 11.54/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.54/2.00    inference(rectify,[],[f38])).
% 11.54/2.00  
% 11.54/2.00  fof(f40,plain,(
% 11.54/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.54/2.00    introduced(choice_axiom,[])).
% 11.54/2.00  
% 11.54/2.00  fof(f41,plain,(
% 11.54/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.54/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 11.54/2.00  
% 11.54/2.00  fof(f61,plain,(
% 11.54/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f41])).
% 11.54/2.00  
% 11.54/2.00  fof(f11,axiom,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f28,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f11])).
% 11.54/2.00  
% 11.54/2.00  fof(f29,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f28])).
% 11.54/2.00  
% 11.54/2.00  fof(f79,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f29])).
% 11.54/2.00  
% 11.54/2.00  fof(f8,axiom,(
% 11.54/2.00    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f22,plain,(
% 11.54/2.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f8])).
% 11.54/2.00  
% 11.54/2.00  fof(f23,plain,(
% 11.54/2.00    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f22])).
% 11.54/2.00  
% 11.54/2.00  fof(f72,plain,(
% 11.54/2.00    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f23])).
% 11.54/2.00  
% 11.54/2.00  fof(f5,axiom,(
% 11.54/2.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f18,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.54/2.00    inference(ennf_transformation,[],[f5])).
% 11.54/2.00  
% 11.54/2.00  fof(f19,plain,(
% 11.54/2.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.54/2.00    inference(flattening,[],[f18])).
% 11.54/2.00  
% 11.54/2.00  fof(f69,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f19])).
% 11.54/2.00  
% 11.54/2.00  fof(f12,axiom,(
% 11.54/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f30,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.54/2.00    inference(ennf_transformation,[],[f12])).
% 11.54/2.00  
% 11.54/2.00  fof(f31,plain,(
% 11.54/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.54/2.00    inference(flattening,[],[f30])).
% 11.54/2.00  
% 11.54/2.00  fof(f80,plain,(
% 11.54/2.00    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f31])).
% 11.54/2.00  
% 11.54/2.00  fof(f89,plain,(
% 11.54/2.00    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f3,axiom,(
% 11.54/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f66,plain,(
% 11.54/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f3])).
% 11.54/2.00  
% 11.54/2.00  fof(f4,axiom,(
% 11.54/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f44,plain,(
% 11.54/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.54/2.00    inference(nnf_transformation,[],[f4])).
% 11.54/2.00  
% 11.54/2.00  fof(f67,plain,(
% 11.54/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.54/2.00    inference(cnf_transformation,[],[f44])).
% 11.54/2.00  
% 11.54/2.00  fof(f2,axiom,(
% 11.54/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f42,plain,(
% 11.54/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.54/2.00    inference(nnf_transformation,[],[f2])).
% 11.54/2.00  
% 11.54/2.00  fof(f43,plain,(
% 11.54/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.54/2.00    inference(flattening,[],[f42])).
% 11.54/2.00  
% 11.54/2.00  fof(f65,plain,(
% 11.54/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f43])).
% 11.54/2.00  
% 11.54/2.00  fof(f83,plain,(
% 11.54/2.00    ( ! [X0,X3] : (m1_subset_1(sK3(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f52])).
% 11.54/2.00  
% 11.54/2.00  fof(f82,plain,(
% 11.54/2.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f47])).
% 11.54/2.00  
% 11.54/2.00  fof(f6,axiom,(
% 11.54/2.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.54/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.54/2.00  
% 11.54/2.00  fof(f20,plain,(
% 11.54/2.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.54/2.00    inference(ennf_transformation,[],[f6])).
% 11.54/2.00  
% 11.54/2.00  fof(f70,plain,(
% 11.54/2.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.54/2.00    inference(cnf_transformation,[],[f20])).
% 11.54/2.00  
% 11.54/2.00  cnf(c_28,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK3(X0,X1))
% 11.54/2.00      | ~ l1_waybel_0(X1,X0)
% 11.54/2.00      | ~ v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | ~ v4_orders_2(X1)
% 11.54/2.00      | ~ v7_waybel_0(X1)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1649,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK3(X0,X1)) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | v1_compts_1(X0) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_22,plain,
% 11.54/2.00      ( ~ r3_waybel_9(X0,X1,X2)
% 11.54/2.00      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 11.54/2.00      | ~ l1_waybel_0(X1,X0)
% 11.54/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | ~ v4_orders_2(X1)
% 11.54/2.00      | ~ v7_waybel_0(X1)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1655,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | m2_yellow_6(sK1(X0,X1,X2),X0,X1) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_13,plain,
% 11.54/2.00      ( ~ m2_yellow_6(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X2,X1)
% 11.54/2.00      | l1_waybel_0(X0,X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X2)
% 11.54/2.00      | ~ v4_orders_2(X2)
% 11.54/2.00      | ~ v7_waybel_0(X2)
% 11.54/2.00      | ~ l1_struct_0(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1664,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | l1_struct_0(X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3855,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1655,c_1664]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11,plain,
% 11.54/2.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_100,plain,
% 11.54/2.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7860,plain,
% 11.54/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,[status(thm)],[c_3855,c_100]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7861,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_7860]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_17,plain,
% 11.54/2.00      ( v3_yellow_6(X0,X1)
% 11.54/2.00      | ~ l1_waybel_0(X0,X1)
% 11.54/2.00      | ~ v2_pre_topc(X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1660,plain,
% 11.54/2.00      ( k10_yellow_6(X0,X1) = k1_xboole_0
% 11.54/2.00      | v3_yellow_6(X1,X0) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7876,plain,
% 11.54/2.00      ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(sK1(X0,X1,X2)) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK1(X0,X1,X2)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_7861,c_1660]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_14,plain,
% 11.54/2.00      ( ~ m2_yellow_6(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X2,X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X2)
% 11.54/2.00      | ~ v4_orders_2(X2)
% 11.54/2.00      | ~ v7_waybel_0(X2)
% 11.54/2.00      | v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_struct_0(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1663,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) = iProver_top
% 11.54/2.00      | l1_struct_0(X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3540,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1655,c_1663]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5920,plain,
% 11.54/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,[status(thm)],[c_3540,c_100]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5921,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_5920]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_15,plain,
% 11.54/2.00      ( ~ m2_yellow_6(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X2,X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X2)
% 11.54/2.00      | ~ v4_orders_2(X2)
% 11.54/2.00      | v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X2)
% 11.54/2.00      | ~ l1_struct_0(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1662,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v4_orders_2(X0) = iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | l1_struct_0(X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3541,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1655,c_1662]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6444,plain,
% 11.54/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,[status(thm)],[c_3541,c_100]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6445,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_6444]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_16,plain,
% 11.54/2.00      ( ~ m2_yellow_6(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X2,X1)
% 11.54/2.00      | ~ v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X2)
% 11.54/2.00      | ~ v4_orders_2(X2)
% 11.54/2.00      | ~ v7_waybel_0(X2)
% 11.54/2.00      | ~ l1_struct_0(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1661,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | l1_struct_0(X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3627,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1655,c_1661]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7450,plain,
% 11.54/2.00      ( l1_pre_topc(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,[status(thm)],[c_3627,c_100]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7451,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_7450]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11267,plain,
% 11.54/2.00      ( v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_7876,c_5921,c_6445,c_7451]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11268,plain,
% 11.54/2.00      ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.54/2.00      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_11267]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_30,negated_conjecture,
% 11.54/2.00      ( ~ m2_yellow_6(X0,sK4,sK5)
% 11.54/2.00      | ~ v3_yellow_6(X0,sK4)
% 11.54/2.00      | ~ v1_compts_1(sK4) ),
% 11.54/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1647,plain,
% 11.54/2.00      ( m2_yellow_6(X0,sK4,sK5) != iProver_top
% 11.54/2.00      | v3_yellow_6(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3542,plain,
% 11.54/2.00      ( r3_waybel_9(sK4,sK5,X0) != iProver_top
% 11.54/2.00      | v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1655,c_1647]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_39,negated_conjecture,
% 11.54/2.00      ( ~ v2_struct_0(sK4) ),
% 11.54/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_40,plain,
% 11.54/2.00      ( v2_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_38,negated_conjecture,
% 11.54/2.00      ( v2_pre_topc(sK4) ),
% 11.54/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_41,plain,
% 11.54/2.00      ( v2_pre_topc(sK4) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_37,negated_conjecture,
% 11.54/2.00      ( l1_pre_topc(sK4) ),
% 11.54/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_42,plain,
% 11.54/2.00      ( l1_pre_topc(sK4) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_34,negated_conjecture,
% 11.54/2.00      ( ~ v1_compts_1(sK4) | ~ v2_struct_0(sK5) ),
% 11.54/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_49,plain,
% 11.54/2.00      ( v1_compts_1(sK4) != iProver_top | v2_struct_0(sK5) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_33,negated_conjecture,
% 11.54/2.00      ( ~ v1_compts_1(sK4) | v4_orders_2(sK5) ),
% 11.54/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_50,plain,
% 11.54/2.00      ( v1_compts_1(sK4) != iProver_top | v4_orders_2(sK5) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_32,negated_conjecture,
% 11.54/2.00      ( ~ v1_compts_1(sK4) | v7_waybel_0(sK5) ),
% 11.54/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_51,plain,
% 11.54/2.00      ( v1_compts_1(sK4) != iProver_top | v7_waybel_0(sK5) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_31,negated_conjecture,
% 11.54/2.00      ( l1_waybel_0(sK5,sK4) | ~ v1_compts_1(sK4) ),
% 11.54/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_52,plain,
% 11.54/2.00      ( l1_waybel_0(sK5,sK4) = iProver_top | v1_compts_1(sK4) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6981,plain,
% 11.54/2.00      ( v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
% 11.54/2.00      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_3542,c_40,c_41,c_42,c_49,c_50,c_51,c_52]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6982,plain,
% 11.54/2.00      ( r3_waybel_9(sK4,sK5,X0) != iProver_top
% 11.54/2.00      | v3_yellow_6(sK1(sK4,sK5,X0),sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_6981]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11284,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 11.54/2.00      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11268,c_6982]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36,negated_conjecture,
% 11.54/2.00      ( m2_yellow_6(sK6(X0),sK4,X0)
% 11.54/2.00      | ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1641,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(X0),sK4,X0) = iProver_top
% 11.54/2.00      | l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3856,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(X0),sK4) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1641,c_1664]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_102,plain,
% 11.54/2.00      ( l1_pre_topc(sK4) != iProver_top | l1_struct_0(sK4) = iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_100]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6678,plain,
% 11.54/2.00      ( v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(X0),sK4) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_3856,c_40,c_42,c_102]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6679,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(X0),sK4) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_6678]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3444,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK6(X0)) = iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1641,c_1662]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4926,plain,
% 11.54/2.00      ( v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK6(X0)) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_3444,c_40,c_42,c_102]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4927,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK6(X0)) = iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_4926]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6691,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK6(X0)) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK6(X0)) != iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK6(X0))) = iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(X0)) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_6679,c_4927]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_27,plain,
% 11.54/2.00      ( v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v2_struct_0(sK2(X0))
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_62,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X0)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_64,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) != iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_62]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_26,plain,
% 11.54/2.00      ( v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v4_orders_2(sK2(X0))
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_65,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X0)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_67,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) = iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_65]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_25,plain,
% 11.54/2.00      ( v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v7_waybel_0(sK2(X0))
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_68,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X0)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_70,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_68]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_24,plain,
% 11.54/2.00      ( l1_waybel_0(sK2(X0),X0)
% 11.54/2.00      | v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_71,plain,
% 11.54/2.00      ( l1_waybel_0(sK2(X0),X0) = iProver_top
% 11.54/2.00      | v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_73,plain,
% 11.54/2.00      ( l1_waybel_0(sK2(sK4),sK4) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_71]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_35,negated_conjecture,
% 11.54/2.00      ( v3_yellow_6(sK6(X0),sK4)
% 11.54/2.00      | ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2421,plain,
% 11.54/2.00      ( v3_yellow_6(sK6(sK2(X0)),sK4)
% 11.54/2.00      | ~ l1_waybel_0(sK2(X0),sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(sK2(X0))
% 11.54/2.00      | ~ v4_orders_2(sK2(X0))
% 11.54/2.00      | ~ v7_waybel_0(sK2(X0)) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_35]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2442,plain,
% 11.54/2.00      ( v3_yellow_6(sK6(sK2(X0)),sK4) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(X0),sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X0)) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X0)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X0)) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2421]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2444,plain,
% 11.54/2.00      ( v3_yellow_6(sK6(sK2(sK4)),sK4) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2442]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2420,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0))
% 11.54/2.00      | ~ l1_waybel_0(sK2(X0),sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(sK2(X0))
% 11.54/2.00      | ~ v4_orders_2(sK2(X0))
% 11.54/2.00      | ~ v7_waybel_0(sK2(X0)) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_36]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2446,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0)) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(X0),sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X0)) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X0)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X0)) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2420]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2448,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2446]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_18,plain,
% 11.54/2.00      ( ~ v3_yellow_6(X0,X1)
% 11.54/2.00      | ~ l1_waybel_0(X0,X1)
% 11.54/2.00      | ~ v2_pre_topc(X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X1)
% 11.54/2.00      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2551,plain,
% 11.54/2.00      ( ~ v3_yellow_6(sK6(sK2(X0)),sK4)
% 11.54/2.00      | ~ l1_waybel_0(sK6(sK2(X0)),sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK6(sK2(X0)))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(sK6(sK2(X0)))
% 11.54/2.00      | ~ v7_waybel_0(sK6(sK2(X0)))
% 11.54/2.00      | ~ l1_pre_topc(sK4)
% 11.54/2.00      | k10_yellow_6(sK4,sK6(sK2(X0))) != k1_xboole_0 ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2557,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK6(sK2(X0))) != k1_xboole_0
% 11.54/2.00      | v3_yellow_6(sK6(sK2(X0)),sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(sK2(X0)),sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK6(sK2(X0))) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK2(X0))) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(sK2(X0))) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2551]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2559,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK6(sK2(sK4))) != k1_xboole_0
% 11.54/2.00      | v3_yellow_6(sK6(sK2(sK4)),sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK6(sK2(sK4))) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2557]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2567,plain,
% 11.54/2.00      ( ~ m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0))
% 11.54/2.00      | l1_waybel_0(sK6(sK2(X0)),sK4)
% 11.54/2.00      | ~ l1_waybel_0(sK2(X0),sK4)
% 11.54/2.00      | v2_struct_0(sK2(X0))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(sK2(X0))
% 11.54/2.00      | ~ v7_waybel_0(sK2(X0))
% 11.54/2.00      | ~ l1_struct_0(sK4) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2578,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(sK2(X0)),sK4,sK2(X0)) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(sK2(X0)),sK4) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(X0),sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X0)) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X0)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X0)) != iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2567]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2580,plain,
% 11.54/2.00      ( m2_yellow_6(sK6(sK2(sK4)),sK4,sK2(sK4)) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK6(sK2(sK4)),sK4) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2578]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3998,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | v7_waybel_0(sK6(X0))
% 11.54/2.00      | ~ l1_struct_0(sK4) ),
% 11.54/2.00      inference(resolution,[status(thm)],[c_14,c_36]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_101,plain,
% 11.54/2.00      ( ~ l1_pre_topc(sK4) | l1_struct_0(sK4) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3457,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(X0)) = iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1641,c_1663]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3458,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | v7_waybel_0(sK6(X0))
% 11.54/2.00      | ~ l1_struct_0(sK4) ),
% 11.54/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3457]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4120,plain,
% 11.54/2.00      ( v7_waybel_0(sK6(X0))
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0) ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_3998,c_39,c_37,c_101,c_3458]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4121,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | v7_waybel_0(sK6(X0)) ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_4120]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4488,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK2(sK4))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(sK2(sK4))
% 11.54/2.00      | v7_waybel_0(sK6(sK2(sK4)))
% 11.54/2.00      | ~ v7_waybel_0(sK2(sK4))
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(resolution,[status(thm)],[c_4121,c_24]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_63,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | ~ v2_struct_0(sK2(sK4))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_66,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | v4_orders_2(sK2(sK4))
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_26]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_69,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | v7_waybel_0(sK2(sK4))
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4491,plain,
% 11.54/2.00      ( v1_compts_1(sK4) | v7_waybel_0(sK6(sK2(sK4))) ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_4488,c_39,c_38,c_37,c_63,c_66,c_69]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4493,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(sK2(sK4))) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_4491]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5532,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | v4_orders_2(sK6(X0))
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_struct_0(sK4) ),
% 11.54/2.00      inference(resolution,[status(thm)],[c_15,c_36]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4928,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | v4_orders_2(sK6(X0))
% 11.54/2.00      | ~ v7_waybel_0(X0) ),
% 11.54/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_4927]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5697,plain,
% 11.54/2.00      ( ~ v7_waybel_0(X0)
% 11.54/2.00      | v4_orders_2(sK6(X0))
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0) ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_5532,c_39,c_37,c_101,c_3445]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5698,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,sK4)
% 11.54/2.00      | v1_compts_1(sK4)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | v4_orders_2(sK6(X0))
% 11.54/2.00      | ~ v7_waybel_0(X0) ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_5697]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5822,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK2(sK4))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4)))
% 11.54/2.00      | ~ v4_orders_2(sK2(sK4))
% 11.54/2.00      | ~ v7_waybel_0(sK2(sK4))
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(resolution,[status(thm)],[c_5698,c_24]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1653,plain,
% 11.54/2.00      ( l1_waybel_0(sK2(X0),X0) = iProver_top
% 11.54/2.00      | v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4938,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4))) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1653,c_4927]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4956,plain,
% 11.54/2.00      ( v1_compts_1(sK4)
% 11.54/2.00      | ~ v2_pre_topc(sK4)
% 11.54/2.00      | v2_struct_0(sK2(sK4))
% 11.54/2.00      | v2_struct_0(sK4)
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4)))
% 11.54/2.00      | ~ v4_orders_2(sK2(sK4))
% 11.54/2.00      | ~ v7_waybel_0(sK2(sK4))
% 11.54/2.00      | ~ l1_pre_topc(sK4) ),
% 11.54/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_4938]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5937,plain,
% 11.54/2.00      ( v4_orders_2(sK6(sK2(sK4))) | v1_compts_1(sK4) ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_5822,c_39,c_38,c_37,c_63,c_66,c_69,c_4956]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5938,plain,
% 11.54/2.00      ( v1_compts_1(sK4) | v4_orders_2(sK6(sK2(sK4))) ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_5937]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_5939,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4))) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_5938]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3628,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK6(X0)) != iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_struct_0(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1641,c_1661]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6646,plain,
% 11.54/2.00      ( v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK6(X0)) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_3628,c_40,c_42,c_102]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6647,plain,
% 11.54/2.00      ( l1_waybel_0(X0,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK6(X0)) != iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_6646]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6658,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1653,c_6647]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7241,plain,
% 11.54/2.00      ( v2_struct_0(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_6658,c_40,c_41,c_42,c_64,c_67,c_70]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7242,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_struct_0(sK6(sK2(sK4))) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_7241]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1,plain,
% 11.54/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1675,plain,
% 11.54/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.54/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_19,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X1,X0)
% 11.54/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.54/2.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | ~ v4_orders_2(X1)
% 11.54/2.00      | ~ v7_waybel_0(X1)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1658,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | r2_hidden(X2,k10_yellow_6(X0,X1)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4262,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(sK0(k10_yellow_6(X0,X1),X2),u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1675,c_1658]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_12,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,X1)
% 11.54/2.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.54/2.00      | ~ v2_pre_topc(X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1665,plain,
% 11.54/2.00      ( l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_9,plain,
% 11.54/2.00      ( m1_subset_1(X0,X1)
% 11.54/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.54/2.00      | ~ r2_hidden(X0,X2) ),
% 11.54/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1668,plain,
% 11.54/2.00      ( m1_subset_1(X0,X1) = iProver_top
% 11.54/2.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.54/2.00      | r2_hidden(X0,X2) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3911,plain,
% 11.54/2.00      ( l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 11.54/2.00      | r2_hidden(X2,k10_yellow_6(X1,X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1665,c_1668]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_7600,plain,
% 11.54/2.00      ( l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) = iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1675,c_3911]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8906,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_4262,c_7600]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_20,plain,
% 11.54/2.00      ( ~ r3_waybel_9(X0,X1,X2)
% 11.54/2.00      | r3_waybel_9(X0,X3,X2)
% 11.54/2.00      | ~ m2_yellow_6(X1,X0,X3)
% 11.54/2.00      | ~ l1_waybel_0(X3,X0)
% 11.54/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X3)
% 11.54/2.00      | ~ v4_orders_2(X3)
% 11.54/2.00      | ~ v7_waybel_0(X3)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1657,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | r3_waybel_9(X0,X3,X2) = iProver_top
% 11.54/2.00      | m2_yellow_6(X1,X0,X3) != iProver_top
% 11.54/2.00      | l1_waybel_0(X3,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X3) = iProver_top
% 11.54/2.00      | v4_orders_2(X3) != iProver_top
% 11.54/2.00      | v7_waybel_0(X3) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8910,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
% 11.54/2.00      | m2_yellow_6(X2,X0,X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(sK0(k10_yellow_6(X0,X2),X3),u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_8906,c_1657]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11304,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
% 11.54/2.00      | m2_yellow_6(X2,X0,X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | l1_waybel_0(X2,X0) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(X2) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v4_orders_2(X2) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X2) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_8910,c_7600]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_23,plain,
% 11.54/2.00      ( ~ r3_waybel_9(X0,sK2(X0),X1)
% 11.54/2.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.54/2.00      | v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1654,plain,
% 11.54/2.00      ( r3_waybel_9(X0,sK2(X0),X1) != iProver_top
% 11.54/2.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11309,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(X1),X1) != iProver_top
% 11.54/2.00      | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.54/2.00      | v1_compts_1(X1) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X1)) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X1)) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X1)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11304,c_1654]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11546,plain,
% 11.54/2.00      ( l1_waybel_0(sK2(X1),X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.54/2.00      | v1_compts_1(X1) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X1)) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X1)) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X1)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_11309,c_7600]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11547,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(X1),X1) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.54/2.00      | v1_compts_1(X1) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X1)) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X1)) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X1)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_11546]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1652,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(X0)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1651,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v4_orders_2(sK2(X0)) = iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1650,plain,
% 11.54/2.00      ( v1_compts_1(X0) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(X0)) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11566,plain,
% 11.54/2.00      ( m2_yellow_6(X0,X1,sK2(X1)) != iProver_top
% 11.54/2.00      | l1_waybel_0(X0,X1) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.54/2.00      | v1_compts_1(X1) = iProver_top
% 11.54/2.00      | v2_pre_topc(X1) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X0) != iProver_top
% 11.54/2.00      | v7_waybel_0(X0) != iProver_top
% 11.54/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.54/2.00      inference(forward_subsumption_resolution,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_11547,c_1652,c_1651,c_1650,c_1653]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11571,plain,
% 11.54/2.00      ( l1_waybel_0(sK6(sK2(sK4)),sK4) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK2(sK4),sK4) != iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK6(sK2(sK4))) = iProver_top
% 11.54/2.00      | v2_struct_0(sK2(sK4)) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | v4_orders_2(sK2(sK4)) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK6(sK2(sK4))) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK2(sK4)) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1641,c_11566]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11617,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top
% 11.54/2.00      | r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_11571,c_40,c_41,c_42,c_64,c_67,c_70,c_73,c_102,c_2448,
% 11.54/2.00                 c_2580,c_4493,c_5939,c_6658]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11618,plain,
% 11.54/2.00      ( r1_tarski(k10_yellow_6(sK4,sK6(sK2(sK4))),X0) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_11617]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_6,plain,
% 11.54/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.54/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1671,plain,
% 11.54/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_8,plain,
% 11.54/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1669,plain,
% 11.54/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.54/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2466,plain,
% 11.54/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1671,c_1669]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_3,plain,
% 11.54/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.54/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1673,plain,
% 11.54/2.00      ( X0 = X1
% 11.54/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.54/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_4610,plain,
% 11.54/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_2466,c_1673]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11626,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK6(sK2(sK4))) = k1_xboole_0
% 11.54/2.00      | v1_compts_1(sK4) = iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_11618,c_4610]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_11838,plain,
% 11.54/2.00      ( v1_compts_1(sK4) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_6691,c_40,c_41,c_42,c_64,c_67,c_70,c_73,c_102,c_2444,
% 11.54/2.00                 c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,c_11626]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36586,plain,
% 11.54/2.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 11.54/2.00      | r3_waybel_9(sK4,sK5,X0) != iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_11284,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,
% 11.54/2.00                 c_73,c_102,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,c_7242,
% 11.54/2.00                 c_11626]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36587,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK1(sK4,sK5,X0)) = k1_xboole_0
% 11.54/2.00      | r3_waybel_9(sK4,sK5,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 11.54/2.00      inference(renaming,[status(thm)],[c_36586]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_36595,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0
% 11.54/2.00      | l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_1649,c_36587]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_29,plain,
% 11.54/2.00      ( ~ l1_waybel_0(X0,X1)
% 11.54/2.00      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 11.54/2.00      | ~ v1_compts_1(X1)
% 11.54/2.00      | ~ v2_pre_topc(X1)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | ~ v4_orders_2(X0)
% 11.54/2.00      | ~ v7_waybel_0(X0)
% 11.54/2.00      | ~ l1_pre_topc(X1) ),
% 11.54/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2277,plain,
% 11.54/2.00      ( ~ l1_waybel_0(sK5,X0)
% 11.54/2.00      | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
% 11.54/2.00      | ~ v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(sK5)
% 11.54/2.00      | ~ v4_orders_2(sK5)
% 11.54/2.00      | ~ v7_waybel_0(sK5)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_29]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2278,plain,
% 11.54/2.00      ( l1_waybel_0(sK5,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0)) = iProver_top
% 11.54/2.00      | v1_compts_1(X0) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2280,plain,
% 11.54/2.00      ( l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) = iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2278]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_37263,plain,
% 11.54/2.00      ( k10_yellow_6(sK4,sK1(sK4,sK5,sK3(sK4,sK5))) = k1_xboole_0 ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_36595,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,
% 11.54/2.00                 c_73,c_102,c_2280,c_2444,c_2448,c_2559,c_2580,c_4493,c_5939,
% 11.54/2.00                 c_7242,c_11626]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_21,plain,
% 11.54/2.00      ( ~ r3_waybel_9(X0,X1,X2)
% 11.54/2.00      | ~ l1_waybel_0(X1,X0)
% 11.54/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.54/2.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(X1)
% 11.54/2.00      | ~ v4_orders_2(X1)
% 11.54/2.00      | ~ v7_waybel_0(X1)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1656,plain,
% 11.54/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.54/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.54/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.54/2.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) = iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(X1) = iProver_top
% 11.54/2.00      | v4_orders_2(X1) != iProver_top
% 11.54/2.00      | v7_waybel_0(X1) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_37290,plain,
% 11.54/2.00      ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) != iProver_top
% 11.54/2.00      | l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | m1_subset_1(sK3(sK4,sK5),u1_struct_0(sK4)) != iProver_top
% 11.54/2.00      | r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_37263,c_1656]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2282,plain,
% 11.54/2.00      ( r3_waybel_9(X0,sK5,sK3(X0,sK5))
% 11.54/2.00      | ~ l1_waybel_0(sK5,X0)
% 11.54/2.00      | ~ v1_compts_1(X0)
% 11.54/2.00      | ~ v2_pre_topc(X0)
% 11.54/2.00      | v2_struct_0(X0)
% 11.54/2.00      | v2_struct_0(sK5)
% 11.54/2.00      | ~ v4_orders_2(sK5)
% 11.54/2.00      | ~ v7_waybel_0(sK5)
% 11.54/2.00      | ~ l1_pre_topc(X0) ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_28]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2283,plain,
% 11.54/2.00      ( r3_waybel_9(X0,sK5,sK3(X0,sK5)) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK5,X0) != iProver_top
% 11.54/2.00      | v1_compts_1(X0) != iProver_top
% 11.54/2.00      | v2_pre_topc(X0) != iProver_top
% 11.54/2.00      | v2_struct_0(X0) = iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_2285,plain,
% 11.54/2.00      ( r3_waybel_9(sK4,sK5,sK3(sK4,sK5)) = iProver_top
% 11.54/2.00      | l1_waybel_0(sK5,sK4) != iProver_top
% 11.54/2.00      | v1_compts_1(sK4) != iProver_top
% 11.54/2.00      | v2_pre_topc(sK4) != iProver_top
% 11.54/2.00      | v2_struct_0(sK5) = iProver_top
% 11.54/2.00      | v2_struct_0(sK4) = iProver_top
% 11.54/2.00      | v4_orders_2(sK5) != iProver_top
% 11.54/2.00      | v7_waybel_0(sK5) != iProver_top
% 11.54/2.00      | l1_pre_topc(sK4) != iProver_top ),
% 11.54/2.00      inference(instantiation,[status(thm)],[c_2283]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_37930,plain,
% 11.54/2.00      ( r2_hidden(sK3(sK4,sK5),k1_xboole_0) = iProver_top ),
% 11.54/2.00      inference(global_propositional_subsumption,
% 11.54/2.00                [status(thm)],
% 11.54/2.00                [c_37290,c_40,c_41,c_42,c_49,c_50,c_51,c_52,c_64,c_67,c_70,
% 11.54/2.00                 c_73,c_102,c_2280,c_2285,c_2444,c_2448,c_2559,c_2580,c_4493,
% 11.54/2.00                 c_5939,c_7242,c_11626]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_10,plain,
% 11.54/2.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.54/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_1667,plain,
% 11.54/2.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 11.54/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_37936,plain,
% 11.54/2.00      ( r1_tarski(k1_xboole_0,sK3(sK4,sK5)) != iProver_top ),
% 11.54/2.00      inference(superposition,[status(thm)],[c_37930,c_1667]) ).
% 11.54/2.00  
% 11.54/2.00  cnf(c_38074,plain,
% 11.54/2.00      ( $false ),
% 11.54/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_37936,c_2466]) ).
% 11.54/2.00  
% 11.54/2.00  
% 11.54/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.54/2.00  
% 11.54/2.00  ------                               Statistics
% 11.54/2.00  
% 11.54/2.00  ------ Selected
% 11.54/2.00  
% 11.54/2.00  total_time:                             1.249
% 11.54/2.00  
%------------------------------------------------------------------------------
