%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 682 expanded)
%              Number of clauses        :   33 (  94 expanded)
%              Number of leaves         :    8 ( 196 expanded)
%              Depth                    :   16
%              Number of atoms          :  501 (8435 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK0(X0,X1))
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f13,plain,(
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
            ( ~ r3_waybel_9(X0,sK1(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK1(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK1(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK1(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f13])).

fof(f29,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | r2_hidden(sK1(X0),k6_yellow_6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,conjecture,(
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

fof(f4,negated_conjecture,(
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
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ r3_waybel_9(X0,X1,X2) )
                  & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f15,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(X1,k6_yellow_6(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,k6_yellow_6(X0))
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X3))
        & m1_subset_1(sK4(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
            ( ~ r3_waybel_9(X0,sK3,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK3,k6_yellow_6(X0))
        & l1_waybel_0(sK3,X0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
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
                ( ~ r3_waybel_9(sK2,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
            & r2_hidden(X1,k6_yellow_6(sK2))
            & l1_waybel_0(X1,sK2)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK2) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(sK2,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK2)) )
            | ~ r2_hidden(X3,k6_yellow_6(sK2))
            | ~ l1_waybel_0(X3,sK2)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( ( ! [X2] :
            ( ~ r3_waybel_9(sK2,sK3,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
        & r2_hidden(sK3,k6_yellow_6(sK2))
        & l1_waybel_0(sK3,sK2)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) )
      | ~ v1_compts_1(sK2) )
    & ( ! [X3] :
          ( ( r3_waybel_9(sK2,X3,sK4(X3))
            & m1_subset_1(sK4(X3),u1_struct_0(sK2)) )
          | ~ r2_hidden(X3,k6_yellow_6(sK2))
          | ~ l1_waybel_0(X3,sK2)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK2) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f34,plain,(
    ! [X3] :
      ( r3_waybel_9(sK2,X3,sK4(X3))
      | ~ r2_hidden(X3,k6_yellow_6(sK2))
      | ~ l1_waybel_0(X3,sK2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X3] :
      ( m1_subset_1(sK4(X3),u1_struct_0(sK2))
      | ~ r2_hidden(X3,k6_yellow_6(sK2))
      | ~ l1_waybel_0(X3,sK2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2] :
      ( ~ r3_waybel_9(sK2,sK3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,
    ( ~ v2_struct_0(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,
    ( v4_orders_2(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,
    ( v7_waybel_0(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,
    ( l1_waybel_0(sK3,sK2)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( ~ r3_waybel_9(X0,sK1(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),k6_yellow_6(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,negated_conjecture,
    ( r3_waybel_9(sK2,X0,sK4(X0))
    | ~ r2_hidden(X0,k6_yellow_6(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_211,plain,
    ( r3_waybel_9(sK2,sK1(sK2),sK4(sK1(sK2)))
    | ~ l1_waybel_0(sK1(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK1(sK2))
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK1(sK2))
    | ~ v7_waybel_0(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_14])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_37,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | ~ v2_struct_0(sK1(sK2))
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_40,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2)
    | v4_orders_2(sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_43,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2)
    | v7_waybel_0(sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( l1_waybel_0(sK1(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_46,plain,
    ( l1_waybel_0(sK1(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_213,plain,
    ( r3_waybel_9(sK2,sK1(sK2),sK4(sK1(sK2)))
    | v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_211,c_18,c_17,c_16,c_37,c_40,c_43,c_46])).

cnf(c_246,plain,
    ( ~ m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_213])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,k6_yellow_6(sK2))
    | m1_subset_1(sK4(X0),u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_198,plain,
    ( m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | ~ l1_waybel_0(sK1(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK1(sK2))
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK1(sK2))
    | ~ v7_waybel_0(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_15])).

cnf(c_200,plain,
    ( m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_198,c_18,c_17,c_16,c_37,c_40,c_43,c_46])).

cnf(c_248,plain,
    ( v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_18,c_17,c_16,c_200])).

cnf(c_0,plain,
    ( r3_waybel_9(X0,X1,sK0(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,negated_conjecture,
    ( ~ r3_waybel_9(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_233,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2))
    | ~ l1_waybel_0(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_8])).

cnf(c_13,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | v7_waybel_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,negated_conjecture,
    ( l1_waybel_0(sK3,sK2)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_235,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2))
    | ~ v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_18,c_17,c_16,c_13,c_12,c_11,c_10])).

cnf(c_255,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_248,c_235])).

cnf(c_270,plain,
    ( ~ l1_waybel_0(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK3) ),
    inference(resolution,[status(thm)],[c_1,c_255])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_270,c_248,c_10,c_11,c_12,c_13,c_16,c_17,c_18])).


%------------------------------------------------------------------------------
