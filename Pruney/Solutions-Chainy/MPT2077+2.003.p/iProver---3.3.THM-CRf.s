%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:24 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.76s
% Verified   : 
% Statistics : Number of formulae       :  265 (6381 expanded)
%              Number of clauses        :  166 (1450 expanded)
%              Number of leaves         :   24 (1601 expanded)
%              Depth                    :   29
%              Number of atoms          : 1806 (66804 expanded)
%              Number of equality atoms :  729 (3742 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal clause size      :   34 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f51])).

fof(f89,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f49])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f50])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f40])).

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

fof(f107,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK5)
      | ~ m2_yellow_6(X2,sK5,sK6)
      | ~ v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f99,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,
    ( ~ v2_struct_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,
    ( v4_orders_2(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,
    ( v7_waybel_0(sK6)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f101,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f54,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f97,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
    ! [X3] :
      ( v3_yellow_6(sK7(X3),sK5)
      | ~ l1_waybel_0(X3,sK5)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_23,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1755,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1)) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

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
    inference(cnf_transformation,[],[f86])).

cnf(c_1756,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_1765,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | l1_waybel_0(X0,X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4381,plain,
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
    inference(superposition,[status(thm)],[c_1756,c_1765])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_112,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9488,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4381,c_112])).

cnf(c_9489,plain,
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
    inference(renaming,[status(thm)],[c_9488])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_1761,plain,
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

cnf(c_9504,plain,
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
    inference(superposition,[status(thm)],[c_9489,c_1761])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1764,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4383,plain,
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
    inference(superposition,[status(thm)],[c_1756,c_1764])).

cnf(c_9371,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_112])).

cnf(c_9372,plain,
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
    inference(renaming,[status(thm)],[c_9371])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1763,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4384,plain,
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
    inference(superposition,[status(thm)],[c_1756,c_1763])).

cnf(c_9471,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4384,c_112])).

cnf(c_9472,plain,
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
    inference(renaming,[status(thm)],[c_9471])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1762,plain,
    ( m2_yellow_6(X0,X1,X2) != iProver_top
    | l1_waybel_0(X2,X1) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4382,plain,
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
    inference(superposition,[status(thm)],[c_1756,c_1762])).

cnf(c_9737,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4382,c_112])).

cnf(c_9738,plain,
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
    inference(renaming,[status(thm)],[c_9737])).

cnf(c_12305,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_9504,c_9372,c_9472,c_9738])).

cnf(c_12306,plain,
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
    inference(renaming,[status(thm)],[c_12305])).

cnf(c_33,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK5,sK6)
    | ~ v3_yellow_6(X0,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1745,plain,
    ( m2_yellow_6(X0,sK5,sK6) != iProver_top
    | v3_yellow_6(X0,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4385,plain,
    ( r3_waybel_9(sK5,sK6,X0) != iProver_top
    | v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_1745])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_43,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_44,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v4_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v1_compts_1(sK5)
    | v7_waybel_0(sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_54,plain,
    ( v1_compts_1(sK5) != iProver_top
    | v7_waybel_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_waybel_0(sK6,sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_55,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9754,plain,
    ( v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4385,c_43,c_44,c_45,c_52,c_53,c_54,c_55])).

cnf(c_9755,plain,
    ( r3_waybel_9(sK5,sK6,X0) != iProver_top
    | v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_9754])).

cnf(c_12322,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12306,c_9755])).

cnf(c_39,negated_conjecture,
    ( m2_yellow_6(sK7(X0),sK5,X0)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1739,plain,
    ( m2_yellow_6(sK7(X0),sK5,X0) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1776,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_1759,plain,
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

cnf(c_4366,plain,
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
    inference(superposition,[status(thm)],[c_1776,c_1759])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1766,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1769,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4027,plain,
    ( l1_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,k10_yellow_6(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_1769])).

cnf(c_8217,plain,
    ( l1_waybel_0(X0,X1) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) = iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_4027])).

cnf(c_9308,plain,
    ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4366,c_8217])).

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
    inference(cnf_transformation,[],[f85])).

cnf(c_1758,plain,
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

cnf(c_9312,plain,
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
    inference(superposition,[status(thm)],[c_9308,c_1758])).

cnf(c_12342,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_9312,c_8217])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1753,plain,
    ( r3_waybel_9(X0,sK3(X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12347,plain,
    ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | l1_waybel_0(sK3(X1),X1) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK3(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK3(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12342,c_1753])).

cnf(c_12743,plain,
    ( l1_waybel_0(sK3(X1),X1) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK3(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK3(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12347,c_8217])).

cnf(c_12744,plain,
    ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | l1_waybel_0(sK3(X1),X1) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK3(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK3(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12743])).

cnf(c_28,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1750,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_waybel_0(sK3(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1749,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(sK3(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1748,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1751,plain,
    ( l1_waybel_0(sK3(X0),X0) = iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12763,plain,
    ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
    | l1_waybel_0(X0,X1) != iProver_top
    | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
    | v1_compts_1(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12744,c_1750,c_1749,c_1748,c_1751])).

cnf(c_12768,plain,
    ( l1_waybel_0(sK7(sK3(sK5)),sK5) != iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK7(sK3(sK5))) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK7(sK3(sK5))) != iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK7(sK3(sK5))) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_12763])).

cnf(c_65,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_67,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_68,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(sK3(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_70,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK3(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_71,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_waybel_0(sK3(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_73,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v7_waybel_0(sK3(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_74,plain,
    ( l1_waybel_0(sK3(X0),X0) = iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_76,plain,
    ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_114,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_2577,plain,
    ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0))
    | ~ l1_waybel_0(sK3(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK3(X0))
    | ~ v4_orders_2(sK3(X0))
    | ~ v7_waybel_0(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_2603,plain,
    ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0)) = iProver_top
    | l1_waybel_0(sK3(X0),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(X0)) = iProver_top
    | v4_orders_2(sK3(X0)) != iProver_top
    | v7_waybel_0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2577])).

cnf(c_2605,plain,
    ( m2_yellow_6(sK7(sK3(sK5)),sK5,sK3(sK5)) = iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2603])).

cnf(c_2808,plain,
    ( ~ m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0))
    | l1_waybel_0(sK7(sK3(X0)),sK5)
    | ~ l1_waybel_0(sK3(X0),sK5)
    | v2_struct_0(sK3(X0))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK3(X0))
    | ~ v7_waybel_0(sK3(X0))
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2819,plain,
    ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0)) != iProver_top
    | l1_waybel_0(sK7(sK3(X0)),sK5) = iProver_top
    | l1_waybel_0(sK3(X0),sK5) != iProver_top
    | v2_struct_0(sK3(X0)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK3(X0)) != iProver_top
    | v7_waybel_0(sK3(X0)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_2821,plain,
    ( m2_yellow_6(sK7(sK3(sK5)),sK5,sK3(sK5)) != iProver_top
    | l1_waybel_0(sK7(sK3(sK5)),sK5) = iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_5636,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK7(X0))
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_14,c_39])).

cnf(c_113,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3770,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK7(X0)) = iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_1764])).

cnf(c_3771,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK7(X0))
    | ~ l1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3770])).

cnf(c_5953,plain,
    ( v7_waybel_0(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5636,c_42,c_40,c_113,c_3771])).

cnf(c_5954,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK7(X0)) ),
    inference(renaming,[status(thm)],[c_5953])).

cnf(c_6195,plain,
    ( v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK3(sK5))
    | v7_waybel_0(sK7(sK3(sK5)))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_5954,c_27])).

cnf(c_66,plain,
    ( v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_69,plain,
    ( v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | v4_orders_2(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_72,plain,
    ( v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | v7_waybel_0(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_6336,plain,
    ( v1_compts_1(sK5)
    | v7_waybel_0(sK7(sK3(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6195,c_42,c_41,c_40,c_66,c_69,c_72])).

cnf(c_6338,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v7_waybel_0(sK7(sK3(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6336])).

cnf(c_5930,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_15,c_39])).

cnf(c_3649,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK7(X0)) = iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_1763])).

cnf(c_3650,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3649])).

cnf(c_6198,plain,
    ( ~ v7_waybel_0(X0)
    | v4_orders_2(sK7(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5930,c_42,c_40,c_113,c_3650])).

cnf(c_6199,plain,
    ( ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK7(X0))
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_6198])).

cnf(c_6232,plain,
    ( v1_compts_1(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK3(sK5))
    | v2_struct_0(sK5)
    | v4_orders_2(sK7(sK3(sK5)))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_6199,c_27])).

cnf(c_6353,plain,
    ( v4_orders_2(sK7(sK3(sK5)))
    | v1_compts_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6232,c_42,c_41,c_40,c_66,c_69,c_72])).

cnf(c_6354,plain,
    ( v1_compts_1(sK5)
    | v4_orders_2(sK7(sK3(sK5))) ),
    inference(renaming,[status(thm)],[c_6353])).

cnf(c_6355,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v4_orders_2(sK7(sK3(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6354])).

cnf(c_3883,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_1762])).

cnf(c_7478,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3883,c_43,c_45,c_114])).

cnf(c_7479,plain,
    ( l1_waybel_0(X0,sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7478])).

cnf(c_7490,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_7479])).

cnf(c_7999,plain,
    ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7490,c_43,c_44,c_45,c_67,c_70,c_73])).

cnf(c_8000,plain,
    ( v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7999])).

cnf(c_13129,plain,
    ( v1_compts_1(sK5) = iProver_top
    | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12768,c_43,c_44,c_45,c_67,c_70,c_73,c_76,c_114,c_2605,c_2821,c_6338,c_6355,c_7490])).

cnf(c_13130,plain,
    ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_13129])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1774,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13137,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) = X0
    | r1_tarski(X0,k10_yellow_6(sK5,sK7(sK3(sK5)))) != iProver_top
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_13130,c_1774])).

cnf(c_38,negated_conjecture,
    ( v3_yellow_6(sK7(X0),sK5)
    | ~ l1_waybel_0(X0,sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2578,plain,
    ( v3_yellow_6(sK7(sK3(X0)),sK5)
    | ~ l1_waybel_0(sK3(X0),sK5)
    | v1_compts_1(sK5)
    | v2_struct_0(sK3(X0))
    | ~ v4_orders_2(sK3(X0))
    | ~ v7_waybel_0(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2599,plain,
    ( v3_yellow_6(sK7(sK3(X0)),sK5) = iProver_top
    | l1_waybel_0(sK3(X0),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(X0)) = iProver_top
    | v4_orders_2(sK3(X0)) != iProver_top
    | v7_waybel_0(sK3(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_2601,plain,
    ( v3_yellow_6(sK7(sK3(sK5)),sK5) = iProver_top
    | l1_waybel_0(sK3(sK5),sK5) != iProver_top
    | v1_compts_1(sK5) = iProver_top
    | v2_struct_0(sK3(sK5)) = iProver_top
    | v4_orders_2(sK3(sK5)) != iProver_top
    | v7_waybel_0(sK3(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2599])).

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
    inference(cnf_transformation,[],[f82])).

cnf(c_2792,plain,
    ( ~ v3_yellow_6(sK7(sK3(X0)),sK5)
    | ~ l1_waybel_0(sK7(sK3(X0)),sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK7(sK3(X0)))
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK7(sK3(X0)))
    | ~ v7_waybel_0(sK7(sK3(X0)))
    | ~ l1_pre_topc(sK5)
    | k10_yellow_6(sK5,sK7(sK3(X0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2798,plain,
    ( k10_yellow_6(sK5,sK7(sK3(X0))) != k1_xboole_0
    | v3_yellow_6(sK7(sK3(X0)),sK5) != iProver_top
    | l1_waybel_0(sK7(sK3(X0)),sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK7(sK3(X0))) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK7(sK3(X0))) != iProver_top
    | v7_waybel_0(sK7(sK3(X0))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2792])).

cnf(c_2800,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
    | v3_yellow_6(sK7(sK3(sK5)),sK5) != iProver_top
    | l1_waybel_0(sK7(sK3(sK5)),sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK7(sK3(sK5))) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK7(sK3(sK5))) != iProver_top
    | v7_waybel_0(sK7(sK3(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1772,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1770,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2613,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1770])).

cnf(c_4973,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2613,c_1774])).

cnf(c_13138,plain,
    ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
    | v1_compts_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_13130,c_4973])).

cnf(c_13234,plain,
    ( v1_compts_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13137,c_43,c_44,c_45,c_67,c_70,c_73,c_76,c_114,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,c_13138])).

cnf(c_36820,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12322,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,c_76,c_114,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,c_13138])).

cnf(c_36821,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
    | r3_waybel_9(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36820])).

cnf(c_36829,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_36821])).

cnf(c_24,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2434,plain,
    ( ~ l1_waybel_0(sK6,X0)
    | m1_subset_1(sK2(X0,sK6),u1_struct_0(X0))
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2435,plain,
    ( l1_waybel_0(sK6,X0) != iProver_top
    | m1_subset_1(sK2(X0,sK6),u1_struct_0(X0)) = iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2434])).

cnf(c_2437,plain,
    ( l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_37426,plain,
    ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36829,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,c_76,c_114,c_2437,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,c_13138])).

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
    inference(cnf_transformation,[],[f87])).

cnf(c_1757,plain,
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

cnf(c_37453,plain,
    ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_37426,c_1757])).

cnf(c_2439,plain,
    ( r3_waybel_9(X0,sK6,sK2(X0,sK6))
    | ~ l1_waybel_0(sK6,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2440,plain,
    ( r3_waybel_9(X0,sK6,sK2(X0,sK6)) = iProver_top
    | l1_waybel_0(sK6,X0) != iProver_top
    | v1_compts_1(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2442,plain,
    ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | v1_compts_1(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK6) != iProver_top
    | v7_waybel_0(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_38270,plain,
    ( r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37453,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,c_76,c_114,c_2437,c_2442,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,c_13138])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1768,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_38276,plain,
    ( r1_tarski(k1_xboole_0,sK2(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38270,c_1768])).

cnf(c_38296,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38276,c_2613])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.76/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.76/1.99  
% 11.76/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.76/1.99  
% 11.76/1.99  ------  iProver source info
% 11.76/1.99  
% 11.76/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.76/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.76/1.99  git: non_committed_changes: false
% 11.76/1.99  git: last_make_outside_of_git: false
% 11.76/1.99  
% 11.76/1.99  ------ 
% 11.76/1.99  
% 11.76/1.99  ------ Input Options
% 11.76/1.99  
% 11.76/1.99  --out_options                           all
% 11.76/1.99  --tptp_safe_out                         true
% 11.76/1.99  --problem_path                          ""
% 11.76/1.99  --include_path                          ""
% 11.76/1.99  --clausifier                            res/vclausify_rel
% 11.76/1.99  --clausifier_options                    --mode clausify
% 11.76/1.99  --stdin                                 false
% 11.76/1.99  --stats_out                             sel
% 11.76/1.99  
% 11.76/1.99  ------ General Options
% 11.76/1.99  
% 11.76/1.99  --fof                                   false
% 11.76/1.99  --time_out_real                         604.99
% 11.76/1.99  --time_out_virtual                      -1.
% 11.76/1.99  --symbol_type_check                     false
% 11.76/1.99  --clausify_out                          false
% 11.76/1.99  --sig_cnt_out                           false
% 11.76/1.99  --trig_cnt_out                          false
% 11.76/1.99  --trig_cnt_out_tolerance                1.
% 11.76/1.99  --trig_cnt_out_sk_spl                   false
% 11.76/1.99  --abstr_cl_out                          false
% 11.76/1.99  
% 11.76/1.99  ------ Global Options
% 11.76/1.99  
% 11.76/1.99  --schedule                              none
% 11.76/1.99  --add_important_lit                     false
% 11.76/1.99  --prop_solver_per_cl                    1000
% 11.76/1.99  --min_unsat_core                        false
% 11.76/1.99  --soft_assumptions                      false
% 11.76/1.99  --soft_lemma_size                       3
% 11.76/1.99  --prop_impl_unit_size                   0
% 11.76/1.99  --prop_impl_unit                        []
% 11.76/1.99  --share_sel_clauses                     true
% 11.76/1.99  --reset_solvers                         false
% 11.76/1.99  --bc_imp_inh                            [conj_cone]
% 11.76/1.99  --conj_cone_tolerance                   3.
% 11.76/1.99  --extra_neg_conj                        none
% 11.76/1.99  --large_theory_mode                     true
% 11.76/1.99  --prolific_symb_bound                   200
% 11.76/1.99  --lt_threshold                          2000
% 11.76/1.99  --clause_weak_htbl                      true
% 11.76/1.99  --gc_record_bc_elim                     false
% 11.76/1.99  
% 11.76/1.99  ------ Preprocessing Options
% 11.76/1.99  
% 11.76/1.99  --preprocessing_flag                    true
% 11.76/1.99  --time_out_prep_mult                    0.1
% 11.76/1.99  --splitting_mode                        input
% 11.76/1.99  --splitting_grd                         true
% 11.76/1.99  --splitting_cvd                         false
% 11.76/1.99  --splitting_cvd_svl                     false
% 11.76/1.99  --splitting_nvd                         32
% 11.76/1.99  --sub_typing                            true
% 11.76/1.99  --prep_gs_sim                           false
% 11.76/1.99  --prep_unflatten                        true
% 11.76/1.99  --prep_res_sim                          true
% 11.76/1.99  --prep_upred                            true
% 11.76/1.99  --prep_sem_filter                       exhaustive
% 11.76/1.99  --prep_sem_filter_out                   false
% 11.76/1.99  --pred_elim                             false
% 11.76/1.99  --res_sim_input                         true
% 11.76/1.99  --eq_ax_congr_red                       true
% 11.76/1.99  --pure_diseq_elim                       true
% 11.76/1.99  --brand_transform                       false
% 11.76/1.99  --non_eq_to_eq                          false
% 11.76/1.99  --prep_def_merge                        true
% 11.76/1.99  --prep_def_merge_prop_impl              false
% 11.76/1.99  --prep_def_merge_mbd                    true
% 11.76/1.99  --prep_def_merge_tr_red                 false
% 11.76/1.99  --prep_def_merge_tr_cl                  false
% 11.76/1.99  --smt_preprocessing                     true
% 11.76/1.99  --smt_ac_axioms                         fast
% 11.76/1.99  --preprocessed_out                      false
% 11.76/1.99  --preprocessed_stats                    false
% 11.76/1.99  
% 11.76/1.99  ------ Abstraction refinement Options
% 11.76/1.99  
% 11.76/1.99  --abstr_ref                             []
% 11.76/1.99  --abstr_ref_prep                        false
% 11.76/1.99  --abstr_ref_until_sat                   false
% 11.76/1.99  --abstr_ref_sig_restrict                funpre
% 11.76/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.76/1.99  --abstr_ref_under                       []
% 11.76/1.99  
% 11.76/1.99  ------ SAT Options
% 11.76/1.99  
% 11.76/1.99  --sat_mode                              false
% 11.76/1.99  --sat_fm_restart_options                ""
% 11.76/1.99  --sat_gr_def                            false
% 11.76/1.99  --sat_epr_types                         true
% 11.76/1.99  --sat_non_cyclic_types                  false
% 11.76/1.99  --sat_finite_models                     false
% 11.76/1.99  --sat_fm_lemmas                         false
% 11.76/1.99  --sat_fm_prep                           false
% 11.76/1.99  --sat_fm_uc_incr                        true
% 11.76/1.99  --sat_out_model                         small
% 11.76/1.99  --sat_out_clauses                       false
% 11.76/1.99  
% 11.76/1.99  ------ QBF Options
% 11.76/1.99  
% 11.76/1.99  --qbf_mode                              false
% 11.76/1.99  --qbf_elim_univ                         false
% 11.76/1.99  --qbf_dom_inst                          none
% 11.76/1.99  --qbf_dom_pre_inst                      false
% 11.76/1.99  --qbf_sk_in                             false
% 11.76/1.99  --qbf_pred_elim                         true
% 11.76/1.99  --qbf_split                             512
% 11.76/1.99  
% 11.76/1.99  ------ BMC1 Options
% 11.76/1.99  
% 11.76/1.99  --bmc1_incremental                      false
% 11.76/1.99  --bmc1_axioms                           reachable_all
% 11.76/1.99  --bmc1_min_bound                        0
% 11.76/1.99  --bmc1_max_bound                        -1
% 11.76/1.99  --bmc1_max_bound_default                -1
% 11.76/1.99  --bmc1_symbol_reachability              true
% 11.76/1.99  --bmc1_property_lemmas                  false
% 11.76/1.99  --bmc1_k_induction                      false
% 11.76/1.99  --bmc1_non_equiv_states                 false
% 11.76/1.99  --bmc1_deadlock                         false
% 11.76/1.99  --bmc1_ucm                              false
% 11.76/1.99  --bmc1_add_unsat_core                   none
% 11.76/1.99  --bmc1_unsat_core_children              false
% 11.76/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.76/1.99  --bmc1_out_stat                         full
% 11.76/1.99  --bmc1_ground_init                      false
% 11.76/1.99  --bmc1_pre_inst_next_state              false
% 11.76/1.99  --bmc1_pre_inst_state                   false
% 11.76/1.99  --bmc1_pre_inst_reach_state             false
% 11.76/1.99  --bmc1_out_unsat_core                   false
% 11.76/1.99  --bmc1_aig_witness_out                  false
% 11.76/1.99  --bmc1_verbose                          false
% 11.76/1.99  --bmc1_dump_clauses_tptp                false
% 11.76/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.76/1.99  --bmc1_dump_file                        -
% 11.76/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.76/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.76/1.99  --bmc1_ucm_extend_mode                  1
% 11.76/1.99  --bmc1_ucm_init_mode                    2
% 11.76/1.99  --bmc1_ucm_cone_mode                    none
% 11.76/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.76/1.99  --bmc1_ucm_relax_model                  4
% 11.76/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.76/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.76/1.99  --bmc1_ucm_layered_model                none
% 11.76/1.99  --bmc1_ucm_max_lemma_size               10
% 11.76/1.99  
% 11.76/1.99  ------ AIG Options
% 11.76/1.99  
% 11.76/1.99  --aig_mode                              false
% 11.76/1.99  
% 11.76/1.99  ------ Instantiation Options
% 11.76/1.99  
% 11.76/1.99  --instantiation_flag                    true
% 11.76/1.99  --inst_sos_flag                         false
% 11.76/1.99  --inst_sos_phase                        true
% 11.76/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.76/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.76/1.99  --inst_lit_sel_side                     num_symb
% 11.76/1.99  --inst_solver_per_active                1400
% 11.76/1.99  --inst_solver_calls_frac                1.
% 11.76/1.99  --inst_passive_queue_type               priority_queues
% 11.76/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.76/1.99  --inst_passive_queues_freq              [25;2]
% 11.76/1.99  --inst_dismatching                      true
% 11.76/1.99  --inst_eager_unprocessed_to_passive     true
% 11.76/1.99  --inst_prop_sim_given                   true
% 11.76/1.99  --inst_prop_sim_new                     false
% 11.76/1.99  --inst_subs_new                         false
% 11.76/1.99  --inst_eq_res_simp                      false
% 11.76/1.99  --inst_subs_given                       false
% 11.76/1.99  --inst_orphan_elimination               true
% 11.76/1.99  --inst_learning_loop_flag               true
% 11.76/1.99  --inst_learning_start                   3000
% 11.76/1.99  --inst_learning_factor                  2
% 11.76/1.99  --inst_start_prop_sim_after_learn       3
% 11.76/1.99  --inst_sel_renew                        solver
% 11.76/1.99  --inst_lit_activity_flag                true
% 11.76/1.99  --inst_restr_to_given                   false
% 11.76/1.99  --inst_activity_threshold               500
% 11.76/1.99  --inst_out_proof                        true
% 11.76/1.99  
% 11.76/1.99  ------ Resolution Options
% 11.76/1.99  
% 11.76/1.99  --resolution_flag                       true
% 11.76/1.99  --res_lit_sel                           adaptive
% 11.76/1.99  --res_lit_sel_side                      none
% 11.76/1.99  --res_ordering                          kbo
% 11.76/1.99  --res_to_prop_solver                    active
% 11.76/1.99  --res_prop_simpl_new                    false
% 11.76/1.99  --res_prop_simpl_given                  true
% 11.76/1.99  --res_passive_queue_type                priority_queues
% 11.76/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.76/1.99  --res_passive_queues_freq               [15;5]
% 11.76/1.99  --res_forward_subs                      full
% 11.76/1.99  --res_backward_subs                     full
% 11.76/1.99  --res_forward_subs_resolution           true
% 11.76/1.99  --res_backward_subs_resolution          true
% 11.76/1.99  --res_orphan_elimination                true
% 11.76/1.99  --res_time_limit                        2.
% 11.76/1.99  --res_out_proof                         true
% 11.76/1.99  
% 11.76/1.99  ------ Superposition Options
% 11.76/1.99  
% 11.76/1.99  --superposition_flag                    true
% 11.76/1.99  --sup_passive_queue_type                priority_queues
% 11.76/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.76/1.99  --sup_passive_queues_freq               [1;4]
% 11.76/1.99  --demod_completeness_check              fast
% 11.76/1.99  --demod_use_ground                      true
% 11.76/1.99  --sup_to_prop_solver                    passive
% 11.76/1.99  --sup_prop_simpl_new                    true
% 11.76/1.99  --sup_prop_simpl_given                  true
% 11.76/1.99  --sup_fun_splitting                     false
% 11.76/1.99  --sup_smt_interval                      50000
% 11.76/1.99  
% 11.76/1.99  ------ Superposition Simplification Setup
% 11.76/1.99  
% 11.76/1.99  --sup_indices_passive                   []
% 11.76/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.76/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_full_bw                           [BwDemod]
% 11.76/1.99  --sup_immed_triv                        [TrivRules]
% 11.76/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.76/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_immed_bw_main                     []
% 11.76/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.76/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.76/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.76/1.99  
% 11.76/1.99  ------ Combination Options
% 11.76/1.99  
% 11.76/1.99  --comb_res_mult                         3
% 11.76/1.99  --comb_sup_mult                         2
% 11.76/1.99  --comb_inst_mult                        10
% 11.76/1.99  
% 11.76/1.99  ------ Debug Options
% 11.76/1.99  
% 11.76/1.99  --dbg_backtrace                         false
% 11.76/1.99  --dbg_dump_prop_clauses                 false
% 11.76/1.99  --dbg_dump_prop_clauses_file            -
% 11.76/1.99  --dbg_out_stat                          false
% 11.76/1.99  ------ Parsing...
% 11.76/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.76/1.99  
% 11.76/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.76/1.99  
% 11.76/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.76/1.99  
% 11.76/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.76/1.99  ------ Proving...
% 11.76/1.99  ------ Problem Properties 
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  clauses                                 42
% 11.76/1.99  conjectures                             10
% 11.76/1.99  EPR                                     17
% 11.76/1.99  Horn                                    18
% 11.76/1.99  unary                                   5
% 11.76/1.99  binary                                  10
% 11.76/1.99  lits                                    217
% 11.76/1.99  lits eq                                 3
% 11.76/1.99  fd_pure                                 0
% 11.76/1.99  fd_pseudo                               0
% 11.76/1.99  fd_cond                                 0
% 11.76/1.99  fd_pseudo_cond                          1
% 11.76/1.99  AC symbols                              0
% 11.76/1.99  
% 11.76/1.99  ------ Input Options Time Limit: Unbounded
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  ------ 
% 11.76/1.99  Current options:
% 11.76/1.99  ------ 
% 11.76/1.99  
% 11.76/1.99  ------ Input Options
% 11.76/1.99  
% 11.76/1.99  --out_options                           all
% 11.76/1.99  --tptp_safe_out                         true
% 11.76/1.99  --problem_path                          ""
% 11.76/1.99  --include_path                          ""
% 11.76/1.99  --clausifier                            res/vclausify_rel
% 11.76/1.99  --clausifier_options                    --mode clausify
% 11.76/1.99  --stdin                                 false
% 11.76/1.99  --stats_out                             sel
% 11.76/1.99  
% 11.76/1.99  ------ General Options
% 11.76/1.99  
% 11.76/1.99  --fof                                   false
% 11.76/1.99  --time_out_real                         604.99
% 11.76/1.99  --time_out_virtual                      -1.
% 11.76/1.99  --symbol_type_check                     false
% 11.76/1.99  --clausify_out                          false
% 11.76/1.99  --sig_cnt_out                           false
% 11.76/1.99  --trig_cnt_out                          false
% 11.76/1.99  --trig_cnt_out_tolerance                1.
% 11.76/1.99  --trig_cnt_out_sk_spl                   false
% 11.76/1.99  --abstr_cl_out                          false
% 11.76/1.99  
% 11.76/1.99  ------ Global Options
% 11.76/1.99  
% 11.76/1.99  --schedule                              none
% 11.76/1.99  --add_important_lit                     false
% 11.76/1.99  --prop_solver_per_cl                    1000
% 11.76/1.99  --min_unsat_core                        false
% 11.76/1.99  --soft_assumptions                      false
% 11.76/1.99  --soft_lemma_size                       3
% 11.76/1.99  --prop_impl_unit_size                   0
% 11.76/1.99  --prop_impl_unit                        []
% 11.76/1.99  --share_sel_clauses                     true
% 11.76/1.99  --reset_solvers                         false
% 11.76/1.99  --bc_imp_inh                            [conj_cone]
% 11.76/1.99  --conj_cone_tolerance                   3.
% 11.76/1.99  --extra_neg_conj                        none
% 11.76/1.99  --large_theory_mode                     true
% 11.76/1.99  --prolific_symb_bound                   200
% 11.76/1.99  --lt_threshold                          2000
% 11.76/1.99  --clause_weak_htbl                      true
% 11.76/1.99  --gc_record_bc_elim                     false
% 11.76/1.99  
% 11.76/1.99  ------ Preprocessing Options
% 11.76/1.99  
% 11.76/1.99  --preprocessing_flag                    true
% 11.76/1.99  --time_out_prep_mult                    0.1
% 11.76/1.99  --splitting_mode                        input
% 11.76/1.99  --splitting_grd                         true
% 11.76/1.99  --splitting_cvd                         false
% 11.76/1.99  --splitting_cvd_svl                     false
% 11.76/1.99  --splitting_nvd                         32
% 11.76/1.99  --sub_typing                            true
% 11.76/1.99  --prep_gs_sim                           false
% 11.76/1.99  --prep_unflatten                        true
% 11.76/1.99  --prep_res_sim                          true
% 11.76/1.99  --prep_upred                            true
% 11.76/1.99  --prep_sem_filter                       exhaustive
% 11.76/1.99  --prep_sem_filter_out                   false
% 11.76/1.99  --pred_elim                             false
% 11.76/1.99  --res_sim_input                         true
% 11.76/1.99  --eq_ax_congr_red                       true
% 11.76/1.99  --pure_diseq_elim                       true
% 11.76/1.99  --brand_transform                       false
% 11.76/1.99  --non_eq_to_eq                          false
% 11.76/1.99  --prep_def_merge                        true
% 11.76/1.99  --prep_def_merge_prop_impl              false
% 11.76/1.99  --prep_def_merge_mbd                    true
% 11.76/1.99  --prep_def_merge_tr_red                 false
% 11.76/1.99  --prep_def_merge_tr_cl                  false
% 11.76/1.99  --smt_preprocessing                     true
% 11.76/1.99  --smt_ac_axioms                         fast
% 11.76/1.99  --preprocessed_out                      false
% 11.76/1.99  --preprocessed_stats                    false
% 11.76/1.99  
% 11.76/1.99  ------ Abstraction refinement Options
% 11.76/1.99  
% 11.76/1.99  --abstr_ref                             []
% 11.76/1.99  --abstr_ref_prep                        false
% 11.76/1.99  --abstr_ref_until_sat                   false
% 11.76/1.99  --abstr_ref_sig_restrict                funpre
% 11.76/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.76/1.99  --abstr_ref_under                       []
% 11.76/1.99  
% 11.76/1.99  ------ SAT Options
% 11.76/1.99  
% 11.76/1.99  --sat_mode                              false
% 11.76/1.99  --sat_fm_restart_options                ""
% 11.76/1.99  --sat_gr_def                            false
% 11.76/1.99  --sat_epr_types                         true
% 11.76/1.99  --sat_non_cyclic_types                  false
% 11.76/1.99  --sat_finite_models                     false
% 11.76/1.99  --sat_fm_lemmas                         false
% 11.76/1.99  --sat_fm_prep                           false
% 11.76/1.99  --sat_fm_uc_incr                        true
% 11.76/1.99  --sat_out_model                         small
% 11.76/1.99  --sat_out_clauses                       false
% 11.76/1.99  
% 11.76/1.99  ------ QBF Options
% 11.76/1.99  
% 11.76/1.99  --qbf_mode                              false
% 11.76/1.99  --qbf_elim_univ                         false
% 11.76/1.99  --qbf_dom_inst                          none
% 11.76/1.99  --qbf_dom_pre_inst                      false
% 11.76/1.99  --qbf_sk_in                             false
% 11.76/1.99  --qbf_pred_elim                         true
% 11.76/1.99  --qbf_split                             512
% 11.76/1.99  
% 11.76/1.99  ------ BMC1 Options
% 11.76/1.99  
% 11.76/1.99  --bmc1_incremental                      false
% 11.76/1.99  --bmc1_axioms                           reachable_all
% 11.76/1.99  --bmc1_min_bound                        0
% 11.76/1.99  --bmc1_max_bound                        -1
% 11.76/1.99  --bmc1_max_bound_default                -1
% 11.76/1.99  --bmc1_symbol_reachability              true
% 11.76/1.99  --bmc1_property_lemmas                  false
% 11.76/1.99  --bmc1_k_induction                      false
% 11.76/1.99  --bmc1_non_equiv_states                 false
% 11.76/1.99  --bmc1_deadlock                         false
% 11.76/1.99  --bmc1_ucm                              false
% 11.76/1.99  --bmc1_add_unsat_core                   none
% 11.76/1.99  --bmc1_unsat_core_children              false
% 11.76/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.76/1.99  --bmc1_out_stat                         full
% 11.76/1.99  --bmc1_ground_init                      false
% 11.76/1.99  --bmc1_pre_inst_next_state              false
% 11.76/1.99  --bmc1_pre_inst_state                   false
% 11.76/1.99  --bmc1_pre_inst_reach_state             false
% 11.76/1.99  --bmc1_out_unsat_core                   false
% 11.76/1.99  --bmc1_aig_witness_out                  false
% 11.76/1.99  --bmc1_verbose                          false
% 11.76/1.99  --bmc1_dump_clauses_tptp                false
% 11.76/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.76/1.99  --bmc1_dump_file                        -
% 11.76/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.76/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.76/1.99  --bmc1_ucm_extend_mode                  1
% 11.76/1.99  --bmc1_ucm_init_mode                    2
% 11.76/1.99  --bmc1_ucm_cone_mode                    none
% 11.76/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.76/1.99  --bmc1_ucm_relax_model                  4
% 11.76/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.76/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.76/1.99  --bmc1_ucm_layered_model                none
% 11.76/1.99  --bmc1_ucm_max_lemma_size               10
% 11.76/1.99  
% 11.76/1.99  ------ AIG Options
% 11.76/1.99  
% 11.76/1.99  --aig_mode                              false
% 11.76/1.99  
% 11.76/1.99  ------ Instantiation Options
% 11.76/1.99  
% 11.76/1.99  --instantiation_flag                    true
% 11.76/1.99  --inst_sos_flag                         false
% 11.76/1.99  --inst_sos_phase                        true
% 11.76/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.76/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.76/1.99  --inst_lit_sel_side                     num_symb
% 11.76/1.99  --inst_solver_per_active                1400
% 11.76/1.99  --inst_solver_calls_frac                1.
% 11.76/1.99  --inst_passive_queue_type               priority_queues
% 11.76/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.76/1.99  --inst_passive_queues_freq              [25;2]
% 11.76/1.99  --inst_dismatching                      true
% 11.76/1.99  --inst_eager_unprocessed_to_passive     true
% 11.76/1.99  --inst_prop_sim_given                   true
% 11.76/1.99  --inst_prop_sim_new                     false
% 11.76/1.99  --inst_subs_new                         false
% 11.76/1.99  --inst_eq_res_simp                      false
% 11.76/1.99  --inst_subs_given                       false
% 11.76/1.99  --inst_orphan_elimination               true
% 11.76/1.99  --inst_learning_loop_flag               true
% 11.76/1.99  --inst_learning_start                   3000
% 11.76/1.99  --inst_learning_factor                  2
% 11.76/1.99  --inst_start_prop_sim_after_learn       3
% 11.76/1.99  --inst_sel_renew                        solver
% 11.76/1.99  --inst_lit_activity_flag                true
% 11.76/1.99  --inst_restr_to_given                   false
% 11.76/1.99  --inst_activity_threshold               500
% 11.76/1.99  --inst_out_proof                        true
% 11.76/1.99  
% 11.76/1.99  ------ Resolution Options
% 11.76/1.99  
% 11.76/1.99  --resolution_flag                       true
% 11.76/1.99  --res_lit_sel                           adaptive
% 11.76/1.99  --res_lit_sel_side                      none
% 11.76/1.99  --res_ordering                          kbo
% 11.76/1.99  --res_to_prop_solver                    active
% 11.76/1.99  --res_prop_simpl_new                    false
% 11.76/1.99  --res_prop_simpl_given                  true
% 11.76/1.99  --res_passive_queue_type                priority_queues
% 11.76/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.76/1.99  --res_passive_queues_freq               [15;5]
% 11.76/1.99  --res_forward_subs                      full
% 11.76/1.99  --res_backward_subs                     full
% 11.76/1.99  --res_forward_subs_resolution           true
% 11.76/1.99  --res_backward_subs_resolution          true
% 11.76/1.99  --res_orphan_elimination                true
% 11.76/1.99  --res_time_limit                        2.
% 11.76/1.99  --res_out_proof                         true
% 11.76/1.99  
% 11.76/1.99  ------ Superposition Options
% 11.76/1.99  
% 11.76/1.99  --superposition_flag                    true
% 11.76/1.99  --sup_passive_queue_type                priority_queues
% 11.76/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.76/1.99  --sup_passive_queues_freq               [1;4]
% 11.76/1.99  --demod_completeness_check              fast
% 11.76/1.99  --demod_use_ground                      true
% 11.76/1.99  --sup_to_prop_solver                    passive
% 11.76/1.99  --sup_prop_simpl_new                    true
% 11.76/1.99  --sup_prop_simpl_given                  true
% 11.76/1.99  --sup_fun_splitting                     false
% 11.76/1.99  --sup_smt_interval                      50000
% 11.76/1.99  
% 11.76/1.99  ------ Superposition Simplification Setup
% 11.76/1.99  
% 11.76/1.99  --sup_indices_passive                   []
% 11.76/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.76/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.76/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_full_bw                           [BwDemod]
% 11.76/1.99  --sup_immed_triv                        [TrivRules]
% 11.76/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.76/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_immed_bw_main                     []
% 11.76/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.76/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.76/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.76/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.76/1.99  
% 11.76/1.99  ------ Combination Options
% 11.76/1.99  
% 11.76/1.99  --comb_res_mult                         3
% 11.76/1.99  --comb_sup_mult                         2
% 11.76/1.99  --comb_inst_mult                        10
% 11.76/1.99  
% 11.76/1.99  ------ Debug Options
% 11.76/1.99  
% 11.76/1.99  --dbg_backtrace                         false
% 11.76/1.99  --dbg_dump_prop_clauses                 false
% 11.76/1.99  --dbg_dump_prop_clauses_file            -
% 11.76/1.99  --dbg_out_stat                          false
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  ------ Proving...
% 11.76/1.99  
% 11.76/1.99  
% 11.76/1.99  % SZS status Theorem for theBenchmark.p
% 11.76/1.99  
% 11.76/1.99   Resolution empty clause
% 11.76/1.99  
% 11.76/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.76/1.99  
% 11.76/1.99  fof(f14,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f35,plain,(
% 11.76/1.99    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f14])).
% 11.76/1.99  
% 11.76/1.99  fof(f36,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f35])).
% 11.76/1.99  
% 11.76/1.99  fof(f51,plain,(
% 11.76/1.99    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f52,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f51])).
% 11.76/1.99  
% 11.76/1.99  fof(f89,plain,(
% 11.76/1.99    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK2(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f52])).
% 11.76/1.99  
% 11.76/1.99  fof(f13,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f33,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f13])).
% 11.76/1.99  
% 11.76/1.99  fof(f34,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f33])).
% 11.76/1.99  
% 11.76/1.99  fof(f49,plain,(
% 11.76/1.99    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f50,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) & m2_yellow_6(sK1(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f49])).
% 11.76/1.99  
% 11.76/1.99  fof(f86,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (m2_yellow_6(sK1(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f50])).
% 11.76/1.99  
% 11.76/1.99  fof(f9,axiom,(
% 11.76/1.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f25,plain,(
% 11.76/1.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f9])).
% 11.76/1.99  
% 11.76/1.99  fof(f26,plain,(
% 11.76/1.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f25])).
% 11.76/1.99  
% 11.76/1.99  fof(f81,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f26])).
% 11.76/1.99  
% 11.76/1.99  fof(f7,axiom,(
% 11.76/1.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f22,plain,(
% 11.76/1.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.76/1.99    inference(ennf_transformation,[],[f7])).
% 11.76/1.99  
% 11.76/1.99  fof(f76,plain,(
% 11.76/1.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f22])).
% 11.76/1.99  
% 11.76/1.99  fof(f10,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f27,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f10])).
% 11.76/1.99  
% 11.76/1.99  fof(f28,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f27])).
% 11.76/1.99  
% 11.76/1.99  fof(f48,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(nnf_transformation,[],[f28])).
% 11.76/1.99  
% 11.76/1.99  fof(f83,plain,(
% 11.76/1.99    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f48])).
% 11.76/1.99  
% 11.76/1.99  fof(f80,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f26])).
% 11.76/1.99  
% 11.76/1.99  fof(f79,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f26])).
% 11.76/1.99  
% 11.76/1.99  fof(f78,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f26])).
% 11.76/1.99  
% 11.76/1.99  fof(f16,conjecture,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f17,negated_conjecture,(
% 11.76/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 11.76/1.99    inference(negated_conjecture,[],[f16])).
% 11.76/1.99  
% 11.76/1.99  fof(f39,plain,(
% 11.76/1.99    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f17])).
% 11.76/1.99  
% 11.76/1.99  fof(f40,plain,(
% 11.76/1.99    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f39])).
% 11.76/1.99  
% 11.76/1.99  fof(f58,plain,(
% 11.76/1.99    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.76/1.99    inference(nnf_transformation,[],[f40])).
% 11.76/1.99  
% 11.76/1.99  fof(f59,plain,(
% 11.76/1.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f58])).
% 11.76/1.99  
% 11.76/1.99  fof(f60,plain,(
% 11.76/1.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.76/1.99    inference(rectify,[],[f59])).
% 11.76/1.99  
% 11.76/1.99  fof(f63,plain,(
% 11.76/1.99    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK7(X3),X0) & m2_yellow_6(sK7(X3),X0,X3)))) )),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f62,plain,(
% 11.76/1.99    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK6)) & l1_waybel_0(sK6,X0) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6))) )),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f61,plain,(
% 11.76/1.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,X1)) & l1_waybel_0(X1,sK5) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK5)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK5) & m2_yellow_6(X4,sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f64,plain,(
% 11.76/1.99    ((! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6)) & l1_waybel_0(sK6,sK5) & v7_waybel_0(sK6) & v4_orders_2(sK6) & ~v2_struct_0(sK6)) | ~v1_compts_1(sK5)) & (! [X3] : ((v3_yellow_6(sK7(X3),sK5) & m2_yellow_6(sK7(X3),sK5,X3)) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK5)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 11.76/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f60,f63,f62,f61])).
% 11.76/1.99  
% 11.76/1.99  fof(f107,plain,(
% 11.76/1.99    ( ! [X2] : (~v3_yellow_6(X2,sK5) | ~m2_yellow_6(X2,sK5,sK6) | ~v1_compts_1(sK5)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f98,plain,(
% 11.76/1.99    ~v2_struct_0(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f99,plain,(
% 11.76/1.99    v2_pre_topc(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f100,plain,(
% 11.76/1.99    l1_pre_topc(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f103,plain,(
% 11.76/1.99    ~v2_struct_0(sK6) | ~v1_compts_1(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f104,plain,(
% 11.76/1.99    v4_orders_2(sK6) | ~v1_compts_1(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f105,plain,(
% 11.76/1.99    v7_waybel_0(sK6) | ~v1_compts_1(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f106,plain,(
% 11.76/1.99    l1_waybel_0(sK6,sK5) | ~v1_compts_1(sK5)),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f101,plain,(
% 11.76/1.99    ( ! [X3] : (m2_yellow_6(sK7(X3),sK5,X3) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f1,axiom,(
% 11.76/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f18,plain,(
% 11.76/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f1])).
% 11.76/1.99  
% 11.76/1.99  fof(f41,plain,(
% 11.76/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.76/1.99    inference(nnf_transformation,[],[f18])).
% 11.76/1.99  
% 11.76/1.99  fof(f42,plain,(
% 11.76/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.76/1.99    inference(rectify,[],[f41])).
% 11.76/1.99  
% 11.76/1.99  fof(f43,plain,(
% 11.76/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f44,plain,(
% 11.76/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.76/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 11.76/1.99  
% 11.76/1.99  fof(f66,plain,(
% 11.76/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f44])).
% 11.76/1.99  
% 11.76/1.99  fof(f11,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f29,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f11])).
% 11.76/1.99  
% 11.76/1.99  fof(f30,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f29])).
% 11.76/1.99  
% 11.76/1.99  fof(f84,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f30])).
% 11.76/1.99  
% 11.76/1.99  fof(f8,axiom,(
% 11.76/1.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f23,plain,(
% 11.76/1.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f8])).
% 11.76/1.99  
% 11.76/1.99  fof(f24,plain,(
% 11.76/1.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f23])).
% 11.76/1.99  
% 11.76/1.99  fof(f77,plain,(
% 11.76/1.99    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f24])).
% 11.76/1.99  
% 11.76/1.99  fof(f5,axiom,(
% 11.76/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f19,plain,(
% 11.76/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.76/1.99    inference(ennf_transformation,[],[f5])).
% 11.76/1.99  
% 11.76/1.99  fof(f20,plain,(
% 11.76/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.76/1.99    inference(flattening,[],[f19])).
% 11.76/1.99  
% 11.76/1.99  fof(f74,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f20])).
% 11.76/1.99  
% 11.76/1.99  fof(f12,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f31,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f12])).
% 11.76/1.99  
% 11.76/1.99  fof(f32,plain,(
% 11.76/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f31])).
% 11.76/1.99  
% 11.76/1.99  fof(f85,plain,(
% 11.76/1.99    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f32])).
% 11.76/1.99  
% 11.76/1.99  fof(f15,axiom,(
% 11.76/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f37,plain,(
% 11.76/1.99    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.76/1.99    inference(ennf_transformation,[],[f15])).
% 11.76/1.99  
% 11.76/1.99  fof(f38,plain,(
% 11.76/1.99    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(flattening,[],[f37])).
% 11.76/1.99  
% 11.76/1.99  fof(f53,plain,(
% 11.76/1.99    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(nnf_transformation,[],[f38])).
% 11.76/1.99  
% 11.76/1.99  fof(f54,plain,(
% 11.76/1.99    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(rectify,[],[f53])).
% 11.76/1.99  
% 11.76/1.99  fof(f56,plain,(
% 11.76/1.99    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f55,plain,(
% 11.76/1.99    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0))))),
% 11.76/1.99    introduced(choice_axiom,[])).
% 11.76/1.99  
% 11.76/1.99  fof(f57,plain,(
% 11.76/1.99    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK3(X0),k6_yellow_6(X0)) & l1_waybel_0(sK3(X0),X0) & v7_waybel_0(sK3(X0)) & v4_orders_2(sK3(X0)) & ~v2_struct_0(sK3(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK4(X0,X3)) & m1_subset_1(sK4(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.76/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 11.76/1.99  
% 11.76/1.99  fof(f97,plain,(
% 11.76/1.99    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK3(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f57])).
% 11.76/1.99  
% 11.76/1.99  fof(f94,plain,(
% 11.76/1.99    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f57])).
% 11.76/1.99  
% 11.76/1.99  fof(f93,plain,(
% 11.76/1.99    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f57])).
% 11.76/1.99  
% 11.76/1.99  fof(f92,plain,(
% 11.76/1.99    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f57])).
% 11.76/1.99  
% 11.76/1.99  fof(f95,plain,(
% 11.76/1.99    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f57])).
% 11.76/1.99  
% 11.76/1.99  fof(f2,axiom,(
% 11.76/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f45,plain,(
% 11.76/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.76/1.99    inference(nnf_transformation,[],[f2])).
% 11.76/1.99  
% 11.76/1.99  fof(f46,plain,(
% 11.76/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.76/1.99    inference(flattening,[],[f45])).
% 11.76/1.99  
% 11.76/1.99  fof(f70,plain,(
% 11.76/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f46])).
% 11.76/1.99  
% 11.76/1.99  fof(f102,plain,(
% 11.76/1.99    ( ! [X3] : (v3_yellow_6(sK7(X3),sK5) | ~l1_waybel_0(X3,sK5) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK5)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f64])).
% 11.76/1.99  
% 11.76/1.99  fof(f82,plain,(
% 11.76/1.99    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f48])).
% 11.76/1.99  
% 11.76/1.99  fof(f3,axiom,(
% 11.76/1.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f71,plain,(
% 11.76/1.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.76/1.99    inference(cnf_transformation,[],[f3])).
% 11.76/1.99  
% 11.76/1.99  fof(f4,axiom,(
% 11.76/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f47,plain,(
% 11.76/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.76/1.99    inference(nnf_transformation,[],[f4])).
% 11.76/1.99  
% 11.76/1.99  fof(f72,plain,(
% 11.76/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.76/1.99    inference(cnf_transformation,[],[f47])).
% 11.76/1.99  
% 11.76/1.99  fof(f88,plain,(
% 11.76/1.99    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f52])).
% 11.76/1.99  
% 11.76/1.99  fof(f87,plain,(
% 11.76/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f50])).
% 11.76/1.99  
% 11.76/1.99  fof(f6,axiom,(
% 11.76/1.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.76/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.76/1.99  
% 11.76/1.99  fof(f21,plain,(
% 11.76/1.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.76/1.99    inference(ennf_transformation,[],[f6])).
% 11.76/1.99  
% 11.76/1.99  fof(f75,plain,(
% 11.76/1.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.76/1.99    inference(cnf_transformation,[],[f21])).
% 11.76/1.99  
% 11.76/1.99  cnf(c_23,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK2(X0,X1))
% 11.76/1.99      | ~ l1_waybel_0(X1,X0)
% 11.76/1.99      | ~ v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | ~ v4_orders_2(X1)
% 11.76/1.99      | ~ v7_waybel_0(X1)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1755,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK2(X0,X1)) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | v1_compts_1(X0) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_22,plain,
% 11.76/1.99      ( ~ r3_waybel_9(X0,X1,X2)
% 11.76/1.99      | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
% 11.76/1.99      | ~ l1_waybel_0(X1,X0)
% 11.76/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | ~ v4_orders_2(X1)
% 11.76/1.99      | ~ v7_waybel_0(X1)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1756,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | m2_yellow_6(sK1(X0,X1,X2),X0,X1) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_13,plain,
% 11.76/1.99      ( ~ m2_yellow_6(X0,X1,X2)
% 11.76/1.99      | ~ l1_waybel_0(X2,X1)
% 11.76/1.99      | l1_waybel_0(X0,X1)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X2)
% 11.76/1.99      | ~ v4_orders_2(X2)
% 11.76/1.99      | ~ v7_waybel_0(X2)
% 11.76/1.99      | ~ l1_struct_0(X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1765,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(X0,X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | l1_struct_0(X1) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4381,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | l1_struct_0(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1756,c_1765]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_11,plain,
% 11.76/1.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_112,plain,
% 11.76/1.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9488,plain,
% 11.76/1.99      ( l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,[status(thm)],[c_4381,c_112]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9489,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_9488]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_17,plain,
% 11.76/1.99      ( v3_yellow_6(X0,X1)
% 11.76/1.99      | ~ l1_waybel_0(X0,X1)
% 11.76/1.99      | ~ v2_pre_topc(X1)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | ~ l1_pre_topc(X1)
% 11.76/1.99      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 11.76/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1761,plain,
% 11.76/1.99      ( k10_yellow_6(X0,X1) = k1_xboole_0
% 11.76/1.99      | v3_yellow_6(X1,X0) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9504,plain,
% 11.76/1.99      ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(sK1(X0,X1,X2)) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK1(X0,X1,X2)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_9489,c_1761]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_14,plain,
% 11.76/1.99      ( ~ m2_yellow_6(X0,X1,X2)
% 11.76/1.99      | ~ l1_waybel_0(X2,X1)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X2)
% 11.76/1.99      | ~ v4_orders_2(X2)
% 11.76/1.99      | ~ v7_waybel_0(X2)
% 11.76/1.99      | v7_waybel_0(X0)
% 11.76/1.99      | ~ l1_struct_0(X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1764,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) = iProver_top
% 11.76/1.99      | l1_struct_0(X1) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4383,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | l1_struct_0(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1756,c_1764]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9371,plain,
% 11.76/1.99      ( l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,[status(thm)],[c_4383,c_112]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9372,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_9371]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_15,plain,
% 11.76/1.99      ( ~ m2_yellow_6(X0,X1,X2)
% 11.76/1.99      | ~ l1_waybel_0(X2,X1)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X2)
% 11.76/1.99      | ~ v4_orders_2(X2)
% 11.76/1.99      | v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X2)
% 11.76/1.99      | ~ l1_struct_0(X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1763,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v4_orders_2(X0) = iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | l1_struct_0(X1) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4384,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | l1_struct_0(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1756,c_1763]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9471,plain,
% 11.76/1.99      ( l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,[status(thm)],[c_4384,c_112]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9472,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(sK1(X0,X1,X2)) = iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_9471]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_16,plain,
% 11.76/1.99      ( ~ m2_yellow_6(X0,X1,X2)
% 11.76/1.99      | ~ l1_waybel_0(X2,X1)
% 11.76/1.99      | ~ v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X2)
% 11.76/1.99      | ~ v4_orders_2(X2)
% 11.76/1.99      | ~ v7_waybel_0(X2)
% 11.76/1.99      | ~ l1_struct_0(X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1762,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | l1_struct_0(X1) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4382,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | l1_struct_0(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1756,c_1762]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9737,plain,
% 11.76/1.99      ( l1_pre_topc(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,[status(thm)],[c_4382,c_112]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9738,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK1(X0,X1,X2)) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_9737]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12305,plain,
% 11.76/1.99      ( v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,
% 11.76/1.99                [status(thm)],
% 11.76/1.99                [c_9504,c_9372,c_9472,c_9738]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12306,plain,
% 11.76/1.99      ( k10_yellow_6(X0,sK1(X0,X1,X2)) = k1_xboole_0
% 11.76/1.99      | r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | v3_yellow_6(sK1(X0,X1,X2),X0) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_12305]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_33,negated_conjecture,
% 11.76/1.99      ( ~ m2_yellow_6(X0,sK5,sK6)
% 11.76/1.99      | ~ v3_yellow_6(X0,sK5)
% 11.76/1.99      | ~ v1_compts_1(sK5) ),
% 11.76/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1745,plain,
% 11.76/1.99      ( m2_yellow_6(X0,sK5,sK6) != iProver_top
% 11.76/1.99      | v3_yellow_6(X0,sK5) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4385,plain,
% 11.76/1.99      ( r3_waybel_9(sK5,sK6,X0) != iProver_top
% 11.76/1.99      | v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/1.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) != iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK6) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK6) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK6) != iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1756,c_1745]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_42,negated_conjecture,
% 11.76/1.99      ( ~ v2_struct_0(sK5) ),
% 11.76/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_43,plain,
% 11.76/1.99      ( v2_struct_0(sK5) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_41,negated_conjecture,
% 11.76/1.99      ( v2_pre_topc(sK5) ),
% 11.76/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_44,plain,
% 11.76/1.99      ( v2_pre_topc(sK5) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_40,negated_conjecture,
% 11.76/1.99      ( l1_pre_topc(sK5) ),
% 11.76/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_45,plain,
% 11.76/1.99      ( l1_pre_topc(sK5) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_37,negated_conjecture,
% 11.76/1.99      ( ~ v1_compts_1(sK5) | ~ v2_struct_0(sK6) ),
% 11.76/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_52,plain,
% 11.76/1.99      ( v1_compts_1(sK5) != iProver_top | v2_struct_0(sK6) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_36,negated_conjecture,
% 11.76/1.99      ( ~ v1_compts_1(sK5) | v4_orders_2(sK6) ),
% 11.76/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_53,plain,
% 11.76/1.99      ( v1_compts_1(sK5) != iProver_top | v4_orders_2(sK6) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_35,negated_conjecture,
% 11.76/1.99      ( ~ v1_compts_1(sK5) | v7_waybel_0(sK6) ),
% 11.76/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_54,plain,
% 11.76/1.99      ( v1_compts_1(sK5) != iProver_top | v7_waybel_0(sK6) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_34,negated_conjecture,
% 11.76/1.99      ( l1_waybel_0(sK6,sK5) | ~ v1_compts_1(sK5) ),
% 11.76/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_55,plain,
% 11.76/1.99      ( l1_waybel_0(sK6,sK5) = iProver_top | v1_compts_1(sK5) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9754,plain,
% 11.76/1.99      ( v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
% 11.76/1.99      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,
% 11.76/1.99                [status(thm)],
% 11.76/1.99                [c_4385,c_43,c_44,c_45,c_52,c_53,c_54,c_55]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9755,plain,
% 11.76/1.99      ( r3_waybel_9(sK5,sK6,X0) != iProver_top
% 11.76/1.99      | v3_yellow_6(sK1(sK5,sK6,X0),sK5) != iProver_top
% 11.76/1.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_9754]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12322,plain,
% 11.76/1.99      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 11.76/1.99      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/1.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) != iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK6) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK6) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK6) != iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_12306,c_9755]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_39,negated_conjecture,
% 11.76/1.99      ( m2_yellow_6(sK7(X0),sK5,X0)
% 11.76/1.99      | ~ l1_waybel_0(X0,sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1739,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(X0),sK5,X0) = iProver_top
% 11.76/1.99      | l1_waybel_0(X0,sK5) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1,plain,
% 11.76/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1776,plain,
% 11.76/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.76/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_19,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2)
% 11.76/1.99      | ~ l1_waybel_0(X1,X0)
% 11.76/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.76/1.99      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | ~ v4_orders_2(X1)
% 11.76/1.99      | ~ v7_waybel_0(X1)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1759,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | r2_hidden(X2,k10_yellow_6(X0,X1)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4366,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(sK0(k10_yellow_6(X0,X1),X2),u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1776,c_1759]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12,plain,
% 11.76/1.99      ( ~ l1_waybel_0(X0,X1)
% 11.76/1.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/1.99      | ~ v2_pre_topc(X1)
% 11.76/1.99      | v2_struct_0(X1)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | ~ l1_pre_topc(X1) ),
% 11.76/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1766,plain,
% 11.76/1.99      ( l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9,plain,
% 11.76/1.99      ( m1_subset_1(X0,X1)
% 11.76/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.76/1.99      | ~ r2_hidden(X0,X2) ),
% 11.76/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1769,plain,
% 11.76/1.99      ( m1_subset_1(X0,X1) = iProver_top
% 11.76/1.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.76/1.99      | r2_hidden(X0,X2) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_4027,plain,
% 11.76/1.99      ( l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 11.76/1.99      | r2_hidden(X2,k10_yellow_6(X1,X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1766,c_1769]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_8217,plain,
% 11.76/1.99      ( l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) = iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1776,c_4027]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9308,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X1),X2)) = iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X0,X1),X2) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_4366,c_8217]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_20,plain,
% 11.76/1.99      ( ~ r3_waybel_9(X0,X1,X2)
% 11.76/1.99      | r3_waybel_9(X0,X3,X2)
% 11.76/1.99      | ~ m2_yellow_6(X1,X0,X3)
% 11.76/1.99      | ~ l1_waybel_0(X3,X0)
% 11.76/1.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(X3)
% 11.76/1.99      | ~ v4_orders_2(X3)
% 11.76/1.99      | ~ v7_waybel_0(X3)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1758,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/1.99      | r3_waybel_9(X0,X3,X2) = iProver_top
% 11.76/1.99      | m2_yellow_6(X1,X0,X3) != iProver_top
% 11.76/1.99      | l1_waybel_0(X3,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X3) = iProver_top
% 11.76/1.99      | v4_orders_2(X3) != iProver_top
% 11.76/1.99      | v7_waybel_0(X3) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_9312,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
% 11.76/1.99      | m2_yellow_6(X2,X0,X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X0) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | m1_subset_1(sK0(k10_yellow_6(X0,X2),X3),u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_9308,c_1758]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12342,plain,
% 11.76/1.99      ( r3_waybel_9(X0,X1,sK0(k10_yellow_6(X0,X2),X3)) = iProver_top
% 11.76/1.99      | m2_yellow_6(X2,X0,X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/1.99      | l1_waybel_0(X2,X0) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X0,X2),X3) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(X2) = iProver_top
% 11.76/1.99      | v4_orders_2(X1) != iProver_top
% 11.76/1.99      | v4_orders_2(X2) != iProver_top
% 11.76/1.99      | v7_waybel_0(X1) != iProver_top
% 11.76/1.99      | v7_waybel_0(X2) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_9312,c_8217]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_25,plain,
% 11.76/1.99      ( ~ r3_waybel_9(X0,sK3(X0),X1)
% 11.76/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.76/1.99      | v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1753,plain,
% 11.76/1.99      ( r3_waybel_9(X0,sK3(X0),X1) != iProver_top
% 11.76/1.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.76/1.99      | v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12347,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(X1),X1) != iProver_top
% 11.76/1.99      | m1_subset_1(sK0(k10_yellow_6(X1,X0),X2),u1_struct_0(X1)) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.76/1.99      | v1_compts_1(X1) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X1)) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X1)) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X1)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_12342,c_1753]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12743,plain,
% 11.76/1.99      ( l1_waybel_0(sK3(X1),X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.76/1.99      | v1_compts_1(X1) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X1)) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X1)) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X1)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(global_propositional_subsumption,
% 11.76/1.99                [status(thm)],
% 11.76/1.99                [c_12347,c_8217]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12744,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(X1),X1) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.76/1.99      | v1_compts_1(X1) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X1)) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X1)) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X1)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_12743]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_28,plain,
% 11.76/1.99      ( v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v7_waybel_0(sK3(X0))
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1750,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X0)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_29,plain,
% 11.76/1.99      ( v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v4_orders_2(sK3(X0))
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1749,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X0)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_30,plain,
% 11.76/1.99      ( v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ v2_struct_0(sK3(X0))
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1748,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X0)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_27,plain,
% 11.76/1.99      ( l1_waybel_0(sK3(X0),X0)
% 11.76/1.99      | v1_compts_1(X0)
% 11.76/1.99      | ~ v2_pre_topc(X0)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ l1_pre_topc(X0) ),
% 11.76/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_1751,plain,
% 11.76/1.99      ( l1_waybel_0(sK3(X0),X0) = iProver_top
% 11.76/1.99      | v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12763,plain,
% 11.76/1.99      ( m2_yellow_6(X0,X1,sK3(X1)) != iProver_top
% 11.76/1.99      | l1_waybel_0(X0,X1) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(X1,X0),X2) = iProver_top
% 11.76/1.99      | v1_compts_1(X1) = iProver_top
% 11.76/1.99      | v2_pre_topc(X1) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(X1) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.76/1.99      inference(forward_subsumption_resolution,
% 11.76/1.99                [status(thm)],
% 11.76/1.99                [c_12744,c_1750,c_1749,c_1748,c_1751]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_12768,plain,
% 11.76/1.99      ( l1_waybel_0(sK7(sK3(sK5)),sK5) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 11.76/1.99      | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK7(sK3(sK5))) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(sK5)) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK7(sK3(sK5))) != iProver_top
% 11.76/1.99      | v4_orders_2(sK3(sK5)) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK7(sK3(sK5))) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(sK5)) != iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1739,c_12763]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_65,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X0)) != iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_67,plain,
% 11.76/1.99      ( v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK3(sK5)) != iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_65]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_68,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X0)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_70,plain,
% 11.76/1.99      ( v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(sK5)) = iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_68]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_71,plain,
% 11.76/1.99      ( v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X0)) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_73,plain,
% 11.76/1.99      ( v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(sK5)) = iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_71]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_74,plain,
% 11.76/1.99      ( l1_waybel_0(sK3(X0),X0) = iProver_top
% 11.76/1.99      | v1_compts_1(X0) = iProver_top
% 11.76/1.99      | v2_pre_topc(X0) != iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_76,plain,
% 11.76/1.99      ( l1_waybel_0(sK3(sK5),sK5) = iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_pre_topc(sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_74]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_114,plain,
% 11.76/1.99      ( l1_pre_topc(sK5) != iProver_top | l1_struct_0(sK5) = iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_112]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2577,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0))
% 11.76/1.99      | ~ l1_waybel_0(sK3(X0),sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(sK3(X0))
% 11.76/1.99      | ~ v4_orders_2(sK3(X0))
% 11.76/1.99      | ~ v7_waybel_0(sK3(X0)) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_39]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2603,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0)) = iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(X0),sK5) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X0)) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X0)) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X0)) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_2577]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2605,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(sK3(sK5)),sK5,sK3(sK5)) = iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_struct_0(sK3(sK5)) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(sK5)) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_2603]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2808,plain,
% 11.76/1.99      ( ~ m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0))
% 11.76/1.99      | l1_waybel_0(sK7(sK3(X0)),sK5)
% 11.76/1.99      | ~ l1_waybel_0(sK3(X0),sK5)
% 11.76/1.99      | v2_struct_0(sK3(X0))
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | ~ v4_orders_2(sK3(X0))
% 11.76/1.99      | ~ v7_waybel_0(sK3(X0))
% 11.76/1.99      | ~ l1_struct_0(sK5) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2819,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(sK3(X0)),sK5,sK3(X0)) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK7(sK3(X0)),sK5) = iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(X0),sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK3(X0)) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(X0)) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(X0)) != iProver_top
% 11.76/1.99      | l1_struct_0(sK5) != iProver_top ),
% 11.76/1.99      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_2821,plain,
% 11.76/1.99      ( m2_yellow_6(sK7(sK3(sK5)),sK5,sK3(sK5)) != iProver_top
% 11.76/1.99      | l1_waybel_0(sK7(sK3(sK5)),sK5) = iProver_top
% 11.76/1.99      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 11.76/1.99      | v2_struct_0(sK3(sK5)) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(sK3(sK5)) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK3(sK5)) != iProver_top
% 11.76/1.99      | l1_struct_0(sK5) != iProver_top ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_2819]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_5636,plain,
% 11.76/1.99      ( ~ l1_waybel_0(X0,sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | v7_waybel_0(sK7(X0))
% 11.76/1.99      | ~ l1_struct_0(sK5) ),
% 11.76/1.99      inference(resolution,[status(thm)],[c_14,c_39]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_113,plain,
% 11.76/1.99      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_3770,plain,
% 11.76/1.99      ( l1_waybel_0(X0,sK5) != iProver_top
% 11.76/1.99      | v1_compts_1(sK5) = iProver_top
% 11.76/1.99      | v2_struct_0(X0) = iProver_top
% 11.76/1.99      | v2_struct_0(sK5) = iProver_top
% 11.76/1.99      | v4_orders_2(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(X0) != iProver_top
% 11.76/1.99      | v7_waybel_0(sK7(X0)) = iProver_top
% 11.76/1.99      | l1_struct_0(sK5) != iProver_top ),
% 11.76/1.99      inference(superposition,[status(thm)],[c_1739,c_1764]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_3771,plain,
% 11.76/1.99      ( ~ l1_waybel_0(X0,sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | v7_waybel_0(sK7(X0))
% 11.76/1.99      | ~ l1_struct_0(sK5) ),
% 11.76/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_3770]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_5953,plain,
% 11.76/1.99      ( v7_waybel_0(sK7(X0))
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ l1_waybel_0(X0,sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(X0) ),
% 11.76/1.99      inference(global_propositional_subsumption,
% 11.76/1.99                [status(thm)],
% 11.76/1.99                [c_5636,c_42,c_40,c_113,c_3771]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_5954,plain,
% 11.76/1.99      ( ~ l1_waybel_0(X0,sK5)
% 11.76/1.99      | v1_compts_1(sK5)
% 11.76/1.99      | v2_struct_0(X0)
% 11.76/1.99      | ~ v4_orders_2(X0)
% 11.76/1.99      | ~ v7_waybel_0(X0)
% 11.76/1.99      | v7_waybel_0(sK7(X0)) ),
% 11.76/1.99      inference(renaming,[status(thm)],[c_5953]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_6195,plain,
% 11.76/1.99      ( v1_compts_1(sK5)
% 11.76/1.99      | ~ v2_pre_topc(sK5)
% 11.76/1.99      | v2_struct_0(sK3(sK5))
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | ~ v4_orders_2(sK3(sK5))
% 11.76/1.99      | v7_waybel_0(sK7(sK3(sK5)))
% 11.76/1.99      | ~ v7_waybel_0(sK3(sK5))
% 11.76/1.99      | ~ l1_pre_topc(sK5) ),
% 11.76/1.99      inference(resolution,[status(thm)],[c_5954,c_27]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_66,plain,
% 11.76/1.99      ( v1_compts_1(sK5)
% 11.76/1.99      | ~ v2_pre_topc(sK5)
% 11.76/1.99      | ~ v2_struct_0(sK3(sK5))
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | ~ l1_pre_topc(sK5) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_30]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_69,plain,
% 11.76/1.99      ( v1_compts_1(sK5)
% 11.76/1.99      | ~ v2_pre_topc(sK5)
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | v4_orders_2(sK3(sK5))
% 11.76/1.99      | ~ l1_pre_topc(sK5) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_29]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_72,plain,
% 11.76/1.99      ( v1_compts_1(sK5)
% 11.76/1.99      | ~ v2_pre_topc(sK5)
% 11.76/1.99      | v2_struct_0(sK5)
% 11.76/1.99      | v7_waybel_0(sK3(sK5))
% 11.76/1.99      | ~ l1_pre_topc(sK5) ),
% 11.76/1.99      inference(instantiation,[status(thm)],[c_28]) ).
% 11.76/1.99  
% 11.76/1.99  cnf(c_6336,plain,
% 11.76/1.99      ( v1_compts_1(sK5) | v7_waybel_0(sK7(sK3(sK5))) ),
% 11.76/1.99      inference(global_propositional_subsumption,
% 11.76/1.99                [status(thm)],
% 11.76/2.00                [c_6195,c_42,c_41,c_40,c_66,c_69,c_72]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6338,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v7_waybel_0(sK7(sK3(sK5))) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_6336]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5930,plain,
% 11.76/2.00      ( ~ l1_waybel_0(X0,sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | v2_struct_0(sK5)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | v4_orders_2(sK7(X0))
% 11.76/2.00      | ~ v7_waybel_0(X0)
% 11.76/2.00      | ~ l1_struct_0(sK5) ),
% 11.76/2.00      inference(resolution,[status(thm)],[c_15,c_39]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3649,plain,
% 11.76/2.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(X0) != iProver_top
% 11.76/2.00      | v4_orders_2(sK7(X0)) = iProver_top
% 11.76/2.00      | v7_waybel_0(X0) != iProver_top
% 11.76/2.00      | l1_struct_0(sK5) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1739,c_1763]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3650,plain,
% 11.76/2.00      ( ~ l1_waybel_0(X0,sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | v2_struct_0(sK5)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | v4_orders_2(sK7(X0))
% 11.76/2.00      | ~ v7_waybel_0(X0)
% 11.76/2.00      | ~ l1_struct_0(sK5) ),
% 11.76/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3649]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6198,plain,
% 11.76/2.00      ( ~ v7_waybel_0(X0)
% 11.76/2.00      | v4_orders_2(sK7(X0))
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | ~ l1_waybel_0(X0,sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(X0) ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_5930,c_42,c_40,c_113,c_3650]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6199,plain,
% 11.76/2.00      ( ~ l1_waybel_0(X0,sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | v4_orders_2(sK7(X0))
% 11.76/2.00      | ~ v7_waybel_0(X0) ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_6198]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6232,plain,
% 11.76/2.00      ( v1_compts_1(sK5)
% 11.76/2.00      | ~ v2_pre_topc(sK5)
% 11.76/2.00      | v2_struct_0(sK3(sK5))
% 11.76/2.00      | v2_struct_0(sK5)
% 11.76/2.00      | v4_orders_2(sK7(sK3(sK5)))
% 11.76/2.00      | ~ v4_orders_2(sK3(sK5))
% 11.76/2.00      | ~ v7_waybel_0(sK3(sK5))
% 11.76/2.00      | ~ l1_pre_topc(sK5) ),
% 11.76/2.00      inference(resolution,[status(thm)],[c_6199,c_27]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6353,plain,
% 11.76/2.00      ( v4_orders_2(sK7(sK3(sK5))) | v1_compts_1(sK5) ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_6232,c_42,c_41,c_40,c_66,c_69,c_72]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6354,plain,
% 11.76/2.00      ( v1_compts_1(sK5) | v4_orders_2(sK7(sK3(sK5))) ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_6353]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6355,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK7(sK3(sK5))) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_6354]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3883,plain,
% 11.76/2.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK7(X0)) != iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(X0) != iProver_top
% 11.76/2.00      | v7_waybel_0(X0) != iProver_top
% 11.76/2.00      | l1_struct_0(sK5) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1739,c_1762]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_7478,plain,
% 11.76/2.00      ( v7_waybel_0(X0) != iProver_top
% 11.76/2.00      | v4_orders_2(X0) != iProver_top
% 11.76/2.00      | l1_waybel_0(X0,sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK7(X0)) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_3883,c_43,c_45,c_114]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_7479,plain,
% 11.76/2.00      ( l1_waybel_0(X0,sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK7(X0)) != iProver_top
% 11.76/2.00      | v4_orders_2(X0) != iProver_top
% 11.76/2.00      | v7_waybel_0(X0) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_7478]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_7490,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 11.76/2.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK3(sK5)) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1751,c_7479]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_7999,plain,
% 11.76/2.00      ( v2_struct_0(sK7(sK3(sK5))) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_7490,c_43,c_44,c_45,c_67,c_70,c_73]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_8000,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(sK7(sK3(sK5))) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_7999]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_13129,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_12768,c_43,c_44,c_45,c_67,c_70,c_73,c_76,c_114,c_2605,
% 11.76/2.00                 c_2821,c_6338,c_6355,c_7490]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_13130,plain,
% 11.76/2.00      ( r1_tarski(k10_yellow_6(sK5,sK7(sK3(sK5))),X0) = iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_13129]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3,plain,
% 11.76/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.76/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1774,plain,
% 11.76/2.00      ( X0 = X1
% 11.76/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.76/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_13137,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK7(sK3(sK5))) = X0
% 11.76/2.00      | r1_tarski(X0,k10_yellow_6(sK5,sK7(sK3(sK5)))) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_13130,c_1774]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_38,negated_conjecture,
% 11.76/2.00      ( v3_yellow_6(sK7(X0),sK5)
% 11.76/2.00      | ~ l1_waybel_0(X0,sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | ~ v7_waybel_0(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2578,plain,
% 11.76/2.00      ( v3_yellow_6(sK7(sK3(X0)),sK5)
% 11.76/2.00      | ~ l1_waybel_0(sK3(X0),sK5)
% 11.76/2.00      | v1_compts_1(sK5)
% 11.76/2.00      | v2_struct_0(sK3(X0))
% 11.76/2.00      | ~ v4_orders_2(sK3(X0))
% 11.76/2.00      | ~ v7_waybel_0(sK3(X0)) ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_38]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2599,plain,
% 11.76/2.00      ( v3_yellow_6(sK7(sK3(X0)),sK5) = iProver_top
% 11.76/2.00      | l1_waybel_0(sK3(X0),sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(sK3(X0)) = iProver_top
% 11.76/2.00      | v4_orders_2(sK3(X0)) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK3(X0)) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_2578]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2601,plain,
% 11.76/2.00      ( v3_yellow_6(sK7(sK3(sK5)),sK5) = iProver_top
% 11.76/2.00      | l1_waybel_0(sK3(sK5),sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top
% 11.76/2.00      | v2_struct_0(sK3(sK5)) = iProver_top
% 11.76/2.00      | v4_orders_2(sK3(sK5)) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK3(sK5)) != iProver_top ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_2599]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_18,plain,
% 11.76/2.00      ( ~ v3_yellow_6(X0,X1)
% 11.76/2.00      | ~ l1_waybel_0(X0,X1)
% 11.76/2.00      | ~ v2_pre_topc(X1)
% 11.76/2.00      | v2_struct_0(X1)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | ~ v7_waybel_0(X0)
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 11.76/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2792,plain,
% 11.76/2.00      ( ~ v3_yellow_6(sK7(sK3(X0)),sK5)
% 11.76/2.00      | ~ l1_waybel_0(sK7(sK3(X0)),sK5)
% 11.76/2.00      | ~ v2_pre_topc(sK5)
% 11.76/2.00      | v2_struct_0(sK7(sK3(X0)))
% 11.76/2.00      | v2_struct_0(sK5)
% 11.76/2.00      | ~ v4_orders_2(sK7(sK3(X0)))
% 11.76/2.00      | ~ v7_waybel_0(sK7(sK3(X0)))
% 11.76/2.00      | ~ l1_pre_topc(sK5)
% 11.76/2.00      | k10_yellow_6(sK5,sK7(sK3(X0))) != k1_xboole_0 ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2798,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK7(sK3(X0))) != k1_xboole_0
% 11.76/2.00      | v3_yellow_6(sK7(sK3(X0)),sK5) != iProver_top
% 11.76/2.00      | l1_waybel_0(sK7(sK3(X0)),sK5) != iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK7(sK3(X0))) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK7(sK3(X0))) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK7(sK3(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_2792]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2800,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK7(sK3(sK5))) != k1_xboole_0
% 11.76/2.00      | v3_yellow_6(sK7(sK3(sK5)),sK5) != iProver_top
% 11.76/2.00      | l1_waybel_0(sK7(sK3(sK5)),sK5) != iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK7(sK3(sK5))) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK7(sK3(sK5))) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK7(sK3(sK5))) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_2798]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6,plain,
% 11.76/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1772,plain,
% 11.76/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_8,plain,
% 11.76/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.76/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1770,plain,
% 11.76/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.76/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2613,plain,
% 11.76/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1772,c_1770]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_4973,plain,
% 11.76/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2613,c_1774]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_13138,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK7(sK3(sK5))) = k1_xboole_0
% 11.76/2.00      | v1_compts_1(sK5) = iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_13130,c_4973]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_13234,plain,
% 11.76/2.00      ( v1_compts_1(sK5) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_13137,c_43,c_44,c_45,c_67,c_70,c_73,c_76,c_114,c_2601,
% 11.76/2.00                 c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,c_13138]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_36820,plain,
% 11.76/2.00      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 11.76/2.00      | k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 11.76/2.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_12322,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,
% 11.76/2.00                 c_76,c_114,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,c_8000,
% 11.76/2.00                 c_13138]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_36821,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,X0)) = k1_xboole_0
% 11.76/2.00      | r3_waybel_9(sK5,sK6,X0) != iProver_top
% 11.76/2.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_36820]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_36829,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0
% 11.76/2.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/2.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) != iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1755,c_36821]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_24,plain,
% 11.76/2.00      ( ~ l1_waybel_0(X0,X1)
% 11.76/2.00      | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 11.76/2.00      | ~ v1_compts_1(X1)
% 11.76/2.00      | ~ v2_pre_topc(X1)
% 11.76/2.00      | v2_struct_0(X1)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | ~ v4_orders_2(X0)
% 11.76/2.00      | ~ v7_waybel_0(X0)
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2434,plain,
% 11.76/2.00      ( ~ l1_waybel_0(sK6,X0)
% 11.76/2.00      | m1_subset_1(sK2(X0,sK6),u1_struct_0(X0))
% 11.76/2.00      | ~ v1_compts_1(X0)
% 11.76/2.00      | ~ v2_pre_topc(X0)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | v2_struct_0(sK6)
% 11.76/2.00      | ~ v4_orders_2(sK6)
% 11.76/2.00      | ~ v7_waybel_0(sK6)
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2435,plain,
% 11.76/2.00      ( l1_waybel_0(sK6,X0) != iProver_top
% 11.76/2.00      | m1_subset_1(sK2(X0,sK6),u1_struct_0(X0)) = iProver_top
% 11.76/2.00      | v1_compts_1(X0) != iProver_top
% 11.76/2.00      | v2_pre_topc(X0) != iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_2434]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2437,plain,
% 11.76/2.00      ( l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/2.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) = iProver_top
% 11.76/2.00      | v1_compts_1(sK5) != iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_2435]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_37426,plain,
% 11.76/2.00      ( k10_yellow_6(sK5,sK1(sK5,sK6,sK2(sK5,sK6))) = k1_xboole_0 ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_36829,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,
% 11.76/2.00                 c_76,c_114,c_2437,c_2601,c_2605,c_2800,c_2821,c_6338,c_6355,
% 11.76/2.00                 c_8000,c_13138]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_21,plain,
% 11.76/2.00      ( ~ r3_waybel_9(X0,X1,X2)
% 11.76/2.00      | ~ l1_waybel_0(X1,X0)
% 11.76/2.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 11.76/2.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
% 11.76/2.00      | ~ v2_pre_topc(X0)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | v2_struct_0(X1)
% 11.76/2.00      | ~ v4_orders_2(X1)
% 11.76/2.00      | ~ v7_waybel_0(X1)
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1757,plain,
% 11.76/2.00      ( r3_waybel_9(X0,X1,X2) != iProver_top
% 11.76/2.00      | l1_waybel_0(X1,X0) != iProver_top
% 11.76/2.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 11.76/2.00      | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2))) = iProver_top
% 11.76/2.00      | v2_pre_topc(X0) != iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(X1) = iProver_top
% 11.76/2.00      | v4_orders_2(X1) != iProver_top
% 11.76/2.00      | v7_waybel_0(X1) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_37453,plain,
% 11.76/2.00      ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) != iProver_top
% 11.76/2.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/2.00      | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 11.76/2.00      | r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_37426,c_1757]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2439,plain,
% 11.76/2.00      ( r3_waybel_9(X0,sK6,sK2(X0,sK6))
% 11.76/2.00      | ~ l1_waybel_0(sK6,X0)
% 11.76/2.00      | ~ v1_compts_1(X0)
% 11.76/2.00      | ~ v2_pre_topc(X0)
% 11.76/2.00      | v2_struct_0(X0)
% 11.76/2.00      | v2_struct_0(sK6)
% 11.76/2.00      | ~ v4_orders_2(sK6)
% 11.76/2.00      | ~ v7_waybel_0(sK6)
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_23]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2440,plain,
% 11.76/2.00      ( r3_waybel_9(X0,sK6,sK2(X0,sK6)) = iProver_top
% 11.76/2.00      | l1_waybel_0(sK6,X0) != iProver_top
% 11.76/2.00      | v1_compts_1(X0) != iProver_top
% 11.76/2.00      | v2_pre_topc(X0) != iProver_top
% 11.76/2.00      | v2_struct_0(X0) = iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2442,plain,
% 11.76/2.00      ( r3_waybel_9(sK5,sK6,sK2(sK5,sK6)) = iProver_top
% 11.76/2.00      | l1_waybel_0(sK6,sK5) != iProver_top
% 11.76/2.00      | v1_compts_1(sK5) != iProver_top
% 11.76/2.00      | v2_pre_topc(sK5) != iProver_top
% 11.76/2.00      | v2_struct_0(sK6) = iProver_top
% 11.76/2.00      | v2_struct_0(sK5) = iProver_top
% 11.76/2.00      | v4_orders_2(sK6) != iProver_top
% 11.76/2.00      | v7_waybel_0(sK6) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK5) != iProver_top ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_2440]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_38270,plain,
% 11.76/2.00      ( r2_hidden(sK2(sK5,sK6),k1_xboole_0) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_37453,c_43,c_44,c_45,c_52,c_53,c_54,c_55,c_67,c_70,c_73,
% 11.76/2.00                 c_76,c_114,c_2437,c_2442,c_2601,c_2605,c_2800,c_2821,c_6338,
% 11.76/2.00                 c_6355,c_8000,c_13138]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_10,plain,
% 11.76/2.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1768,plain,
% 11.76/2.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_38276,plain,
% 11.76/2.00      ( r1_tarski(k1_xboole_0,sK2(sK5,sK6)) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_38270,c_1768]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_38296,plain,
% 11.76/2.00      ( $false ),
% 11.76/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_38276,c_2613]) ).
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.76/2.00  
% 11.76/2.00  ------                               Statistics
% 11.76/2.00  
% 11.76/2.00  ------ Selected
% 11.76/2.00  
% 11.76/2.00  total_time:                             1.32
% 11.76/2.00  
%------------------------------------------------------------------------------
