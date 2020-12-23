%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:59 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  379 (21889 expanded)
%              Number of clauses        :  279 (3757 expanded)
%              Number of leaves         :   23 (5444 expanded)
%              Depth                    :   37
%              Number of atoms          : 3054 (326047 expanded)
%              Number of equality atoms :  408 (3129 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   36 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v10_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
                  & r1_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v10_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
                  & r1_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2))
            | ~ r1_waybel_9(X0,X2) )
          & v10_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
            | ~ r1_waybel_9(X0,X1) )
          & v10_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_2(X0,sK9),k10_yellow_6(X0,sK9))
          | ~ r1_waybel_9(X0,sK9) )
        & v10_waybel_0(sK9,X0)
        & l1_waybel_0(sK9,X0)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1))
              | ~ r1_waybel_9(X0,X1) )
            & v10_waybel_0(X1,X0)
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_2(sK8,X1),k10_yellow_6(sK8,X1))
            | ~ r1_waybel_9(sK8,X1) )
          & v10_waybel_0(X1,sK8)
          & l1_waybel_0(X1,sK8)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8)
          | ~ m1_subset_1(X2,u1_struct_0(sK8)) )
      & l1_waybel_9(sK8)
      & v1_compts_1(sK8)
      & v2_lattice3(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8)
      & v4_orders_2(sK8)
      & v3_orders_2(sK8)
      & v8_pre_topc(sK8)
      & v2_pre_topc(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
      | ~ r1_waybel_9(sK8,sK9) )
    & v10_waybel_0(sK9,sK8)
    & l1_waybel_0(sK9,sK8)
    & v7_waybel_0(sK9)
    & v4_orders_2(sK9)
    & ~ v2_struct_0(sK9)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8)
        | ~ m1_subset_1(X2,u1_struct_0(sK8)) )
    & l1_waybel_9(sK8)
    & v1_compts_1(sK8)
    & v2_lattice3(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8)
    & v4_orders_2(sK8)
    & v3_orders_2(sK8)
    & v8_pre_topc(sK8)
    & v2_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f56,f58,f57])).

fof(f99,plain,(
    l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f48])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    l1_waybel_9(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f72,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,(
    v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK1(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK1(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK1(X0,X1))
              & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r3_orders_2(X0,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r3_orders_2(X0,X3,X5) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X3,X5)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X3,X4)
                      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
                    & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f95,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8)
      | ~ m1_subset_1(X2,u1_struct_0(sK8)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,X3,X4)
      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    v10_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v10_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v10_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
                    & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f43])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v10_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X4)
                 => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ? [X3] :
              ( ? [X4] :
                  ( X3 != X4
                  & r3_waybel_9(X0,X1,X4)
                  & r3_waybel_9(X0,X1,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f52,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( X3 != X4
          & r3_waybel_9(X0,X1,X4)
          & r3_waybel_9(X0,X1,X3)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sK6(X0,X1) != X3
        & r3_waybel_9(X0,X1,sK6(X0,X1))
        & r3_waybel_9(X0,X1,X3)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( X3 != X4
              & r3_waybel_9(X0,X1,X4)
              & r3_waybel_9(X0,X1,X3)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( sK5(X0,X1) != X4
            & r3_waybel_9(X0,X1,X4)
            & r3_waybel_9(X0,X1,sK5(X0,X1))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ( sK5(X0,X1) != sK6(X0,X1)
            & r3_waybel_9(X0,X1,sK6(X0,X1))
            & r3_waybel_9(X0,X1,sK5(X0,X1))
            & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f50,f52,f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK5(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_waybel_9(X0,X1)
          <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_waybel_9(X0,X1)
              | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r1_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_waybel_9(X0,X1)
      | ~ r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,
    ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r1_waybel_9(sK8,sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v10_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_2(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_2(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v10_waybel_0(X2,X0)
              | ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
                & m1_subset_1(sK7(X0),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f54])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_2(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_2(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v10_waybel_0(X2,X0)
      | m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK5(X0,X1) != sK6(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,X1,sK6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_17,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_12,plain,
    ( l1_pre_topc(X0)
    | ~ l1_waybel_9(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( l1_waybel_9(sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1724,plain,
    ( l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_1725,plain,
    ( l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1724])).

cnf(c_2697,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1725])).

cnf(c_2698,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2697])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,negated_conjecture,
    ( v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,negated_conjecture,
    ( v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_11,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_103,plain,
    ( ~ l1_waybel_9(sK8)
    | l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_130,plain,
    ( ~ v1_lattice3(sK8)
    | ~ v2_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2702,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2698,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2703,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2702])).

cnf(c_2824,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2703])).

cnf(c_2825,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2824])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_30,negated_conjecture,
    ( v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_29,negated_conjecture,
    ( v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2827,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2825,c_31,c_30,c_29])).

cnf(c_4669,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
    inference(subtyping,[status(esa)],[c_2827])).

cnf(c_5165,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4669])).

cnf(c_4,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_688,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_4])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1590,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_688,c_37])).

cnf(c_1591,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1590])).

cnf(c_1595,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_yellow_0(sK8,X0)
    | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | ~ r2_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1591,c_33])).

cnf(c_1596,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1595])).

cnf(c_4679,plain,
    ( ~ r2_lattice3(sK8,X0_70,X0_69)
    | r2_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_69))
    | r1_yellow_0(sK8,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1596])).

cnf(c_5151,plain,
    ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
    | r2_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_69)) = iProver_top
    | r1_yellow_0(sK8,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4679])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_748,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_1])).

cnf(c_15,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK8,X0),sK8,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1025,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k4_waybel_1(X0,sK3(X0)) != k4_waybel_1(sK8,X4)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_1026,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r3_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK8)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_39,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1030,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | r3_orders_2(sK8,X1,X2)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1031,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r3_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(renaming,[status(thm)],[c_1030])).

cnf(c_1203,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(X3,X4,X5)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X6,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X3)
    | X1 != X4
    | X2 != X5
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X6)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_748,c_1031])).

cnf(c_1204,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v3_orders_2(sK8)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1208,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | r1_orders_2(sK8,X1,X2)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | ~ r3_waybel_9(sK8,X0,X1)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_39,c_36,c_33,c_103,c_130])).

cnf(c_1209,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(renaming,[status(thm)],[c_1208])).

cnf(c_2980,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1209])).

cnf(c_2981,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_2980])).

cnf(c_2985,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_orders_2(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | ~ r3_waybel_9(sK8,sK9,X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2981,c_31,c_30,c_29])).

cnf(c_2986,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_2985])).

cnf(c_4667,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
    | r1_orders_2(sK8,X0_69,X1_69)
    | ~ m1_subset_1(X2_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2_69) ),
    inference(subtyping,[status(esa)],[c_2986])).

cnf(c_4688,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
    | r1_orders_2(sK8,X0_69,X1_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_4667])).

cnf(c_5168,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4688])).

cnf(c_16,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r3_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1136,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X4,X5,X6)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X4)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X4)
    | ~ v3_orders_2(X0)
    | X0 != X4
    | X2 != X5
    | X3 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_748,c_16])).

cnf(c_1137,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1136])).

cnf(c_734,plain,
    ( ~ l1_waybel_9(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_2])).

cnf(c_1141,plain,
    ( v2_struct_0(X1)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_waybel_9(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v1_compts_1(X0)
    | ~ v2_lattice3(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ v3_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1137,c_734])).

cnf(c_1142,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_1141])).

cnf(c_1402,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1142,c_39])).

cnf(c_1403,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1402])).

cnf(c_1407,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1408,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1407])).

cnf(c_2950,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1408])).

cnf(c_2951,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2950])).

cnf(c_2955,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_orders_2(sK8,X0,X1)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | ~ r3_waybel_9(sK8,sK9,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2951,c_31,c_30,c_29])).

cnf(c_2956,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_2955])).

cnf(c_4668,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
    | r1_orders_2(sK8,X0_69,X1_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_2956])).

cnf(c_4748,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4668])).

cnf(c_4689,plain,
    ( sP5_iProver_split
    | sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4667])).

cnf(c_4751,plain,
    ( sP5_iProver_split = iProver_top
    | sP4_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4689])).

cnf(c_4752,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4688])).

cnf(c_4687,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_69)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_4667])).

cnf(c_5169,plain,
    ( k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4687])).

cnf(c_5484,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5169])).

cnf(c_5817,plain,
    ( m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5168,c_4748,c_4751,c_4752,c_5484])).

cnf(c_5818,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5817])).

cnf(c_5830,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5151,c_5818])).

cnf(c_5,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_665,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_1614,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_665,c_37])).

cnf(c_1615,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1614])).

cnf(c_1619,plain,
    ( m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_yellow_0(sK8,X0)
    | ~ r2_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1615,c_33])).

cnf(c_1620,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1619])).

cnf(c_4678,plain,
    ( ~ r2_lattice3(sK8,X0_70,X0_69)
    | r1_yellow_0(sK8,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0_70,X0_69),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1620])).

cnf(c_5152,plain,
    ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
    | r1_yellow_0(sK8,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK0(sK8,X0_70,X0_69),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4678])).

cnf(c_6623,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
    | r1_orders_2(sK8,X0_69,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5830,c_5152])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_711,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11,c_3])).

cnf(c_1566,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_711,c_37])).

cnf(c_1567,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1566])).

cnf(c_1571,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_yellow_0(sK8,X0)
    | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
    | ~ r2_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_33])).

cnf(c_1572,plain,
    ( ~ r2_lattice3(sK8,X0,X1)
    | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
    | r1_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1571])).

cnf(c_4680,plain,
    ( ~ r2_lattice3(sK8,X0_70,X0_69)
    | ~ r1_orders_2(sK8,X0_69,sK0(sK8,X0_70,X0_69))
    | r1_yellow_0(sK8,X0_70)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1572])).

cnf(c_5150,plain,
    ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
    | r1_orders_2(sK8,X0_69,sK0(sK8,X0_70,X0_69)) != iProver_top
    | r1_yellow_0(sK8,X0_70) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4680])).

cnf(c_6627,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_5150])).

cnf(c_27,negated_conjecture,
    ( v10_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_13,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_983,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK8,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_984,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK8)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_983])).

cnf(c_988,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v10_waybel_0(X0,sK8)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v7_waybel_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_984,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_989,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_988])).

cnf(c_1929,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_989])).

cnf(c_1930,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_1929])).

cnf(c_1934,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1930,c_31,c_30,c_29,c_28])).

cnf(c_1935,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(renaming,[status(thm)],[c_1934])).

cnf(c_4671,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1_69) ),
    inference(subtyping,[status(esa)],[c_1935])).

cnf(c_4685,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_4671])).

cnf(c_5162,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4685])).

cnf(c_14,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1483,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_39])).

cnf(c_1484,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1483])).

cnf(c_1488,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1484,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1489,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1488])).

cnf(c_1854,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1489])).

cnf(c_1855,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_1854])).

cnf(c_1859,plain,
    ( m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_31,c_30,c_29,c_28])).

cnf(c_1860,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1859])).

cnf(c_4674,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_1860])).

cnf(c_4726,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4674])).

cnf(c_4686,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4671])).

cnf(c_4739,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4686])).

cnf(c_4740,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4685])).

cnf(c_4684,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_69)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_4671])).

cnf(c_5163,plain,
    ( k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4684])).

cnf(c_5456,plain,
    ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5163])).

cnf(c_5761,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5162,c_4726,c_4739,c_4740,c_5456])).

cnf(c_5762,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5761])).

cnf(c_6678,plain,
    ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6627,c_5762])).

cnf(c_6687,plain,
    ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5165,c_6678])).

cnf(c_54,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_55,plain,
    ( v4_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_56,plain,
    ( v7_waybel_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2724,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1725])).

cnf(c_2725,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2724])).

cnf(c_2729,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2725,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2730,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2729])).

cnf(c_2813,plain,
    ( m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2730])).

cnf(c_2814,plain,
    ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2813])).

cnf(c_2815,plain,
    ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_6690,plain,
    ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6687,c_54,c_55,c_56,c_2815])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r1_waybel_9(X1,X0)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r1_waybel_9(sK8,sK9) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_466,plain,
    ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ l1_waybel_0(X0,X1)
    | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1)
    | sK9 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_467,plain,
    ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ l1_waybel_0(sK9,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_33,c_28,c_103])).

cnf(c_470,plain,
    ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_2353,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_470])).

cnf(c_2354,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2353])).

cnf(c_2580,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2354,c_1725])).

cnf(c_2581,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2580])).

cnf(c_2585,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2581,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2586,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2585])).

cnf(c_2881,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2586])).

cnf(c_2882,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2881])).

cnf(c_2884,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_31,c_30,c_29])).

cnf(c_2885,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2884])).

cnf(c_3834,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2885])).

cnf(c_4664,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_3834])).

cnf(c_5172,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4664])).

cnf(c_2826,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_3835,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3834])).

cnf(c_4696,plain,
    ( ~ m1_subset_1(X0_69,X0_71)
    | m1_subset_1(X1_69,X0_71)
    | X1_69 != X0_69 ),
    theory(equality)).

cnf(c_5436,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | X0_69 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4696])).

cnf(c_5477,plain,
    ( m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | k1_waybel_2(sK8,sK9) != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5436])).

cnf(c_5478,plain,
    ( k1_waybel_2(sK8,sK9) != sK4(sK8,sK9)
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5477])).

cnf(c_24,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1070,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2
    | k4_waybel_1(X0,sK7(X0)) != k4_waybel_1(sK8,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_1071,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | ~ v3_orders_2(sK8)
    | k1_waybel_2(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_1070])).

cnf(c_1075,plain,
    ( v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v10_waybel_0(X0,sK8)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v7_waybel_0(X0)
    | k1_waybel_2(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1071,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1076,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_1075])).

cnf(c_1902,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1076])).

cnf(c_1903,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k1_waybel_2(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_1902])).

cnf(c_1907,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | k1_waybel_2(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1903,c_31,c_30,c_29,c_28])).

cnf(c_1908,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_waybel_2(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(renaming,[status(thm)],[c_1907])).

cnf(c_4672,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1_69)
    | k1_waybel_2(sK8,sK9) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1908])).

cnf(c_4682,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | k1_waybel_2(sK8,sK9) = X0_69
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_4672])).

cnf(c_5159,plain,
    ( k1_waybel_2(sK8,sK9) = X0_69
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4682])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK7(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X0)
    | k1_waybel_2(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1444,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v10_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK7(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(X0,X1) = X2
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_1445,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_1449,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1450,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v10_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1449])).

cnf(c_1878,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_2(sK8,X0) = X1
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_1450])).

cnf(c_1879,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k1_waybel_2(sK8,sK9) = X0 ),
    inference(unflattening,[status(thm)],[c_1878])).

cnf(c_1883,plain,
    ( m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | k1_waybel_2(sK8,sK9) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1879,c_31,c_30,c_29,c_28])).

cnf(c_1884,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | k1_waybel_2(sK8,sK9) = X0 ),
    inference(renaming,[status(thm)],[c_1883])).

cnf(c_4673,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_69)
    | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | k1_waybel_2(sK8,sK9) = X0_69 ),
    inference(subtyping,[status(esa)],[c_1884])).

cnf(c_4729,plain,
    ( k1_waybel_2(sK8,sK9) = X0_69
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4673])).

cnf(c_4683,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4672])).

cnf(c_4732,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4683])).

cnf(c_4733,plain,
    ( k1_waybel_2(sK8,sK9) = X0_69
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4682])).

cnf(c_4681,plain,
    ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_69)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4672])).

cnf(c_5160,plain,
    ( k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_69)
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4681])).

cnf(c_5450,plain,
    ( m1_subset_1(sK7(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5160])).

cnf(c_5487,plain,
    ( m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | k1_waybel_2(sK8,sK9) = X0_69 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5159,c_4729,c_4732,c_4733,c_5450])).

cnf(c_5488,plain,
    ( k1_waybel_2(sK8,sK9) = X0_69
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5487])).

cnf(c_5496,plain,
    ( k1_waybel_2(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5165,c_5488])).

cnf(c_4698,plain,
    ( ~ r3_waybel_9(X0_68,X1_68,X0_69)
    | r3_waybel_9(X0_68,X1_68,X1_69)
    | X1_69 != X0_69 ),
    theory(equality)).

cnf(c_5463,plain,
    ( r3_waybel_9(sK8,sK9,X0_69)
    | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | X0_69 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4698])).

cnf(c_5500,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | k1_waybel_2(sK8,sK9) != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5463])).

cnf(c_5501,plain,
    ( k1_waybel_2(sK8,sK9) != sK4(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) = iProver_top
    | r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5500])).

cnf(c_6163,plain,
    ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5172,c_54,c_55,c_56,c_2815,c_2826,c_3835,c_5478,c_5496,c_5501])).

cnf(c_6164,plain,
    ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6163])).

cnf(c_6697,plain,
    ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6690,c_6164])).

cnf(c_5577,plain,
    ( k1_waybel_2(sK8,sK9) = sK4(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5496,c_54,c_55,c_56,c_2815])).

cnf(c_5580,plain,
    ( sK4(sK8,sK9) = X0_69
    | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
    | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5577,c_5488])).

cnf(c_6831,plain,
    ( sK5(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6697,c_5580])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2257,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_23,c_470])).

cnf(c_2258,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2257])).

cnf(c_2658,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2258,c_1725])).

cnf(c_2659,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2658])).

cnf(c_2663,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2664,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2663])).

cnf(c_2835,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2664])).

cnf(c_2836,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2835])).

cnf(c_2838,plain,
    ( m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2836,c_31,c_30,c_29])).

cnf(c_2839,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2838])).

cnf(c_3838,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2839])).

cnf(c_3839,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3838])).

cnf(c_6893,plain,
    ( sK5(sK8,sK9) = sK4(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6831,c_54,c_55,c_56,c_2815,c_2826,c_3839,c_5478,c_5496,c_5501,c_6687])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6(X0,X1) != sK5(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2449,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK8,sK9) != X2
    | sK6(X0,X1) != sK5(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_470])).

cnf(c_2450,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6(X0,X1) != sK5(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2449])).

cnf(c_2502,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6(X0,X1) != sK5(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2450,c_1725])).

cnf(c_2503,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2502])).

cnf(c_2507,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2503,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2508,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2507])).

cnf(c_2927,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2508])).

cnf(c_2928,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2927])).

cnf(c_2930,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2928,c_31,c_30,c_29])).

cnf(c_2931,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2930])).

cnf(c_3830,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | sK6(sK8,sK9) != sK5(sK8,sK9) ),
    inference(equality_resolution_simp,[status(thm)],[c_2931])).

cnf(c_4666,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | sK6(sK8,sK9) != sK5(sK8,sK9) ),
    inference(subtyping,[status(esa)],[c_3830])).

cnf(c_5170,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4666])).

cnf(c_4758,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4666])).

cnf(c_6079,plain,
    ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | sK6(sK8,sK9) != sK5(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5170,c_54,c_55,c_56,c_2815,c_2826,c_4758,c_5478,c_5496,c_5501])).

cnf(c_6080,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6079])).

cnf(c_6899,plain,
    ( sK6(sK8,sK9) != sK4(sK8,sK9)
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6893,c_6080])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2401,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_20,c_470])).

cnf(c_2402,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2401])).

cnf(c_2541,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2402,c_1725])).

cnf(c_2542,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2541])).

cnf(c_2546,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2542,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2547,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2546])).

cnf(c_2904,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2547])).

cnf(c_2905,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2904])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_31,c_30,c_29])).

cnf(c_2908,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2907])).

cnf(c_3832,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2908])).

cnf(c_4665,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_3832])).

cnf(c_5171,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4665])).

cnf(c_3833,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3832])).

cnf(c_6086,plain,
    ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5171,c_54,c_55,c_56,c_2815,c_2826,c_3833,c_5478,c_5496,c_5501])).

cnf(c_6087,plain,
    ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6086])).

cnf(c_6698,plain,
    ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6690,c_6087])).

cnf(c_6886,plain,
    ( sK6(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6698,c_5580])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2305,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_2(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_470])).

cnf(c_2306,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2305])).

cnf(c_2619,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2306,c_1725])).

cnf(c_2620,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2619])).

cnf(c_2624,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2620,c_41,c_40,c_36,c_34,c_33,c_103,c_130])).

cnf(c_2625,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2624])).

cnf(c_2858,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_2625])).

cnf(c_2859,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2858])).

cnf(c_2861,plain,
    ( m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_31,c_30,c_29])).

cnf(c_2862,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2861])).

cnf(c_3836,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
    | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2862])).

cnf(c_3837,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
    | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
    | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6899,c_6886,c_6687,c_5501,c_5496,c_5478,c_3837,c_2826,c_2815,c_56,c_55,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.60/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.00  
% 2.60/1.00  ------  iProver source info
% 2.60/1.00  
% 2.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.00  git: non_committed_changes: false
% 2.60/1.00  git: last_make_outside_of_git: false
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     num_symb
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       true
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  ------ Parsing...
% 2.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 17 0s  sf_e  pe_s  pe_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/1.00  ------ Proving...
% 2.60/1.00  ------ Problem Properties 
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  clauses                                 25
% 2.60/1.00  conjectures                             0
% 2.60/1.00  EPR                                     3
% 2.60/1.00  Horn                                    17
% 2.60/1.00  unary                                   2
% 2.60/1.00  binary                                  5
% 2.60/1.00  lits                                    85
% 2.60/1.00  lits eq                                 6
% 2.60/1.00  fd_pure                                 0
% 2.60/1.00  fd_pseudo                               0
% 2.60/1.00  fd_cond                                 2
% 2.60/1.00  fd_pseudo_cond                          0
% 2.60/1.00  AC symbols                              0
% 2.60/1.00  
% 2.60/1.00  ------ Schedule dynamic 5 is on 
% 2.60/1.00  
% 2.60/1.00  ------ no conjectures: strip conj schedule 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ 
% 2.60/1.00  Current options:
% 2.60/1.00  ------ 
% 2.60/1.00  
% 2.60/1.00  ------ Input Options
% 2.60/1.00  
% 2.60/1.00  --out_options                           all
% 2.60/1.00  --tptp_safe_out                         true
% 2.60/1.00  --problem_path                          ""
% 2.60/1.00  --include_path                          ""
% 2.60/1.00  --clausifier                            res/vclausify_rel
% 2.60/1.00  --clausifier_options                    --mode clausify
% 2.60/1.00  --stdin                                 false
% 2.60/1.00  --stats_out                             all
% 2.60/1.00  
% 2.60/1.00  ------ General Options
% 2.60/1.00  
% 2.60/1.00  --fof                                   false
% 2.60/1.00  --time_out_real                         305.
% 2.60/1.00  --time_out_virtual                      -1.
% 2.60/1.00  --symbol_type_check                     false
% 2.60/1.00  --clausify_out                          false
% 2.60/1.00  --sig_cnt_out                           false
% 2.60/1.00  --trig_cnt_out                          false
% 2.60/1.00  --trig_cnt_out_tolerance                1.
% 2.60/1.00  --trig_cnt_out_sk_spl                   false
% 2.60/1.00  --abstr_cl_out                          false
% 2.60/1.00  
% 2.60/1.00  ------ Global Options
% 2.60/1.00  
% 2.60/1.00  --schedule                              default
% 2.60/1.00  --add_important_lit                     false
% 2.60/1.00  --prop_solver_per_cl                    1000
% 2.60/1.00  --min_unsat_core                        false
% 2.60/1.00  --soft_assumptions                      false
% 2.60/1.00  --soft_lemma_size                       3
% 2.60/1.00  --prop_impl_unit_size                   0
% 2.60/1.00  --prop_impl_unit                        []
% 2.60/1.00  --share_sel_clauses                     true
% 2.60/1.00  --reset_solvers                         false
% 2.60/1.00  --bc_imp_inh                            [conj_cone]
% 2.60/1.00  --conj_cone_tolerance                   3.
% 2.60/1.00  --extra_neg_conj                        none
% 2.60/1.00  --large_theory_mode                     true
% 2.60/1.00  --prolific_symb_bound                   200
% 2.60/1.00  --lt_threshold                          2000
% 2.60/1.00  --clause_weak_htbl                      true
% 2.60/1.00  --gc_record_bc_elim                     false
% 2.60/1.00  
% 2.60/1.00  ------ Preprocessing Options
% 2.60/1.00  
% 2.60/1.00  --preprocessing_flag                    true
% 2.60/1.00  --time_out_prep_mult                    0.1
% 2.60/1.00  --splitting_mode                        input
% 2.60/1.00  --splitting_grd                         true
% 2.60/1.00  --splitting_cvd                         false
% 2.60/1.00  --splitting_cvd_svl                     false
% 2.60/1.00  --splitting_nvd                         32
% 2.60/1.00  --sub_typing                            true
% 2.60/1.00  --prep_gs_sim                           true
% 2.60/1.00  --prep_unflatten                        true
% 2.60/1.00  --prep_res_sim                          true
% 2.60/1.00  --prep_upred                            true
% 2.60/1.00  --prep_sem_filter                       exhaustive
% 2.60/1.00  --prep_sem_filter_out                   false
% 2.60/1.00  --pred_elim                             true
% 2.60/1.00  --res_sim_input                         true
% 2.60/1.00  --eq_ax_congr_red                       true
% 2.60/1.00  --pure_diseq_elim                       true
% 2.60/1.00  --brand_transform                       false
% 2.60/1.00  --non_eq_to_eq                          false
% 2.60/1.00  --prep_def_merge                        true
% 2.60/1.00  --prep_def_merge_prop_impl              false
% 2.60/1.00  --prep_def_merge_mbd                    true
% 2.60/1.00  --prep_def_merge_tr_red                 false
% 2.60/1.00  --prep_def_merge_tr_cl                  false
% 2.60/1.00  --smt_preprocessing                     true
% 2.60/1.00  --smt_ac_axioms                         fast
% 2.60/1.00  --preprocessed_out                      false
% 2.60/1.00  --preprocessed_stats                    false
% 2.60/1.00  
% 2.60/1.00  ------ Abstraction refinement Options
% 2.60/1.00  
% 2.60/1.00  --abstr_ref                             []
% 2.60/1.00  --abstr_ref_prep                        false
% 2.60/1.00  --abstr_ref_until_sat                   false
% 2.60/1.00  --abstr_ref_sig_restrict                funpre
% 2.60/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.00  --abstr_ref_under                       []
% 2.60/1.00  
% 2.60/1.00  ------ SAT Options
% 2.60/1.00  
% 2.60/1.00  --sat_mode                              false
% 2.60/1.00  --sat_fm_restart_options                ""
% 2.60/1.00  --sat_gr_def                            false
% 2.60/1.00  --sat_epr_types                         true
% 2.60/1.00  --sat_non_cyclic_types                  false
% 2.60/1.00  --sat_finite_models                     false
% 2.60/1.00  --sat_fm_lemmas                         false
% 2.60/1.00  --sat_fm_prep                           false
% 2.60/1.00  --sat_fm_uc_incr                        true
% 2.60/1.00  --sat_out_model                         small
% 2.60/1.00  --sat_out_clauses                       false
% 2.60/1.00  
% 2.60/1.00  ------ QBF Options
% 2.60/1.00  
% 2.60/1.00  --qbf_mode                              false
% 2.60/1.00  --qbf_elim_univ                         false
% 2.60/1.00  --qbf_dom_inst                          none
% 2.60/1.00  --qbf_dom_pre_inst                      false
% 2.60/1.00  --qbf_sk_in                             false
% 2.60/1.00  --qbf_pred_elim                         true
% 2.60/1.00  --qbf_split                             512
% 2.60/1.00  
% 2.60/1.00  ------ BMC1 Options
% 2.60/1.00  
% 2.60/1.00  --bmc1_incremental                      false
% 2.60/1.00  --bmc1_axioms                           reachable_all
% 2.60/1.00  --bmc1_min_bound                        0
% 2.60/1.00  --bmc1_max_bound                        -1
% 2.60/1.00  --bmc1_max_bound_default                -1
% 2.60/1.00  --bmc1_symbol_reachability              true
% 2.60/1.00  --bmc1_property_lemmas                  false
% 2.60/1.00  --bmc1_k_induction                      false
% 2.60/1.00  --bmc1_non_equiv_states                 false
% 2.60/1.00  --bmc1_deadlock                         false
% 2.60/1.00  --bmc1_ucm                              false
% 2.60/1.00  --bmc1_add_unsat_core                   none
% 2.60/1.00  --bmc1_unsat_core_children              false
% 2.60/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.00  --bmc1_out_stat                         full
% 2.60/1.00  --bmc1_ground_init                      false
% 2.60/1.00  --bmc1_pre_inst_next_state              false
% 2.60/1.00  --bmc1_pre_inst_state                   false
% 2.60/1.00  --bmc1_pre_inst_reach_state             false
% 2.60/1.00  --bmc1_out_unsat_core                   false
% 2.60/1.00  --bmc1_aig_witness_out                  false
% 2.60/1.00  --bmc1_verbose                          false
% 2.60/1.00  --bmc1_dump_clauses_tptp                false
% 2.60/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.00  --bmc1_dump_file                        -
% 2.60/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.00  --bmc1_ucm_extend_mode                  1
% 2.60/1.00  --bmc1_ucm_init_mode                    2
% 2.60/1.00  --bmc1_ucm_cone_mode                    none
% 2.60/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.00  --bmc1_ucm_relax_model                  4
% 2.60/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.00  --bmc1_ucm_layered_model                none
% 2.60/1.00  --bmc1_ucm_max_lemma_size               10
% 2.60/1.00  
% 2.60/1.00  ------ AIG Options
% 2.60/1.00  
% 2.60/1.00  --aig_mode                              false
% 2.60/1.00  
% 2.60/1.00  ------ Instantiation Options
% 2.60/1.00  
% 2.60/1.00  --instantiation_flag                    true
% 2.60/1.00  --inst_sos_flag                         false
% 2.60/1.00  --inst_sos_phase                        true
% 2.60/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.00  --inst_lit_sel_side                     none
% 2.60/1.00  --inst_solver_per_active                1400
% 2.60/1.00  --inst_solver_calls_frac                1.
% 2.60/1.00  --inst_passive_queue_type               priority_queues
% 2.60/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.60/1.00  --inst_passive_queues_freq              [25;2]
% 2.60/1.00  --inst_dismatching                      true
% 2.60/1.00  --inst_eager_unprocessed_to_passive     true
% 2.60/1.00  --inst_prop_sim_given                   true
% 2.60/1.00  --inst_prop_sim_new                     false
% 2.60/1.00  --inst_subs_new                         false
% 2.60/1.00  --inst_eq_res_simp                      false
% 2.60/1.00  --inst_subs_given                       false
% 2.60/1.00  --inst_orphan_elimination               true
% 2.60/1.00  --inst_learning_loop_flag               true
% 2.60/1.00  --inst_learning_start                   3000
% 2.60/1.00  --inst_learning_factor                  2
% 2.60/1.00  --inst_start_prop_sim_after_learn       3
% 2.60/1.00  --inst_sel_renew                        solver
% 2.60/1.00  --inst_lit_activity_flag                true
% 2.60/1.00  --inst_restr_to_given                   false
% 2.60/1.00  --inst_activity_threshold               500
% 2.60/1.00  --inst_out_proof                        true
% 2.60/1.00  
% 2.60/1.00  ------ Resolution Options
% 2.60/1.00  
% 2.60/1.00  --resolution_flag                       false
% 2.60/1.00  --res_lit_sel                           adaptive
% 2.60/1.00  --res_lit_sel_side                      none
% 2.60/1.00  --res_ordering                          kbo
% 2.60/1.00  --res_to_prop_solver                    active
% 2.60/1.00  --res_prop_simpl_new                    false
% 2.60/1.00  --res_prop_simpl_given                  true
% 2.60/1.00  --res_passive_queue_type                priority_queues
% 2.60/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.60/1.00  --res_passive_queues_freq               [15;5]
% 2.60/1.00  --res_forward_subs                      full
% 2.60/1.00  --res_backward_subs                     full
% 2.60/1.00  --res_forward_subs_resolution           true
% 2.60/1.00  --res_backward_subs_resolution          true
% 2.60/1.00  --res_orphan_elimination                true
% 2.60/1.00  --res_time_limit                        2.
% 2.60/1.00  --res_out_proof                         true
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Options
% 2.60/1.00  
% 2.60/1.00  --superposition_flag                    true
% 2.60/1.00  --sup_passive_queue_type                priority_queues
% 2.60/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.00  --demod_completeness_check              fast
% 2.60/1.00  --demod_use_ground                      true
% 2.60/1.00  --sup_to_prop_solver                    passive
% 2.60/1.00  --sup_prop_simpl_new                    true
% 2.60/1.00  --sup_prop_simpl_given                  true
% 2.60/1.00  --sup_fun_splitting                     false
% 2.60/1.00  --sup_smt_interval                      50000
% 2.60/1.00  
% 2.60/1.00  ------ Superposition Simplification Setup
% 2.60/1.00  
% 2.60/1.00  --sup_indices_passive                   []
% 2.60/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_full_bw                           [BwDemod]
% 2.60/1.00  --sup_immed_triv                        [TrivRules]
% 2.60/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_immed_bw_main                     []
% 2.60/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.00  
% 2.60/1.00  ------ Combination Options
% 2.60/1.00  
% 2.60/1.00  --comb_res_mult                         3
% 2.60/1.00  --comb_sup_mult                         2
% 2.60/1.00  --comb_inst_mult                        10
% 2.60/1.00  
% 2.60/1.00  ------ Debug Options
% 2.60/1.00  
% 2.60/1.00  --dbg_backtrace                         false
% 2.60/1.00  --dbg_dump_prop_clauses                 false
% 2.60/1.00  --dbg_dump_prop_clauses_file            -
% 2.60/1.00  --dbg_out_stat                          false
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  ------ Proving...
% 2.60/1.00  
% 2.60/1.00  
% 2.60/1.00  % SZS status Theorem for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.00  
% 2.60/1.00  fof(f11,conjecture,(
% 2.60/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f12,negated_conjecture,(
% 2.60/1.00    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v10_waybel_0(X1,X0) => (r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) & r1_waybel_9(X0,X1))))))),
% 2.60/1.00    inference(negated_conjecture,[],[f11])).
% 2.60/1.00  
% 2.60/1.00  fof(f15,plain,(
% 2.60/1.00    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v10_waybel_0(X2,X0) => (r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) & r1_waybel_9(X0,X2))))))),
% 2.60/1.00    inference(rectify,[],[f12])).
% 2.60/1.00  
% 2.60/1.00  fof(f34,plain,(
% 2.60/1.00    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f15])).
% 2.60/1.00  
% 2.60/1.00  fof(f35,plain,(
% 2.60/1.00    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_2(X0,X2),k10_yellow_6(X0,X2)) | ~r1_waybel_9(X0,X2)) & v10_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.60/1.00    inference(flattening,[],[f34])).
% 2.60/1.00  
% 2.60/1.00  fof(f56,plain,(
% 2.60/1.00    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.60/1.00    inference(rectify,[],[f35])).
% 2.60/1.00  
% 2.60/1.00  fof(f58,plain,(
% 2.60/1.00    ( ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_2(X0,sK9),k10_yellow_6(X0,sK9)) | ~r1_waybel_9(X0,sK9)) & v10_waybel_0(sK9,X0) & l1_waybel_0(sK9,X0) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9))) )),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f57,plain,(
% 2.60/1.00    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_2(X0,X1),k10_yellow_6(X0,X1)) | ~r1_waybel_9(X0,X1)) & v10_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_2(sK8,X1),k10_yellow_6(sK8,X1)) | ~r1_waybel_9(sK8,X1)) & v10_waybel_0(X1,sK8) & l1_waybel_0(X1,sK8) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) & l1_waybel_9(sK8) & v1_compts_1(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v4_orders_2(sK8) & v3_orders_2(sK8) & v8_pre_topc(sK8) & v2_pre_topc(sK8))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f59,plain,(
% 2.60/1.00    ((~r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9)) | ~r1_waybel_9(sK8,sK9)) & v10_waybel_0(sK9,sK8) & l1_waybel_0(sK9,sK8) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) & l1_waybel_9(sK8) & v1_compts_1(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v4_orders_2(sK8) & v3_orders_2(sK8) & v8_pre_topc(sK8) & v2_pre_topc(sK8)),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f56,f58,f57])).
% 2.60/1.00  
% 2.60/1.00  fof(f99,plain,(
% 2.60/1.00    l1_waybel_0(sK9,sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f8,axiom,(
% 2.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f28,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f8])).
% 2.60/1.00  
% 2.60/1.00  fof(f29,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(flattening,[],[f28])).
% 2.60/1.00  
% 2.60/1.00  fof(f48,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f49,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f48])).
% 2.60/1.00  
% 2.60/1.00  fof(f78,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f49])).
% 2.60/1.00  
% 2.60/1.00  fof(f5,axiom,(
% 2.60/1.00    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f23,plain,(
% 2.60/1.00    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f5])).
% 2.60/1.00  
% 2.60/1.00  fof(f71,plain,(
% 2.60/1.00    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f94,plain,(
% 2.60/1.00    l1_waybel_9(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f86,plain,(
% 2.60/1.00    v2_pre_topc(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f87,plain,(
% 2.60/1.00    v8_pre_topc(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f91,plain,(
% 2.60/1.00    v1_lattice3(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f93,plain,(
% 2.60/1.00    v1_compts_1(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f72,plain,(
% 2.60/1.00    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f23])).
% 2.60/1.00  
% 2.60/1.00  fof(f2,axiom,(
% 2.60/1.00    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f18,plain,(
% 2.60/1.00    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f2])).
% 2.60/1.00  
% 2.60/1.00  fof(f19,plain,(
% 2.60/1.00    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.60/1.00    inference(flattening,[],[f18])).
% 2.60/1.00  
% 2.60/1.00  fof(f62,plain,(
% 2.60/1.00    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f19])).
% 2.60/1.00  
% 2.60/1.00  fof(f96,plain,(
% 2.60/1.00    ~v2_struct_0(sK9)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f97,plain,(
% 2.60/1.00    v4_orders_2(sK9)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f98,plain,(
% 2.60/1.00    v7_waybel_0(sK9)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f3,axiom,(
% 2.60/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f20,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f3])).
% 2.60/1.00  
% 2.60/1.00  fof(f21,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (r1_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.60/1.00    inference(flattening,[],[f20])).
% 2.60/1.00  
% 2.60/1.00  fof(f37,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.60/1.00    inference(nnf_transformation,[],[f21])).
% 2.60/1.00  
% 2.60/1.00  fof(f38,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.60/1.00    inference(rectify,[],[f37])).
% 2.60/1.00  
% 2.60/1.00  fof(f40,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X4,X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,sK1(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f39,plain,(
% 2.60/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f41,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r1_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,sK1(X0,X1),X5) | ~r2_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r2_lattice3(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~r1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 2.60/1.00  
% 2.60/1.00  fof(f67,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f90,plain,(
% 2.60/1.00    v5_orders_2(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f1,axiom,(
% 2.60/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f16,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f1])).
% 2.60/1.00  
% 2.60/1.00  fof(f17,plain,(
% 2.60/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(flattening,[],[f16])).
% 2.60/1.00  
% 2.60/1.00  fof(f36,plain,(
% 2.60/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(nnf_transformation,[],[f17])).
% 2.60/1.00  
% 2.60/1.00  fof(f60,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f36])).
% 2.60/1.00  
% 2.60/1.00  fof(f7,axiom,(
% 2.60/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r3_orders_2(X0,X3,X4))))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f13,plain,(
% 2.60/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r3_orders_2(X0,X3,X5))))))))),
% 2.60/1.00    inference(rectify,[],[f7])).
% 2.60/1.00  
% 2.60/1.00  fof(f26,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f13])).
% 2.60/1.00  
% 2.60/1.00  fof(f27,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r3_orders_2(X0,X3,X5) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(flattening,[],[f26])).
% 2.60/1.00  
% 2.60/1.00  fof(f45,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(rectify,[],[f27])).
% 2.60/1.00  
% 2.60/1.00  fof(f46,plain,(
% 2.60/1.00    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f47,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 2.60/1.00  
% 2.60/1.00  fof(f76,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f47])).
% 2.60/1.00  
% 2.60/1.00  fof(f104,plain,(
% 2.60/1.00    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f76])).
% 2.60/1.00  
% 2.60/1.00  fof(f95,plain,(
% 2.60/1.00    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) )),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f88,plain,(
% 2.60/1.00    v3_orders_2(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f89,plain,(
% 2.60/1.00    v4_orders_2(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f92,plain,(
% 2.60/1.00    v2_lattice3(sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f75,plain,(
% 2.60/1.00    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f47])).
% 2.60/1.00  
% 2.60/1.00  fof(f105,plain,(
% 2.60/1.00    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,X3,X4) | ~r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f75])).
% 2.60/1.00  
% 2.60/1.00  fof(f66,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f68,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r1_yellow_0(X0,X1) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f41])).
% 2.60/1.00  
% 2.60/1.00  fof(f100,plain,(
% 2.60/1.00    v10_waybel_0(sK9,sK8)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f6,axiom,(
% 2.60/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v10_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f24,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f6])).
% 2.60/1.00  
% 2.60/1.00  fof(f25,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(flattening,[],[f24])).
% 2.60/1.00  
% 2.60/1.00  fof(f43,plain,(
% 2.60/1.00    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f44,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f43])).
% 2.60/1.00  
% 2.60/1.00  fof(f74,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f44])).
% 2.60/1.00  
% 2.60/1.00  fof(f102,plain,(
% 2.60/1.00    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f74])).
% 2.60/1.00  
% 2.60/1.00  fof(f73,plain,(
% 2.60/1.00    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f44])).
% 2.60/1.00  
% 2.60/1.00  fof(f103,plain,(
% 2.60/1.00    ( ! [X0,X3,X1] : (r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v10_waybel_0(X1,X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(equality_resolution,[],[f73])).
% 2.60/1.00  
% 2.60/1.00  fof(f77,plain,(
% 2.60/1.00    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f49])).
% 2.60/1.00  
% 2.60/1.00  fof(f9,axiom,(
% 2.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f14,plain,(
% 2.60/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 2.60/1.00    inference(rectify,[],[f9])).
% 2.60/1.00  
% 2.60/1.00  fof(f30,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f14])).
% 2.60/1.00  
% 2.60/1.00  fof(f31,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(flattening,[],[f30])).
% 2.60/1.00  
% 2.60/1.00  fof(f50,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(rectify,[],[f31])).
% 2.60/1.00  
% 2.60/1.00  fof(f52,plain,(
% 2.60/1.00    ( ! [X3] : (! [X1,X0] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sK6(X0,X1) != X3 & r3_waybel_9(X0,X1,sK6(X0,X1)) & r3_waybel_9(X0,X1,X3) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))) )),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f51,plain,(
% 2.60/1.00    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK5(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f53,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK5(X0,X1) != sK6(X0,X1) & r3_waybel_9(X0,X1,sK6(X0,X1)) & r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f50,f52,f51])).
% 2.60/1.00  
% 2.60/1.00  fof(f81,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK5(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f4,axiom,(
% 2.60/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f22,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : ((r1_waybel_9(X0,X1) <=> r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.60/1.00    inference(ennf_transformation,[],[f4])).
% 2.60/1.00  
% 2.60/1.00  fof(f42,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (((r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.60/1.00    inference(nnf_transformation,[],[f22])).
% 2.60/1.00  
% 2.60/1.00  fof(f70,plain,(
% 2.60/1.00    ( ! [X0,X1] : (r1_waybel_9(X0,X1) | ~r1_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f42])).
% 2.60/1.00  
% 2.60/1.00  fof(f101,plain,(
% 2.60/1.00    ~r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9)) | ~r1_waybel_9(sK8,sK9)),
% 2.60/1.00    inference(cnf_transformation,[],[f59])).
% 2.60/1.00  
% 2.60/1.00  fof(f10,axiom,(
% 2.60/1.00    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v10_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_2(X0,X2) = X1))))),
% 2.60/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.60/1.00  
% 2.60/1.00  fof(f32,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_2(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.60/1.00    inference(ennf_transformation,[],[f10])).
% 2.60/1.00  
% 2.60/1.00  fof(f33,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(flattening,[],[f32])).
% 2.60/1.00  
% 2.60/1.00  fof(f54,plain,(
% 2.60/1.00    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 2.60/1.00    introduced(choice_axiom,[])).
% 2.60/1.00  
% 2.60/1.00  fof(f55,plain,(
% 2.60/1.00    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f54])).
% 2.60/1.00  
% 2.60/1.00  fof(f85,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f55])).
% 2.60/1.00  
% 2.60/1.00  fof(f84,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (k1_waybel_2(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v10_waybel_0(X2,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f55])).
% 2.60/1.00  
% 2.60/1.00  fof(f79,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f83,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK5(X0,X1) != sK6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f82,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  fof(f80,plain,(
% 2.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.60/1.00    inference(cnf_transformation,[],[f53])).
% 2.60/1.00  
% 2.60/1.00  cnf(c_28,negated_conjecture,
% 2.60/1.00      ( l1_waybel_0(sK9,sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_17,plain,
% 2.60/1.00      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_pre_topc(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_12,plain,
% 2.60/1.00      ( l1_pre_topc(X0) | ~ l1_waybel_9(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_33,negated_conjecture,
% 2.60/1.00      ( l1_waybel_9(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1724,plain,
% 2.60/1.00      ( l1_pre_topc(X0) | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1725,plain,
% 2.60/1.00      ( l1_pre_topc(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1724]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2697,plain,
% 2.60/1.00      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_1725]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2698,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2697]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_41,negated_conjecture,
% 2.60/1.00      ( v2_pre_topc(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_40,negated_conjecture,
% 2.60/1.00      ( v8_pre_topc(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_36,negated_conjecture,
% 2.60/1.00      ( v1_lattice3(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_34,negated_conjecture,
% 2.60/1.00      ( v1_compts_1(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_11,plain,
% 2.60/1.00      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_103,plain,
% 2.60/1.00      ( ~ l1_waybel_9(sK8) | l1_orders_2(sK8) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2,plain,
% 2.60/1.00      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_130,plain,
% 2.60/1.00      ( ~ v1_lattice3(sK8) | ~ v2_struct_0(sK8) | ~ l1_orders_2(sK8) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2702,plain,
% 2.60/1.00      ( v2_struct_0(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2698,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2703,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2702]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2824,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_2703]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2825,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2824]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_31,negated_conjecture,
% 2.60/1.00      ( ~ v2_struct_0(sK9) ),
% 2.60/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_30,negated_conjecture,
% 2.60/1.00      ( v4_orders_2(sK9) ),
% 2.60/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_29,negated_conjecture,
% 2.60/1.00      ( v7_waybel_0(sK9) ),
% 2.60/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2827,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2825,c_31,c_30,c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4669,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_2827]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5165,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4669]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_688,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_11,c_4]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_37,negated_conjecture,
% 2.60/1.00      ( v5_orders_2(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1590,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_688,c_37]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1591,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_9(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1590]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1595,plain,
% 2.60/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.60/1.00      | ~ r2_lattice3(sK8,X0,X1) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1591,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1596,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1595]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4679,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0_70,X0_69)
% 2.60/1.00      | r2_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_69))
% 2.60/1.00      | r1_yellow_0(sK8,X0_70)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1596]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5151,plain,
% 2.60/1.00      ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_69)) = iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,X0_70) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4679]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1,plain,
% 2.60/1.00      ( r1_orders_2(X0,X1,X2)
% 2.60/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | ~ l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_748,plain,
% 2.60/1.00      ( r1_orders_2(X0,X1,X2)
% 2.60/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_11,c_1]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_15,plain,
% 2.60/1.00      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
% 2.60/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r3_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_32,negated_conjecture,
% 2.60/1.00      ( v5_pre_topc(k4_waybel_1(sK8,X0),sK8,sK8)
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 2.60/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1025,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r3_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | k4_waybel_1(X0,sK3(X0)) != k4_waybel_1(sK8,X4)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1026,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r3_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v2_lattice3(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(sK8)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(sK8)
% 2.60/1.00      | ~ v5_orders_2(sK8)
% 2.60/1.00      | ~ v1_lattice3(sK8)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(sK8)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1025]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_39,negated_conjecture,
% 2.60/1.00      ( v3_orders_2(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_38,negated_conjecture,
% 2.60/1.00      ( v4_orders_2(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_35,negated_conjecture,
% 2.60/1.00      ( v2_lattice3(sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1030,plain,
% 2.60/1.00      ( v2_struct_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | r3_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1026,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1031,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r3_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1030]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1203,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(X3,X4,X5)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X5,u1_struct_0(X3))
% 2.60/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X6,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(X3)
% 2.60/1.00      | v2_struct_0(X3)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(X3)
% 2.60/1.00      | X1 != X4
% 2.60/1.00      | X2 != X5
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X6)
% 2.60/1.00      | sK8 != X3 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_748,c_1031]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1204,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(sK8)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(sK8)
% 2.60/1.00      | ~ v3_orders_2(sK8)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1203]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1208,plain,
% 2.60/1.00      ( ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1204,c_39,c_36,c_33,c_103,c_130]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1209,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1208]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2980,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_1209]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2981,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2980]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2985,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2981,c_31,c_30,c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2986,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2985]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4667,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69)
% 2.60/1.00      | ~ m1_subset_1(X2_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2_69) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_2986]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4688,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ sP5_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 2.60/1.00                [c_4667]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5168,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP5_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4688]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_16,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r3_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1136,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r1_orders_2(X4,X5,X6)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X6,u1_struct_0(X4))
% 2.60/1.00      | ~ m1_subset_1(X5,u1_struct_0(X4))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X4)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X4)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X4)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | X0 != X4
% 2.60/1.00      | X2 != X5
% 2.60/1.00      | X3 != X6 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_748,c_16]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1137,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r1_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1136]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_734,plain,
% 2.60/1.00      ( ~ l1_waybel_9(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_11,c_2]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1141,plain,
% 2.60/1.00      ( v2_struct_0(X1)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | r1_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1137,c_734]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1142,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r1_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1141]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1402,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.60/1.00      | r1_orders_2(X0,X2,X3)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_1142,c_39]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1403,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v2_lattice3(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(sK8)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(sK8)
% 2.60/1.00      | ~ v5_orders_2(sK8)
% 2.60/1.00      | ~ v1_lattice3(sK8)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1402]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1407,plain,
% 2.60/1.00      ( ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1403,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1408,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1407]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2950,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.60/1.00      | r1_orders_2(sK8,X1,X2)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_1408]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2951,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2950]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2955,plain,
% 2.60/1.00      ( m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | ~ r3_waybel_9(sK8,sK9,X0) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2951,c_31,c_30,c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2956,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.60/1.00      | r1_orders_2(sK8,X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2955]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4668,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | ~ r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_2956]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4748,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4668]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4689,plain,
% 2.60/1.00      ( sP5_iProver_split | sP4_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[])],
% 2.60/1.00                [c_4667]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4751,plain,
% 2.60/1.00      ( sP5_iProver_split = iProver_top
% 2.60/1.00      | sP4_iProver_split = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4689]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4752,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP5_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4688]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4687,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.00      | ~ sP4_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 2.60/1.00                [c_4667]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5169,plain,
% 2.60/1.00      ( k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP4_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4687]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5484,plain,
% 2.60/1.00      ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP4_iProver_split != iProver_top ),
% 2.60/1.00      inference(equality_resolution,[status(thm)],[c_5169]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5817,plain,
% 2.60/1.00      ( m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_5168,c_4748,c_4751,c_4752,c_5484]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5818,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,X1_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_5817]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5830,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)) = iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_5151,c_5818]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_665,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1614,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_665,c_37]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1615,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_9(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1614]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1619,plain,
% 2.60/1.00      ( m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ r2_lattice3(sK8,X0,X1) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1615,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1620,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1619]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4678,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0_70,X0_69)
% 2.60/1.00      | r1_yellow_0(sK8,X0_70)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK0(sK8,X0_70,X0_69),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1620]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5152,plain,
% 2.60/1.00      ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,X0_70) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(sK0(sK8,X0_70,X0_69),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4678]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6623,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_69)) = iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(X1_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(forward_subsumption_resolution,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_5830,c_5152]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ l1_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_711,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0) ),
% 2.60/1.00      inference(resolution,[status(thm)],[c_11,c_3]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1566,plain,
% 2.60/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 2.60/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 2.60/1.00      | r1_yellow_0(X0,X1)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_711,c_37]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1567,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_9(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1566]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1571,plain,
% 2.60/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
% 2.60/1.00      | ~ r2_lattice3(sK8,X0,X1) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1567,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1572,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0,X1)
% 2.60/1.00      | ~ r1_orders_2(sK8,X1,sK0(sK8,X0,X1))
% 2.60/1.00      | r1_yellow_0(sK8,X0)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1571]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4680,plain,
% 2.60/1.00      ( ~ r2_lattice3(sK8,X0_70,X0_69)
% 2.60/1.00      | ~ r1_orders_2(sK8,X0_69,sK0(sK8,X0_70,X0_69))
% 2.60/1.00      | r1_yellow_0(sK8,X0_70)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1572]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5150,plain,
% 2.60/1.00      ( r2_lattice3(sK8,X0_70,X0_69) != iProver_top
% 2.60/1.00      | r1_orders_2(sK8,X0_69,sK0(sK8,X0_70,X0_69)) != iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,X0_70) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4680]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6627,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) != iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_6623,c_5150]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_27,negated_conjecture,
% 2.60/1.00      ( v10_waybel_0(sK9,sK8) ),
% 2.60/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_13,plain,
% 2.60/1.00      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 2.60/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_983,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK8,X3)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_984,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v2_lattice3(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(sK8)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(sK8)
% 2.60/1.00      | ~ v5_orders_2(sK8)
% 2.60/1.00      | ~ v1_lattice3(sK8)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | ~ v3_orders_2(sK8)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_983]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_988,plain,
% 2.60/1.00      ( v2_struct_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_984,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_989,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_988]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1929,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_989]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1930,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.60/1.00      | ~ l1_waybel_0(sK9,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1929]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1934,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1930,c_31,c_30,c_29,c_28]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1935,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1934]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4671,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1_69) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1935]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4685,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ sP3_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.60/1.00                [c_4671]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5162,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP3_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4685]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_14,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1483,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r2_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_39]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1484,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v2_lattice3(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(sK8)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_waybel_9(sK8)
% 2.60/1.00      | ~ v5_orders_2(sK8)
% 2.60/1.00      | ~ v1_lattice3(sK8)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1483]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1488,plain,
% 2.60/1.00      ( ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1484,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1489,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1488]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1854,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_1489]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1855,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.60/1.00      | ~ l1_waybel_0(sK9,sK8)
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_1854]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1859,plain,
% 2.60/1.00      ( m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_1855,c_31,c_30,c_29,c_28]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1860,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.60/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_1859]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4674,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69)
% 2.60/1.00      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_1860]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4726,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4674]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4686,plain,
% 2.60/1.00      ( sP3_iProver_split | sP2_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[])],
% 2.60/1.00                [c_4671]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4739,plain,
% 2.60/1.00      ( sP3_iProver_split = iProver_top
% 2.60/1.00      | sP2_iProver_split = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4686]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4740,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP3_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4685]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4684,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.00      | ~ sP2_iProver_split ),
% 2.60/1.00      inference(splitting,
% 2.60/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.60/1.00                [c_4671]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5163,plain,
% 2.60/1.00      ( k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP2_iProver_split != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4684]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5456,plain,
% 2.60/1.00      ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | sP2_iProver_split != iProver_top ),
% 2.60/1.00      inference(equality_resolution,[status(thm)],[c_5163]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5761,plain,
% 2.60/1.00      ( m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
% 2.60/1.00      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_5162,c_4726,c_4739,c_4740,c_5456]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5762,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r2_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_69) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_5761]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6678,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
% 2.60/1.00      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_6627,c_5762]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6687,plain,
% 2.60/1.00      ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top
% 2.60/1.00      | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(superposition,[status(thm)],[c_5165,c_6678]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_54,plain,
% 2.60/1.00      ( v2_struct_0(sK9) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_55,plain,
% 2.60/1.00      ( v4_orders_2(sK9) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_56,plain,
% 2.60/1.00      ( v7_waybel_0(sK9) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_18,plain,
% 2.60/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.60/1.00      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 2.60/1.00      | ~ v2_pre_topc(X1)
% 2.60/1.00      | ~ v8_pre_topc(X1)
% 2.60/1.00      | ~ v1_compts_1(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ l1_pre_topc(X1)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2724,plain,
% 2.60/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.60/1.00      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 2.60/1.00      | ~ v2_pre_topc(X1)
% 2.60/1.00      | ~ v8_pre_topc(X1)
% 2.60/1.00      | ~ v1_compts_1(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | sK8 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_1725]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2725,plain,
% 2.60/1.00      ( ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2724]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2729,plain,
% 2.60/1.00      ( v2_struct_0(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2725,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2730,plain,
% 2.60/1.00      ( ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2729]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2813,plain,
% 2.60/1.00      ( m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_2730]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2814,plain,
% 2.60/1.00      ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2813]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2815,plain,
% 2.60/1.00      ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.60/1.00      | v4_orders_2(sK9) != iProver_top
% 2.60/1.00      | v7_waybel_0(sK9) != iProver_top
% 2.60/1.00      | v2_struct_0(sK9) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_6690,plain,
% 2.60/1.00      ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_6687,c_54,c_55,c_56,c_2815]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_21,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.60/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_pre_topc(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_9,plain,
% 2.60/1.00      ( ~ l1_waybel_0(X0,X1)
% 2.60/1.00      | r1_waybel_9(X1,X0)
% 2.60/1.00      | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.60/1.00      | ~ l1_orders_2(X1) ),
% 2.60/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_26,negated_conjecture,
% 2.60/1.00      ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.60/1.00      | ~ r1_waybel_9(sK8,sK9) ),
% 2.60/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_466,plain,
% 2.60/1.00      ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.60/1.00      | ~ l1_waybel_0(X0,X1)
% 2.60/1.00      | ~ r1_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.60/1.00      | ~ l1_orders_2(X1)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != X1 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_467,plain,
% 2.60/1.00      ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.60/1.00      | ~ l1_waybel_0(sK9,sK8)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ l1_orders_2(sK8) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_466]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_469,plain,
% 2.60/1.00      ( ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9)) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_467,c_33,c_28,c_103]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_470,plain,
% 2.60/1.00      ( ~ r2_hidden(k1_waybel_2(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_469]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2353,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_pre_topc(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | k1_waybel_2(sK8,sK9) != X2
% 2.60/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_470]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2354,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_pre_topc(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2353]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2580,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_2354,c_1725]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2581,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(sK8)
% 2.60/1.00      | ~ v8_pre_topc(sK8)
% 2.60/1.00      | ~ v1_compts_1(sK8)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | v2_struct_0(sK8)
% 2.60/1.00      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2580]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2585,plain,
% 2.60/1.00      ( v2_struct_0(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2581,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2586,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2585]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2881,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X0)
% 2.60/1.00      | v2_struct_0(X0)
% 2.60/1.00      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.60/1.00      | sK9 != X0
% 2.60/1.00      | sK8 != sK8 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_2586]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2882,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ v4_orders_2(sK9)
% 2.60/1.00      | ~ v7_waybel_0(sK9)
% 2.60/1.00      | v2_struct_0(sK9)
% 2.60/1.00      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(unflattening,[status(thm)],[c_2881]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2884,plain,
% 2.60/1.00      ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.60/1.00      | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(global_propositional_subsumption,
% 2.60/1.00                [status(thm)],
% 2.60/1.00                [c_2882,c_31,c_30,c_29]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2885,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.00      inference(renaming,[status(thm)],[c_2884]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3834,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(equality_resolution_simp,[status(thm)],[c_2885]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4664,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.60/1.00      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.00      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.00      inference(subtyping,[status(esa)],[c_3834]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5172,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.00      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_4664]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_2826,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top
% 2.60/1.00      | v4_orders_2(sK9) != iProver_top
% 2.60/1.00      | v7_waybel_0(sK9) != iProver_top
% 2.60/1.00      | v2_struct_0(sK9) = iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_3835,plain,
% 2.60/1.00      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.00      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.60/1.00      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.00      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_3834]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_4696,plain,
% 2.60/1.00      ( ~ m1_subset_1(X0_69,X0_71)
% 2.60/1.00      | m1_subset_1(X1_69,X0_71)
% 2.60/1.00      | X1_69 != X0_69 ),
% 2.60/1.00      theory(equality) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5436,plain,
% 2.60/1.00      ( m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | X0_69 != sK4(sK8,sK9) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_4696]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5477,plain,
% 2.60/1.00      ( m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.00      | k1_waybel_2(sK8,sK9) != sK4(sK8,sK9) ),
% 2.60/1.00      inference(instantiation,[status(thm)],[c_5436]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_5478,plain,
% 2.60/1.00      ( k1_waybel_2(sK8,sK9) != sK4(sK8,sK9)
% 2.60/1.00      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.60/1.00      | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.00      inference(predicate_to_equality,[status(thm)],[c_5477]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_24,plain,
% 2.60/1.00      ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
% 2.60/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | k1_waybel_2(X0,X1) = X2 ),
% 2.60/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1070,plain,
% 2.60/1.00      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.00      | ~ v10_waybel_0(X1,X0)
% 2.60/1.00      | ~ l1_waybel_0(X1,X0)
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.60/1.00      | ~ v2_pre_topc(X0)
% 2.60/1.00      | ~ v8_pre_topc(X0)
% 2.60/1.00      | ~ v2_lattice3(X0)
% 2.60/1.00      | ~ v1_compts_1(X0)
% 2.60/1.00      | ~ v4_orders_2(X1)
% 2.60/1.00      | ~ v4_orders_2(X0)
% 2.60/1.00      | ~ v7_waybel_0(X1)
% 2.60/1.00      | ~ l1_waybel_9(X0)
% 2.60/1.00      | ~ v5_orders_2(X0)
% 2.60/1.00      | ~ v1_lattice3(X0)
% 2.60/1.00      | v2_struct_0(X1)
% 2.60/1.00      | ~ v3_orders_2(X0)
% 2.60/1.00      | k1_waybel_2(X0,X1) = X2
% 2.60/1.00      | k4_waybel_1(X0,sK7(X0)) != k4_waybel_1(sK8,X3)
% 2.60/1.00      | sK8 != X0 ),
% 2.60/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 2.60/1.00  
% 2.60/1.00  cnf(c_1071,plain,
% 2.60/1.00      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.00      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.00      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v2_lattice3(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v4_orders_2(sK8)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ l1_waybel_9(sK8)
% 2.60/1.01      | ~ v5_orders_2(sK8)
% 2.60/1.01      | ~ v1_lattice3(sK8)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | ~ v3_orders_2(sK8)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_1070]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1075,plain,
% 2.60/1.01      ( v2_struct_0(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1071,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1076,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_1075]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1902,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2)
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1076]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1903,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | ~ l1_waybel_0(sK9,sK8)
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_1902]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1907,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1903,c_31,c_30,c_29,c_28]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1908,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_1907]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4672,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.01      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X1_69,u1_struct_0(sK8))
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1_69)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0_69 ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_1908]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4682,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.01      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0_69
% 2.60/1.01      | ~ sP1_iProver_split ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.60/1.01                [c_4672]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5159,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = X0_69
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | sP1_iProver_split != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4682]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_25,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | ~ v10_waybel_0(X1,X0)
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK7(X0),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v2_lattice3(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_waybel_9(X0)
% 2.60/1.01      | ~ v5_orders_2(X0)
% 2.60/1.01      | ~ v1_lattice3(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | ~ v3_orders_2(X0)
% 2.60/1.01      | k1_waybel_2(X0,X1) = X2 ),
% 2.60/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1444,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | ~ v10_waybel_0(X1,X0)
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK7(X0),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v2_lattice3(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_waybel_9(X0)
% 2.60/1.01      | ~ v5_orders_2(X0)
% 2.60/1.01      | ~ v1_lattice3(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k1_waybel_2(X0,X1) = X2
% 2.60/1.01      | sK8 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1445,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v2_lattice3(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v4_orders_2(sK8)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ l1_waybel_9(sK8)
% 2.60/1.01      | ~ v5_orders_2(sK8)
% 2.60/1.01      | ~ v1_lattice3(sK8)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1 ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_1444]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1449,plain,
% 2.60/1.01      ( ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1445,c_41,c_40,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1450,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ v10_waybel_0(X0,sK8)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1 ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_1449]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1878,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k1_waybel_2(sK8,X0) = X1
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_1450]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1879,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | ~ l1_waybel_0(sK9,sK8)
% 2.60/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0 ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_1878]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1883,plain,
% 2.60/1.01      ( m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_1879,c_31,c_30,c_29,c_28]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_1884,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.60/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0 ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_1883]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4673,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.01      | ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0_69 ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_1884]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4729,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = X0_69
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | m1_subset_1(sK7(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4673]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4683,plain,
% 2.60/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[])],
% 2.60/1.01                [c_4672]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4732,plain,
% 2.60/1.01      ( sP1_iProver_split = iProver_top
% 2.60/1.01      | sP0_iProver_split = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4683]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4733,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = X0_69
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | sP1_iProver_split != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4682]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4681,plain,
% 2.60/1.01      ( ~ m1_subset_1(X0_69,u1_struct_0(sK8))
% 2.60/1.01      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.01      | ~ sP0_iProver_split ),
% 2.60/1.01      inference(splitting,
% 2.60/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.60/1.01                [c_4672]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5160,plain,
% 2.60/1.01      ( k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_69)
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | sP0_iProver_split != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4681]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5450,plain,
% 2.60/1.01      ( m1_subset_1(sK7(sK8),u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | sP0_iProver_split != iProver_top ),
% 2.60/1.01      inference(equality_resolution,[status(thm)],[c_5160]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5487,plain,
% 2.60/1.01      ( m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | k1_waybel_2(sK8,sK9) = X0_69 ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_5159,c_4729,c_4732,c_4733,c_5450]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5488,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = X0_69
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_5487]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5496,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = sK4(sK8,sK9)
% 2.60/1.01      | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_5165,c_5488]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4698,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0_68,X1_68,X0_69)
% 2.60/1.01      | r3_waybel_9(X0_68,X1_68,X1_69)
% 2.60/1.01      | X1_69 != X0_69 ),
% 2.60/1.01      theory(equality) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5463,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,X0_69)
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.60/1.01      | X0_69 != sK4(sK8,sK9) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_4698]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5500,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.60/1.01      | k1_waybel_2(sK8,sK9) != sK4(sK8,sK9) ),
% 2.60/1.01      inference(instantiation,[status(thm)],[c_5463]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5501,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) != sK4(sK8,sK9)
% 2.60/1.01      | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) = iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_5500]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6163,plain,
% 2.60/1.01      ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_5172,c_54,c_55,c_56,c_2815,c_2826,c_3835,c_5478,
% 2.60/1.01                 c_5496,c_5501]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6164,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_6163]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6697,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_6690,c_6164]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5577,plain,
% 2.60/1.01      ( k1_waybel_2(sK8,sK9) = sK4(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_5496,c_54,c_55,c_56,c_2815]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5580,plain,
% 2.60/1.01      ( sK4(sK8,sK9) = X0_69
% 2.60/1.01      | r3_waybel_9(sK8,sK9,X0_69) != iProver_top
% 2.60/1.01      | m1_subset_1(X0_69,u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_5577,c_5488]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6831,plain,
% 2.60/1.01      ( sK5(sK8,sK9) = sK4(sK8,sK9)
% 2.60/1.01      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_6697,c_5580]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_23,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1) ),
% 2.60/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2257,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) != X2
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_470]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2258,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2257]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2658,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK8 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_2258,c_1725]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2659,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(sK8)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2658]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2663,plain,
% 2.60/1.01      ( v2_struct_0(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2659,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2664,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2663]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2835,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_2664]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2836,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2835]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2838,plain,
% 2.60/1.01      ( m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2836,c_31,c_30,c_29]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2839,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2838]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3838,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_2839]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3839,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_3838]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6893,plain,
% 2.60/1.01      ( sK5(sK8,sK9) = sK4(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_6831,c_54,c_55,c_56,c_2815,c_2826,c_3839,c_5478,
% 2.60/1.01                 c_5496,c_5501,c_6687]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_19,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | sK6(X0,X1) != sK5(X0,X1) ),
% 2.60/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2449,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) != X2
% 2.60/1.01      | sK6(X0,X1) != sK5(X0,X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_470]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2450,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | sK6(X0,X1) != sK5(X0,X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2449]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2502,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | sK6(X0,X1) != sK5(X0,X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK8 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_2450,c_1725]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2503,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(sK8)
% 2.60/1.01      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2502]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2507,plain,
% 2.60/1.01      ( v2_struct_0(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2503,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2508,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2507]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2927,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_2508]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2928,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2927]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2930,plain,
% 2.60/1.01      ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2928,c_31,c_30,c_29]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2931,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2930]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3830,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_2931]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4666,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_3830]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5170,plain,
% 2.60/1.01      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4666]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4758,plain,
% 2.60/1.01      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4666]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6079,plain,
% 2.60/1.01      ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | sK6(sK8,sK9) != sK5(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_5170,c_54,c_55,c_56,c_2815,c_2826,c_4758,c_5478,
% 2.60/1.01                 c_5496,c_5501]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6080,plain,
% 2.60/1.01      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_6079]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6899,plain,
% 2.60/1.01      ( sK6(sK8,sK9) != sK4(sK8,sK9)
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.60/1.01      inference(demodulation,[status(thm)],[c_6893,c_6080]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_20,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.60/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1) ),
% 2.60/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2401,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) != X2
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_470]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2402,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2401]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2541,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK8 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_2402,c_1725]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2542,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(sK8)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2541]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2546,plain,
% 2.60/1.01      ( v2_struct_0(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2542,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2547,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2546]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2904,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_2547]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2905,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2904]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2907,plain,
% 2.60/1.01      ( ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2905,c_31,c_30,c_29]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2908,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2907]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3832,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_2908]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_4665,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.01      inference(subtyping,[status(esa)],[c_3832]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_5171,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_4665]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3833,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_3832]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6086,plain,
% 2.60/1.01      ( r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_5171,c_54,c_55,c_56,c_2815,c_2826,c_3833,c_5478,
% 2.60/1.01                 c_5496,c_5501]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6087,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_6086]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6698,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_6690,c_6087]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_6886,plain,
% 2.60/1.01      ( sK6(sK8,sK9) = sK4(sK8,sK9)
% 2.60/1.01      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.60/1.01      inference(superposition,[status(thm)],[c_6698,c_5580]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_22,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1) ),
% 2.60/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2305,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k1_waybel_2(sK8,sK9) != X2
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_470]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2306,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | ~ l1_pre_topc(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2305]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2619,plain,
% 2.60/1.01      ( ~ r3_waybel_9(X0,X1,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X1,X0)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(X0))
% 2.60/1.01      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.60/1.01      | ~ v2_pre_topc(X0)
% 2.60/1.01      | ~ v8_pre_topc(X0)
% 2.60/1.01      | ~ v1_compts_1(X0)
% 2.60/1.01      | ~ v4_orders_2(X1)
% 2.60/1.01      | ~ v7_waybel_0(X1)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(X1)
% 2.60/1.01      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK8 != X0 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_2306,c_1725]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2620,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v2_pre_topc(sK8)
% 2.60/1.01      | ~ v8_pre_topc(sK8)
% 2.60/1.01      | ~ v1_compts_1(sK8)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | v2_struct_0(sK8)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2619]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2624,plain,
% 2.60/1.01      ( v2_struct_0(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2620,c_41,c_40,c_36,c_34,c_33,c_103,c_130]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2625,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ l1_waybel_0(X0,sK8)
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2624]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2858,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,X0,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(X0)
% 2.60/1.01      | ~ v7_waybel_0(X0)
% 2.60/1.01      | v2_struct_0(X0)
% 2.60/1.01      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.60/1.01      | sK9 != X0
% 2.60/1.01      | sK8 != sK8 ),
% 2.60/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_2625]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2859,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ v4_orders_2(sK9)
% 2.60/1.01      | ~ v7_waybel_0(sK9)
% 2.60/1.01      | v2_struct_0(sK9)
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(unflattening,[status(thm)],[c_2858]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2861,plain,
% 2.60/1.01      ( m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(global_propositional_subsumption,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_2859,c_31,c_30,c_29]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_2862,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.60/1.01      inference(renaming,[status(thm)],[c_2861]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3836,plain,
% 2.60/1.01      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9))
% 2.60/1.01      | ~ r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.60/1.01      | ~ m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8))
% 2.60/1.01      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) ),
% 2.60/1.01      inference(equality_resolution_simp,[status(thm)],[c_2862]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(c_3837,plain,
% 2.60/1.01      ( r3_waybel_9(sK8,sK9,k1_waybel_2(sK8,sK9)) != iProver_top
% 2.60/1.01      | r1_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top
% 2.60/1.01      | m1_subset_1(k1_waybel_2(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.60/1.01      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
% 2.60/1.01      inference(predicate_to_equality,[status(thm)],[c_3836]) ).
% 2.60/1.01  
% 2.60/1.01  cnf(contradiction,plain,
% 2.60/1.01      ( $false ),
% 2.60/1.01      inference(minisat,
% 2.60/1.01                [status(thm)],
% 2.60/1.01                [c_6899,c_6886,c_6687,c_5501,c_5496,c_5478,c_3837,c_2826,
% 2.60/1.01                 c_2815,c_56,c_55,c_54]) ).
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.01  
% 2.60/1.01  ------                               Statistics
% 2.60/1.01  
% 2.60/1.01  ------ General
% 2.60/1.01  
% 2.60/1.01  abstr_ref_over_cycles:                  0
% 2.60/1.01  abstr_ref_under_cycles:                 0
% 2.60/1.01  gc_basic_clause_elim:                   0
% 2.60/1.01  forced_gc_time:                         0
% 2.60/1.01  parsing_time:                           0.011
% 2.60/1.01  unif_index_cands_time:                  0.
% 2.60/1.01  unif_index_add_time:                    0.
% 2.60/1.01  orderings_time:                         0.
% 2.60/1.01  out_proof_time:                         0.025
% 2.60/1.01  total_time:                             0.208
% 2.60/1.01  num_of_symbols:                         83
% 2.60/1.01  num_of_terms:                           3047
% 2.60/1.01  
% 2.60/1.01  ------ Preprocessing
% 2.60/1.01  
% 2.60/1.01  num_of_splits:                          6
% 2.60/1.01  num_of_split_atoms:                     6
% 2.60/1.01  num_of_reused_defs:                     0
% 2.60/1.01  num_eq_ax_congr_red:                    60
% 2.60/1.01  num_of_sem_filtered_clauses:            1
% 2.60/1.01  num_of_subtypes:                        6
% 2.60/1.01  monotx_restored_types:                  0
% 2.60/1.01  sat_num_of_epr_types:                   0
% 2.60/1.01  sat_num_of_non_cyclic_types:            0
% 2.60/1.01  sat_guarded_non_collapsed_types:        1
% 2.60/1.01  num_pure_diseq_elim:                    0
% 2.60/1.01  simp_replaced_by:                       0
% 2.60/1.01  res_preprocessed:                       130
% 2.60/1.01  prep_upred:                             0
% 2.60/1.01  prep_unflattend:                        125
% 2.60/1.01  smt_new_axioms:                         0
% 2.60/1.01  pred_elim_cands:                        5
% 2.60/1.01  pred_elim:                              19
% 2.60/1.01  pred_elim_cl:                           23
% 2.60/1.01  pred_elim_cycles:                       28
% 2.60/1.01  merged_defs:                            0
% 2.60/1.01  merged_defs_ncl:                        0
% 2.60/1.01  bin_hyper_res:                          0
% 2.60/1.01  prep_cycles:                            4
% 2.60/1.01  pred_elim_time:                         0.083
% 2.60/1.01  splitting_time:                         0.
% 2.60/1.01  sem_filter_time:                        0.
% 2.60/1.01  monotx_time:                            0.
% 2.60/1.01  subtype_inf_time:                       0.
% 2.60/1.01  
% 2.60/1.01  ------ Problem properties
% 2.60/1.01  
% 2.60/1.01  clauses:                                25
% 2.60/1.01  conjectures:                            0
% 2.60/1.01  epr:                                    3
% 2.60/1.01  horn:                                   17
% 2.60/1.01  ground:                                 10
% 2.60/1.01  unary:                                  2
% 2.60/1.01  binary:                                 5
% 2.60/1.01  lits:                                   85
% 2.60/1.01  lits_eq:                                6
% 2.60/1.01  fd_pure:                                0
% 2.60/1.01  fd_pseudo:                              0
% 2.60/1.01  fd_cond:                                2
% 2.60/1.01  fd_pseudo_cond:                         0
% 2.60/1.01  ac_symbols:                             0
% 2.60/1.01  
% 2.60/1.01  ------ Propositional Solver
% 2.60/1.01  
% 2.60/1.01  prop_solver_calls:                      28
% 2.60/1.01  prop_fast_solver_calls:                 2595
% 2.60/1.01  smt_solver_calls:                       0
% 2.60/1.01  smt_fast_solver_calls:                  0
% 2.60/1.01  prop_num_of_clauses:                    1463
% 2.60/1.01  prop_preprocess_simplified:             4945
% 2.60/1.01  prop_fo_subsumed:                       171
% 2.60/1.01  prop_solver_time:                       0.
% 2.60/1.01  smt_solver_time:                        0.
% 2.60/1.01  smt_fast_solver_time:                   0.
% 2.60/1.01  prop_fast_solver_time:                  0.
% 2.60/1.01  prop_unsat_core_time:                   0.
% 2.60/1.01  
% 2.60/1.01  ------ QBF
% 2.60/1.01  
% 2.60/1.01  qbf_q_res:                              0
% 2.60/1.01  qbf_num_tautologies:                    0
% 2.60/1.01  qbf_prep_cycles:                        0
% 2.60/1.01  
% 2.60/1.01  ------ BMC1
% 2.60/1.01  
% 2.60/1.01  bmc1_current_bound:                     -1
% 2.60/1.01  bmc1_last_solved_bound:                 -1
% 2.60/1.01  bmc1_unsat_core_size:                   -1
% 2.60/1.01  bmc1_unsat_core_parents_size:           -1
% 2.60/1.01  bmc1_merge_next_fun:                    0
% 2.60/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.01  
% 2.60/1.01  ------ Instantiation
% 2.60/1.01  
% 2.60/1.01  inst_num_of_clauses:                    249
% 2.60/1.01  inst_num_in_passive:                    17
% 2.60/1.01  inst_num_in_active:                     194
% 2.60/1.01  inst_num_in_unprocessed:                38
% 2.60/1.01  inst_num_of_loops:                      210
% 2.60/1.01  inst_num_of_learning_restarts:          0
% 2.60/1.01  inst_num_moves_active_passive:          12
% 2.60/1.01  inst_lit_activity:                      0
% 2.60/1.01  inst_lit_activity_moves:                0
% 2.60/1.01  inst_num_tautologies:                   0
% 2.60/1.01  inst_num_prop_implied:                  0
% 2.60/1.01  inst_num_existing_simplified:           0
% 2.60/1.01  inst_num_eq_res_simplified:             0
% 2.60/1.01  inst_num_child_elim:                    0
% 2.60/1.01  inst_num_of_dismatching_blockings:      0
% 2.60/1.01  inst_num_of_non_proper_insts:           231
% 2.60/1.01  inst_num_of_duplicates:                 0
% 2.60/1.01  inst_inst_num_from_inst_to_res:         0
% 2.60/1.01  inst_dismatching_checking_time:         0.
% 2.60/1.01  
% 2.60/1.01  ------ Resolution
% 2.60/1.01  
% 2.60/1.01  res_num_of_clauses:                     0
% 2.60/1.01  res_num_in_passive:                     0
% 2.60/1.01  res_num_in_active:                      0
% 2.60/1.01  res_num_of_loops:                       134
% 2.60/1.01  res_forward_subset_subsumed:            9
% 2.60/1.01  res_backward_subset_subsumed:           0
% 2.60/1.01  res_forward_subsumed:                   0
% 2.60/1.01  res_backward_subsumed:                  0
% 2.60/1.01  res_forward_subsumption_resolution:     5
% 2.60/1.01  res_backward_subsumption_resolution:    0
% 2.60/1.01  res_clause_to_clause_subsumption:       200
% 2.60/1.01  res_orphan_elimination:                 0
% 2.60/1.01  res_tautology_del:                      55
% 2.60/1.01  res_num_eq_res_simplified:              5
% 2.60/1.01  res_num_sel_changes:                    0
% 2.60/1.01  res_moves_from_active_to_pass:          0
% 2.60/1.01  
% 2.60/1.01  ------ Superposition
% 2.60/1.01  
% 2.60/1.01  sup_time_total:                         0.
% 2.60/1.01  sup_time_generating:                    0.
% 2.60/1.01  sup_time_sim_full:                      0.
% 2.60/1.01  sup_time_sim_immed:                     0.
% 2.60/1.01  
% 2.60/1.01  sup_num_of_clauses:                     40
% 2.60/1.01  sup_num_in_active:                      34
% 2.60/1.01  sup_num_in_passive:                     6
% 2.60/1.01  sup_num_of_loops:                       41
% 2.60/1.01  sup_fw_superposition:                   11
% 2.60/1.01  sup_bw_superposition:                   12
% 2.60/1.01  sup_immediate_simplified:               3
% 2.60/1.01  sup_given_eliminated:                   0
% 2.60/1.01  comparisons_done:                       0
% 2.60/1.01  comparisons_avoided:                    0
% 2.60/1.01  
% 2.60/1.01  ------ Simplifications
% 2.60/1.01  
% 2.60/1.01  
% 2.60/1.01  sim_fw_subset_subsumed:                 3
% 2.60/1.01  sim_bw_subset_subsumed:                 5
% 2.60/1.01  sim_fw_subsumed:                        0
% 2.60/1.01  sim_bw_subsumed:                        0
% 2.60/1.01  sim_fw_subsumption_res:                 1
% 2.60/1.01  sim_bw_subsumption_res:                 0
% 2.60/1.01  sim_tautology_del:                      1
% 2.60/1.01  sim_eq_tautology_del:                   1
% 2.60/1.01  sim_eq_res_simp:                        0
% 2.60/1.01  sim_fw_demodulated:                     0
% 2.60/1.01  sim_bw_demodulated:                     5
% 2.60/1.01  sim_light_normalised:                   0
% 2.60/1.01  sim_joinable_taut:                      0
% 2.60/1.01  sim_joinable_simp:                      0
% 2.60/1.01  sim_ac_normalised:                      0
% 2.60/1.01  sim_smt_subsumption:                    0
% 2.60/1.01  
%------------------------------------------------------------------------------
