%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:00 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  351 (20944 expanded)
%              Number of clauses        :  256 (3445 expanded)
%              Number of leaves         :   22 (5264 expanded)
%              Depth                    :   33
%              Number of atoms          : 2780 (316641 expanded)
%              Number of equality atoms :  385 (2934 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   36 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
           => ( v11_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
             => ( v11_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                  & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
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
             => ( v11_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
                  & r2_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
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
    inference(flattening,[],[f31])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
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
    inference(rectify,[],[f32])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ( ~ r2_hidden(k1_waybel_9(X0,sK9),k10_yellow_6(X0,sK9))
          | ~ r2_waybel_9(X0,sK9) )
        & v11_waybel_0(sK9,X0)
        & l1_waybel_0(sK9,X0)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
              | ~ r2_waybel_9(X0,X1) )
            & v11_waybel_0(X1,X0)
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
          ( ( ~ r2_hidden(k1_waybel_9(sK8,X1),k10_yellow_6(sK8,X1))
            | ~ r2_waybel_9(sK8,X1) )
          & v11_waybel_0(X1,sK8)
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

fof(f55,plain,
    ( ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
      | ~ r2_waybel_9(sK8,sK9) )
    & v11_waybel_0(sK9,sK8)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f52,f54,f53])).

fof(f93,plain,(
    l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f44])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    l1_waybel_9(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f66,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK1(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK0(X0,X1,X2))
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK1(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK1(X0,X1))
              & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f55])).

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
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
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
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(rectify,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f70])).

fof(f89,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8)
      | ~ m1_subset_1(X2,u1_struct_0(sK8)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
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
    inference(equality_resolution,[],[f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    v11_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
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
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f39])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f68])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
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
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
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
    inference(equality_resolution,[],[f67])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f45])).

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

fof(f13,plain,(
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
    inference(rectify,[],[f8])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f46,plain,(
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
    inference(rectify,[],[f28])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f46,f48,f47])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_waybel_9(X0,X1)
              | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r2_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_waybel_9(X0,X1)
      | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,
    ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r2_waybel_9(sK8,sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
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
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
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
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_9(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
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
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_waybel_9(X0,X2) = X1
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
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
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( l1_pre_topc(X0)
    | ~ l1_waybel_9(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_9(sK8) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1295,plain,
    ( l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_1296,plain,
    ( l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1295])).

cnf(c_2144,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_1296])).

cnf(c_2145,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2144])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_38,negated_conjecture,
    ( v8_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9,plain,
    ( ~ l1_waybel_9(X0)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_101,plain,
    ( ~ l1_waybel_9(sK8)
    | l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_128,plain,
    ( ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2149,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2145,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_2150,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2149])).

cnf(c_2271,plain,
    ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_2150])).

cnf(c_2272,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2271])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_27,negated_conjecture,
    ( v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2274,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_29,c_28,c_27])).

cnf(c_4116,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
    inference(subtyping,[status(esa)],[c_2274])).

cnf(c_4612,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4116])).

cnf(c_2,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_541,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1161,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_541,c_35])).

cnf(c_1162,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0)
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1161])).

cnf(c_1166,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | ~ r1_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_31])).

cnf(c_1167,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0) ),
    inference(renaming,[status(thm)],[c_1166])).

cnf(c_4122,plain,
    ( ~ r1_lattice3(sK8,X0_70,X0_68)
    | r1_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_68))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0_70) ),
    inference(subtyping,[status(esa)],[c_1167])).

cnf(c_4606,plain,
    ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
    | r1_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_68)) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4122])).

cnf(c_13,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_30,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(sK8,X0),sK8,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_685,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK3(X0)) != k4_waybel_1(sK8,X4)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_686,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_37,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_690,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | r1_orders_2(sK8,X2,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_691,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
    inference(renaming,[status(thm)],[c_690])).

cnf(c_2427,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_691])).

cnf(c_2428,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_2427])).

cnf(c_2432,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_orders_2(sK8,X1,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | ~ r3_waybel_9(sK8,sK9,X0)
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2428,c_29,c_28,c_27])).

cnf(c_2433,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_2432])).

cnf(c_4114,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
    | r1_orders_2(sK8,X1_68,X0_68)
    | ~ m1_subset_1(X2_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2_68) ),
    inference(subtyping,[status(esa)],[c_2433])).

cnf(c_4135,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
    | r1_orders_2(sK8,X1_68,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_4114])).

cnf(c_4615,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4135])).

cnf(c_14,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1071,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | m1_subset_1(sK3(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_1072,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1071])).

cnf(c_1076,plain,
    ( ~ v7_waybel_0(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1072,c_39,c_38,c_37,c_36,c_35,c_34,c_32,c_31])).

cnf(c_1077,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1076])).

cnf(c_2397,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
    | r1_orders_2(sK8,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1077])).

cnf(c_2398,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2397])).

cnf(c_2402,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_orders_2(sK8,X1,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | ~ r3_waybel_9(sK8,sK9,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_29,c_28,c_27])).

cnf(c_2403,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
    | r1_orders_2(sK8,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_2402])).

cnf(c_4115,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
    | r1_orders_2(sK8,X1_68,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_2403])).

cnf(c_4195,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4115])).

cnf(c_4136,plain,
    ( sP5_iProver_split
    | sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4114])).

cnf(c_4198,plain,
    ( sP5_iProver_split = iProver_top
    | sP4_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4136])).

cnf(c_4199,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4135])).

cnf(c_4134,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_68)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_4114])).

cnf(c_4616,plain,
    ( k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4134])).

cnf(c_4931,plain,
    ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4616])).

cnf(c_5360,plain,
    ( m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4615,c_4195,c_4198,c_4199,c_4931])).

cnf(c_5361,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5360])).

cnf(c_5372,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),X0_68) = iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4606,c_5361])).

cnf(c_3,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_518,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_9,c_3])).

cnf(c_1185,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_518,c_35])).

cnf(c_1186,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0)
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1185])).

cnf(c_1190,plain,
    ( r2_yellow_0(sK8,X0)
    | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_31])).

cnf(c_1191,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0) ),
    inference(renaming,[status(thm)],[c_1190])).

cnf(c_4121,plain,
    ( ~ r1_lattice3(sK8,X0_70,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | m1_subset_1(sK0(sK8,X0_70,X0_68),u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0_70) ),
    inference(subtyping,[status(esa)],[c_1191])).

cnf(c_4607,plain,
    ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK0(sK8,X0_70,X0_68),u1_struct_0(sK8)) = iProver_top
    | r2_yellow_0(sK8,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4121])).

cnf(c_6058,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
    | r1_orders_2(sK8,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5372,c_4607])).

cnf(c_1,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_564,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_9,c_1])).

cnf(c_1137,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,X1)
    | ~ l1_waybel_9(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_564,c_35])).

cnf(c_1138,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0)
    | ~ l1_waybel_9(sK8) ),
    inference(unflattening,[status(thm)],[c_1137])).

cnf(c_1142,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
    | ~ r1_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_31])).

cnf(c_1143,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0) ),
    inference(renaming,[status(thm)],[c_1142])).

cnf(c_4123,plain,
    ( ~ r1_lattice3(sK8,X0_70,X0_68)
    | ~ r1_orders_2(sK8,sK0(sK8,X0_70,X0_68),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | r2_yellow_0(sK8,X0_70) ),
    inference(subtyping,[status(esa)],[c_1143])).

cnf(c_4605,plain,
    ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
    | r1_orders_2(sK8,sK0(sK8,X0_70,X0_68),X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,X0_70) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4123])).

cnf(c_6062,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6058,c_4605])).

cnf(c_25,negated_conjecture,
    ( v11_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_11,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_643,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK8,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_644,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v11_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_648,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v11_waybel_0(X0,sK8)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_649,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ v11_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_1022,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_649])).

cnf(c_1023,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_1022])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1023,c_29,c_28,c_27,c_26])).

cnf(c_1028,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(renaming,[status(thm)],[c_1027])).

cnf(c_4124,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1_68) ),
    inference(subtyping,[status(esa)],[c_1028])).

cnf(c_4132,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_4124])).

cnf(c_4603,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4132])).

cnf(c_12,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_971,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | sK9 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_972,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(sK9)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK9)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ r3_waybel_9(sK8,sK9,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,c_26])).

cnf(c_977,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_4126,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_977])).

cnf(c_4158,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4126])).

cnf(c_4133,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4124])).

cnf(c_4168,plain,
    ( sP3_iProver_split = iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4133])).

cnf(c_4169,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4132])).

cnf(c_4131,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_68)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_4124])).

cnf(c_4604,plain,
    ( k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4131])).

cnf(c_4903,plain,
    ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4604])).

cnf(c_5307,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4603,c_4158,c_4168,c_4169,c_4903])).

cnf(c_5308,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5307])).

cnf(c_6153,plain,
    ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6062,c_4158,c_4168,c_4169,c_4903])).

cnf(c_6162,plain,
    ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4612,c_6153])).

cnf(c_52,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_53,plain,
    ( v4_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_54,plain,
    ( v7_waybel_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f71])).

cnf(c_2171,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_1296])).

cnf(c_2172,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_2171])).

cnf(c_2176,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2172,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_2177,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2176])).

cnf(c_2260,plain,
    ( m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_2177])).

cnf(c_2261,plain,
    ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2260])).

cnf(c_2262,plain,
    ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_6165,plain,
    ( r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6162,c_52,c_53,c_54,c_2262])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_7,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r2_waybel_9(X1,X0)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r2_waybel_9(sK8,sK9) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_444,plain,
    ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ l1_waybel_0(X0,X1)
    | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_orders_2(X1)
    | sK9 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_445,plain,
    ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ l1_waybel_0(sK9,sK8)
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_31,c_26,c_101])).

cnf(c_448,plain,
    ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_1800,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_448])).

cnf(c_1801,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1800])).

cnf(c_2027,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1801,c_1296])).

cnf(c_2028,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2027])).

cnf(c_2032,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_2033,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2032])).

cnf(c_2328,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK5(sK8,X0))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_2033])).

cnf(c_2329,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2328])).

cnf(c_2331,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2329,c_29,c_28,c_27])).

cnf(c_2332,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2331])).

cnf(c_3281,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2332])).

cnf(c_4111,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(subtyping,[status(esa)],[c_3281])).

cnf(c_4619,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4111])).

cnf(c_2273,plain,
    ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2272])).

cnf(c_3282,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3281])).

cnf(c_4144,plain,
    ( ~ m1_subset_1(X0_68,X0_69)
    | m1_subset_1(X1_68,X0_69)
    | X1_68 != X0_68 ),
    theory(equality)).

cnf(c_4883,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | X0_68 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4144])).

cnf(c_4924,plain,
    ( m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
    | k1_waybel_9(sK8,sK9) != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4883])).

cnf(c_4925,plain,
    ( k1_waybel_9(sK8,sK9) != sK4(sK8,sK9)
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4924])).

cnf(c_22,plain,
    ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_730,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2
    | k4_waybel_1(X0,sK7(X0)) != k4_waybel_1(sK8,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_731,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v11_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(X0)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(X0)
    | k1_waybel_9(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_735,plain,
    ( ~ v7_waybel_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v11_waybel_0(X0,sK8)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_736,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ v11_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_995,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k1_waybel_9(sK8,X0) = X1
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_736])).

cnf(c_996,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k1_waybel_9(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,X0)
    | k1_waybel_9(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_29,c_28,c_27,c_26])).

cnf(c_1001,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | k1_waybel_9(sK8,sK9) = X0
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
    inference(renaming,[status(thm)],[c_1000])).

cnf(c_4125,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1_68)
    | k1_waybel_9(sK8,sK9) = X0_68 ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_4129,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | k1_waybel_9(sK8,sK9) = X0_68
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_4125])).

cnf(c_4600,plain,
    ( k1_waybel_9(sK8,sK9) = X0_68
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4129])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK7(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_947,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK7(X0),u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_9(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(X0,X1) = X2
    | sK9 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_948,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v3_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(sK9)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK9)
    | ~ l1_waybel_9(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | v2_struct_0(sK9)
    | k1_waybel_9(sK8,sK9) = X0 ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_952,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | k1_waybel_9(sK8,sK9) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,c_26])).

cnf(c_4127,plain,
    ( ~ r3_waybel_9(sK8,sK9,X0_68)
    | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
    | k1_waybel_9(sK8,sK9) = X0_68 ),
    inference(subtyping,[status(esa)],[c_952])).

cnf(c_4155,plain,
    ( k1_waybel_9(sK8,sK9) = X0_68
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK7(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4127])).

cnf(c_4130,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_4125])).

cnf(c_4161,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4130])).

cnf(c_4162,plain,
    ( k1_waybel_9(sK8,sK9) = X0_68
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4129])).

cnf(c_4128,plain,
    ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
    | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_68)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_4125])).

cnf(c_4601,plain,
    ( k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_68)
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4128])).

cnf(c_4897,plain,
    ( m1_subset_1(sK7(sK8),u1_struct_0(sK8)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4601])).

cnf(c_4934,plain,
    ( m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | k1_waybel_9(sK8,sK9) = X0_68 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4600,c_4155,c_4161,c_4162,c_4897])).

cnf(c_4935,plain,
    ( k1_waybel_9(sK8,sK9) = X0_68
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4934])).

cnf(c_4943,plain,
    ( k1_waybel_9(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4612,c_4935])).

cnf(c_4145,plain,
    ( ~ r3_waybel_9(X0_67,X1_67,X0_68)
    | r3_waybel_9(X0_67,X1_67,X1_68)
    | X1_68 != X0_68 ),
    theory(equality)).

cnf(c_4910,plain,
    ( r3_waybel_9(sK8,sK9,X0_68)
    | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | X0_68 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4145])).

cnf(c_4947,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
    | k1_waybel_9(sK8,sK9) != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4910])).

cnf(c_4948,plain,
    ( k1_waybel_9(sK8,sK9) != sK4(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) = iProver_top
    | r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4947])).

cnf(c_5610,plain,
    ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4619,c_52,c_53,c_54,c_2262,c_2273,c_3282,c_4925,c_4943,c_4948])).

cnf(c_6172,plain,
    ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6165,c_5610])).

cnf(c_5045,plain,
    ( k1_waybel_9(sK8,sK9) = sK4(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4943,c_52,c_53,c_54,c_2262])).

cnf(c_5048,plain,
    ( sK4(sK8,sK9) = X0_68
    | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
    | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5045,c_4935])).

cnf(c_6211,plain,
    ( sK5(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6172,c_5048])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_1704,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_21,c_448])).

cnf(c_1705,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1704])).

cnf(c_2105,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1705,c_1296])).

cnf(c_2106,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2105])).

cnf(c_2110,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2106,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_2111,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2110])).

cnf(c_2282,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_2111])).

cnf(c_2283,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2282])).

cnf(c_2285,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2283,c_29,c_28,c_27])).

cnf(c_2286,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2285])).

cnf(c_3285,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2286])).

cnf(c_3286,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3285])).

cnf(c_6232,plain,
    ( sK5(sK8,sK9) = sK4(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6211,c_52,c_53,c_54,c_2262,c_2273,c_3286,c_4925,c_4943,c_4948,c_6162])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_1896,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK8,sK9) != X2
    | sK6(X0,X1) != sK5(X0,X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_17,c_448])).

cnf(c_1897,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
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
    inference(unflattening,[status(thm)],[c_1896])).

cnf(c_1949,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
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
    inference(resolution_lifted,[status(thm)],[c_1897,c_1296])).

cnf(c_1950,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1949])).

cnf(c_1954,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_1955,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_1954])).

cnf(c_2374,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK6(sK8,X0) != sK5(sK8,X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1955])).

cnf(c_2375,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2374])).

cnf(c_2377,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2375,c_29,c_28,c_27])).

cnf(c_2378,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | sK6(sK8,sK9) != sK5(sK8,sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2377])).

cnf(c_3277,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | sK6(sK8,sK9) != sK5(sK8,sK9) ),
    inference(equality_resolution_simp,[status(thm)],[c_2378])).

cnf(c_4113,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | sK6(sK8,sK9) != sK5(sK8,sK9) ),
    inference(subtyping,[status(esa)],[c_3277])).

cnf(c_4617,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4113])).

cnf(c_4205,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4113])).

cnf(c_5564,plain,
    ( sK6(sK8,sK9) != sK5(sK8,sK9)
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4617,c_52,c_53,c_54,c_2262,c_2273,c_4205,c_4925,c_4943,c_4948])).

cnf(c_6237,plain,
    ( sK6(sK8,sK9) != sK4(sK8,sK9)
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6232,c_5564])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1848,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_18,c_448])).

cnf(c_1849,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1848])).

cnf(c_1988,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1849,c_1296])).

cnf(c_1989,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1988])).

cnf(c_1993,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1989,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_1994,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_1993])).

cnf(c_2351,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,X0,sK6(sK8,X0))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1994])).

cnf(c_2352,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2351])).

cnf(c_2354,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_29,c_28,c_27])).

cnf(c_2355,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2354])).

cnf(c_3279,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2355])).

cnf(c_4112,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(subtyping,[status(esa)],[c_3279])).

cnf(c_4618,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4112])).

cnf(c_3280,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3279])).

cnf(c_5571,plain,
    ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4618,c_52,c_53,c_54,c_2262,c_2273,c_3280,c_4925,c_4943,c_4948])).

cnf(c_6173,plain,
    ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6165,c_5571])).

cnf(c_6225,plain,
    ( sK6(sK8,sK9) = sK4(sK8,sK9)
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6173,c_5048])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1752,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_waybel_9(sK8,sK9) != X2
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(resolution_lifted,[status(thm)],[c_20,c_448])).

cnf(c_1753,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_1752])).

cnf(c_2066,plain,
    ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1753,c_1296])).

cnf(c_2067,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v2_pre_topc(sK8)
    | ~ v8_pre_topc(sK8)
    | ~ v1_compts_1(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2066])).

cnf(c_2071,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_39,c_38,c_34,c_32,c_31,c_101,c_128])).

cnf(c_2072,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2071])).

cnf(c_2305,plain,
    ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_2072])).

cnf(c_2306,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9)
    | v2_struct_0(sK9)
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(unflattening,[status(thm)],[c_2305])).

cnf(c_2308,plain,
    ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_29,c_28,c_27])).

cnf(c_2309,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
    | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
    inference(renaming,[status(thm)],[c_2308])).

cnf(c_3283,plain,
    ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
    | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2309])).

cnf(c_3284,plain,
    ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
    | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3283])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6237,c_6225,c_6162,c_4948,c_4943,c_4925,c_3284,c_2273,c_2262,c_54,c_53,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:29:08 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 2.57/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/0.98  
% 2.57/0.98  ------  iProver source info
% 2.57/0.98  
% 2.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/0.98  git: non_committed_changes: false
% 2.57/0.98  git: last_make_outside_of_git: false
% 2.57/0.98  
% 2.57/0.98  ------ 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options
% 2.57/0.98  
% 2.57/0.98  --out_options                           all
% 2.57/0.98  --tptp_safe_out                         true
% 2.57/0.98  --problem_path                          ""
% 2.57/0.98  --include_path                          ""
% 2.57/0.98  --clausifier                            res/vclausify_rel
% 2.57/0.98  --clausifier_options                    --mode clausify
% 2.57/0.98  --stdin                                 false
% 2.57/0.98  --stats_out                             all
% 2.57/0.98  
% 2.57/0.98  ------ General Options
% 2.57/0.98  
% 2.57/0.98  --fof                                   false
% 2.57/0.98  --time_out_real                         305.
% 2.57/0.98  --time_out_virtual                      -1.
% 2.57/0.98  --symbol_type_check                     false
% 2.57/0.98  --clausify_out                          false
% 2.57/0.98  --sig_cnt_out                           false
% 2.57/0.98  --trig_cnt_out                          false
% 2.57/0.98  --trig_cnt_out_tolerance                1.
% 2.57/0.98  --trig_cnt_out_sk_spl                   false
% 2.57/0.98  --abstr_cl_out                          false
% 2.57/0.98  
% 2.57/0.98  ------ Global Options
% 2.57/0.98  
% 2.57/0.98  --schedule                              default
% 2.57/0.98  --add_important_lit                     false
% 2.57/0.98  --prop_solver_per_cl                    1000
% 2.57/0.98  --min_unsat_core                        false
% 2.57/0.98  --soft_assumptions                      false
% 2.57/0.98  --soft_lemma_size                       3
% 2.57/0.98  --prop_impl_unit_size                   0
% 2.57/0.98  --prop_impl_unit                        []
% 2.57/0.98  --share_sel_clauses                     true
% 2.57/0.98  --reset_solvers                         false
% 2.57/0.98  --bc_imp_inh                            [conj_cone]
% 2.57/0.98  --conj_cone_tolerance                   3.
% 2.57/0.98  --extra_neg_conj                        none
% 2.57/0.98  --large_theory_mode                     true
% 2.57/0.98  --prolific_symb_bound                   200
% 2.57/0.98  --lt_threshold                          2000
% 2.57/0.98  --clause_weak_htbl                      true
% 2.57/0.98  --gc_record_bc_elim                     false
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing Options
% 2.57/0.98  
% 2.57/0.98  --preprocessing_flag                    true
% 2.57/0.98  --time_out_prep_mult                    0.1
% 2.57/0.98  --splitting_mode                        input
% 2.57/0.98  --splitting_grd                         true
% 2.57/0.98  --splitting_cvd                         false
% 2.57/0.98  --splitting_cvd_svl                     false
% 2.57/0.98  --splitting_nvd                         32
% 2.57/0.98  --sub_typing                            true
% 2.57/0.98  --prep_gs_sim                           true
% 2.57/0.98  --prep_unflatten                        true
% 2.57/0.98  --prep_res_sim                          true
% 2.57/0.98  --prep_upred                            true
% 2.57/0.98  --prep_sem_filter                       exhaustive
% 2.57/0.98  --prep_sem_filter_out                   false
% 2.57/0.98  --pred_elim                             true
% 2.57/0.98  --res_sim_input                         true
% 2.57/0.98  --eq_ax_congr_red                       true
% 2.57/0.98  --pure_diseq_elim                       true
% 2.57/0.98  --brand_transform                       false
% 2.57/0.98  --non_eq_to_eq                          false
% 2.57/0.98  --prep_def_merge                        true
% 2.57/0.98  --prep_def_merge_prop_impl              false
% 2.57/0.98  --prep_def_merge_mbd                    true
% 2.57/0.98  --prep_def_merge_tr_red                 false
% 2.57/0.98  --prep_def_merge_tr_cl                  false
% 2.57/0.98  --smt_preprocessing                     true
% 2.57/0.98  --smt_ac_axioms                         fast
% 2.57/0.98  --preprocessed_out                      false
% 2.57/0.98  --preprocessed_stats                    false
% 2.57/0.98  
% 2.57/0.98  ------ Abstraction refinement Options
% 2.57/0.98  
% 2.57/0.98  --abstr_ref                             []
% 2.57/0.98  --abstr_ref_prep                        false
% 2.57/0.98  --abstr_ref_until_sat                   false
% 2.57/0.98  --abstr_ref_sig_restrict                funpre
% 2.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.98  --abstr_ref_under                       []
% 2.57/0.98  
% 2.57/0.98  ------ SAT Options
% 2.57/0.98  
% 2.57/0.98  --sat_mode                              false
% 2.57/0.98  --sat_fm_restart_options                ""
% 2.57/0.98  --sat_gr_def                            false
% 2.57/0.98  --sat_epr_types                         true
% 2.57/0.98  --sat_non_cyclic_types                  false
% 2.57/0.98  --sat_finite_models                     false
% 2.57/0.98  --sat_fm_lemmas                         false
% 2.57/0.98  --sat_fm_prep                           false
% 2.57/0.98  --sat_fm_uc_incr                        true
% 2.57/0.98  --sat_out_model                         small
% 2.57/0.98  --sat_out_clauses                       false
% 2.57/0.98  
% 2.57/0.98  ------ QBF Options
% 2.57/0.98  
% 2.57/0.98  --qbf_mode                              false
% 2.57/0.98  --qbf_elim_univ                         false
% 2.57/0.98  --qbf_dom_inst                          none
% 2.57/0.98  --qbf_dom_pre_inst                      false
% 2.57/0.98  --qbf_sk_in                             false
% 2.57/0.98  --qbf_pred_elim                         true
% 2.57/0.98  --qbf_split                             512
% 2.57/0.98  
% 2.57/0.98  ------ BMC1 Options
% 2.57/0.98  
% 2.57/0.98  --bmc1_incremental                      false
% 2.57/0.98  --bmc1_axioms                           reachable_all
% 2.57/0.98  --bmc1_min_bound                        0
% 2.57/0.98  --bmc1_max_bound                        -1
% 2.57/0.98  --bmc1_max_bound_default                -1
% 2.57/0.98  --bmc1_symbol_reachability              true
% 2.57/0.98  --bmc1_property_lemmas                  false
% 2.57/0.98  --bmc1_k_induction                      false
% 2.57/0.98  --bmc1_non_equiv_states                 false
% 2.57/0.98  --bmc1_deadlock                         false
% 2.57/0.98  --bmc1_ucm                              false
% 2.57/0.98  --bmc1_add_unsat_core                   none
% 2.57/0.98  --bmc1_unsat_core_children              false
% 2.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.98  --bmc1_out_stat                         full
% 2.57/0.98  --bmc1_ground_init                      false
% 2.57/0.98  --bmc1_pre_inst_next_state              false
% 2.57/0.98  --bmc1_pre_inst_state                   false
% 2.57/0.98  --bmc1_pre_inst_reach_state             false
% 2.57/0.98  --bmc1_out_unsat_core                   false
% 2.57/0.98  --bmc1_aig_witness_out                  false
% 2.57/0.98  --bmc1_verbose                          false
% 2.57/0.98  --bmc1_dump_clauses_tptp                false
% 2.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.98  --bmc1_dump_file                        -
% 2.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.98  --bmc1_ucm_extend_mode                  1
% 2.57/0.98  --bmc1_ucm_init_mode                    2
% 2.57/0.98  --bmc1_ucm_cone_mode                    none
% 2.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.98  --bmc1_ucm_relax_model                  4
% 2.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.98  --bmc1_ucm_layered_model                none
% 2.57/0.98  --bmc1_ucm_max_lemma_size               10
% 2.57/0.98  
% 2.57/0.98  ------ AIG Options
% 2.57/0.98  
% 2.57/0.98  --aig_mode                              false
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation Options
% 2.57/0.98  
% 2.57/0.98  --instantiation_flag                    true
% 2.57/0.98  --inst_sos_flag                         false
% 2.57/0.98  --inst_sos_phase                        true
% 2.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel_side                     num_symb
% 2.57/0.98  --inst_solver_per_active                1400
% 2.57/0.98  --inst_solver_calls_frac                1.
% 2.57/0.98  --inst_passive_queue_type               priority_queues
% 2.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.98  --inst_passive_queues_freq              [25;2]
% 2.57/0.98  --inst_dismatching                      true
% 2.57/0.98  --inst_eager_unprocessed_to_passive     true
% 2.57/0.98  --inst_prop_sim_given                   true
% 2.57/0.98  --inst_prop_sim_new                     false
% 2.57/0.98  --inst_subs_new                         false
% 2.57/0.98  --inst_eq_res_simp                      false
% 2.57/0.98  --inst_subs_given                       false
% 2.57/0.98  --inst_orphan_elimination               true
% 2.57/0.98  --inst_learning_loop_flag               true
% 2.57/0.98  --inst_learning_start                   3000
% 2.57/0.98  --inst_learning_factor                  2
% 2.57/0.98  --inst_start_prop_sim_after_learn       3
% 2.57/0.98  --inst_sel_renew                        solver
% 2.57/0.98  --inst_lit_activity_flag                true
% 2.57/0.98  --inst_restr_to_given                   false
% 2.57/0.98  --inst_activity_threshold               500
% 2.57/0.98  --inst_out_proof                        true
% 2.57/0.98  
% 2.57/0.98  ------ Resolution Options
% 2.57/0.98  
% 2.57/0.98  --resolution_flag                       true
% 2.57/0.98  --res_lit_sel                           adaptive
% 2.57/0.98  --res_lit_sel_side                      none
% 2.57/0.98  --res_ordering                          kbo
% 2.57/0.98  --res_to_prop_solver                    active
% 2.57/0.98  --res_prop_simpl_new                    false
% 2.57/0.98  --res_prop_simpl_given                  true
% 2.57/0.98  --res_passive_queue_type                priority_queues
% 2.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.98  --res_passive_queues_freq               [15;5]
% 2.57/0.98  --res_forward_subs                      full
% 2.57/0.98  --res_backward_subs                     full
% 2.57/0.98  --res_forward_subs_resolution           true
% 2.57/0.98  --res_backward_subs_resolution          true
% 2.57/0.98  --res_orphan_elimination                true
% 2.57/0.98  --res_time_limit                        2.
% 2.57/0.98  --res_out_proof                         true
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Options
% 2.57/0.98  
% 2.57/0.98  --superposition_flag                    true
% 2.57/0.98  --sup_passive_queue_type                priority_queues
% 2.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.98  --demod_completeness_check              fast
% 2.57/0.98  --demod_use_ground                      true
% 2.57/0.98  --sup_to_prop_solver                    passive
% 2.57/0.98  --sup_prop_simpl_new                    true
% 2.57/0.98  --sup_prop_simpl_given                  true
% 2.57/0.98  --sup_fun_splitting                     false
% 2.57/0.98  --sup_smt_interval                      50000
% 2.57/0.99  
% 2.57/0.99  ------ Superposition Simplification Setup
% 2.57/0.99  
% 2.57/0.99  --sup_indices_passive                   []
% 2.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_full_bw                           [BwDemod]
% 2.57/0.99  --sup_immed_triv                        [TrivRules]
% 2.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_immed_bw_main                     []
% 2.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  
% 2.57/0.99  ------ Combination Options
% 2.57/0.99  
% 2.57/0.99  --comb_res_mult                         3
% 2.57/0.99  --comb_sup_mult                         2
% 2.57/0.99  --comb_inst_mult                        10
% 2.57/0.99  
% 2.57/0.99  ------ Debug Options
% 2.57/0.99  
% 2.57/0.99  --dbg_backtrace                         false
% 2.57/0.99  --dbg_dump_prop_clauses                 false
% 2.57/0.99  --dbg_dump_prop_clauses_file            -
% 2.57/0.99  --dbg_out_stat                          false
% 2.57/0.99  ------ Parsing...
% 2.57/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe:16:0s pe_e  sf_s  rm: 17 0s  sf_e  pe_s  pe_e 
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/0.99  ------ Proving...
% 2.57/0.99  ------ Problem Properties 
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  clauses                                 25
% 2.57/0.99  conjectures                             0
% 2.57/0.99  EPR                                     3
% 2.57/0.99  Horn                                    17
% 2.57/0.99  unary                                   2
% 2.57/0.99  binary                                  5
% 2.57/0.99  lits                                    85
% 2.57/0.99  lits eq                                 6
% 2.57/0.99  fd_pure                                 0
% 2.57/0.99  fd_pseudo                               0
% 2.57/0.99  fd_cond                                 2
% 2.57/0.99  fd_pseudo_cond                          0
% 2.57/0.99  AC symbols                              0
% 2.57/0.99  
% 2.57/0.99  ------ Schedule dynamic 5 is on 
% 2.57/0.99  
% 2.57/0.99  ------ no conjectures: strip conj schedule 
% 2.57/0.99  
% 2.57/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  ------ 
% 2.57/0.99  Current options:
% 2.57/0.99  ------ 
% 2.57/0.99  
% 2.57/0.99  ------ Input Options
% 2.57/0.99  
% 2.57/0.99  --out_options                           all
% 2.57/0.99  --tptp_safe_out                         true
% 2.57/0.99  --problem_path                          ""
% 2.57/0.99  --include_path                          ""
% 2.57/0.99  --clausifier                            res/vclausify_rel
% 2.57/0.99  --clausifier_options                    --mode clausify
% 2.57/0.99  --stdin                                 false
% 2.57/0.99  --stats_out                             all
% 2.57/0.99  
% 2.57/0.99  ------ General Options
% 2.57/0.99  
% 2.57/0.99  --fof                                   false
% 2.57/0.99  --time_out_real                         305.
% 2.57/0.99  --time_out_virtual                      -1.
% 2.57/0.99  --symbol_type_check                     false
% 2.57/0.99  --clausify_out                          false
% 2.57/0.99  --sig_cnt_out                           false
% 2.57/0.99  --trig_cnt_out                          false
% 2.57/0.99  --trig_cnt_out_tolerance                1.
% 2.57/0.99  --trig_cnt_out_sk_spl                   false
% 2.57/0.99  --abstr_cl_out                          false
% 2.57/0.99  
% 2.57/0.99  ------ Global Options
% 2.57/0.99  
% 2.57/0.99  --schedule                              default
% 2.57/0.99  --add_important_lit                     false
% 2.57/0.99  --prop_solver_per_cl                    1000
% 2.57/0.99  --min_unsat_core                        false
% 2.57/0.99  --soft_assumptions                      false
% 2.57/0.99  --soft_lemma_size                       3
% 2.57/0.99  --prop_impl_unit_size                   0
% 2.57/0.99  --prop_impl_unit                        []
% 2.57/0.99  --share_sel_clauses                     true
% 2.57/0.99  --reset_solvers                         false
% 2.57/0.99  --bc_imp_inh                            [conj_cone]
% 2.57/0.99  --conj_cone_tolerance                   3.
% 2.57/0.99  --extra_neg_conj                        none
% 2.57/0.99  --large_theory_mode                     true
% 2.57/0.99  --prolific_symb_bound                   200
% 2.57/0.99  --lt_threshold                          2000
% 2.57/0.99  --clause_weak_htbl                      true
% 2.57/0.99  --gc_record_bc_elim                     false
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing Options
% 2.57/0.99  
% 2.57/0.99  --preprocessing_flag                    true
% 2.57/0.99  --time_out_prep_mult                    0.1
% 2.57/0.99  --splitting_mode                        input
% 2.57/0.99  --splitting_grd                         true
% 2.57/0.99  --splitting_cvd                         false
% 2.57/0.99  --splitting_cvd_svl                     false
% 2.57/0.99  --splitting_nvd                         32
% 2.57/0.99  --sub_typing                            true
% 2.57/0.99  --prep_gs_sim                           true
% 2.57/0.99  --prep_unflatten                        true
% 2.57/0.99  --prep_res_sim                          true
% 2.57/0.99  --prep_upred                            true
% 2.57/0.99  --prep_sem_filter                       exhaustive
% 2.57/0.99  --prep_sem_filter_out                   false
% 2.57/0.99  --pred_elim                             true
% 2.57/0.99  --res_sim_input                         true
% 2.57/0.99  --eq_ax_congr_red                       true
% 2.57/0.99  --pure_diseq_elim                       true
% 2.57/0.99  --brand_transform                       false
% 2.57/0.99  --non_eq_to_eq                          false
% 2.57/0.99  --prep_def_merge                        true
% 2.57/0.99  --prep_def_merge_prop_impl              false
% 2.57/0.99  --prep_def_merge_mbd                    true
% 2.57/0.99  --prep_def_merge_tr_red                 false
% 2.57/0.99  --prep_def_merge_tr_cl                  false
% 2.57/0.99  --smt_preprocessing                     true
% 2.57/0.99  --smt_ac_axioms                         fast
% 2.57/0.99  --preprocessed_out                      false
% 2.57/0.99  --preprocessed_stats                    false
% 2.57/0.99  
% 2.57/0.99  ------ Abstraction refinement Options
% 2.57/0.99  
% 2.57/0.99  --abstr_ref                             []
% 2.57/0.99  --abstr_ref_prep                        false
% 2.57/0.99  --abstr_ref_until_sat                   false
% 2.57/0.99  --abstr_ref_sig_restrict                funpre
% 2.57/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.99  --abstr_ref_under                       []
% 2.57/0.99  
% 2.57/0.99  ------ SAT Options
% 2.57/0.99  
% 2.57/0.99  --sat_mode                              false
% 2.57/0.99  --sat_fm_restart_options                ""
% 2.57/0.99  --sat_gr_def                            false
% 2.57/0.99  --sat_epr_types                         true
% 2.57/0.99  --sat_non_cyclic_types                  false
% 2.57/0.99  --sat_finite_models                     false
% 2.57/0.99  --sat_fm_lemmas                         false
% 2.57/0.99  --sat_fm_prep                           false
% 2.57/0.99  --sat_fm_uc_incr                        true
% 2.57/0.99  --sat_out_model                         small
% 2.57/0.99  --sat_out_clauses                       false
% 2.57/0.99  
% 2.57/0.99  ------ QBF Options
% 2.57/0.99  
% 2.57/0.99  --qbf_mode                              false
% 2.57/0.99  --qbf_elim_univ                         false
% 2.57/0.99  --qbf_dom_inst                          none
% 2.57/0.99  --qbf_dom_pre_inst                      false
% 2.57/0.99  --qbf_sk_in                             false
% 2.57/0.99  --qbf_pred_elim                         true
% 2.57/0.99  --qbf_split                             512
% 2.57/0.99  
% 2.57/0.99  ------ BMC1 Options
% 2.57/0.99  
% 2.57/0.99  --bmc1_incremental                      false
% 2.57/0.99  --bmc1_axioms                           reachable_all
% 2.57/0.99  --bmc1_min_bound                        0
% 2.57/0.99  --bmc1_max_bound                        -1
% 2.57/0.99  --bmc1_max_bound_default                -1
% 2.57/0.99  --bmc1_symbol_reachability              true
% 2.57/0.99  --bmc1_property_lemmas                  false
% 2.57/0.99  --bmc1_k_induction                      false
% 2.57/0.99  --bmc1_non_equiv_states                 false
% 2.57/0.99  --bmc1_deadlock                         false
% 2.57/0.99  --bmc1_ucm                              false
% 2.57/0.99  --bmc1_add_unsat_core                   none
% 2.57/0.99  --bmc1_unsat_core_children              false
% 2.57/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.99  --bmc1_out_stat                         full
% 2.57/0.99  --bmc1_ground_init                      false
% 2.57/0.99  --bmc1_pre_inst_next_state              false
% 2.57/0.99  --bmc1_pre_inst_state                   false
% 2.57/0.99  --bmc1_pre_inst_reach_state             false
% 2.57/0.99  --bmc1_out_unsat_core                   false
% 2.57/0.99  --bmc1_aig_witness_out                  false
% 2.57/0.99  --bmc1_verbose                          false
% 2.57/0.99  --bmc1_dump_clauses_tptp                false
% 2.57/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.99  --bmc1_dump_file                        -
% 2.57/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.99  --bmc1_ucm_extend_mode                  1
% 2.57/0.99  --bmc1_ucm_init_mode                    2
% 2.57/0.99  --bmc1_ucm_cone_mode                    none
% 2.57/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.99  --bmc1_ucm_relax_model                  4
% 2.57/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.99  --bmc1_ucm_layered_model                none
% 2.57/0.99  --bmc1_ucm_max_lemma_size               10
% 2.57/0.99  
% 2.57/0.99  ------ AIG Options
% 2.57/0.99  
% 2.57/0.99  --aig_mode                              false
% 2.57/0.99  
% 2.57/0.99  ------ Instantiation Options
% 2.57/0.99  
% 2.57/0.99  --instantiation_flag                    true
% 2.57/0.99  --inst_sos_flag                         false
% 2.57/0.99  --inst_sos_phase                        true
% 2.57/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.99  --inst_lit_sel_side                     none
% 2.57/0.99  --inst_solver_per_active                1400
% 2.57/0.99  --inst_solver_calls_frac                1.
% 2.57/0.99  --inst_passive_queue_type               priority_queues
% 2.57/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.57/0.99  --inst_passive_queues_freq              [25;2]
% 2.57/0.99  --inst_dismatching                      true
% 2.57/0.99  --inst_eager_unprocessed_to_passive     true
% 2.57/0.99  --inst_prop_sim_given                   true
% 2.57/0.99  --inst_prop_sim_new                     false
% 2.57/0.99  --inst_subs_new                         false
% 2.57/0.99  --inst_eq_res_simp                      false
% 2.57/0.99  --inst_subs_given                       false
% 2.57/0.99  --inst_orphan_elimination               true
% 2.57/0.99  --inst_learning_loop_flag               true
% 2.57/0.99  --inst_learning_start                   3000
% 2.57/0.99  --inst_learning_factor                  2
% 2.57/0.99  --inst_start_prop_sim_after_learn       3
% 2.57/0.99  --inst_sel_renew                        solver
% 2.57/0.99  --inst_lit_activity_flag                true
% 2.57/0.99  --inst_restr_to_given                   false
% 2.57/0.99  --inst_activity_threshold               500
% 2.57/0.99  --inst_out_proof                        true
% 2.57/0.99  
% 2.57/0.99  ------ Resolution Options
% 2.57/0.99  
% 2.57/0.99  --resolution_flag                       false
% 2.57/0.99  --res_lit_sel                           adaptive
% 2.57/0.99  --res_lit_sel_side                      none
% 2.57/0.99  --res_ordering                          kbo
% 2.57/0.99  --res_to_prop_solver                    active
% 2.57/0.99  --res_prop_simpl_new                    false
% 2.57/0.99  --res_prop_simpl_given                  true
% 2.57/0.99  --res_passive_queue_type                priority_queues
% 2.57/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.57/0.99  --res_passive_queues_freq               [15;5]
% 2.57/0.99  --res_forward_subs                      full
% 2.57/0.99  --res_backward_subs                     full
% 2.57/0.99  --res_forward_subs_resolution           true
% 2.57/0.99  --res_backward_subs_resolution          true
% 2.57/0.99  --res_orphan_elimination                true
% 2.57/0.99  --res_time_limit                        2.
% 2.57/0.99  --res_out_proof                         true
% 2.57/0.99  
% 2.57/0.99  ------ Superposition Options
% 2.57/0.99  
% 2.57/0.99  --superposition_flag                    true
% 2.57/0.99  --sup_passive_queue_type                priority_queues
% 2.57/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.99  --demod_completeness_check              fast
% 2.57/0.99  --demod_use_ground                      true
% 2.57/0.99  --sup_to_prop_solver                    passive
% 2.57/0.99  --sup_prop_simpl_new                    true
% 2.57/0.99  --sup_prop_simpl_given                  true
% 2.57/0.99  --sup_fun_splitting                     false
% 2.57/0.99  --sup_smt_interval                      50000
% 2.57/0.99  
% 2.57/0.99  ------ Superposition Simplification Setup
% 2.57/0.99  
% 2.57/0.99  --sup_indices_passive                   []
% 2.57/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_full_bw                           [BwDemod]
% 2.57/0.99  --sup_immed_triv                        [TrivRules]
% 2.57/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_immed_bw_main                     []
% 2.57/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.99  
% 2.57/0.99  ------ Combination Options
% 2.57/0.99  
% 2.57/0.99  --comb_res_mult                         3
% 2.57/0.99  --comb_sup_mult                         2
% 2.57/0.99  --comb_inst_mult                        10
% 2.57/0.99  
% 2.57/0.99  ------ Debug Options
% 2.57/0.99  
% 2.57/0.99  --dbg_backtrace                         false
% 2.57/0.99  --dbg_dump_prop_clauses                 false
% 2.57/0.99  --dbg_dump_prop_clauses_file            -
% 2.57/0.99  --dbg_out_stat                          false
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  ------ Proving...
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  % SZS status Theorem for theBenchmark.p
% 2.57/0.99  
% 2.57/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/0.99  
% 2.57/0.99  fof(f10,conjecture,(
% 2.57/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f11,negated_conjecture,(
% 2.57/0.99    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 2.57/0.99    inference(negated_conjecture,[],[f10])).
% 2.57/0.99  
% 2.57/0.99  fof(f14,plain,(
% 2.57/0.99    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v11_waybel_0(X2,X0) => (r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) & r2_waybel_9(X0,X2))))))),
% 2.57/0.99    inference(rectify,[],[f11])).
% 2.57/0.99  
% 2.57/0.99  fof(f31,plain,(
% 2.57/0.99    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f14])).
% 2.57/0.99  
% 2.57/0.99  fof(f32,plain,(
% 2.57/0.99    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.57/0.99    inference(flattening,[],[f31])).
% 2.57/0.99  
% 2.57/0.99  fof(f52,plain,(
% 2.57/0.99    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 2.57/0.99    inference(rectify,[],[f32])).
% 2.57/0.99  
% 2.57/0.99  fof(f54,plain,(
% 2.57/0.99    ( ! [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_9(X0,sK9),k10_yellow_6(X0,sK9)) | ~r2_waybel_9(X0,sK9)) & v11_waybel_0(sK9,X0) & l1_waybel_0(sK9,X0) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9))) )),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f53,plain,(
% 2.57/0.99    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_9(sK8,X1),k10_yellow_6(sK8,X1)) | ~r2_waybel_9(sK8,X1)) & v11_waybel_0(X1,sK8) & l1_waybel_0(X1,sK8) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) & l1_waybel_9(sK8) & v1_compts_1(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v4_orders_2(sK8) & v3_orders_2(sK8) & v8_pre_topc(sK8) & v2_pre_topc(sK8))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f55,plain,(
% 2.57/0.99    ((~r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9)) | ~r2_waybel_9(sK8,sK9)) & v11_waybel_0(sK9,sK8) & l1_waybel_0(sK9,sK8) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) & l1_waybel_9(sK8) & v1_compts_1(sK8) & v2_lattice3(sK8) & v1_lattice3(sK8) & v5_orders_2(sK8) & v4_orders_2(sK8) & v3_orders_2(sK8) & v8_pre_topc(sK8) & v2_pre_topc(sK8)),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f52,f54,f53])).
% 2.57/0.99  
% 2.57/0.99  fof(f93,plain,(
% 2.57/0.99    l1_waybel_0(sK9,sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f7,axiom,(
% 2.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f25,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f7])).
% 2.57/0.99  
% 2.57/0.99  fof(f26,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.99    inference(flattening,[],[f25])).
% 2.57/0.99  
% 2.57/0.99  fof(f44,plain,(
% 2.57/0.99    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f45,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f44])).
% 2.57/0.99  
% 2.57/0.99  fof(f72,plain,(
% 2.57/0.99    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f45])).
% 2.57/0.99  
% 2.57/0.99  fof(f4,axiom,(
% 2.57/0.99    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f20,plain,(
% 2.57/0.99    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 2.57/0.99    inference(ennf_transformation,[],[f4])).
% 2.57/0.99  
% 2.57/0.99  fof(f65,plain,(
% 2.57/0.99    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f20])).
% 2.57/0.99  
% 2.57/0.99  fof(f88,plain,(
% 2.57/0.99    l1_waybel_9(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f80,plain,(
% 2.57/0.99    v2_pre_topc(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f81,plain,(
% 2.57/0.99    v8_pre_topc(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f85,plain,(
% 2.57/0.99    v1_lattice3(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f87,plain,(
% 2.57/0.99    v1_compts_1(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f66,plain,(
% 2.57/0.99    ( ! [X0] : (l1_orders_2(X0) | ~l1_waybel_9(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f20])).
% 2.57/0.99  
% 2.57/0.99  fof(f1,axiom,(
% 2.57/0.99    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f15,plain,(
% 2.57/0.99    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.57/0.99    inference(ennf_transformation,[],[f1])).
% 2.57/0.99  
% 2.57/0.99  fof(f16,plain,(
% 2.57/0.99    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 2.57/0.99    inference(flattening,[],[f15])).
% 2.57/0.99  
% 2.57/0.99  fof(f56,plain,(
% 2.57/0.99    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f16])).
% 2.57/0.99  
% 2.57/0.99  fof(f90,plain,(
% 2.57/0.99    ~v2_struct_0(sK9)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f91,plain,(
% 2.57/0.99    v4_orders_2(sK9)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f92,plain,(
% 2.57/0.99    v7_waybel_0(sK9)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f2,axiom,(
% 2.57/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f17,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f2])).
% 2.57/0.99  
% 2.57/0.99  fof(f18,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.57/0.99    inference(flattening,[],[f17])).
% 2.57/0.99  
% 2.57/0.99  fof(f33,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.57/0.99    inference(nnf_transformation,[],[f18])).
% 2.57/0.99  
% 2.57/0.99  fof(f34,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.57/0.99    inference(rectify,[],[f33])).
% 2.57/0.99  
% 2.57/0.99  fof(f36,plain,(
% 2.57/0.99    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,X5,sK1(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f35,plain,(
% 2.57/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f37,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,X5,sK1(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 2.57/0.99  
% 2.57/0.99  fof(f61,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,sK0(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f37])).
% 2.57/0.99  
% 2.57/0.99  fof(f84,plain,(
% 2.57/0.99    v5_orders_2(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f6,axiom,(
% 2.57/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f12,plain,(
% 2.57/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 2.57/0.99    inference(rectify,[],[f6])).
% 2.57/0.99  
% 2.57/0.99  fof(f23,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f12])).
% 2.57/0.99  
% 2.57/0.99  fof(f24,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(flattening,[],[f23])).
% 2.57/0.99  
% 2.57/0.99  fof(f41,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(rectify,[],[f24])).
% 2.57/0.99  
% 2.57/0.99  fof(f42,plain,(
% 2.57/0.99    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f43,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 2.57/0.99  
% 2.57/0.99  fof(f70,plain,(
% 2.57/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f43])).
% 2.57/0.99  
% 2.57/0.99  fof(f98,plain,(
% 2.57/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(equality_resolution,[],[f70])).
% 2.57/0.99  
% 2.57/0.99  fof(f89,plain,(
% 2.57/0.99    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK8,X2),sK8,sK8) | ~m1_subset_1(X2,u1_struct_0(sK8))) )),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f82,plain,(
% 2.57/0.99    v3_orders_2(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f83,plain,(
% 2.57/0.99    v4_orders_2(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f86,plain,(
% 2.57/0.99    v2_lattice3(sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f69,plain,(
% 2.57/0.99    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f43])).
% 2.57/0.99  
% 2.57/0.99  fof(f99,plain,(
% 2.57/0.99    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(equality_resolution,[],[f69])).
% 2.57/0.99  
% 2.57/0.99  fof(f60,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X1) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f37])).
% 2.57/0.99  
% 2.57/0.99  fof(f62,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X0,X1) | ~r1_orders_2(X0,sK0(X0,X1,X2),X2) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f37])).
% 2.57/0.99  
% 2.57/0.99  fof(f94,plain,(
% 2.57/0.99    v11_waybel_0(sK9,sK8)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f5,axiom,(
% 2.57/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f21,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f5])).
% 2.57/0.99  
% 2.57/0.99  fof(f22,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(flattening,[],[f21])).
% 2.57/0.99  
% 2.57/0.99  fof(f39,plain,(
% 2.57/0.99    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f40,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) & m1_subset_1(sK2(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f39])).
% 2.57/0.99  
% 2.57/0.99  fof(f68,plain,(
% 2.57/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f40])).
% 2.57/0.99  
% 2.57/0.99  fof(f96,plain,(
% 2.57/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(equality_resolution,[],[f68])).
% 2.57/0.99  
% 2.57/0.99  fof(f67,plain,(
% 2.57/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f40])).
% 2.57/0.99  
% 2.57/0.99  fof(f97,plain,(
% 2.57/0.99    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(equality_resolution,[],[f67])).
% 2.57/0.99  
% 2.57/0.99  fof(f71,plain,(
% 2.57/0.99    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f45])).
% 2.57/0.99  
% 2.57/0.99  fof(f8,axiom,(
% 2.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f13,plain,(
% 2.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 2.57/0.99    inference(rectify,[],[f8])).
% 2.57/0.99  
% 2.57/0.99  fof(f27,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f13])).
% 2.57/0.99  
% 2.57/0.99  fof(f28,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.99    inference(flattening,[],[f27])).
% 2.57/0.99  
% 2.57/0.99  fof(f46,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.99    inference(rectify,[],[f28])).
% 2.57/0.99  
% 2.57/0.99  fof(f48,plain,(
% 2.57/0.99    ( ! [X3] : (! [X1,X0] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sK6(X0,X1) != X3 & r3_waybel_9(X0,X1,sK6(X0,X1)) & r3_waybel_9(X0,X1,X3) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))) )),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f47,plain,(
% 2.57/0.99    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK5(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f49,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK5(X0,X1) != sK6(X0,X1) & r3_waybel_9(X0,X1,sK6(X0,X1)) & r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f46,f48,f47])).
% 2.57/0.99  
% 2.57/0.99  fof(f75,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK5(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f49])).
% 2.57/0.99  
% 2.57/0.99  fof(f3,axiom,(
% 2.57/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f19,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : ((r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.57/0.99    inference(ennf_transformation,[],[f3])).
% 2.57/0.99  
% 2.57/0.99  fof(f38,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (((r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r2_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.57/0.99    inference(nnf_transformation,[],[f19])).
% 2.57/0.99  
% 2.57/0.99  fof(f64,plain,(
% 2.57/0.99    ( ! [X0,X1] : (r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f38])).
% 2.57/0.99  
% 2.57/0.99  fof(f95,plain,(
% 2.57/0.99    ~r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9)) | ~r2_waybel_9(sK8,sK9)),
% 2.57/0.99    inference(cnf_transformation,[],[f55])).
% 2.57/0.99  
% 2.57/0.99  fof(f9,axiom,(
% 2.57/0.99    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 2.57/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.57/0.99  
% 2.57/0.99  fof(f29,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_9(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.57/0.99    inference(ennf_transformation,[],[f9])).
% 2.57/0.99  
% 2.57/0.99  fof(f30,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(flattening,[],[f29])).
% 2.57/0.99  
% 2.57/0.99  fof(f50,plain,(
% 2.57/0.99    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 2.57/0.99    introduced(choice_axiom,[])).
% 2.57/0.99  
% 2.57/0.99  fof(f51,plain,(
% 2.57/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f50])).
% 2.57/0.99  
% 2.57/0.99  fof(f79,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f51])).
% 2.57/0.99  
% 2.57/0.99  fof(f78,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f51])).
% 2.57/0.99  
% 2.57/0.99  fof(f73,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f49])).
% 2.57/0.99  
% 2.57/0.99  fof(f77,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK5(X0,X1) != sK6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f49])).
% 2.57/0.99  
% 2.57/0.99  fof(f76,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_waybel_9(X0,X1,sK6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f49])).
% 2.57/0.99  
% 2.57/0.99  fof(f74,plain,(
% 2.57/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.57/0.99    inference(cnf_transformation,[],[f49])).
% 2.57/0.99  
% 2.57/0.99  cnf(c_26,negated_conjecture,
% 2.57/0.99      ( l1_waybel_0(sK9,sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_15,plain,
% 2.57/0.99      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_10,plain,
% 2.57/0.99      ( l1_pre_topc(X0) | ~ l1_waybel_9(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_31,negated_conjecture,
% 2.57/0.99      ( l1_waybel_9(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1295,plain,
% 2.57/0.99      ( l1_pre_topc(X0) | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1296,plain,
% 2.57/0.99      ( l1_pre_topc(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1295]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2144,plain,
% 2.57/0.99      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2145,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2144]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_39,negated_conjecture,
% 2.57/0.99      ( v2_pre_topc(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_38,negated_conjecture,
% 2.57/0.99      ( v8_pre_topc(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_34,negated_conjecture,
% 2.57/0.99      ( v1_lattice3(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_32,negated_conjecture,
% 2.57/0.99      ( v1_compts_1(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_9,plain,
% 2.57/0.99      ( ~ l1_waybel_9(X0) | l1_orders_2(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_101,plain,
% 2.57/0.99      ( ~ l1_waybel_9(sK8) | l1_orders_2(sK8) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_0,plain,
% 2.57/0.99      ( ~ l1_orders_2(X0) | ~ v1_lattice3(X0) | ~ v2_struct_0(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_128,plain,
% 2.57/0.99      ( ~ l1_orders_2(sK8) | ~ v1_lattice3(sK8) | ~ v2_struct_0(sK8) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2149,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2145,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2150,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2149]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2271,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,X0,sK4(sK8,X0))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_2150]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2272,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2271]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_29,negated_conjecture,
% 2.57/0.99      ( ~ v2_struct_0(sK9) ),
% 2.57/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_28,negated_conjecture,
% 2.57/0.99      ( v4_orders_2(sK9) ),
% 2.57/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_27,negated_conjecture,
% 2.57/0.99      ( v7_waybel_0(sK9) ),
% 2.57/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2274,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2272,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4116,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_2274]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4612,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4116]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ l1_orders_2(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_541,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0) ),
% 2.57/0.99      inference(resolution,[status(thm)],[c_9,c_2]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_35,negated_conjecture,
% 2.57/0.99      ( v5_orders_2(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1161,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,X1,sK0(X0,X1,X2))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_541,c_35]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1162,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1161]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1166,plain,
% 2.57/0.99      ( r2_yellow_0(sK8,X0)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.57/0.99      | ~ r1_lattice3(sK8,X0,X1) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1162,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1167,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | r1_lattice3(sK8,X0,sK0(sK8,X0,X1))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1166]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4122,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0_70,X0_68)
% 2.57/0.99      | r1_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_68))
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_1167]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4606,plain,
% 2.57/0.99      ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,X0_70,sK0(sK8,X0_70,X0_68)) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4122]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_13,plain,
% 2.57/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
% 2.57/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.57/0.99      | r1_orders_2(X0,X3,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_30,negated_conjecture,
% 2.57/0.99      ( v5_pre_topc(k4_waybel_1(sK8,X0),sK8,sK8)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 2.57/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_685,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.57/0.99      | r1_orders_2(X0,X3,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X4,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k4_waybel_1(X0,sK3(X0)) != k4_waybel_1(sK8,X4)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_686,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v2_lattice3(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_685]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_37,negated_conjecture,
% 2.57/0.99      ( v3_orders_2(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_36,negated_conjecture,
% 2.57/0.99      ( v4_orders_2(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_33,negated_conjecture,
% 2.57/0.99      ( v2_lattice3(sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_690,plain,
% 2.57/0.99      ( ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_686,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_691,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_690]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2427,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X3)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_691]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2428,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2427]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2432,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2428,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2433,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2432]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4114,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X2_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X2_68) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_2433]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4135,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ sP5_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 2.57/0.99                [c_4114]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4615,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP5_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4135]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_14,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.57/0.99      | r1_orders_2(X0,X3,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1071,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
% 2.57/0.99      | r1_orders_2(X0,X3,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK3(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1072,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1071]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1076,plain,
% 2.57/0.99      ( ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1072,c_39,c_38,c_37,c_36,c_35,c_34,c_32,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1077,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1076]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2397,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X2)
% 2.57/0.99      | r1_orders_2(sK8,X2,X1)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1077]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2398,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2397]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2402,plain,
% 2.57/0.99      ( m1_subset_1(sK3(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,X0) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2398,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2403,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1)
% 2.57/0.99      | r1_orders_2(sK8,X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2402]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4115,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68)
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_2403]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4195,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4115]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4136,plain,
% 2.57/0.99      ( sP5_iProver_split | sP4_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[])],
% 2.57/0.99                [c_4114]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4198,plain,
% 2.57/0.99      ( sP5_iProver_split = iProver_top
% 2.57/0.99      | sP4_iProver_split = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4136]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4199,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP5_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4135]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4134,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | ~ sP4_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 2.57/0.99                [c_4114]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4616,plain,
% 2.57/0.99      ( k4_waybel_1(sK8,sK3(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP4_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4134]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4931,plain,
% 2.57/0.99      ( m1_subset_1(sK3(sK8),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP4_iProver_split != iProver_top ),
% 2.57/0.99      inference(equality_resolution,[status(thm)],[c_4616]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5360,plain,
% 2.57/0.99      ( m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4615,c_4195,c_4198,c_4199,c_4931]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5361,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,X1_68,X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_5360]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5372,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_4606,c_5361]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ l1_orders_2(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_518,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0) ),
% 2.57/0.99      inference(resolution,[status(thm)],[c_9,c_3]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1185,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_518,c_35]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1186,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1185]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1190,plain,
% 2.57/0.99      ( r2_yellow_0(sK8,X0)
% 2.57/0.99      | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ r1_lattice3(sK8,X0,X1) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1186,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1191,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK0(sK8,X0,X1),u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1190]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4121,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0_70,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK0(sK8,X0_70,X0_68),u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_1191]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4607,plain,
% 2.57/0.99      ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK0(sK8,X0_70,X0_68),u1_struct_0(sK8)) = iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4121]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6058,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,sK0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X1_68),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(X1_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(forward_subsumption_resolution,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_5372,c_4607]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ l1_orders_2(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_564,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0) ),
% 2.57/0.99      inference(resolution,[status(thm)],[c_9,c_1]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1137,plain,
% 2.57/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 2.57/0.99      | ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | r2_yellow_0(X0,X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_564,c_35]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1138,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1137]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1142,plain,
% 2.57/0.99      ( r2_yellow_0(sK8,X0)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
% 2.57/0.99      | ~ r1_lattice3(sK8,X0,X1) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1138,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1143,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0,X1)
% 2.57/0.99      | ~ r1_orders_2(sK8,sK0(sK8,X0,X1),X1)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1142]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4123,plain,
% 2.57/0.99      ( ~ r1_lattice3(sK8,X0_70,X0_68)
% 2.57/0.99      | ~ r1_orders_2(sK8,sK0(sK8,X0_70,X0_68),X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_1143]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4605,plain,
% 2.57/0.99      ( r1_lattice3(sK8,X0_70,X0_68) != iProver_top
% 2.57/0.99      | r1_orders_2(sK8,sK0(sK8,X0_70,X0_68),X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,X0_70) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4123]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6062,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_6058,c_4605]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_25,negated_conjecture,
% 2.57/0.99      ( v11_waybel_0(sK9,sK8) ),
% 2.57/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_11,plain,
% 2.57/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK2(X0)),X0,X0)
% 2.57/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_643,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k4_waybel_1(X0,sK2(X0)) != k4_waybel_1(sK8,X3)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_644,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v2_lattice3(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_643]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_648,plain,
% 2.57/0.99      ( ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_644,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_649,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_648]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1022,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK8),u1_waybel_0(sK8,X0)),X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X2)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_649]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1023,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | ~ l1_waybel_0(sK9,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1022]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1027,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1023,c_29,c_28,c_27,c_26]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1028,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1027]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4124,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X1_68) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_1028]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4132,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ sP3_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.57/0.99                [c_4124]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4603,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP3_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4132]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_12,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_971,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK2(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK9 != X1
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_972,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | ~ l1_waybel_0(sK9,sK8)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK2(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v2_lattice3(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_971]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_976,plain,
% 2.57/0.99      ( r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_972,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,
% 2.57/0.99                 c_28,c_27,c_26]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_977,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_976]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4126,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_977]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4158,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK2(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4126]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4133,plain,
% 2.57/0.99      ( sP3_iProver_split | sP2_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[])],
% 2.57/0.99                [c_4124]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4168,plain,
% 2.57/0.99      ( sP3_iProver_split = iProver_top
% 2.57/0.99      | sP2_iProver_split = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4133]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4169,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP3_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4132]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4131,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | ~ sP2_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.57/0.99                [c_4124]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4604,plain,
% 2.57/0.99      ( k4_waybel_1(sK8,sK2(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP2_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4131]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4903,plain,
% 2.57/0.99      ( m1_subset_1(sK2(sK8),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP2_iProver_split != iProver_top ),
% 2.57/0.99      inference(equality_resolution,[status(thm)],[c_4604]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5307,plain,
% 2.57/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4603,c_4158,c_4168,c_4169,c_4903]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5308,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | r1_lattice3(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)),X0_68) = iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_5307]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6153,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_6062,c_4158,c_4168,c_4169,c_4903]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6162,plain,
% 2.57/0.99      ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_4612,c_6153]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_52,plain,
% 2.57/0.99      ( v2_struct_0(sK9) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_53,plain,
% 2.57/0.99      ( v4_orders_2(sK9) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_54,plain,
% 2.57/0.99      ( v7_waybel_0(sK9) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_16,plain,
% 2.57/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.57/0.99      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 2.57/0.99      | ~ v2_pre_topc(X1)
% 2.57/0.99      | ~ v8_pre_topc(X1)
% 2.57/0.99      | ~ v1_compts_1(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ l1_pre_topc(X1)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2171,plain,
% 2.57/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.57/0.99      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 2.57/0.99      | ~ v2_pre_topc(X1)
% 2.57/0.99      | ~ v8_pre_topc(X1)
% 2.57/0.99      | ~ v1_compts_1(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK8 != X1 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2172,plain,
% 2.57/0.99      ( ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2171]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2176,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8)) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2172,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2177,plain,
% 2.57/0.99      ( ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2176]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2260,plain,
% 2.57/0.99      ( m1_subset_1(sK4(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_2177]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2261,plain,
% 2.57/0.99      ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2260]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2262,plain,
% 2.57/0.99      ( m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.57/0.99      | v4_orders_2(sK9) != iProver_top
% 2.57/0.99      | v7_waybel_0(sK9) != iProver_top
% 2.57/0.99      | v2_struct_0(sK9) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_2261]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6165,plain,
% 2.57/0.99      ( r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) = iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_6162,c_52,c_53,c_54,c_2262]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_19,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.57/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_7,plain,
% 2.57/0.99      ( ~ l1_waybel_0(X0,X1)
% 2.57/0.99      | r2_waybel_9(X1,X0)
% 2.57/0.99      | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.57/0.99      | ~ l1_orders_2(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_24,negated_conjecture,
% 2.57/0.99      ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.57/0.99      | ~ r2_waybel_9(sK8,sK9) ),
% 2.57/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_444,plain,
% 2.57/0.99      ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,X1)
% 2.57/0.99      | ~ r2_yellow_0(X1,k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.57/0.99      | ~ l1_orders_2(X1)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != X1 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_445,plain,
% 2.57/0.99      ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(sK9,sK8)
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ l1_orders_2(sK8) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_447,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9)) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_445,c_31,c_26,c_101]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_448,plain,
% 2.57/0.99      ( ~ r2_hidden(k1_waybel_9(sK8,sK9),k10_yellow_6(sK8,sK9))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_447]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1800,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != X2
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_448]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1801,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1800]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2027,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(X0,X1,sK5(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1801,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2028,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2027]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2032,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2028,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2033,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2032]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2328,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK5(sK8,X0))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_2033]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2329,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2328]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2331,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2329,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2332,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2331]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3281,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_2332]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4111,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_3281]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4619,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4111]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2273,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) = iProver_top
% 2.57/0.99      | v4_orders_2(sK9) != iProver_top
% 2.57/0.99      | v7_waybel_0(sK9) != iProver_top
% 2.57/0.99      | v2_struct_0(sK9) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_2272]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3282,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3281]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4144,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0_68,X0_69)
% 2.57/0.99      | m1_subset_1(X1_68,X0_69)
% 2.57/0.99      | X1_68 != X0_68 ),
% 2.57/0.99      theory(equality) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4883,plain,
% 2.57/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | X0_68 != sK4(sK8,sK9) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_4144]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4924,plain,
% 2.57/0.99      ( m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != sK4(sK8,sK9) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_4883]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4925,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) != sK4(sK8,sK9)
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.57/0.99      | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4924]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_22,plain,
% 2.57/0.99      ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
% 2.57/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(X0,X1) = X2 ),
% 2.57/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_730,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(X0,X1) = X2
% 2.57/0.99      | k4_waybel_1(X0,sK7(X0)) != k4_waybel_1(sK8,X3)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_731,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v2_lattice3(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k1_waybel_9(sK8,X0) = X1
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_730]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_735,plain,
% 2.57/0.99      ( ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k1_waybel_9(sK8,X0) = X1
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_731,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_736,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ v11_waybel_0(X0,sK8)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k1_waybel_9(sK8,X0) = X1
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_735]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_995,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,X1)
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k1_waybel_9(sK8,X0) = X1
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X2)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_736]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_996,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ l1_waybel_0(sK9,sK8)
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_995]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1000,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_996,c_29,c_28,c_27,c_26]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1001,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1000]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4125,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(X1_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X1_68)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0_68 ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_1001]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4129,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0_68
% 2.57/0.99      | ~ sP1_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.57/0.99                [c_4125]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4600,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = X0_68
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP1_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4129]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_23,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ v11_waybel_0(X1,X0)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK7(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(X0,X1) = X2 ),
% 2.57/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_947,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK7(X0),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v3_orders_2(X0)
% 2.57/0.99      | ~ v2_lattice3(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_waybel_9(X0)
% 2.57/0.99      | ~ v5_orders_2(X0)
% 2.57/0.99      | ~ v1_lattice3(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(X0,X1) = X2
% 2.57/0.99      | sK9 != X1
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_948,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ l1_waybel_0(sK9,sK8)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v3_orders_2(sK8)
% 2.57/0.99      | ~ v2_lattice3(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v4_orders_2(sK8)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | ~ l1_waybel_9(sK8)
% 2.57/0.99      | ~ v5_orders_2(sK8)
% 2.57/0.99      | ~ v1_lattice3(sK8)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0 ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_947]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_952,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0)
% 2.57/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0 ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_948,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_29,
% 2.57/0.99                 c_28,c_27,c_26]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4127,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK7(sK8),u1_struct_0(sK8))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0_68 ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_952]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4155,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = X0_68
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK7(sK8),u1_struct_0(sK8)) = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4127]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4130,plain,
% 2.57/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[])],
% 2.57/0.99                [c_4125]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4161,plain,
% 2.57/0.99      ( sP1_iProver_split = iProver_top
% 2.57/0.99      | sP0_iProver_split = iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4130]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4162,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = X0_68
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP1_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4129]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4128,plain,
% 2.57/0.99      ( ~ m1_subset_1(X0_68,u1_struct_0(sK8))
% 2.57/0.99      | k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | ~ sP0_iProver_split ),
% 2.57/0.99      inference(splitting,
% 2.57/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.57/0.99                [c_4125]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4601,plain,
% 2.57/0.99      ( k4_waybel_1(sK8,sK7(sK8)) != k4_waybel_1(sK8,X0_68)
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP0_iProver_split != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4897,plain,
% 2.57/0.99      ( m1_subset_1(sK7(sK8),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | sP0_iProver_split != iProver_top ),
% 2.57/0.99      inference(equality_resolution,[status(thm)],[c_4601]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4934,plain,
% 2.57/0.99      ( m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | k1_waybel_9(sK8,sK9) = X0_68 ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4600,c_4155,c_4161,c_4162,c_4897]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4935,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = X0_68
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_4934]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4943,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = sK4(sK8,sK9)
% 2.57/0.99      | m1_subset_1(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_4612,c_4935]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4145,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0_67,X1_67,X0_68)
% 2.57/0.99      | r3_waybel_9(X0_67,X1_67,X1_68)
% 2.57/0.99      | X1_68 != X0_68 ),
% 2.57/0.99      theory(equality) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4910,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,X0_68)
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.57/0.99      | X0_68 != sK4(sK8,sK9) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_4145]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4947,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,sK4(sK8,sK9))
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != sK4(sK8,sK9) ),
% 2.57/0.99      inference(instantiation,[status(thm)],[c_4910]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4948,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) != sK4(sK8,sK9)
% 2.57/0.99      | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) = iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK4(sK8,sK9)) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4947]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5610,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4619,c_52,c_53,c_54,c_2262,c_2273,c_3282,c_4925,
% 2.57/0.99                 c_4943,c_4948]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6172,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK5(sK8,sK9)) = iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_6165,c_5610]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5045,plain,
% 2.57/0.99      ( k1_waybel_9(sK8,sK9) = sK4(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4943,c_52,c_53,c_54,c_2262]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5048,plain,
% 2.57/0.99      ( sK4(sK8,sK9) = X0_68
% 2.57/0.99      | r3_waybel_9(sK8,sK9,X0_68) != iProver_top
% 2.57/0.99      | m1_subset_1(X0_68,u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(demodulation,[status(thm)],[c_5045,c_4935]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6211,plain,
% 2.57/0.99      ( sK5(sK8,sK9) = sK4(sK8,sK9)
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_6172,c_5048]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_21,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1704,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != X2
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_448]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1705,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1704]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2105,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1705,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2106,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2105]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2110,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2106,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2111,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2110]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2282,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_2111]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2283,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2282]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2285,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2283,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2286,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2285]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3285,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_2286]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3286,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3285]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6232,plain,
% 2.57/0.99      ( sK5(sK8,sK9) = sK4(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_6211,c_52,c_53,c_54,c_2262,c_2273,c_3286,c_4925,
% 2.57/0.99                 c_4943,c_4948,c_6162]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_17,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK6(X0,X1) != sK5(X0,X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1896,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != X2
% 2.57/0.99      | sK6(X0,X1) != sK5(X0,X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_448]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1897,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK6(X0,X1) != sK5(X0,X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1896]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1949,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | sK6(X0,X1) != sK5(X0,X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1897,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1950,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8)
% 2.57/0.99      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1949]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1954,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1950,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1955,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1954]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2374,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | sK6(sK8,X0) != sK5(sK8,X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1955]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2375,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2374]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2377,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2375,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2378,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2377]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3277,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | sK6(sK8,sK9) != sK5(sK8,sK9) ),
% 2.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_2378]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4113,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | sK6(sK8,sK9) != sK5(sK8,sK9) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_3277]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4617,plain,
% 2.57/0.99      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4113]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4205,plain,
% 2.57/0.99      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4113]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5564,plain,
% 2.57/0.99      ( sK6(sK8,sK9) != sK5(sK8,sK9)
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4617,c_52,c_53,c_54,c_2262,c_2273,c_4205,c_4925,
% 2.57/0.99                 c_4943,c_4948]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6237,plain,
% 2.57/0.99      ( sK6(sK8,sK9) != sK4(sK8,sK9)
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(demodulation,[status(thm)],[c_6232,c_5564]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_18,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.57/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1848,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != X2
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_448]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1849,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1848]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1988,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(X0,X1,sK6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1849,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1989,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1988]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1993,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_1989,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1994,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_1993]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2351,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,X0,sK6(sK8,X0))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1994]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2352,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2351]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2354,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2352,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2355,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2354]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3279,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_2355]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4112,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(subtyping,[status(esa)],[c_3279]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_4618,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4112]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3280,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3279]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_5571,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_4618,c_52,c_53,c_54,c_2262,c_2273,c_3280,c_4925,
% 2.57/0.99                 c_4943,c_4948]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6173,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,sK6(sK8,sK9)) = iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_6165,c_5571]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_6225,plain,
% 2.57/0.99      ( sK6(sK8,sK9) = sK4(sK8,sK9)
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) != iProver_top ),
% 2.57/0.99      inference(superposition,[status(thm)],[c_6173,c_5048]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_20,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1) ),
% 2.57/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1752,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k1_waybel_9(sK8,sK9) != X2
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_448]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_1753,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | ~ l1_pre_topc(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_1752]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2066,plain,
% 2.57/0.99      ( ~ r3_waybel_9(X0,X1,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X1,X0)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(X0))
% 2.57/0.99      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(X0)
% 2.57/0.99      | ~ v8_pre_topc(X0)
% 2.57/0.99      | ~ v1_compts_1(X0)
% 2.57/0.99      | ~ v4_orders_2(X1)
% 2.57/0.99      | ~ v7_waybel_0(X1)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(X1)
% 2.57/0.99      | k10_yellow_6(X0,X1) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK8 != X0 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_1753,c_1296]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2067,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v2_pre_topc(sK8)
% 2.57/0.99      | ~ v8_pre_topc(sK8)
% 2.57/0.99      | ~ v1_compts_1(sK8)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | v2_struct_0(sK8)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2066]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2071,plain,
% 2.57/0.99      ( v2_struct_0(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2067,c_39,c_38,c_34,c_32,c_31,c_101,c_128]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2072,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ l1_waybel_0(X0,sK8)
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2071]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2305,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,X0,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(X0)
% 2.57/0.99      | ~ v7_waybel_0(X0)
% 2.57/0.99      | v2_struct_0(X0)
% 2.57/0.99      | k10_yellow_6(sK8,X0) != k10_yellow_6(sK8,sK9)
% 2.57/0.99      | sK9 != X0
% 2.57/0.99      | sK8 != sK8 ),
% 2.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_2072]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2306,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | ~ v4_orders_2(sK9)
% 2.57/0.99      | ~ v7_waybel_0(sK9)
% 2.57/0.99      | v2_struct_0(sK9)
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(unflattening,[status(thm)],[c_2305]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2308,plain,
% 2.57/0.99      ( ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(global_propositional_subsumption,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_2306,c_29,c_28,c_27]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_2309,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9)))
% 2.57/0.99      | k10_yellow_6(sK8,sK9) != k10_yellow_6(sK8,sK9) ),
% 2.57/0.99      inference(renaming,[status(thm)],[c_2308]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3283,plain,
% 2.57/0.99      ( ~ r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9))
% 2.57/0.99      | ~ m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8))
% 2.57/0.99      | ~ r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) ),
% 2.57/0.99      inference(equality_resolution_simp,[status(thm)],[c_2309]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(c_3284,plain,
% 2.57/0.99      ( r3_waybel_9(sK8,sK9,k1_waybel_9(sK8,sK9)) != iProver_top
% 2.57/0.99      | m1_subset_1(k1_waybel_9(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 2.57/0.99      | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 2.57/0.99      | r2_yellow_0(sK8,k2_relset_1(u1_struct_0(sK9),u1_struct_0(sK8),u1_waybel_0(sK8,sK9))) != iProver_top ),
% 2.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3283]) ).
% 2.57/0.99  
% 2.57/0.99  cnf(contradiction,plain,
% 2.57/0.99      ( $false ),
% 2.57/0.99      inference(minisat,
% 2.57/0.99                [status(thm)],
% 2.57/0.99                [c_6237,c_6225,c_6162,c_4948,c_4943,c_4925,c_3284,c_2273,
% 2.57/0.99                 c_2262,c_54,c_53,c_52]) ).
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/0.99  
% 2.57/0.99  ------                               Statistics
% 2.57/0.99  
% 2.57/0.99  ------ General
% 2.57/0.99  
% 2.57/0.99  abstr_ref_over_cycles:                  0
% 2.57/0.99  abstr_ref_under_cycles:                 0
% 2.57/0.99  gc_basic_clause_elim:                   0
% 2.57/0.99  forced_gc_time:                         0
% 2.57/0.99  parsing_time:                           0.012
% 2.57/0.99  unif_index_cands_time:                  0.
% 2.57/0.99  unif_index_add_time:                    0.
% 2.57/0.99  orderings_time:                         0.
% 2.57/0.99  out_proof_time:                         0.023
% 2.57/0.99  total_time:                             0.197
% 2.57/0.99  num_of_symbols:                         82
% 2.57/0.99  num_of_terms:                           2996
% 2.57/0.99  
% 2.57/0.99  ------ Preprocessing
% 2.57/0.99  
% 2.57/0.99  num_of_splits:                          6
% 2.57/0.99  num_of_split_atoms:                     6
% 2.57/0.99  num_of_reused_defs:                     0
% 2.57/0.99  num_eq_ax_congr_red:                    57
% 2.57/0.99  num_of_sem_filtered_clauses:            1
% 2.57/0.99  num_of_subtypes:                        6
% 2.57/0.99  monotx_restored_types:                  0
% 2.57/0.99  sat_num_of_epr_types:                   0
% 2.57/0.99  sat_num_of_non_cyclic_types:            0
% 2.57/0.99  sat_guarded_non_collapsed_types:        1
% 2.57/0.99  num_pure_diseq_elim:                    0
% 2.57/0.99  simp_replaced_by:                       0
% 2.57/0.99  res_preprocessed:                       128
% 2.57/0.99  prep_upred:                             0
% 2.57/0.99  prep_unflattend:                        101
% 2.57/0.99  smt_new_axioms:                         0
% 2.57/0.99  pred_elim_cands:                        5
% 2.57/0.99  pred_elim:                              18
% 2.57/0.99  pred_elim_cl:                           21
% 2.57/0.99  pred_elim_cycles:                       25
% 2.57/0.99  merged_defs:                            0
% 2.57/0.99  merged_defs_ncl:                        0
% 2.57/0.99  bin_hyper_res:                          0
% 2.57/0.99  prep_cycles:                            4
% 2.57/0.99  pred_elim_time:                         0.075
% 2.57/0.99  splitting_time:                         0.
% 2.57/0.99  sem_filter_time:                        0.
% 2.57/0.99  monotx_time:                            0.
% 2.57/0.99  subtype_inf_time:                       0.
% 2.57/0.99  
% 2.57/0.99  ------ Problem properties
% 2.57/0.99  
% 2.57/0.99  clauses:                                25
% 2.57/0.99  conjectures:                            0
% 2.57/0.99  epr:                                    3
% 2.57/0.99  horn:                                   17
% 2.57/0.99  ground:                                 10
% 2.57/0.99  unary:                                  2
% 2.57/0.99  binary:                                 5
% 2.57/0.99  lits:                                   85
% 2.57/0.99  lits_eq:                                6
% 2.57/0.99  fd_pure:                                0
% 2.57/0.99  fd_pseudo:                              0
% 2.57/0.99  fd_cond:                                2
% 2.57/0.99  fd_pseudo_cond:                         0
% 2.57/0.99  ac_symbols:                             0
% 2.57/0.99  
% 2.57/0.99  ------ Propositional Solver
% 2.57/0.99  
% 2.57/0.99  prop_solver_calls:                      28
% 2.57/0.99  prop_fast_solver_calls:                 2357
% 2.57/0.99  smt_solver_calls:                       0
% 2.57/0.99  smt_fast_solver_calls:                  0
% 2.57/0.99  prop_num_of_clauses:                    1320
% 2.57/0.99  prop_preprocess_simplified:             4676
% 2.57/0.99  prop_fo_subsumed:                       163
% 2.57/0.99  prop_solver_time:                       0.
% 2.57/0.99  smt_solver_time:                        0.
% 2.57/0.99  smt_fast_solver_time:                   0.
% 2.57/0.99  prop_fast_solver_time:                  0.
% 2.57/0.99  prop_unsat_core_time:                   0.
% 2.57/0.99  
% 2.57/0.99  ------ QBF
% 2.57/0.99  
% 2.57/0.99  qbf_q_res:                              0
% 2.57/0.99  qbf_num_tautologies:                    0
% 2.57/0.99  qbf_prep_cycles:                        0
% 2.57/0.99  
% 2.57/0.99  ------ BMC1
% 2.57/0.99  
% 2.57/0.99  bmc1_current_bound:                     -1
% 2.57/0.99  bmc1_last_solved_bound:                 -1
% 2.57/0.99  bmc1_unsat_core_size:                   -1
% 2.57/0.99  bmc1_unsat_core_parents_size:           -1
% 2.57/0.99  bmc1_merge_next_fun:                    0
% 2.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.57/0.99  
% 2.57/0.99  ------ Instantiation
% 2.57/0.99  
% 2.57/0.99  inst_num_of_clauses:                    236
% 2.57/0.99  inst_num_in_passive:                    22
% 2.57/0.99  inst_num_in_active:                     188
% 2.57/0.99  inst_num_in_unprocessed:                26
% 2.57/0.99  inst_num_of_loops:                      210
% 2.57/0.99  inst_num_of_learning_restarts:          0
% 2.57/0.99  inst_num_moves_active_passive:          18
% 2.57/0.99  inst_lit_activity:                      0
% 2.57/0.99  inst_lit_activity_moves:                0
% 2.57/0.99  inst_num_tautologies:                   0
% 2.57/0.99  inst_num_prop_implied:                  0
% 2.57/0.99  inst_num_existing_simplified:           0
% 2.57/0.99  inst_num_eq_res_simplified:             0
% 2.57/0.99  inst_num_child_elim:                    0
% 2.57/0.99  inst_num_of_dismatching_blockings:      1
% 2.57/0.99  inst_num_of_non_proper_insts:           203
% 2.57/0.99  inst_num_of_duplicates:                 0
% 2.57/0.99  inst_inst_num_from_inst_to_res:         0
% 2.57/0.99  inst_dismatching_checking_time:         0.
% 2.57/0.99  
% 2.57/0.99  ------ Resolution
% 2.57/0.99  
% 2.57/0.99  res_num_of_clauses:                     0
% 2.57/0.99  res_num_in_passive:                     0
% 2.57/0.99  res_num_in_active:                      0
% 2.57/0.99  res_num_of_loops:                       132
% 2.57/0.99  res_forward_subset_subsumed:            6
% 2.57/0.99  res_backward_subset_subsumed:           0
% 2.57/0.99  res_forward_subsumed:                   0
% 2.57/0.99  res_backward_subsumed:                  0
% 2.57/0.99  res_forward_subsumption_resolution:     5
% 2.57/0.99  res_backward_subsumption_resolution:    0
% 2.57/0.99  res_clause_to_clause_subsumption:       186
% 2.57/0.99  res_orphan_elimination:                 0
% 2.57/0.99  res_tautology_del:                      44
% 2.57/0.99  res_num_eq_res_simplified:              5
% 2.57/0.99  res_num_sel_changes:                    0
% 2.57/0.99  res_moves_from_active_to_pass:          0
% 2.57/0.99  
% 2.57/0.99  ------ Superposition
% 2.57/0.99  
% 2.57/0.99  sup_time_total:                         0.
% 2.57/0.99  sup_time_generating:                    0.
% 2.57/0.99  sup_time_sim_full:                      0.
% 2.57/0.99  sup_time_sim_immed:                     0.
% 2.57/0.99  
% 2.57/0.99  sup_num_of_clauses:                     39
% 2.57/0.99  sup_num_in_active:                      33
% 2.57/0.99  sup_num_in_passive:                     6
% 2.57/0.99  sup_num_of_loops:                       41
% 2.57/0.99  sup_fw_superposition:                   12
% 2.57/0.99  sup_bw_superposition:                   11
% 2.57/0.99  sup_immediate_simplified:               2
% 2.57/0.99  sup_given_eliminated:                   0
% 2.57/0.99  comparisons_done:                       0
% 2.57/0.99  comparisons_avoided:                    0
% 2.57/0.99  
% 2.57/0.99  ------ Simplifications
% 2.57/0.99  
% 2.57/0.99  
% 2.57/0.99  sim_fw_subset_subsumed:                 2
% 2.57/0.99  sim_bw_subset_subsumed:                 7
% 2.57/0.99  sim_fw_subsumed:                        0
% 2.57/0.99  sim_bw_subsumed:                        0
% 2.57/0.99  sim_fw_subsumption_res:                 1
% 2.57/0.99  sim_bw_subsumption_res:                 0
% 2.57/0.99  sim_tautology_del:                      1
% 2.57/0.99  sim_eq_tautology_del:                   1
% 2.57/0.99  sim_eq_res_simp:                        0
% 2.57/0.99  sim_fw_demodulated:                     0
% 2.57/0.99  sim_bw_demodulated:                     4
% 2.57/0.99  sim_light_normalised:                   0
% 2.57/0.99  sim_joinable_taut:                      0
% 2.57/0.99  sim_joinable_simp:                      0
% 2.57/0.99  sim_ac_normalised:                      0
% 2.57/0.99  sim_smt_subsumption:                    0
% 2.57/0.99  
%------------------------------------------------------------------------------
