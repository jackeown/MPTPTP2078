%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:03 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 382 expanded)
%              Number of clauses        :   47 (  67 expanded)
%              Number of leaves         :   10 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  527 (3526 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_waybel_9(X0,X1,X3)
          & r3_waybel_9(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_waybel_9(X0,X1,sK4)
        & r3_waybel_9(X0,X2,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_waybel_9(X0,X1,X3)
              & r3_waybel_9(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m2_yellow_6(X2,X0,X1) )
     => ( ? [X3] :
            ( ~ r3_waybel_9(X0,X1,X3)
            & r3_waybel_9(X0,sK3,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m2_yellow_6(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_waybel_9(X0,sK2,X3)
                & r3_waybel_9(X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m2_yellow_6(X2,X0,sK2) )
        & l1_waybel_0(sK2,X0)
        & v7_waybel_0(sK2)
        & v4_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_waybel_9(X0,X1,X3)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(sK1,X1,X3)
                  & r3_waybel_9(sK1,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m2_yellow_6(X2,sK1,X1) )
          & l1_waybel_0(X1,sK1)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r3_waybel_9(sK1,sK2,sK4)
    & r3_waybel_9(sK1,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m2_yellow_6(sK3,sK1,sK2)
    & l1_waybel_0(sK2,sK1)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f23,f22,f21,f20])).

fof(f41,plain,(
    m2_yellow_6(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK0(X0,X1,X2))
        & m1_connsp_2(sK0(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK0(X0,X1,X2))
                    & m1_connsp_2(sK0(X0,X1,X2),X0,X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK0(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ~ r3_waybel_9(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    r3_waybel_9(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( m2_yellow_6(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ r2_waybel_0(X1,X0,X3)
    | r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_290,plain,
    ( l1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_17])).

cnf(c_298,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ r2_waybel_0(sK1,X0,X2)
    | r2_waybel_0(sK1,X1,X2)
    | ~ l1_waybel_0(X1,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_8,c_290])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_300,plain,
    ( v2_struct_0(X1)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,sK1)
    | r2_waybel_0(sK1,X1,X2)
    | ~ r2_waybel_0(sK1,X0,X2)
    | ~ m2_yellow_6(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_19])).

cnf(c_301,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ r2_waybel_0(sK1,X0,X2)
    | r2_waybel_0(sK1,X1,X2)
    | ~ l1_waybel_0(X1,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_502,plain,
    ( ~ r2_waybel_0(sK1,sK3,X0)
    | r2_waybel_0(sK1,sK2,X0)
    | ~ l1_waybel_0(sK2,sK1)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_12,c_301])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_506,plain,
    ( ~ r2_waybel_0(sK1,sK3,X0)
    | r2_waybel_0(sK1,sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_16,c_15,c_14,c_13])).

cnf(c_591,plain,
    ( ~ r2_waybel_0(sK1,sK3,X0_47)
    | r2_waybel_0(sK1,sK2,X0_47) ),
    inference(subtyping,[status(esa)],[c_506])).

cnf(c_657,plain,
    ( ~ r2_waybel_0(sK1,sK3,sK0(sK1,sK2,sK4))
    | r2_waybel_0(sK1,sK2,sK0(sK1,sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( m1_connsp_2(sK0(X0,X1,X2),X0,X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_waybel_0(X1,X3,X0)
    | ~ r3_waybel_9(X1,X3,X2)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_189,plain,
    ( r2_waybel_0(X0,X1,sK0(X0,X2,X3))
    | ~ r3_waybel_9(X0,X1,X3)
    | r3_waybel_9(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_waybel_0(X2,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_249,plain,
    ( r2_waybel_0(sK1,X0,sK0(sK1,X1,sK4))
    | ~ r3_waybel_9(sK1,X0,sK4)
    | r3_waybel_9(sK1,X1,sK4)
    | ~ l1_waybel_0(X0,sK1)
    | ~ l1_waybel_0(X1,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_189])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_251,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK1)
    | ~ l1_waybel_0(X0,sK1)
    | r3_waybel_9(sK1,X1,sK4)
    | ~ r3_waybel_9(sK1,X0,sK4)
    | r2_waybel_0(sK1,X0,sK0(sK1,X1,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_19,c_18,c_17])).

cnf(c_252,plain,
    ( r2_waybel_0(sK1,X0,sK0(sK1,X1,sK4))
    | ~ r3_waybel_9(sK1,X0,sK4)
    | r3_waybel_9(sK1,X1,sK4)
    | ~ l1_waybel_0(X0,sK1)
    | ~ l1_waybel_0(X1,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_594,plain,
    ( r2_waybel_0(sK1,X0_46,sK0(sK1,X1_46,sK4))
    | ~ r3_waybel_9(sK1,X0_46,sK4)
    | r3_waybel_9(sK1,X1_46,sK4)
    | ~ l1_waybel_0(X0_46,sK1)
    | ~ l1_waybel_0(X1_46,sK1)
    | v2_struct_0(X0_46)
    | v2_struct_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_252])).

cnf(c_648,plain,
    ( r2_waybel_0(sK1,sK3,sK0(sK1,X0_46,sK4))
    | r3_waybel_9(sK1,X0_46,sK4)
    | ~ r3_waybel_9(sK1,sK3,sK4)
    | ~ l1_waybel_0(X0_46,sK1)
    | ~ l1_waybel_0(sK3,sK1)
    | v2_struct_0(X0_46)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_653,plain,
    ( r2_waybel_0(sK1,sK3,sK0(sK1,sK2,sK4))
    | ~ r3_waybel_9(sK1,sK3,sK4)
    | r3_waybel_9(sK1,sK2,sK4)
    | ~ l1_waybel_0(sK3,sK1)
    | ~ l1_waybel_0(sK2,sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_0,plain,
    ( ~ r2_waybel_0(X0,X1,sK0(X0,X1,X2))
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_226,plain,
    ( ~ r2_waybel_0(sK1,X0,sK0(sK1,X0,sK4))
    | r3_waybel_9(sK1,X0,sK4)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_11])).

cnf(c_230,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK1)
    | r3_waybel_9(sK1,X0,sK4)
    | ~ r2_waybel_0(sK1,X0,sK0(sK1,X0,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_19,c_18,c_17])).

cnf(c_231,plain,
    ( ~ r2_waybel_0(sK1,X0,sK0(sK1,X0,sK4))
    | r3_waybel_9(sK1,X0,sK4)
    | ~ l1_waybel_0(X0,sK1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_595,plain,
    ( ~ r2_waybel_0(sK1,X0_46,sK0(sK1,X0_46,sK4))
    | r3_waybel_9(sK1,X0_46,sK4)
    | ~ l1_waybel_0(X0_46,sK1)
    | v2_struct_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_231])).

cnf(c_643,plain,
    ( ~ r2_waybel_0(sK1,sK2,sK0(sK1,sK2,sK4))
    | r3_waybel_9(sK1,sK2,sK4)
    | ~ l1_waybel_0(sK2,sK1)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_7,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_326,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ l1_waybel_0(X1,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_7,c_290])).

cnf(c_328,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,sK1)
    | ~ m2_yellow_6(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_19])).

cnf(c_329,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ l1_waybel_0(X1,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_492,plain,
    ( ~ l1_waybel_0(sK2,sK1)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | ~ v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_12,c_329])).

cnf(c_4,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_401,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ l1_waybel_0(X1,sK1)
    | l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_4,c_290])).

cnf(c_403,plain,
    ( v2_struct_0(X1)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | l1_waybel_0(X0,sK1)
    | ~ l1_waybel_0(X1,sK1)
    | ~ m2_yellow_6(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_19])).

cnf(c_404,plain,
    ( ~ m2_yellow_6(X0,sK1,X1)
    | ~ l1_waybel_0(X1,sK1)
    | l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_462,plain,
    ( l1_waybel_0(sK3,sK1)
    | ~ l1_waybel_0(sK2,sK1)
    | ~ v4_orders_2(sK2)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_12,c_404])).

cnf(c_9,negated_conjecture,
    ( ~ r3_waybel_9(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,negated_conjecture,
    ( r3_waybel_9(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_657,c_653,c_643,c_492,c_462,c_9,c_10,c_13,c_14,c_15,c_16])).


%------------------------------------------------------------------------------
