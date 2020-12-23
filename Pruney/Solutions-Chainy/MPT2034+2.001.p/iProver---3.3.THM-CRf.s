%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:57 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  222 (3202 expanded)
%              Number of clauses        :  164 ( 770 expanded)
%              Number of leaves         :   13 ( 864 expanded)
%              Depth                    :   31
%              Number of atoms          : 1534 (41742 expanded)
%              Number of equality atoms :  373 (2881 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal clause size      :   34 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
                     => ? [X4] :
                          ( r2_hidden(X2,k10_yellow_6(X0,X4))
                          & m2_yellow_6(X4,X0,X3) ) )
                  & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
              | ~ m2_yellow_6(X4,X0,X3) )
          & m2_yellow_6(X3,X0,X1) )
     => ( ! [X4] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
            | ~ m2_yellow_6(X4,X0,sK0(X0,X1,X2)) )
        & m2_yellow_6(sK0(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                    | ~ m2_yellow_6(X4,X0,sK0(X0,X1,X2)) )
                & m2_yellow_6(sK0(X0,X1,X2),X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK0(X0,X1,X2),X0,X1)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0] :
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

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(X0,X1,X4)
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
          & r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5,k10_yellow_6(X0,X1))
        & r3_waybel_9(X0,X1,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(X0,X1,X4)
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,sK4))
            & r3_waybel_9(X0,sK4,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | ~ r3_waybel_9(X0,sK4,X4)
                | ~ r3_waybel_9(X0,sK4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_waybel_0(sK4,X0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
                & r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & ! [X3] :
                ( ! [X4] :
                    ( X3 = X4
                    | ~ r3_waybel_9(X0,X1,X4)
                    | ~ r3_waybel_9(X0,X1,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(sK3,X1))
              & r3_waybel_9(sK3,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(sK3,X1,X4)
                  | ~ r3_waybel_9(sK3,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
              | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
          & l1_waybel_0(X1,sK3)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v1_compts_1(sK3)
      & v8_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4))
    & r3_waybel_9(sK3,sK4,sK5)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & ! [X3] :
        ( ! [X4] :
            ( X3 = X4
            | ~ r3_waybel_9(sK3,sK4,X4)
            | ~ r3_waybel_9(sK3,sK4,X3)
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v1_compts_1(sK3)
    & v8_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f47,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK1(X0,X1))
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK1(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    r3_waybel_9(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X4,X3] :
      ( X3 = X4
      | ~ r3_waybel_9(sK3,sK4,X4)
      | ~ r3_waybel_9(sK3,sK4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
    inference(cnf_transformation,[],[f33])).

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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
        & m2_yellow_6(sK2(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
      | ~ m2_yellow_6(X4,X0,sK0(X0,X1,X2))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( m2_yellow_6(sK0(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_569,plain,
    ( m2_yellow_6(sK0(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_570,plain,
    ( m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_574,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_24,c_20])).

cnf(c_575,plain,
    ( m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_1815,plain,
    ( m2_yellow_6(sK0(sK3,X0_49,X0_50),sK3,X0_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_575])).

cnf(c_2271,plain,
    ( m2_yellow_6(sK0(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1815])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_21,negated_conjecture,
    ( v1_compts_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_257,plain,
    ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_258,plain,
    ( m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_22,negated_conjecture,
    ( v8_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_262,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_258,c_24,c_23,c_22,c_20])).

cnf(c_263,plain,
    ( m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_1820,plain,
    ( m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_2266,plain,
    ( m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_7,plain,
    ( r3_waybel_9(X0,X1,sK1(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v8_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_284,plain,
    ( r3_waybel_9(X0,X1,sK1(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v8_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_285,plain,
    ( r3_waybel_9(sK3,X0,sK1(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | ~ v8_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_289,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK3,X0,sK1(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_24,c_23,c_22,c_20])).

cnf(c_290,plain,
    ( r3_waybel_9(sK3,X0,sK1(sK3,X0))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_1819,plain,
    ( r3_waybel_9(sK3,X0_49,sK1(sK3,X0_49))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_2267,plain,
    ( r3_waybel_9(sK3,X0_49,sK1(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1819])).

cnf(c_9,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_537,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_538,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | r3_waybel_9(sK3,X2,X1)
    | ~ m2_yellow_6(X0,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X2,sK3)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK3,X0,X1)
    | r3_waybel_9(sK3,X2,X1)
    | ~ m2_yellow_6(X0,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X2,sK3)
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_24,c_20])).

cnf(c_541,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | r3_waybel_9(sK3,X2,X1)
    | ~ m2_yellow_6(X0,sK3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X2,sK3)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_1816,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | r3_waybel_9(sK3,X1_49,X0_50)
    | ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_541])).

cnf(c_2270,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | r3_waybel_9(sK3,X1_49,X0_50) = iProver_top
    | m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1816])).

cnf(c_3221,plain,
    ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) != iProver_top
    | r3_waybel_9(sK3,X2_49,sK1(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X0_49,sK3,X2_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X2_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v4_orders_2(X2_49) != iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X2_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_2270])).

cnf(c_3956,plain,
    ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_3221])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_379,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_380,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_702,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_380,c_20])).

cnf(c_703,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_705,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK3)
    | ~ m2_yellow_6(X0,sK3,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_24])).

cnf(c_706,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_705])).

cnf(c_1812,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49)
    | v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_2274,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top
    | v7_waybel_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_3,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_351,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_352,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_728,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_20])).

cnf(c_729,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_731,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK3)
    | ~ m2_yellow_6(X0,sK3,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_24])).

cnf(c_732,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_731])).

cnf(c_1811,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | v4_orders_2(X0_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_732])).

cnf(c_2275,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v4_orders_2(X0_49) = iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_4,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_323,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_324,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_754,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_20])).

cnf(c_755,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_757,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK3)
    | ~ m2_yellow_6(X0,sK3,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_24])).

cnf(c_758,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_757])).

cnf(c_1810,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | ~ v2_struct_0(X0_49)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_2276,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X0_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_1,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_407,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_408,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_676,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_408,c_20])).

cnf(c_677,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | l1_waybel_0(X0,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_679,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK3)
    | ~ l1_waybel_0(X1,sK3)
    | ~ m2_yellow_6(X0,sK3,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_24])).

cnf(c_680,plain,
    ( ~ m2_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | l1_waybel_0(X0,sK3)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_1813,plain,
    ( ~ m2_yellow_6(X0_49,sK3,X1_49)
    | ~ l1_waybel_0(X1_49,sK3)
    | l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_2273,plain,
    ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | l1_waybel_0(X0_49,sK3) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_4004,plain,
    ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) = iProver_top
    | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3956,c_2274,c_2275,c_2276,c_2273])).

cnf(c_13,negated_conjecture,
    ( r3_waybel_9(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1828,negated_conjecture,
    ( r3_waybel_9(sK3,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2258,plain,
    ( r3_waybel_9(sK3,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_15,negated_conjecture,
    ( ~ r3_waybel_9(sK3,sK4,X0)
    | ~ r3_waybel_9(sK3,sK4,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1826,negated_conjecture,
    ( ~ r3_waybel_9(sK3,sK4,X0_50)
    | ~ r3_waybel_9(sK3,sK4,X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK3))
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2260,plain,
    ( X0_50 = X1_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | r3_waybel_9(sK3,sK4,X1_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_2645,plain,
    ( sK5 = X0_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2258,c_2260])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2648,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | sK5 = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_37])).

cnf(c_2649,plain,
    ( sK5 = X0_50
    | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2648])).

cnf(c_4007,plain,
    ( sK1(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_2649])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,plain,
    ( v4_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( v7_waybel_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_33,plain,
    ( l1_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4291,plain,
    ( sK1(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4007,c_30,c_31,c_32,c_33])).

cnf(c_4300,plain,
    ( sK1(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_4291])).

cnf(c_2503,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | v4_orders_2(X0_49)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_2504,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(X0_49) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2503])).

cnf(c_2508,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | v7_waybel_0(X0_49)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1812])).

cnf(c_2509,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(X0_49) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2508])).

cnf(c_2513,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK4)
    | l1_waybel_0(X0_49,sK3)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2514,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | l1_waybel_0(X0_49,sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2513])).

cnf(c_4318,plain,
    ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | sK1(sK3,X0_49) = sK5
    | v2_struct_0(X0_49) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4300,c_30,c_31,c_32,c_33,c_2504,c_2509,c_2514])).

cnf(c_4319,plain,
    ( sK1(sK3,X0_49) = sK5
    | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(renaming,[status(thm)],[c_4318])).

cnf(c_4327,plain,
    ( sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK0(sK3,sK4,X0_50)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_4319])).

cnf(c_2518,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4))
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_2519,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2518])).

cnf(c_2895,plain,
    ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,X0_49)
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v2_struct_0(sK0(sK3,sK4,X0_50))
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1810])).

cnf(c_3180,plain,
    ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ v2_struct_0(sK0(sK3,sK4,X0_50))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_3181,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK0(sK3,sK4,X0_50)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3180])).

cnf(c_4452,plain,
    ( r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_30,c_31,c_32,c_33,c_2519,c_3181])).

cnf(c_4453,plain,
    ( sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4452])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1829,negated_conjecture,
    ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2257,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_4461,plain,
    ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4453,c_2257])).

cnf(c_39,plain,
    ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2521,plain,
    ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_3183,plain,
    ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK0(sK3,sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_4362,plain,
    ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK0(sK3,sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_4538,plain,
    ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4461,c_30,c_31,c_32,c_33,c_37,c_39,c_2521,c_3183,c_4362])).

cnf(c_4543,plain,
    ( r3_waybel_9(sK3,sK0(sK3,sK4,sK5),sK5) = iProver_top
    | l1_waybel_0(sK0(sK3,sK4,sK5),sK3) != iProver_top
    | v2_struct_0(sK0(sK3,sK4,sK5)) = iProver_top
    | v4_orders_2(sK0(sK3,sK4,sK5)) != iProver_top
    | v7_waybel_0(sK0(sK3,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4538,c_2267])).

cnf(c_2597,plain,
    ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | v4_orders_2(sK0(sK3,sK4,X0_50))
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_2598,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK0(sK3,sK4,X0_50)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_2600,plain,
    ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK0(sK3,sK4,sK5)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2598])).

cnf(c_2596,plain,
    ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | v7_waybel_0(sK0(sK3,sK4,X0_50))
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_2602,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK0(sK3,sK4,X0_50)) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2596])).

cnf(c_2604,plain,
    ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK0(sK3,sK4,sK5)) = iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2602])).

cnf(c_2595,plain,
    ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
    | l1_waybel_0(sK0(sK3,sK4,X0_50),sK3)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_2606,plain,
    ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
    | l1_waybel_0(sK0(sK3,sK4,X0_50),sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2595])).

cnf(c_2608,plain,
    ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
    | l1_waybel_0(sK0(sK3,sK4,sK5),sK3) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2606])).

cnf(c_4802,plain,
    ( r3_waybel_9(sK3,sK0(sK3,sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4543,c_30,c_31,c_32,c_33,c_37,c_39,c_2521,c_2600,c_2604,c_2608,c_3183])).

cnf(c_10,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_504,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_505,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_24,c_20])).

cnf(c_510,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_1817,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,X0_49,X0_50)))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_2269,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,X0_49,X0_50))) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_11,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_471,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_472,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_476,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK3,X0,X1)
    | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_24,c_20])).

cnf(c_477,plain,
    ( ~ r3_waybel_9(sK3,X0,X1)
    | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_1818,plain,
    ( ~ r3_waybel_9(sK3,X0_49,X0_50)
    | m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ l1_waybel_0(X0_49,sK3)
    | v2_struct_0(X0_49)
    | ~ v4_orders_2(X0_49)
    | ~ v7_waybel_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_2268,plain,
    ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
    | m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_5,plain,
    ( ~ m2_yellow_6(X0,X1,sK0(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_602,plain,
    ( ~ m2_yellow_6(X0,X1,sK0(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
    | r2_hidden(X3,k10_yellow_6(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_603,plain,
    ( ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_605,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_24,c_20])).

cnf(c_606,plain,
    ( ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
    | r2_hidden(X2,k10_yellow_6(sK3,X1))
    | ~ l1_waybel_0(X1,sK3)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_1814,plain,
    ( ~ m2_yellow_6(X0_49,sK3,sK0(sK3,X1_49,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
    | ~ r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
    | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49))
    | ~ l1_waybel_0(X1_49,sK3)
    | v2_struct_0(X1_49)
    | ~ v4_orders_2(X1_49)
    | ~ v7_waybel_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_606])).

cnf(c_2272,plain,
    ( m2_yellow_6(X0_49,sK3,sK0(sK3,X1_49,X0_50)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49)) = iProver_top
    | l1_waybel_0(X1_49,sK3) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v4_orders_2(X1_49) != iProver_top
    | v7_waybel_0(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_3308,plain,
    ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK0(sK3,X0_49,X0_50)) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK0(sK3,X0_49,X0_50)) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK0(sK3,X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_2272])).

cnf(c_3100,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2273])).

cnf(c_3101,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK0(sK3,X0_49,X0_50)) = iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2275])).

cnf(c_3102,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK0(sK3,X0_49,X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2274])).

cnf(c_3103,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK0(sK3,X0_49,X0_50)) != iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2276])).

cnf(c_5141,plain,
    ( v7_waybel_0(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v4_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3308,c_3100,c_3101,c_3102,c_3103])).

cnf(c_5142,plain,
    ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
    | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_5141])).

cnf(c_5158,plain,
    ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK0(sK3,X0_49,X0_50)) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v4_orders_2(sK0(sK3,X0_49,X0_50)) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top
    | v7_waybel_0(sK0(sK3,X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_5142])).

cnf(c_5243,plain,
    ( v7_waybel_0(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v4_orders_2(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5158,c_3100,c_3101,c_3102,c_3103])).

cnf(c_5244,plain,
    ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
    | l1_waybel_0(X0_49,sK3) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v4_orders_2(X0_49) != iProver_top
    | v7_waybel_0(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_5243])).

cnf(c_5256,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
    | l1_waybel_0(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | v7_waybel_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4802,c_5244])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5256,c_39,c_37,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.99  
% 2.33/0.99  ------  iProver source info
% 2.33/0.99  
% 2.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.99  git: non_committed_changes: false
% 2.33/0.99  git: last_make_outside_of_git: false
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     num_symb
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       true
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  ------ Parsing...
% 2.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 20
% 2.33/0.99  conjectures                             9
% 2.33/0.99  EPR                                     10
% 2.33/0.99  Horn                                    10
% 2.33/0.99  unary                                   8
% 2.33/0.99  binary                                  0
% 2.33/0.99  lits                                    84
% 2.33/0.99  lits eq                                 1
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 0
% 2.33/0.99  fd_pseudo_cond                          1
% 2.33/0.99  AC symbols                              0
% 2.33/0.99  
% 2.33/0.99  ------ Schedule dynamic 5 is on 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  Current options:
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     none
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       false
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ Proving...
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  % SZS status Theorem for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  fof(f3,axiom,(
% 2.33/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3))) & ~r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f13,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,X3)) & m2_yellow_6(X3,X0,X1)) | r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f3])).
% 2.33/0.99  
% 2.33/0.99  fof(f14,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,X3)) & m2_yellow_6(X3,X0,X1)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f13])).
% 2.33/0.99  
% 2.33/0.99  fof(f23,plain,(
% 2.33/0.99    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,X3)) & m2_yellow_6(X3,X0,X1)) => (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,sK0(X0,X1,X2))) & m2_yellow_6(sK0(X0,X1,X2),X0,X1)))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f24,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,sK0(X0,X1,X2))) & m2_yellow_6(sK0(X0,X1,X2),X0,X1)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f23])).
% 2.33/0.99  
% 2.33/0.99  fof(f39,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (m2_yellow_6(sK0(X0,X1,X2),X0,X1) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f24])).
% 2.33/0.99  
% 2.33/0.99  fof(f7,conjecture,(
% 2.33/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f8,negated_conjecture,(
% 2.33/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 2.33/0.99    inference(negated_conjecture,[],[f7])).
% 2.33/0.99  
% 2.33/0.99  fof(f9,plain,(
% 2.33/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 2.33/0.99    inference(rectify,[],[f8])).
% 2.33/0.99  
% 2.33/0.99  fof(f21,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : ((? [X4] : ((~r2_hidden(X4,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X4)) & m1_subset_1(X4,u1_struct_0(X0))) & ! [X2] : (! [X3] : ((X2 = X3 | (~r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f9])).
% 2.33/0.99  
% 2.33/0.99  fof(f22,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X4] : (~r2_hidden(X4,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) & ! [X2] : (! [X3] : (X2 = X3 | ~r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f21])).
% 2.33/0.99  
% 2.33/0.99  fof(f29,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(X0,X1,X4) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/0.99    inference(rectify,[],[f22])).
% 2.33/0.99  
% 2.33/0.99  fof(f32,plain,(
% 2.33/0.99    ( ! [X0,X1] : (? [X2] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (~r2_hidden(sK5,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,sK5) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f31,plain,(
% 2.33/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(X0,X1,X4) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_hidden(X2,k10_yellow_6(X0,sK4)) & r3_waybel_9(X0,sK4,X2) & m1_subset_1(X2,u1_struct_0(X0))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(X0,sK4,X4) | ~r3_waybel_9(X0,sK4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(sK4,X0) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))) )),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f30,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(X0,X1,X4) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_hidden(X2,k10_yellow_6(sK3,X1)) & r3_waybel_9(sK3,X1,X2) & m1_subset_1(X2,u1_struct_0(sK3))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(sK3,X1,X4) | ~r3_waybel_9(sK3,X1,X3) | ~m1_subset_1(X4,u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v1_compts_1(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f33,plain,(
% 2.33/0.99    ((~r2_hidden(sK5,k10_yellow_6(sK3,sK4)) & r3_waybel_9(sK3,sK4,sK5) & m1_subset_1(sK5,u1_struct_0(sK3))) & ! [X3] : (! [X4] : (X3 = X4 | ~r3_waybel_9(sK3,sK4,X4) | ~r3_waybel_9(sK3,sK4,X3) | ~m1_subset_1(X4,u1_struct_0(sK3))) | ~m1_subset_1(X3,u1_struct_0(sK3))) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v1_compts_1(sK3) & v8_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 2.33/0.99  
% 2.33/0.99  fof(f47,plain,(
% 2.33/0.99    v2_pre_topc(sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f46,plain,(
% 2.33/0.99    ~v2_struct_0(sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f50,plain,(
% 2.33/0.99    l1_pre_topc(sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f4,axiom,(
% 2.33/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f15,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f4])).
% 2.33/0.99  
% 2.33/0.99  fof(f16,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f15])).
% 2.33/0.99  
% 2.33/0.99  fof(f25,plain,(
% 2.33/0.99    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f26,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f25])).
% 2.33/0.99  
% 2.33/0.99  fof(f41,plain,(
% 2.33/0.99    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f26])).
% 2.33/0.99  
% 2.33/0.99  fof(f49,plain,(
% 2.33/0.99    v1_compts_1(sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f48,plain,(
% 2.33/0.99    v8_pre_topc(sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f42,plain,(
% 2.33/0.99    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK1(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f26])).
% 2.33/0.99  
% 2.33/0.99  fof(f5,axiom,(
% 2.33/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f17,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f5])).
% 2.33/0.99  
% 2.33/0.99  fof(f18,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f17])).
% 2.33/0.99  
% 2.33/0.99  fof(f43,plain,(
% 2.33/0.99    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f18])).
% 2.33/0.99  
% 2.33/0.99  fof(f1,axiom,(
% 2.33/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f10,plain,(
% 2.33/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.33/0.99    inference(ennf_transformation,[],[f1])).
% 2.33/0.99  
% 2.33/0.99  fof(f34,plain,(
% 2.33/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f10])).
% 2.33/0.99  
% 2.33/0.99  fof(f2,axiom,(
% 2.33/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f11,plain,(
% 2.33/0.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f2])).
% 2.33/0.99  
% 2.33/0.99  fof(f12,plain,(
% 2.33/0.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f11])).
% 2.33/0.99  
% 2.33/0.99  fof(f37,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f12])).
% 2.33/0.99  
% 2.33/0.99  fof(f36,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f12])).
% 2.33/0.99  
% 2.33/0.99  fof(f35,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f12])).
% 2.33/0.99  
% 2.33/0.99  fof(f38,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f12])).
% 2.33/0.99  
% 2.33/0.99  fof(f57,plain,(
% 2.33/0.99    r3_waybel_9(sK3,sK4,sK5)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f55,plain,(
% 2.33/0.99    ( ! [X4,X3] : (X3 = X4 | ~r3_waybel_9(sK3,sK4,X4) | ~r3_waybel_9(sK3,sK4,X3) | ~m1_subset_1(X4,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f56,plain,(
% 2.33/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f51,plain,(
% 2.33/0.99    ~v2_struct_0(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f52,plain,(
% 2.33/0.99    v4_orders_2(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f53,plain,(
% 2.33/0.99    v7_waybel_0(sK4)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f54,plain,(
% 2.33/0.99    l1_waybel_0(sK4,sK3)),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f58,plain,(
% 2.33/0.99    ~r2_hidden(sK5,k10_yellow_6(sK3,sK4))),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f6,axiom,(
% 2.33/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 2.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f19,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f6])).
% 2.33/0.99  
% 2.33/0.99  fof(f20,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f19])).
% 2.33/0.99  
% 2.33/0.99  fof(f27,plain,(
% 2.33/0.99    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & m2_yellow_6(sK2(X0,X1,X2),X0,X1)))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f28,plain,(
% 2.33/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) & m2_yellow_6(sK2(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f27])).
% 2.33/0.99  
% 2.33/0.99  fof(f45,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f28])).
% 2.33/0.99  
% 2.33/0.99  fof(f44,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (m2_yellow_6(sK2(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f28])).
% 2.33/0.99  
% 2.33/0.99  fof(f40,plain,(
% 2.33/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,sK0(X0,X1,X2)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f24])).
% 2.33/0.99  
% 2.33/0.99  cnf(c_6,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(X0,X1,X2),X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_23,negated_conjecture,
% 2.33/0.99      ( v2_pre_topc(sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_569,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(X0,X1,X2),X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_570,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_569]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_24,negated_conjecture,
% 2.33/0.99      ( ~ v2_struct_0(sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_20,negated_conjecture,
% 2.33/0.99      ( l1_pre_topc(sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_574,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_570,c_24,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_575,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_574]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1815,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,X0_49,X0_50),sK3,X0_49)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_575]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2271,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1815]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_8,plain,
% 2.33/0.99      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v8_pre_topc(X0)
% 2.33/0.99      | ~ v1_compts_1(X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_21,negated_conjecture,
% 2.33/0.99      ( v1_compts_1(sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_257,plain,
% 2.33/0.99      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v8_pre_topc(X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_258,plain,
% 2.33/0.99      ( m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | ~ v8_pre_topc(sK3)
% 2.33/0.99      | ~ v2_pre_topc(sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_257]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_22,negated_conjecture,
% 2.33/0.99      ( v8_pre_topc(sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_262,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_258,c_24,c_23,c_22,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_263,plain,
% 2.33/0.99      ( m1_subset_1(sK1(sK3,X0),u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_262]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1820,plain,
% 2.33/0.99      ( m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_263]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2266,plain,
% 2.33/0.99      ( m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_7,plain,
% 2.33/0.99      ( r3_waybel_9(X0,X1,sK1(X0,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v8_pre_topc(X0)
% 2.33/0.99      | ~ v1_compts_1(X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_284,plain,
% 2.33/0.99      ( r3_waybel_9(X0,X1,sK1(X0,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v8_pre_topc(X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_285,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0,sK1(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | ~ v8_pre_topc(sK3)
% 2.33/0.99      | ~ v2_pre_topc(sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_284]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_289,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | r3_waybel_9(sK3,X0,sK1(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_285,c_24,c_23,c_22,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_290,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0,sK1(sK3,X0))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_289]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1819,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,sK1(sK3,X0_49))
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_290]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2267,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,sK1(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1819]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_9,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | r3_waybel_9(X0,X3,X2)
% 2.33/0.99      | ~ m2_yellow_6(X1,X0,X3)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X3,X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X3)
% 2.33/0.99      | ~ v4_orders_2(X3)
% 2.33/0.99      | ~ v7_waybel_0(X3)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_537,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | r3_waybel_9(X0,X3,X2)
% 2.33/0.99      | ~ m2_yellow_6(X1,X0,X3)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X3,X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X3)
% 2.33/0.99      | ~ v4_orders_2(X3)
% 2.33/0.99      | ~ v7_waybel_0(X3)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_538,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | r3_waybel_9(sK3,X2,X1)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X2)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X2,sK3)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_537]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_540,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | r3_waybel_9(sK3,X2,X1)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X2)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X2,sK3)
% 2.33/0.99      | v2_struct_0(X2) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_538,c_24,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_541,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | r3_waybel_9(sK3,X2,X1)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X2)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X2,sK3)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_540]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1816,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0_49,X0_50)
% 2.33/0.99      | r3_waybel_9(sK3,X1_49,X0_50)
% 2.33/0.99      | ~ m2_yellow_6(X0_49,sK3,X1_49)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_541]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2270,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,X1_49,X0_50) = iProver_top
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1816]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3221,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) != iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,X2_49,sK1(sK3,X1_49)) = iProver_top
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,X2_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(X2_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v2_struct_0(X2_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X2_49) != iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X2_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2266,c_2270]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3956,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) = iProver_top
% 2.33/0.99      | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2267,c_3221]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_0,plain,
% 2.33/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_struct_0(X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_379,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(X3)
% 2.33/0.99      | X1 != X3 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_380,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_379]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_702,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | v7_waybel_0(X0)
% 2.33/0.99      | sK3 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_380,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_703,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | v7_waybel_0(X0) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_702]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_705,plain,
% 2.33/0.99      ( v2_struct_0(X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | v7_waybel_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_703,c_24]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_706,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_705]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1812,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,X1_49)
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49)
% 2.33/0.99      | v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_706]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2274,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_struct_0(X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_351,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X3)
% 2.33/0.99      | X1 != X3 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_352,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_728,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | sK3 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_352,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_729,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_728]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_731,plain,
% 2.33/0.99      ( v2_struct_0(X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_729,c_24]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_732,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_731]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1811,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,X1_49)
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_732]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2275,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) = iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_struct_0(X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_323,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X3)
% 2.33/0.99      | X1 != X3 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_324,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_323]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_754,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | sK3 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_324,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_755,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_754]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_757,plain,
% 2.33/0.99      ( v2_struct_0(X1)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_755,c_24]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_758,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_757]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1810,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,X1_49)
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | ~ v2_struct_0(X0_49)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_758]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2276,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1810]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | l1_waybel_0(X0,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_struct_0(X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_407,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | l1_waybel_0(X0,X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X3)
% 2.33/0.99      | X1 != X3 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_408,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | l1_waybel_0(X0,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_676,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,X2)
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | l1_waybel_0(X0,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | sK3 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_408,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_677,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_679,plain,
% 2.33/0.99      ( v2_struct_0(X1)
% 2.33/0.99      | l1_waybel_0(X0,sK3)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_677,c_24]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_680,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,X1)
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_679]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1813,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,X1_49)
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_680]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2273,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,X1_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) = iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1813]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4004,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,sK1(sK3,X1_49)) = iProver_top
% 2.33/0.99      | m2_yellow_6(X1_49,sK3,X0_49) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(forward_subsumption_resolution,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_3956,c_2274,c_2275,c_2276,c_2273]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_13,negated_conjecture,
% 2.33/0.99      ( r3_waybel_9(sK3,sK4,sK5) ),
% 2.33/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1828,negated_conjecture,
% 2.33/0.99      ( r3_waybel_9(sK3,sK4,sK5) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2258,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK4,sK5) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1828]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_15,negated_conjecture,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,sK4,X0)
% 2.33/0.99      | ~ r3_waybel_9(sK3,sK4,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | X1 = X0 ),
% 2.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1826,negated_conjecture,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,sK4,X0_50)
% 2.33/0.99      | ~ r3_waybel_9(sK3,sK4,X1_50)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | ~ m1_subset_1(X1_50,u1_struct_0(sK3))
% 2.33/0.99      | X1_50 = X0_50 ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2260,plain,
% 2.33/0.99      ( X0_50 = X1_50
% 2.33/0.99      | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,sK4,X1_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2645,plain,
% 2.33/0.99      ( sK5 = X0_50
% 2.33/0.99      | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2258,c_2260]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_14,negated_conjecture,
% 2.33/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.33/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_37,plain,
% 2.33/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2648,plain,
% 2.33/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
% 2.33/0.99      | sK5 = X0_50 ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_2645,c_37]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2649,plain,
% 2.33/0.99      ( sK5 = X0_50
% 2.33/0.99      | r3_waybel_9(sK3,sK4,X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_2648]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4007,plain,
% 2.33/0.99      ( sK1(sK3,X0_49) = sK5
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_4004,c_2649]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_19,negated_conjecture,
% 2.33/0.99      ( ~ v2_struct_0(sK4) ),
% 2.33/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_30,plain,
% 2.33/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_18,negated_conjecture,
% 2.33/0.99      ( v4_orders_2(sK4) ),
% 2.33/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_31,plain,
% 2.33/0.99      ( v4_orders_2(sK4) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_17,negated_conjecture,
% 2.33/0.99      ( v7_waybel_0(sK4) ),
% 2.33/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_32,plain,
% 2.33/0.99      ( v7_waybel_0(sK4) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_16,negated_conjecture,
% 2.33/0.99      ( l1_waybel_0(sK4,sK3) ),
% 2.33/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_33,plain,
% 2.33/0.99      ( l1_waybel_0(sK4,sK3) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4291,plain,
% 2.33/0.99      ( sK1(sK3,X0_49) = sK5
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | m1_subset_1(sK1(sK3,X0_49),u1_struct_0(sK3)) != iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_4007,c_30,c_31,c_32,c_33]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4300,plain,
% 2.33/0.99      ( sK1(sK3,X0_49) = sK5
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2266,c_4291]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2503,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,sK4)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | v4_orders_2(X0_49)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1811]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2504,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2503]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2508,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,sK4)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | v7_waybel_0(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1812]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2509,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) = iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2508]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2513,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,sK4)
% 2.33/0.99      | l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1813]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2514,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2513]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4318,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | sK1(sK3,X0_49) = sK5
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_4300,c_30,c_31,c_32,c_33,c_2504,c_2509,c_2514]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4319,plain,
% 2.33/0.99      ( sK1(sK3,X0_49) = sK5
% 2.33/0.99      | m2_yellow_6(X0_49,sK3,sK4) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_4318]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4327,plain,
% 2.33/0.99      ( sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,sK4,X0_50)) = iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2271,c_4319]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2518,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK4))
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1815]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2519,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) = iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2518]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2895,plain,
% 2.33/0.99      ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,X0_49)
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v2_struct_0(sK0(sK3,sK4,X0_50))
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_1810]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3180,plain,
% 2.33/0.99      ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | ~ v2_struct_0(sK0(sK3,sK4,X0_50))
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2895]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3181,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,sK4,X0_50)) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_3180]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4452,plain,
% 2.33/0.99      ( r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5 ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_4327,c_30,c_31,c_32,c_33,c_2519,c_3181]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4453,plain,
% 2.33/0.99      ( sK1(sK3,sK0(sK3,sK4,X0_50)) = sK5
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK4)) = iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_4452]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_12,negated_conjecture,
% 2.33/0.99      ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
% 2.33/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1829,negated_conjecture,
% 2.33/0.99      ( ~ r2_hidden(sK5,k10_yellow_6(sK3,sK4)) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2257,plain,
% 2.33/0.99      ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4461,plain,
% 2.33/0.99      ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5
% 2.33/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_4453,c_2257]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_39,plain,
% 2.33/0.99      ( r2_hidden(sK5,k10_yellow_6(sK3,sK4)) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2521,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) = iProver_top
% 2.33/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2519]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3183,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,sK4,sK5)) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_3181]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4362,plain,
% 2.33/0.99      ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5
% 2.33/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,sK4,sK5)) = iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_4327]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4538,plain,
% 2.33/0.99      ( sK1(sK3,sK0(sK3,sK4,sK5)) = sK5 ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_4461,c_30,c_31,c_32,c_33,c_37,c_39,c_2521,c_3183,
% 2.33/0.99                 c_4362]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4543,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,sK4,sK5),sK5) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,sK4,sK5),sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,sK4,sK5)) = iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,sK4,sK5)) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,sK4,sK5)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_4538,c_2267]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2597,plain,
% 2.33/0.99      ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | v4_orders_2(sK0(sK3,sK4,X0_50))
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2503]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2598,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,sK4,X0_50)) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2600,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,sK4,sK5)) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2598]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2596,plain,
% 2.33/0.99      ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | v7_waybel_0(sK0(sK3,sK4,X0_50))
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2508]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2602,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,sK4,X0_50)) = iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2596]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2604,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,sK4,sK5)) = iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2602]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2595,plain,
% 2.33/0.99      ( ~ m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4)
% 2.33/0.99      | l1_waybel_0(sK0(sK3,sK4,X0_50),sK3)
% 2.33/0.99      | ~ l1_waybel_0(sK4,sK3)
% 2.33/0.99      | v2_struct_0(sK4)
% 2.33/0.99      | ~ v4_orders_2(sK4)
% 2.33/0.99      | ~ v7_waybel_0(sK4) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2513]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2606,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,X0_50),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,sK4,X0_50),sK3) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2595]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2608,plain,
% 2.33/0.99      ( m2_yellow_6(sK0(sK3,sK4,sK5),sK3,sK4) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,sK4,sK5),sK3) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_2606]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_4802,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,sK4,sK5),sK5) = iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_4543,c_30,c_31,c_32,c_33,c_37,c_39,c_2521,c_2600,
% 2.33/0.99                 c_2604,c_2608,c_3183]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_10,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_504,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(X0,sK2(X0,X1,X2)))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_505,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_504]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_509,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_505,c_24,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_510,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X1,k10_yellow_6(sK3,sK2(sK3,X0,X1)))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_509]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1817,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0_49,X0_50)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,X0_49,X0_50)))
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_510]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2269,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,X0_49,X0_50))) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_11,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | ~ v2_pre_topc(X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_471,plain,
% 2.33/0.99      ( ~ r3_waybel_9(X0,X1,X2)
% 2.33/0.99      | m2_yellow_6(sK2(X0,X1,X2),X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.99      | ~ l1_waybel_0(X1,X0)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(X0)
% 2.33/0.99      | sK3 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_472,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_471]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_476,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_472,c_24,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_477,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0,X1)
% 2.33/0.99      | m2_yellow_6(sK2(sK3,X0,X1),sK3,X0)
% 2.33/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0,sK3)
% 2.33/0.99      | v2_struct_0(X0)
% 2.33/0.99      | ~ v4_orders_2(X0)
% 2.33/0.99      | ~ v7_waybel_0(X0) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_476]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1818,plain,
% 2.33/0.99      ( ~ r3_waybel_9(sK3,X0_49,X0_50)
% 2.33/0.99      | m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49)
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | ~ l1_waybel_0(X0_49,sK3)
% 2.33/0.99      | v2_struct_0(X0_49)
% 2.33/0.99      | ~ v4_orders_2(X0_49)
% 2.33/0.99      | ~ v7_waybel_0(X0_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_477]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2268,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,X0_49,X0_50) != iProver_top
% 2.33/0.99      | m2_yellow_6(sK2(sK3,X0_49,X0_50),sK3,X0_49) = iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,sK0(X1,X2,X3))
% 2.33/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.99      | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
% 2.33/0.99      | r2_hidden(X3,k10_yellow_6(X1,X2))
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | ~ v2_pre_topc(X1)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_602,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,X1,sK0(X1,X2,X3))
% 2.33/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.99      | ~ r2_hidden(X3,k10_yellow_6(X1,X0))
% 2.33/0.99      | r2_hidden(X3,k10_yellow_6(X1,X2))
% 2.33/0.99      | ~ l1_waybel_0(X2,X1)
% 2.33/0.99      | v2_struct_0(X2)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X2)
% 2.33/0.99      | ~ v7_waybel_0(X2)
% 2.33/0.99      | ~ l1_pre_topc(X1)
% 2.33/0.99      | sK3 != X1 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_603,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.33/0.99      | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(sK3,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | v2_struct_0(sK3)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ l1_pre_topc(sK3) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_602]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_605,plain,
% 2.33/0.99      ( ~ v7_waybel_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.33/0.99      | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(sK3,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_603,c_24,c_20]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_606,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0,sK3,sK0(sK3,X1,X2))
% 2.33/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.33/0.99      | ~ r2_hidden(X2,k10_yellow_6(sK3,X0))
% 2.33/0.99      | r2_hidden(X2,k10_yellow_6(sK3,X1))
% 2.33/0.99      | ~ l1_waybel_0(X1,sK3)
% 2.33/0.99      | v2_struct_0(X1)
% 2.33/0.99      | ~ v4_orders_2(X1)
% 2.33/0.99      | ~ v7_waybel_0(X1) ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_605]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1814,plain,
% 2.33/0.99      ( ~ m2_yellow_6(X0_49,sK3,sK0(sK3,X1_49,X0_50))
% 2.33/0.99      | ~ m1_subset_1(X0_50,u1_struct_0(sK3))
% 2.33/0.99      | ~ r2_hidden(X0_50,k10_yellow_6(sK3,X0_49))
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49))
% 2.33/0.99      | ~ l1_waybel_0(X1_49,sK3)
% 2.33/0.99      | v2_struct_0(X1_49)
% 2.33/0.99      | ~ v4_orders_2(X1_49)
% 2.33/0.99      | ~ v7_waybel_0(X1_49) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_606]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_2272,plain,
% 2.33/0.99      ( m2_yellow_6(X0_49,sK3,sK0(sK3,X1_49,X0_50)) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X1_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X1_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X1_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X1_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X1_49) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_1814]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3308,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,X0_49,X0_50)) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,X0_49,X0_50)) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,X0_49,X0_50)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2268,c_2272]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3100,plain,
% 2.33/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) = iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2271,c_2273]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3101,plain,
% 2.33/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,X0_49,X0_50)) = iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2271,c_2275]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3102,plain,
% 2.33/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,X0_49,X0_50)) = iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2271,c_2274]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_3103,plain,
% 2.33/0.99      ( m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,X0_49,X0_50)) != iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2271,c_2276]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5141,plain,
% 2.33/0.99      ( v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_3308,c_3100,c_3101,c_3102,c_3103]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5142,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X1_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X1_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,sK2(sK3,sK0(sK3,X0_49,X0_50),X1_50))) != iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_5141]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5158,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | l1_waybel_0(sK0(sK3,X0_49,X0_50),sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v2_struct_0(sK0(sK3,X0_49,X0_50)) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v4_orders_2(sK0(sK3,X0_49,X0_50)) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK0(sK3,X0_49,X0_50)) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_2269,c_5142]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5243,plain,
% 2.33/0.99      ( v7_waybel_0(X0_49) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_5158,c_3100,c_3101,c_3102,c_3103]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5244,plain,
% 2.33/0.99      ( r3_waybel_9(sK3,sK0(sK3,X0_49,X0_50),X0_50) != iProver_top
% 2.33/0.99      | m1_subset_1(X0_50,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(X0_50,k10_yellow_6(sK3,X0_49)) = iProver_top
% 2.33/0.99      | l1_waybel_0(X0_49,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(X0_49) = iProver_top
% 2.33/0.99      | v4_orders_2(X0_49) != iProver_top
% 2.33/0.99      | v7_waybel_0(X0_49) != iProver_top ),
% 2.33/0.99      inference(renaming,[status(thm)],[c_5243]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_5256,plain,
% 2.33/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 2.33/0.99      | r2_hidden(sK5,k10_yellow_6(sK3,sK4)) = iProver_top
% 2.33/0.99      | l1_waybel_0(sK4,sK3) != iProver_top
% 2.33/0.99      | v2_struct_0(sK4) = iProver_top
% 2.33/0.99      | v4_orders_2(sK4) != iProver_top
% 2.33/0.99      | v7_waybel_0(sK4) != iProver_top ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_4802,c_5244]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(contradiction,plain,
% 2.33/0.99      ( $false ),
% 2.33/0.99      inference(minisat,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_5256,c_39,c_37,c_33,c_32,c_31,c_30]) ).
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  ------                               Statistics
% 2.33/0.99  
% 2.33/0.99  ------ General
% 2.33/0.99  
% 2.33/0.99  abstr_ref_over_cycles:                  0
% 2.33/0.99  abstr_ref_under_cycles:                 0
% 2.33/0.99  gc_basic_clause_elim:                   0
% 2.33/0.99  forced_gc_time:                         0
% 2.33/0.99  parsing_time:                           0.011
% 2.33/0.99  unif_index_cands_time:                  0.
% 2.33/0.99  unif_index_add_time:                    0.
% 2.33/0.99  orderings_time:                         0.
% 2.33/0.99  out_proof_time:                         0.015
% 2.33/0.99  total_time:                             0.192
% 2.33/0.99  num_of_symbols:                         53
% 2.33/0.99  num_of_terms:                           4097
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing
% 2.33/0.99  
% 2.33/0.99  num_of_splits:                          0
% 2.33/0.99  num_of_split_atoms:                     0
% 2.33/0.99  num_of_reused_defs:                     0
% 2.33/0.99  num_eq_ax_congr_red:                    20
% 2.33/0.99  num_of_sem_filtered_clauses:            1
% 2.33/0.99  num_of_subtypes:                        4
% 2.33/0.99  monotx_restored_types:                  0
% 2.33/0.99  sat_num_of_epr_types:                   0
% 2.33/0.99  sat_num_of_non_cyclic_types:            0
% 2.33/0.99  sat_guarded_non_collapsed_types:        1
% 2.33/0.99  num_pure_diseq_elim:                    0
% 2.33/0.99  simp_replaced_by:                       0
% 2.33/0.99  res_preprocessed:                       122
% 2.33/0.99  prep_upred:                             0
% 2.33/0.99  prep_unflattend:                        63
% 2.33/0.99  smt_new_axioms:                         0
% 2.33/0.99  pred_elim_cands:                        8
% 2.33/0.99  pred_elim:                              5
% 2.33/0.99  pred_elim_cl:                           5
% 2.33/0.99  pred_elim_cycles:                       7
% 2.33/0.99  merged_defs:                            0
% 2.33/0.99  merged_defs_ncl:                        0
% 2.33/0.99  bin_hyper_res:                          0
% 2.33/0.99  prep_cycles:                            4
% 2.33/0.99  pred_elim_time:                         0.029
% 2.33/0.99  splitting_time:                         0.
% 2.33/0.99  sem_filter_time:                        0.
% 2.33/0.99  monotx_time:                            0.
% 2.33/0.99  subtype_inf_time:                       0.
% 2.33/0.99  
% 2.33/0.99  ------ Problem properties
% 2.33/0.99  
% 2.33/0.99  clauses:                                20
% 2.33/0.99  conjectures:                            9
% 2.33/0.99  epr:                                    10
% 2.33/0.99  horn:                                   10
% 2.33/0.99  ground:                                 8
% 2.33/0.99  unary:                                  8
% 2.33/0.99  binary:                                 0
% 2.33/0.99  lits:                                   84
% 2.33/0.99  lits_eq:                                1
% 2.33/0.99  fd_pure:                                0
% 2.33/0.99  fd_pseudo:                              0
% 2.33/0.99  fd_cond:                                0
% 2.33/0.99  fd_pseudo_cond:                         1
% 2.33/0.99  ac_symbols:                             0
% 2.33/0.99  
% 2.33/0.99  ------ Propositional Solver
% 2.33/0.99  
% 2.33/0.99  prop_solver_calls:                      27
% 2.33/0.99  prop_fast_solver_calls:                 1735
% 2.33/0.99  smt_solver_calls:                       0
% 2.33/0.99  smt_fast_solver_calls:                  0
% 2.33/0.99  prop_num_of_clauses:                    1276
% 2.33/0.99  prop_preprocess_simplified:             5090
% 2.33/0.99  prop_fo_subsumed:                       85
% 2.33/0.99  prop_solver_time:                       0.
% 2.33/0.99  smt_solver_time:                        0.
% 2.33/0.99  smt_fast_solver_time:                   0.
% 2.33/0.99  prop_fast_solver_time:                  0.
% 2.33/0.99  prop_unsat_core_time:                   0.
% 2.33/0.99  
% 2.33/0.99  ------ QBF
% 2.33/0.99  
% 2.33/0.99  qbf_q_res:                              0
% 2.33/0.99  qbf_num_tautologies:                    0
% 2.33/0.99  qbf_prep_cycles:                        0
% 2.33/0.99  
% 2.33/0.99  ------ BMC1
% 2.33/0.99  
% 2.33/0.99  bmc1_current_bound:                     -1
% 2.33/0.99  bmc1_last_solved_bound:                 -1
% 2.33/0.99  bmc1_unsat_core_size:                   -1
% 2.33/0.99  bmc1_unsat_core_parents_size:           -1
% 2.33/0.99  bmc1_merge_next_fun:                    0
% 2.33/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation
% 2.33/0.99  
% 2.33/0.99  inst_num_of_clauses:                    356
% 2.33/0.99  inst_num_in_passive:                    13
% 2.33/0.99  inst_num_in_active:                     243
% 2.33/0.99  inst_num_in_unprocessed:                100
% 2.33/0.99  inst_num_of_loops:                      270
% 2.33/0.99  inst_num_of_learning_restarts:          0
% 2.33/0.99  inst_num_moves_active_passive:          22
% 2.33/0.99  inst_lit_activity:                      0
% 2.33/0.99  inst_lit_activity_moves:                0
% 2.33/0.99  inst_num_tautologies:                   0
% 2.33/0.99  inst_num_prop_implied:                  0
% 2.33/0.99  inst_num_existing_simplified:           0
% 2.33/0.99  inst_num_eq_res_simplified:             0
% 2.33/0.99  inst_num_child_elim:                    0
% 2.33/0.99  inst_num_of_dismatching_blockings:      14
% 2.33/0.99  inst_num_of_non_proper_insts:           268
% 2.33/0.99  inst_num_of_duplicates:                 0
% 2.33/0.99  inst_inst_num_from_inst_to_res:         0
% 2.33/0.99  inst_dismatching_checking_time:         0.
% 2.33/0.99  
% 2.33/0.99  ------ Resolution
% 2.33/0.99  
% 2.33/0.99  res_num_of_clauses:                     0
% 2.33/0.99  res_num_in_passive:                     0
% 2.33/0.99  res_num_in_active:                      0
% 2.33/0.99  res_num_of_loops:                       126
% 2.33/0.99  res_forward_subset_subsumed:            4
% 2.33/0.99  res_backward_subset_subsumed:           0
% 2.33/0.99  res_forward_subsumed:                   0
% 2.33/0.99  res_backward_subsumed:                  0
% 2.33/0.99  res_forward_subsumption_resolution:     0
% 2.33/0.99  res_backward_subsumption_resolution:    0
% 2.33/0.99  res_clause_to_clause_subsumption:       293
% 2.33/0.99  res_orphan_elimination:                 0
% 2.33/0.99  res_tautology_del:                      22
% 2.33/0.99  res_num_eq_res_simplified:              0
% 2.33/0.99  res_num_sel_changes:                    0
% 2.33/0.99  res_moves_from_active_to_pass:          0
% 2.33/0.99  
% 2.33/0.99  ------ Superposition
% 2.33/0.99  
% 2.33/0.99  sup_time_total:                         0.
% 2.33/0.99  sup_time_generating:                    0.
% 2.33/0.99  sup_time_sim_full:                      0.
% 2.33/0.99  sup_time_sim_immed:                     0.
% 2.33/0.99  
% 2.33/0.99  sup_num_of_clauses:                     62
% 2.33/0.99  sup_num_in_active:                      53
% 2.33/0.99  sup_num_in_passive:                     9
% 2.33/0.99  sup_num_of_loops:                       53
% 2.33/0.99  sup_fw_superposition:                   34
% 2.33/0.99  sup_bw_superposition:                   32
% 2.33/0.99  sup_immediate_simplified:               19
% 2.33/0.99  sup_given_eliminated:                   0
% 2.33/0.99  comparisons_done:                       0
% 2.33/0.99  comparisons_avoided:                    0
% 2.33/0.99  
% 2.33/0.99  ------ Simplifications
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  sim_fw_subset_subsumed:                 9
% 2.33/0.99  sim_bw_subset_subsumed:                 2
% 2.33/0.99  sim_fw_subsumed:                        8
% 2.33/0.99  sim_bw_subsumed:                        0
% 2.33/0.99  sim_fw_subsumption_res:                 4
% 2.33/0.99  sim_bw_subsumption_res:                 0
% 2.33/0.99  sim_tautology_del:                      0
% 2.33/0.99  sim_eq_tautology_del:                   2
% 2.33/0.99  sim_eq_res_simp:                        0
% 2.33/0.99  sim_fw_demodulated:                     3
% 2.33/0.99  sim_bw_demodulated:                     1
% 2.33/0.99  sim_light_normalised:                   5
% 2.33/0.99  sim_joinable_taut:                      0
% 2.33/0.99  sim_joinable_simp:                      0
% 2.33/0.99  sim_ac_normalised:                      0
% 2.33/0.99  sim_smt_subsumption:                    0
% 2.33/0.99  
%------------------------------------------------------------------------------
